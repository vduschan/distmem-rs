use std::{collections::HashMap, sync::Arc};

use bincode::{
    Decode, Encode,
    error::{DecodeError, EncodeError},
};
use futures::{SinkExt, StreamExt};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::{
    net::{
        TcpStream,
        tcp::{OwnedReadHalf, OwnedWriteHalf},
    },
    sync::{Mutex, oneshot},
};
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

#[derive(Debug, Default)]
pub struct RequestIdFactory(usize);
impl RequestIdFactory {
    #[allow(dead_code)]
    pub fn get(&mut self) -> RequestId {
        let id = RequestId(self.0);
        self.0 += 1;
        id
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub struct RequestId(usize);

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Request {
    Ping(usize),
}

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Response {
    Ping(usize),
}

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Message {
    Request(RequestId, Request),
    Response(RequestId, Response),
}

#[allow(dead_code)]
pub fn new_transport(stream: TcpStream) -> (Arc<TransportSender>, TransportReceiver) {
    let stream = stream.into_split();
    let reader = FramedRead::new(stream.0, LengthDelimitedCodec::new());
    let writer = FramedWrite::new(stream.1, LengthDelimitedCodec::new());

    let sender = Arc::new(TransportSender {
        requests: Default::default(),
        writer: Mutex::new(writer),
    });
    let receiver = TransportReceiver {
        reader,
        sender: sender.clone(),
    };
    (sender, receiver)
}

pub struct TransportSender {
    requests: Mutex<(RequestIdFactory, HashMap<RequestId, oneshot::Sender<Response>>)>,
    writer: Mutex<FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>>,
}

#[derive(Debug, Error)]
pub enum TransportError {
    #[error("Encoding error: {err}")]
    EncodingError { err: EncodeError },

    #[error("Decoding error: {err}")]
    DecodingError { err: DecodeError },

    #[error("Medium error: {err}")]
    MediumError { err: String },

    #[error("Medium closed")]
    MediumClosed,
}

impl TransportSender {
    async fn send_msg(&self, msg: Message) -> Result<(), TransportError> {
        let msg: Vec<u8> = bincode::encode_to_vec(&msg, bincode::config::standard())
            .map_err(|err| TransportError::EncodingError { err })?;
        self.writer
            .lock()
            .await
            .send(msg.into())
            .await
            .map_err(|err| TransportError::MediumError { err: err.to_string() })?;
        Ok(())
    }
    #[allow(dead_code)]
    pub async fn request(&self, request: Request) -> Result<Response, TransportError> {
        let (request_id, response_receiver) = {
            let mut requests = self.requests.lock().await;

            let request_id = requests.0.get();
            let (response_sender, response_receiver) = oneshot::channel();
            requests.1.insert(request_id, response_sender);

            (request_id, response_receiver)
        };

        self.send_msg(Message::Request(request_id, request)).await?;
        Ok(response_receiver
            .await
            .expect("invariant: response_sender shouldn't be dropped"))
    }
    async fn complete_request(&self, request_id: RequestId, response: Response) {
        let response_sender = self
            .requests
            .lock()
            .await
            .1
            .remove(&request_id)
            .expect("invariant: response_sender should exist");
        response_sender
            .send(response)
            .expect("invariant: esponse_receiver shouldn't be dropped")
    }
}

pub struct TransportReceiver {
    reader: FramedRead<OwnedReadHalf, LengthDelimitedCodec>,
    sender: Arc<TransportSender>,
}
impl TransportReceiver {
    #[allow(dead_code)]
    pub async fn recv(&mut self) -> Result<PendingRequest, TransportError> {
        loop {
            let msg = self.reader.next().await.ok_or(TransportError::MediumClosed)?;
            let msg = msg.map_err(|err| TransportError::MediumError { err: err.to_string() })?;
            let (msg, _decoded_bytes) = bincode::decode_from_slice::<Message, _>(&msg, bincode::config::standard())
                .map_err(|err| TransportError::DecodingError { err })?;

            match msg {
                Message::Request(request_id, request) => {
                    return Ok(PendingRequest {
                        request: (request_id, request),
                        sender: self.sender.clone(),
                    });
                }
                Message::Response(request_id, response) => self.sender.complete_request(request_id, response).await,
            }
        }
    }
}

pub struct PendingRequest {
    request: (RequestId, Request),
    sender: Arc<TransportSender>,
}
impl PendingRequest {
    #[allow(dead_code)]
    pub fn request(&self) -> &Request {
        &self.request.1
    }
    #[allow(dead_code)]
    pub async fn complete_request(self, response: Response) -> Result<(), TransportError> {
        self.sender.send_msg(Message::Response(self.request.0, response)).await
    }
}

#[cfg(test)]
mod tests {
    use tokio::net::TcpListener;

    use super::*;

    #[tokio::test]
    async fn test_transport() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();

        let peer_0 = TcpStream::connect(addr).await.unwrap();
        let (peer_0_sender, mut peer_0_receiver) = new_transport(peer_0);
        tokio::spawn(async move {
            loop {
                let request = peer_0_receiver.recv().await.unwrap();
                tokio::spawn(async move {
                    println!("peer_0 got {:?} request", request.request());
                    assert!(matches!(request.request(), Request::Ping(1)));
                    request.complete_request(Response::Ping(2)).await.unwrap();
                });
            }
        });

        let peer_1 = listener.accept().await.unwrap().0;
        let (peer_1_sender, mut peer_1_receiver) = new_transport(peer_1);
        tokio::spawn(async move {
            loop {
                let request = peer_1_receiver.recv().await.unwrap();
                tokio::spawn(async move {
                    println!("peer_1 got {:?} request", request.request());
                    assert!(matches!(request.request(), Request::Ping(0)));
                    request.complete_request(Response::Ping(3)).await.unwrap();
                });
            }
        });

        let response_0 = peer_0_sender.request(Request::Ping(0)).await.unwrap();
        println!("peer_0 got {:?} response", response_0);
        assert!(matches!(response_0, Response::Ping(3)));

        let response_1 = peer_1_sender.request(Request::Ping(1)).await.unwrap();
        println!("peer_1 got {:?} response", response_1);
        assert!(matches!(response_1, Response::Ping(2)));
    }
}
