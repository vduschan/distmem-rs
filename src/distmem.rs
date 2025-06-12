use std::{num::NonZeroUsize, sync::Arc};

use tokio::{
    net::TcpStream,
    sync::{RwLock, mpsc, oneshot},
    task::JoinHandle,
};

use crate::{
    interceptmem::{
        addr_space::{AddrSpace, PageFaultBuffer, PageFaultReceiverAsync, PageFaultReceiverError},
        page_addr::PageAddr,
    },
    nonempty_range::NonEmptyRange,
    transport::{Request, Response, TransportReceiver, TransportSender, new_transport},
};

#[allow(dead_code)]
struct State {
    addrspace: AddrSpace,
}

mod engine {
    use crate::{interceptmem::addr_space::PageFault, transport::PendingRequest};

    use super::*;

    async fn handle_transport_request(request: PendingRequest, state: Arc<RwLock<State>>) {
        let response = match request.request() {
            Request::Ping(val) => Response::Ping(*val),
            Request::Reserve(range) => {
                let ret = state.write().await.addrspace.reserve(range).map_err(|_err| ());
                Response::Reserve(ret)
            }
        };
        request.complete_request(response).await.unwrap();
    }

    async fn transport_handler(mut transport_receiver: TransportReceiver, state: Arc<RwLock<State>>) {
        while let Ok(request) = transport_receiver.recv().await {
            let state = state.clone();
            tokio::spawn(async move {
                handle_transport_request(request, state).await;
            });
        }
    }

    async fn request_handler(
        mut request_receiver: mpsc::Receiver<(Request, oneshot::Sender<Response>)>,
        transport_sender: Arc<TransportSender>,
    ) {
        while let Some((request, response_sender)) = request_receiver.recv().await {
            let transport_sender = transport_sender.clone();
            tokio::spawn(async move {
                let response = transport_sender.request(request).await.unwrap();
                response_sender.send(response).unwrap();
            });
        }
    }

    async fn handle_pagefault(
        _pagefault: PageFault,
        _transport_sender: Arc<TransportSender>,
        _state: Arc<RwLock<State>>,
    ) {
        todo!()
    }

    async fn pagefault_handler(
        mut pagefault_receiver: PageFaultReceiverAsync,
        transport_sender: Arc<TransportSender>,
        state: Arc<RwLock<State>>,
    ) {
        let mut buf = PageFaultBuffer::new(NonZeroUsize::new(1000).unwrap());
        loop {
            let pagefaults = match pagefault_receiver.recv(&mut buf).await {
                Ok(faults) => faults,
                Err(PageFaultReceiverError::AddrSpaceDropped) => return,
                Err(err) => panic!("failed receiving the pagefaults: {:?}", err),
            };
            for pagefault in pagefaults {
                let transport_sender = transport_sender.clone();
                let state = state.clone();
                tokio::spawn(async move { handle_pagefault(pagefault, transport_sender, state).await });
            }
        }
    }

    pub async fn run(
        stream: TcpStream,
        request_receiver: mpsc::Receiver<(Request, oneshot::Sender<Response>)>,
        pagefault_receiver: PageFaultReceiverAsync,
        state: Arc<RwLock<State>>,
    ) {
        let (transport_sender, transport_receiver) = new_transport(stream);

        let transport_handler = {
            let state = state.clone();
            tokio::spawn(async move { transport_handler(transport_receiver, state).await })
        };

        let request_handler = {
            let transport_sender = transport_sender.clone();
            tokio::spawn(async move {
                request_handler(request_receiver, transport_sender).await;
            })
        };

        let pagefault_handler = {
            tokio::spawn(async move {
                pagefault_handler(pagefault_receiver, transport_sender, state).await;
            })
        };

        tokio::try_join!(transport_handler, request_handler, pagefault_handler).unwrap();
    }
}

#[allow(dead_code)]
pub struct DistAddrSpace {
    state: Arc<RwLock<State>>,
    engine: JoinHandle<()>,
    request_sender: mpsc::Sender<(Request, oneshot::Sender<Response>)>,
}

impl DistAddrSpace {
    pub fn new(stream: TcpStream, user_mode_only: bool) -> Self {
        let (addrspace, pagefault_receiver) = AddrSpace::new(user_mode_only).unwrap();
        let state = Arc::new(RwLock::new(State { addrspace }));

        let (request_sender, request_receiver) = mpsc::channel(1024);
        let engine = {
            let state = state.clone();
            tokio::spawn(async move {
                let pagefault_receiver = PageFaultReceiverAsync::from(pagefault_receiver);
                engine::run(stream, request_receiver, pagefault_receiver, state).await;
            })
        };

        DistAddrSpace {
            state,
            engine,
            request_sender,
        }
    }

    #[allow(dead_code)]
    async fn request(&self, request: Request) -> Response {
        let (response_sender, response_receiver) = oneshot::channel();
        self.request_sender.send((request, response_sender)).await.unwrap();
        response_receiver.await.unwrap()
    }

    pub async fn reserve_any(&self, length: NonZeroUsize) -> NonEmptyRange<PageAddr> {
        let mut to_release = Vec::new();
        let reserved = loop {
            let reserved = self.state.write().await.addrspace.reserve_any(length).unwrap();
            if let Response::Reserve(ret) = self.request(Request::Reserve(reserved.clone())).await {
                if ret.is_ok() {
                    break reserved;
                } else {
                    to_release.push(reserved);
                }
            } else {
                panic!("logic error: got wrong response");
            }
        };
        let mut state = self.state.write().await;
        for range in to_release {
            state.addrspace.release(&range).unwrap();
        }
        reserved
    }
}
