use std::{net::SocketAddr, num::NonZeroUsize, process};

use distmem_rs::distmem::DistAddrSpace;
use nix::{
    libc::EXIT_SUCCESS,
    sys::wait::{WaitStatus, waitpid},
    unistd::{ForkResult, fork},
};
use tokio::{
    net::{TcpListener, TcpStream},
    runtime::Runtime,
};

#[test]
fn test_distmem() {
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    match unsafe { fork() }.unwrap() {
        ForkResult::Parent { child } => {
            drop(listener);

            let rt = Runtime::new().unwrap();
            rt.block_on(async move {
                parent(addr).await;
            });

            let child_status = waitpid(child, None).unwrap();
            assert!(matches!(child_status, WaitStatus::Exited(_child, EXIT_SUCCESS)));
        }
        ForkResult::Child => {
            let rt = Runtime::new().unwrap();
            rt.block_on(async move { child(listener).await });
            process::exit(EXIT_SUCCESS);
        }
    }
}

async fn parent(addr: SocketAddr) {
    let stream = TcpStream::connect(addr).await.unwrap();
    println!("Parent got TcpStream");

    let _addrspace = DistAddrSpace::new(stream, true);
}

async fn child(listener: std::net::TcpListener) {
    listener.set_nonblocking(true).unwrap();
    let listener = TcpListener::from_std(listener).unwrap();

    let stream = listener.accept().await.unwrap().0;
    println!("Child got TcpStream");

    let addrspace = DistAddrSpace::new(stream, true);
    let reserved = addrspace
        .reserve_any(NonZeroUsize::new(1024 * 1024 * 1024 /* 1GB */).unwrap())
        .await;
    println!("Child reserved {:?}", reserved);
}
