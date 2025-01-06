use std::collections::VecDeque;
use std::io::{self, prelude::*, Error, ErrorKind};
use std::net::{TcpListener, TcpStream};
use std::sync::Mutex;
use std::thread;
use std::time::Duration;

const DEFAULT_TIMEOUT: Option<Duration> = Some(Duration::from_millis(1000));

fn main() -> io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:7878")?;

    let storage: Mutex<VecDeque<String>> = Mutex::new(VecDeque::new());

    thread::scope(|s| {
        // accept connections and process them one at a time
        for stream in listener.incoming() {
            match stream {
                Ok(stream) => {
                    println!("Got client {:?}", stream.peer_addr());
                    // leak the join handle: this is okay, as the OS will clean up after us,
                    // and we don't care about waiting for it to finish
                    let _join_handle = s.spawn(|| {
                        if let Err(e) = handle_client(stream, &storage) {
                            println!("Error handling client: {:?}", e);
                        }
                    });
                }
                Err(e) => {
                    println!("Error connecting: {:?}", e);
                }
            }
        }
    });

    Ok(())
}

/// Process a single connection from a single client.
///
/// Drops the stream when it has finished.
fn handle_client(mut stream: TcpStream, storage_ref: &Mutex<VecDeque<String>>) -> io::Result<()> {
    stream.set_read_timeout(DEFAULT_TIMEOUT)?;
    stream.set_write_timeout(DEFAULT_TIMEOUT)?;

    let mut buffer = String::new();
    stream.read_to_string(&mut buffer)?;
    println!("Received: {:?}", buffer);

    let command = match simple_db::parse(&buffer) {
        Ok(s) => s,
        Err(e) => {
            println!("Error parsing command: {:?}", e);
            writeln!(stream, "Error: {}!", e)?;
            return Ok(());
        }
    };

    println!("Got command {:?}", command);

    let mut guard = storage_ref
        .lock()
        .map_err(|_e| Error::new(ErrorKind::Other, "Failed to lock storage mutex!"))?;

    match command {
        simple_db::Command::Publish(message) => {
            guard.push_back(message);
            writeln!(stream, "OK")?;
        }
        simple_db::Command::Retrieve => match guard.pop_front() {
            Some(message) => writeln!(stream, "Got: {:?}", message)?,
            None => writeln!(stream, "Error: Queue empty!")?,
        },
    }
    Ok(())
}
