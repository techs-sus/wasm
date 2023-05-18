use std::{path::Path, sync::Arc, time::Duration};

use anyhow::Context;
use futures::{
	channel::mpsc::{channel, Receiver},
	lock::Mutex,
	SinkExt, StreamExt,
};
use localtunnel_client::{broadcast, open_tunnel, ClientConfig};
use notify::{Config, Event, RecommendedWatcher, RecursiveMode, Watcher};
use rocket::State;
// use uuid::Uuid;

#[macro_use]
extern crate rocket;

#[get("/wasm_src/<id>")]
async fn wasm_src(state: &State<Data>, id: i32) -> String {
	state.rx.lock().await.next().await.unwrap();
	// beautiful polling :wow:
	std::fs::read_to_string("wasm/roblox/wasm.luau")
		.context("Failed reading file")
		.unwrap()
}

#[derive(Debug)]
struct Data {
	pub uri: String,
	pub rx: Arc<Mutex<Receiver<notify::Result<Event>>>>,
}

#[get("/dev")]
fn index(data: &State<Data>) -> Option<String> {
	let src = std::fs::read_to_string("./dev_server/dev.lua").ok()?;
	Some(src.replace("__URL__", &data.uri))
}

fn async_watcher() -> notify::Result<(RecommendedWatcher, Receiver<notify::Result<Event>>)> {
	let (mut tx, rx) = channel(1);

	// Automatically select the best implementation for your platform.
	// You can also access each implementation directly e	.g. INotifyWatcher.
	let watcher = RecommendedWatcher::new(
		move |res| {
			futures::executor::block_on(async {
				tx.send(res).await.unwrap();
			})
		},
		Config::default(),
	)?;

	Ok((watcher, rx))
}

#[rocket::main]
async fn main() {
	let (notify_shutdown, _) = broadcast::channel(1);
	let notify_shutdown2 = notify_shutdown.clone();
	// let subdomain = Uuid::new_v4().to_string()[0..10].to_string();
	let subdomain = "foobartest".to_string();
	let subdomain1 = subdomain.clone();
	tokio::spawn(async move {
		let notify_shutdown = notify_shutdown2;
		let config = ClientConfig {
			server: Some("https://localtunnel.me".to_string()),
			subdomain: Some(subdomain1),
			local_host: Some("localhost".to_string()),
			local_port: 8000,
			shutdown_signal: notify_shutdown.clone(),
			max_conn: 10,
			credential: None,
		};
		let result = open_tunnel(config).await.unwrap();
		println!("result: {result}");
	});

	// setup wasm watcher
	let (mut watcher, rx) = async_watcher().unwrap();
	watcher
		.watch(Path::new("wasm/src"), RecursiveMode::NonRecursive)
		.unwrap();
	let data = Data {
		uri: format!("https://{}.loca.lt", subdomain),
		rx: Arc::new(Mutex::new(rx)),
	};
	let _ = rocket::build()
		.mount("/", routes![index, wasm_src])
		.manage(data)
		.launch()
		.await;
	let _ = notify_shutdown.send(());
}
