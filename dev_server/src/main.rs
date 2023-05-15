use anyhow::Context;
use localtunnel_client::{broadcast, open_tunnel, ClientConfig};
use rocket::State;
use uuid::Uuid;

#[macro_use]
extern crate rocket;

#[get("/wasm_src/<id>")]
fn wasm_src(id: i32) -> String {
	std::fs::read_to_string("wasm/roblox/wasm.luau")
		.context("Failed reading file")
		.unwrap()
}

#[get("/dev")]
fn index(state: &State<String>) -> String {
	format!(
		"
	local gui = Instance.new('ScreenGui');
	gui.DisplayOrder = 10000000000;
	local button = Instance.new('TextButton')
	button.Size = UDim2.fromScale(0.1, 0.1);
	button.Position = UDim2.fromScale(0.5, 0.5)
	button.Text = \"Reload\"
	button.Parent = gui
	local http = game:GetService('HttpService')
	local init = loadstring(http:GetAsync('https://raw.githubusercontent.com/techs-sus/wasm/master/wasm/roblox/init.server.luau'))
	button.MouseButton1Down:Connect(function()
		print('Reloading')
		WASM_SRC = http:RequestAsync({{
			Url = '{state}/wasm_src/' .. math.random(1, 10000000),
			Method = 'GET'
		}}).Body
		init()
	end)
	gui.Parent = owner.PlayerGui

	"
	)
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
	let _ = rocket::build()
		.mount("/", routes![index, wasm_src])
		.manage(format!("https://{}.loca.lt", subdomain))
		.launch()
		.await;
	let _ = notify_shutdown.send(());
}
