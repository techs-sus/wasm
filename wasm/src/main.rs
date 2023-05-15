extern crate wee_alloc;

use roblox_rs::{println, *};

// Use `wee_alloc` as the global allocator.
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

pub fn main() {
	println!("Hello from wasm!!!");
}
