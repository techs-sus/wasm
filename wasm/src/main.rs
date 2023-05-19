extern crate wee_alloc;

use roblox_rs::{println, *};

// Use `wee_alloc` as the global allocator.
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

pub fn main() {
	println!("Hello From Wasm.");
	let my_fancy_part = Part::new();
	println!("WOW!");
	my_fancy_part.set_anchored(true);
	my_fancy_part.set_color(&Color3::from_rgb(254., 0., 0.));
	my_fancy_part.set_parent(&Some(&Workspace::instance()));
	my_fancy_part.set_size(&Vector3::new_with_position(25., 420., 25.));
	my_fancy_part.set_position(&Vector3::new_with_position(55., 160., 30.));
}
