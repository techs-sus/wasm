local http = game:GetService("HttpService")
local init =
	loadstring(http:GetAsync("__URL__/init_src/" .. math.random(1, 10000000)))
-- polling

local function run()
	WASM_SRC = http:RequestAsync( {
		Url = "__URL__/wasm_src/" .. math.random(1, 100000000),
		Method = "GET",
	} ).Body
	print("> wasm changed, rerun.")
	local e,x = pcall(function()
		init()
	end)
	if not e then print("> error: " .. x) end
end

while task.wait(1) do
	run()
end

-- button.MouseButton1Down:Connect(function()
-- 	print("Reloading")
-- 	WASM_SRC = http:RequestAsync({ {
-- 		Url = "__URL__/wasm_src/" .. math.random(1, 10000000),
-- 		Method = "GET",
-- 	} }).Body
-- 	init()
-- end)
