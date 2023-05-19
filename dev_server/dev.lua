local http = game:GetService("HttpService")
local init =
	loadstring(http:GetAsync("https://raw.githubusercontent.com/techs-sus/wasm/master/wasm/roblox/init.server.luau"))
-- polling

local function run()
	WASM_SRC = http:RequestAsync( {
		Url = "__URL__/wasm_src/" .. math.random(1, 100000000),
		Method = "GET",
	} ).Body
	print("> wasm changed, rerun.")
	-- local e,x = pcall(function()
		init()
	-- end)
	-- if e then print("> error: " .. x) end
	task.wait(1)
end

while task.wait() do
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
