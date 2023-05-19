local http = game:GetService("HttpService")
local rt = loadstring(http:GetAsync('https://raw.githubusercontent.com/roblox-rs/bindings/master/roblox/runtime.luau'))()
local wasm, memory, util
local createPointer, getPointer, dropPointer, invokeOnce, readString, writeStringReturn

local function wrapConstructorNumber(constructor)
	return function(...)
		return createPointer(constructor(...))
	end
end

local function wrapConstructorString(constructor)
	return function(addr, len)
		return createPointer(constructor(addr, len))
	end
end

local env = {
	-- libraries
	lib_task_delay = function(delay, stack, fn_ptr)
		task.delay(delay, invokeOnce, stack, fn_ptr)
	end,

	lib_task_defer = function(stack, fn_ptr)
		task.defer(invokeOnce, stack, fn_ptr)
	end,

	lib_task_spawn = function(stack, fn_ptr)
		task.spawn(invokeOnce, stack, fn_ptr)
	end,

	lib_task_wait = function(delay)
		task.wait(delay)
	end,

	-- pointers
	drop_pointer = function(ptr)
		dropPointer(ptr)
	end,

	clone_pointer = function(ptr)
		return createPointer(getPointer(ptr))
	end,

	-- Instances

	get_game = function()
		print("> wasm tried to get game")
		return createPointer(game)
	end,

	-- testing/logging
	print = function(addr, len)
		task.defer(print, readString(addr, len))
	end,
	error = function(addr, len)
		error(readString(addr, len))
	end,
}

-- the abi is massive
local abi = loadstring(http:GetAsync("https://raw.githubusercontent.com/roblox-rs/bindings/master/roblox/abi.luau"))()
for i, v in pairs(abi.ffi) do
	env[i] = v
end

local WASM_SRC = WASM_SRC or http:GetAsync("https://raw.githubusercontent.com/techs-sus/wasm/master/wasm/roblox/wasm.luau")
local __wasm = loadstring(WASM_SRC)()
wasm = __wasm({
	env = {
		func_list = env,
	},
})

memory = wasm.memory_list.memory
util = loadstring(http:GetAsync('https://raw.githubusercontent.com/roblox-rs/bindings/master/roblox/util.luau'))()(rt, wasm, memory)

abi.load(wasm, rt, util)

createPointer, getPointer, dropPointer, invokeOnce, readString =
	util.createPointer, util.getPointer, util.dropPointer, util.invokeOnce, util.readString

wasm.func_list.hook()
wasm.func_list.main()
