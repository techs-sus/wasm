local Integer = (function()
local Numeric = {}

local NUM_ZERO, NUM_ONE, NUM_SIX_FOUR
local NUM_BIT_26, NUM_BIT_52

local bit_lshift = bit32.lshift
local bit_rshift = bit32.rshift
local bit_arshift = bit32.arshift

local bit_and = bit32.band
local bit_or = bit32.bor
local bit_xor = bit32.bxor
local bit_not = bit32.bnot

local bit_extract = bit32.extract
local bit_replace = bit32.replace

local from_u32, from_u64, into_u64
local num_subtract, num_divide_unsigned, num_negate
local num_or, num_shift_left, num_shift_right_unsigned
local num_is_negative, num_is_zero, num_is_less_unsigned

-- X: a[0 ..21]
-- Y: a[22..31]
--  | b[0 ..11]
-- Z: b[12..31]
local constructor = Vector3.new

function Numeric.from_u32(data_1, data_2)
	local x = bit_and(data_1, 0x3FFFFF)
	local y = bit_and(data_2, 0x3FFFFF)
	local z = bit_replace(bit_rshift(data_1, 22), bit_rshift(data_2, 22), 10, 10)

	return constructor(x, y, z)
end

local function load_d1(value)
	return bit_replace(bit_and(value.X, 0x3FFFFF), value.Z, 22, 10)
end

local function load_d2(value)
	return bit_replace(bit_and(value.Y, 0x3FFFFF), bit_rshift(value.Z, 10), 22, 10)
end

function Numeric.into_u32(value)
	return load_d1(value), load_d2(value)
end

function Numeric.from_u64(value)
	return from_u32(bit_and(value % 0x100000000), bit_and(value / 0x100000000))
end

function Numeric.into_u64(value)
	return load_d1(value) + load_d2(value) * 0x100000000
end

function Numeric.add(lhs, rhs)
	local data_1 = load_d1(lhs) + load_d1(rhs)
	local data_2 = load_d2(lhs) + load_d2(rhs)

	if data_1 >= 0x100000000 then
		data_1 = data_1 - 0x100000000
		data_2 = data_2 + 1
	end

	if data_2 >= 0x100000000 then
		data_2 = data_2 - 0x100000000
	end

	return from_u32(data_1, data_2)
end

function Numeric.subtract(lhs, rhs)
	local data_1 = load_d1(lhs) - load_d1(rhs)
	local data_2 = load_d2(lhs) - load_d2(rhs)

	if data_1 < 0 then
		data_1 = data_1 + 0x100000000
		data_2 = data_2 - 1
	end

	if data_2 < 0 then
		data_2 = data_2 + 0x100000000
	end

	return from_u32(data_1, data_2)
end

function Numeric.multiply(lhs, rhs)
	if num_is_zero(lhs) or num_is_zero(rhs) then
		return NUM_ZERO
	elseif num_is_less_unsigned(lhs, NUM_BIT_26) and num_is_less_unsigned(rhs, NUM_BIT_26) then
		return from_u64(load_d1(lhs) * load_d1(rhs))
	end

	-- Divide each long into 4 chunks of 16 bits, and then add up 4x4 products.
	-- We can skip products that would overflow.
	local lhs_1, lhs_2 = load_d1(lhs), load_d2(lhs)
	local rhs_1, rhs_2 = load_d1(rhs), load_d2(rhs)

	local a48 = bit_rshift(lhs_2, 16)
	local a32 = bit_and(lhs_2, 0xFFFF)
	local a16 = bit_rshift(lhs_1, 16)
	local a00 = bit_and(lhs_1, 0xFFFF)

	local b48 = bit_rshift(rhs_2, 16)
	local b32 = bit_and(rhs_2, 0xFFFF)
	local b16 = bit_rshift(rhs_1, 16)
	local b00 = bit_and(rhs_1, 0xFFFF)

	local c00 = a00 * b00
	local c16 = bit_rshift(c00, 16)

	c00 = bit_and(c00, 0xFFFF)
	c16 = c16 + a16 * b00

	local c32 = bit_rshift(c16, 16)

	c16 = bit_and(c16, 0xFFFF)
	c16 = c16 + a00 * b16
	c32 = c32 + bit_rshift(c16, 16)
	c16 = bit_and(c16, 0xFFFF)
	c32 = c32 + a32 * b00

	local c48 = bit_rshift(c32, 16)

	c32 = bit_and(c32, 0xFFFF)
	c32 = c32 + a16 * b16
	c48 = c48 + bit_rshift(c32, 16)
	c32 = bit_and(c32, 0xFFFF)
	c32 = c32 + a00 * b32
	c48 = c48 + bit_rshift(c32, 16)
	c32 = bit_and(c32, 0xFFFF)
	c48 = c48 + a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48
	c48 = bit_and(c48, 0xFFFF)

	local data_1 = bit_replace(c00, c16, 16, 16)
	local data_2 = bit_replace(c32, c48, 16, 16)

	return from_u32(data_1, data_2)
end

function Numeric.divide_unsigned(lhs, rhs)
	if num_is_zero(rhs) then
		error("division by zero")
	elseif num_is_zero(lhs) then
		return NUM_ZERO, NUM_ZERO
	elseif num_is_less_unsigned(lhs, NUM_BIT_52) and num_is_less_unsigned(rhs, NUM_BIT_52) then
		local lhs_u = into_u64(lhs)
		local rhs_u = into_u64(rhs)

		return from_u64(lhs_u / rhs_u), from_u64(lhs_u % rhs_u)
	end

	local quotient = NUM_ZERO
	local remainder = NUM_ZERO

	local num_1, num_2 = load_d1(lhs), load_d2(lhs)

	for i = 63, 0, -1 do
		local temp = num_shift_left(remainder, NUM_ONE)
		local rem_1, rem_2 = load_d1(temp), load_d2(temp)

		if i > 31 then
			rem_1 = bit_or(rem_1, bit_extract(num_2, i - 32, 1))
		else
			rem_1 = bit_or(rem_1, bit_extract(num_1, i, 1))
		end

		remainder = from_u32(rem_1, rem_2)

		if not num_is_less_unsigned(remainder, rhs) then
			remainder = num_subtract(remainder, rhs)
			quotient = num_or(quotient, num_shift_left(NUM_ONE, from_u32(i, 0)))
		end
	end

	return quotient, remainder
end

function Numeric.divide_signed(lhs, rhs)
	local left_negative = num_is_negative(lhs)
	local right_negative = num_is_negative(rhs)

	if left_negative then
		lhs = num_negate(lhs)
	end

	if right_negative then
		rhs = num_negate(rhs)
	end

	local quotient, remainder = num_divide_unsigned(lhs, rhs)

	if left_negative ~= right_negative then
		quotient = num_negate(quotient)
	end

	if left_negative then
		remainder = num_negate(remainder)
	end

	return quotient, remainder
end

function Numeric.negate(value)
	local data_1 = bit_not(load_d1(value)) + 1
	local data_2 = bit_not(load_d2(value))

	if data_1 >= 0x100000000 then
		data_1 = data_1 - 0x100000000
		data_2 = data_2 + 1
	end

	if data_2 >= 0x100000000 then
		data_2 = data_2 - 0x100000000
	end

	return from_u32(data_1, data_2)
end

function Numeric.bit_and(lhs, rhs)
	local x = bit_and(lhs.X, rhs.X)
	local y = bit_and(lhs.Y, rhs.Y)
	local z = bit_and(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

function Numeric.bit_not(value)
	local x = bit_and(bit_not(value.X), 0xFFFFFF)
	local y = bit_and(bit_not(value.Y), 0xFFFFFF)
	local z = bit_and(bit_not(value.Z), 0xFFFFFF)

	return constructor(x, y, z)
end

function Numeric.bit_or(lhs, rhs)
	local x = bit_or(lhs.X, rhs.X)
	local y = bit_or(lhs.Y, rhs.Y)
	local z = bit_or(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

function Numeric.bit_xor(lhs, rhs)
	local x = bit_xor(lhs.X, rhs.X)
	local y = bit_xor(lhs.Y, rhs.Y)
	local z = bit_xor(lhs.Z, rhs.Z)

	return constructor(x, y, z)
end

function Numeric.shift_left(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local pad = 32 - count
		local lhs_1, lhs_2 = load_d1(lhs), load_d2(lhs)

		local data_1 = bit_lshift(lhs_1, count)
		local data_2 = bit_replace(bit_rshift(lhs_1, pad), lhs_2, count, pad)

		return from_u32(data_1, data_2)
	else
		local lhs_1 = load_d1(lhs)

		return from_u32(0, bit_lshift(lhs_1, count - 32))
	end
end

function Numeric.shift_right_unsigned(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local lhs_1, lhs_2 = load_d1(lhs), load_d2(lhs)

		local data_1 = bit_replace(bit_rshift(lhs_1, count), lhs_2, 32 - count, count)
		local data_2 = bit_rshift(lhs_2, count)

		return from_u32(data_1, data_2)
	else
		local lhs_2 = load_d2(lhs)

		return from_u32(bit_rshift(lhs_2, count - 32), 0)
	end
end

function Numeric.shift_right_signed(lhs, rhs)
	local count = rhs.X % 64

	if count == 0 then
		return lhs
	elseif count < 32 then
		local lhs_1, lhs_2 = load_d1(lhs), load_d2(lhs)

		local data_1 = bit_replace(bit_rshift(lhs_1, count), lhs_2, 32 - count, count)
		local data_2 = bit_arshift(lhs_2, count)

		return from_u32(data_1, data_2)
	else
		local lhs_2 = load_d2(lhs)

		local data_1 = bit_arshift(lhs_2, count - 32)
		local data_2 = lhs_2 >= 0x80000000 and 0xFFFFFFFF or 0

		return from_u32(data_1, data_2)
	end
end

function Numeric.rotate_left(lhs, rhs)
	if num_is_zero(rhs) then
		return lhs
	else
		local data_1 = num_shift_left(lhs, rhs)
		local data_2 = num_shift_right_unsigned(lhs, num_subtract(NUM_SIX_FOUR, rhs))

		return num_or(data_1, data_2)
	end
end

function Numeric.rotate_right(lhs, rhs)
	if num_is_zero(rhs) then
		return lhs
	else
		local data_1 = num_shift_right_unsigned(lhs, rhs)
		local data_2 = num_shift_left(lhs, num_subtract(NUM_SIX_FOUR, rhs))

		return num_or(data_1, data_2)
	end
end

function Numeric.is_negative(value)
	return value.Z >= 0x80000
end

function Numeric.is_zero(value)
	return value.X == 0 and value.Y == 0 and value.Z == 0
end

function Numeric.is_equal(lhs, rhs)
	return lhs.X == rhs.X and lhs.Y == rhs.Y and lhs.Z == rhs.Z
end

function Numeric.is_less_unsigned(lhs, rhs)
	local data_l_2 = load_d2(lhs)
	local data_r_2 = load_d2(rhs)

	return data_l_2 < data_r_2 or (data_l_2 == data_r_2 and load_d1(lhs) < load_d1(rhs))
end

function Numeric.is_greater_unsigned(lhs, rhs)
	local data_l_2 = load_d2(lhs)
	local data_r_2 = load_d2(rhs)

	return data_l_2 > data_r_2 or (data_l_2 == data_r_2 and load_d1(lhs) > load_d1(rhs))
end

function Numeric.is_less_signed(lhs, rhs)
	local neg_a = num_is_negative(lhs)
	local neg_b = num_is_negative(rhs)

	if neg_a and not neg_b then
		return true
	elseif not neg_a and neg_b then
		return false
	else
		return num_is_negative(num_subtract(lhs, rhs))
	end
end

function Numeric.is_greater_signed(lhs, rhs)
	local neg_a = num_is_negative(lhs)
	local neg_b = num_is_negative(rhs)

	if neg_a and not neg_b then
		return false
	elseif not neg_a and neg_b then
		return true
	else
		return num_is_negative(num_subtract(rhs, lhs))
	end
end

from_u32 = Numeric.from_u32
from_u64 = Numeric.from_u64
into_u64 = Numeric.into_u64

num_subtract = Numeric.subtract
num_divide_unsigned = Numeric.divide_unsigned
num_negate = Numeric.negate

num_or = Numeric.bit_or
num_shift_left = Numeric.shift_left
num_shift_right_unsigned = Numeric.shift_right_unsigned

num_is_negative = Numeric.is_negative
num_is_zero = Numeric.is_zero
num_is_less_unsigned = Numeric.is_less_unsigned

NUM_ZERO = from_u64(0)
NUM_ONE = from_u64(1)
NUM_SIX_FOUR = from_u64(64)
NUM_BIT_26 = from_u64(0x4000000)
NUM_BIT_52 = from_u64(0x10000000000000)

Numeric.ZERO = NUM_ZERO
Numeric.ONE = NUM_ONE

return table.freeze(Numeric)

end)()
local rt = (function()
local module = {}

local to_u32 = bit32.band

local bit_or = bit32.bor
local bit_and = bit32.band
local bit_lshift = bit32.lshift
local bit_rshift = bit32.rshift

local num_from_u32 = Integer.from_u32
local num_into_u32 = Integer.into_u32

local function to_i32(num)
	if num >= 0x80000000 then
		return num - 0x100000000
	else
		return num
	end
end

local function no_op(num)
	return num
end

module.i64 = Integer

do
	local add = {}
	local sub = {}
	local mul = {}
	local div = {}
	local rem = {}
	local neg = {}
	local min = {}
	local max = {}
	local copysign = {}
	local nearest = {}

	local assert = assert

	local math_abs = math.abs
	local math_fmod = math.fmod
	local math_round = math.round
	local math_sign = math.sign
	local math_min = math.min
	local math_max = math.max

	local string_byte = string.byte
	local string_pack = string.pack

	local num_divide_signed = Integer.divide_signed
	local num_divide_unsigned = Integer.divide_unsigned

	function add.i32(lhs, rhs)
		return to_u32(lhs + rhs)
	end

	function sub.i32(lhs, rhs)
		return to_u32(lhs - rhs)
	end

	function mul.i32(lhs, rhs)
		if (lhs + rhs) < 0x8000000 then
			return to_u32(lhs * rhs)
		else
			local a16 = bit_rshift(lhs, 16)
			local a00 = bit_and(lhs, 0xFFFF)
			local b16 = bit_rshift(rhs, 16)
			local b00 = bit_and(rhs, 0xFFFF)

			local c00 = a00 * b00
			local c16 = a16 * b00 + a00 * b16

			return to_u32(c00 + bit_lshift(c16, 16))
		end
	end

	function div.i32(lhs, rhs)
		assert(rhs ~= 0, "division by zero")

		lhs = to_i32(lhs)
		rhs = to_i32(rhs)

		return to_u32(lhs / rhs)
	end

	function div.u32(lhs, rhs)
		assert(rhs ~= 0, "division by zero")

		return to_u32(lhs / rhs)
	end

	function rem.i32(lhs, rhs)
		assert(rhs ~= 0, "division by zero")

		lhs = to_i32(lhs)
		rhs = to_i32(rhs)

		return to_u32(math_fmod(lhs, rhs))
	end

	add.i64 = Integer.add
	sub.i64 = Integer.subtract
	mul.i64 = Integer.multiply
	div.i64 = num_divide_signed

	function rem.i64(lhs, rhs)
		local _, remainder = num_divide_signed(lhs, rhs)

		return remainder
	end

	div.u64 = num_divide_unsigned

	function rem.u64(lhs, rhs)
		local _, remainder = num_divide_unsigned(lhs, rhs)

		return remainder
	end

	function neg.f32(num)
		return -num
	end

	function min.f32(lhs, rhs)
		if rhs == rhs then
			return math_min(lhs, rhs)
		else
			return rhs
		end
	end

	function max.f32(lhs, rhs)
		if rhs == rhs then
			return math_max(lhs, rhs)
		else
			return rhs
		end
	end

	function copysign.f32(lhs, rhs)
		local packed = string_pack("<d", rhs)
		local sign = string_byte(packed, 8)

		if sign >= 0x80 then
			return -math_abs(lhs)
		else
			return math_abs(lhs)
		end
	end

	function nearest.f32(num)
		local result = math_round(num)

		if (math_abs(num) + 0.5) % 2 == 1 then
			result = result - math_sign(result)
		end

		return result
	end

	neg.f64 = neg.f32
	min.f64 = min.f32
	max.f64 = max.f32
	copysign.f64 = copysign.f32
	nearest.f64 = nearest.f32

	module.add = add
	module.sub = sub
	module.mul = mul
	module.div = div
	module.rem = rem
	module.neg = neg
	module.min = min
	module.max = max
	module.copysign = copysign
	module.nearest = nearest
end

do
	local clz = {}
	local ctz = {}
	local popcnt = {}

	local bit_countlz = bit32.countlz
	local bit_countrz = bit32.countrz

	local function popcnt_i32(num)
		local count = 0

		while num ~= 0 do
			num = bit_and(num, num - 1)
			count = count + 1
		end

		return count
	end

	popcnt.i32 = popcnt_i32

	function clz.i64(num)
		local data_1, data_2 = num_into_u32(num)
		local temp

		if data_2 == 0 then
			temp = bit_countlz(data_1) + 32
		else
			temp = bit_countlz(data_2)
		end

		return num_from_u32(temp, 0)
	end

	function ctz.i64(num)
		local data_1, data_2 = num_into_u32(num)
		local temp

		if data_1 == 0 then
			temp = bit_countrz(data_2) + 32
		else
			temp = bit_countrz(data_1)
		end

		return num_from_u32(temp, 0)
	end

	function popcnt.i64(num)
		local data_1, data_2 = num_into_u32(num)
		local temp = popcnt_i32(data_1) + popcnt_i32(data_2)

		return num_from_u32(temp, 0)
	end

	module.clz = clz
	module.ctz = ctz
	module.popcnt = popcnt
end

do
	local eq = {}
	local ne = {}
	local le = {}
	local lt = {}
	local ge = {}
	local gt = {}

	local num_is_equal = Integer.is_equal
	local num_is_less_signed = Integer.is_less_signed
	local num_is_less_unsigned = Integer.is_less_unsigned
	local num_is_greater_signed = Integer.is_greater_signed
	local num_is_greater_unsigned = Integer.is_greater_unsigned

	function le.i32(lhs, rhs)
		return to_i32(lhs) <= to_i32(rhs)
	end

	function lt.i32(lhs, rhs)
		return to_i32(lhs) < to_i32(rhs)
	end

	function ge.i32(lhs, rhs)
		return to_i32(lhs) >= to_i32(rhs)
	end

	function gt.i32(lhs, rhs)
		return to_i32(lhs) > to_i32(rhs)
	end

	eq.i64 = num_is_equal

	function ne.i64(lhs, rhs)
		return not num_is_equal(lhs, rhs)
	end

	function le.i64(lhs, rhs)
		return num_is_less_signed(lhs, rhs) or num_is_equal(lhs, rhs)
	end

	function le.u64(lhs, rhs)
		return num_is_less_unsigned(lhs, rhs) or num_is_equal(lhs, rhs)
	end

	lt.i64 = num_is_less_signed
	lt.u64 = num_is_less_unsigned

	function ge.i64(lhs, rhs)
		return num_is_greater_signed(lhs, rhs) or num_is_equal(lhs, rhs)
	end

	function ge.u64(lhs, rhs)
		return num_is_greater_unsigned(lhs, rhs) or num_is_equal(lhs, rhs)
	end

	gt.i64 = num_is_greater_signed
	gt.u64 = num_is_greater_unsigned

	module.eq = eq
	module.ne = ne
	module.le = le
	module.lt = lt
	module.ge = ge
	module.gt = gt
end

do
	local band = {}
	local bor = {}
	local bxor = {}
	local bnot = {}

	band.i64 = Integer.bit_and
	bor.i64 = Integer.bit_or
	bxor.i64 = Integer.bit_xor
	bnot.i64 = Integer.bit_not

	module.band = band
	module.bor = bor
	module.bxor = bxor
	module.bnot = bnot
end

do
	local shl = {}
	local shr = {}
	local rotl = {}
	local rotr = {}

	local bit_arshift = bit32.arshift
	local bit_lrotate = bit32.lrotate
	local bit_rrotate = bit32.rrotate

	function shl.i32(lhs, rhs)
		return bit_lshift(lhs, rhs % 32)
	end

	function shr.u32(lhs, rhs)
		return bit_rshift(lhs, rhs % 32)
	end

	function shr.i32(lhs, rhs)
		return bit_arshift(lhs, rhs % 32)
	end

	function rotl.i32(lhs, rhs)
		return bit_lrotate(lhs, rhs % 32)
	end

	function rotr.i32(lhs, rhs)
		return bit_rrotate(lhs, rhs % 32)
	end

	shl.i64 = Integer.shift_left
	shr.i64 = Integer.shift_right_signed
	shr.u64 = Integer.shift_right_unsigned
	rotl.i64 = Integer.rotate_left
	rotr.i64 = Integer.rotate_right

	module.shl = shl
	module.shr = shr
	module.rotl = rotl
	module.rotr = rotr
end

do
	local wrap = {}
	local truncate = {}
	local saturate = {}
	local extend = {}
	local convert = {}
	local demote = {}
	local promote = {}
	local reinterpret = {}

	local math_ceil = math.ceil
	local math_floor = math.floor
	local math_clamp = math.clamp

	local string_pack = string.pack
	local string_unpack = string.unpack

	local NUM_ZERO = Integer.ZERO
	local NUM_MIN_I64 = num_from_u32(0, 0x80000000)
	local NUM_MAX_I64 = num_from_u32(0xFFFFFFFF, 0x7FFFFFFF)
	local NUM_MAX_U64 = num_from_u32(0xFFFFFFFF, 0xFFFFFFFF)

	local num_from_u64 = Integer.from_u64
	local num_into_u64 = Integer.into_u64

	local num_negate = Integer.negate
	local num_is_negative = Integer.is_negative

	local function truncate_f64(num)
		if num >= 0 then
			return math_floor(num)
		else
			return math_ceil(num)
		end
	end

	function wrap.i32_i64(num)
		local data_1, _ = num_into_u32(num)

		return data_1
	end

	function truncate.i32_f32(num)
		return to_u32(truncate_f64(num))
	end

	truncate.i32_f64 = to_u32
	truncate.u32_f32 = truncate_f64
	truncate.u32_f64 = truncate_f64

	function truncate.i64_f32(num)
		if num < 0 then
			local temp = num_from_u64(-num)

			return num_negate(temp)
		else
			return num_from_u64(num)
		end
	end

	truncate.i64_f64 = truncate.i64_f32

	function truncate.u64_f32(num)
		if num <= 0 then
			return NUM_ZERO
		else
			return num_from_u64(math_floor(num))
		end
	end

	truncate.u64_f64 = truncate.u64_f32

	truncate.f32 = truncate_f64
	truncate.f64 = truncate_f64

	function saturate.i32_f32(num)
		local temp = math_clamp(truncate_f64(num), -0x80000000, 0x7FFFFFFF)

		return to_u32(temp)
	end

	saturate.i32_f64 = saturate.i32_f32

	function saturate.u32_f32(num)
		local temp = math_clamp(truncate_f64(num), 0, 0xFFFFFFFF)

		return to_u32(temp)
	end

	saturate.u32_f64 = saturate.u32_f32

	local truncate_i64_f64 = truncate.i64_f64

	function saturate.i64_f32(num)
		if num >= 2 ^ 63 - 1 then
			return NUM_MAX_I64
		elseif num <= -2 ^ 63 then
			return NUM_MIN_I64
		else
			return truncate_i64_f64(num)
		end
	end

	saturate.i64_f64 = saturate.i64_f32

	function saturate.u64_f32(num)
		if num >= 2 ^ 64 then
			return NUM_MAX_U64
		elseif num <= 0 then
			return NUM_ZERO
		else
			return truncate_i64_f64(num)
		end
	end

	saturate.u64_f64 = saturate.u64_f32

	function extend.i32_n8(num)
		num = bit_and(num, 0xFF)

		if num >= 0x80 then
			return to_u32(num - 0x100)
		else
			return num
		end
	end

	function extend.i32_n16(num)
		num = bit_and(num, 0xFFFF)

		if num >= 0x8000 then
			return to_u32(num - 0x10000)
		else
			return num
		end
	end

	function extend.i64_n8(num)
		local data_1, _ = num_into_u32(num)

		data_1 = bit_and(data_1, 0xFF)

		if data_1 >= 0x80 then
			local temp = num_from_u32(-data_1 + 0x100, 0)

			return num_negate(temp)
		else
			return num_from_u32(data_1, 0)
		end
	end

	function extend.i64_n16(num)
		local data_1, _ = num_into_u32(num)

		data_1 = bit_and(data_1, 0xFFFF)

		if data_1 >= 0x8000 then
			local temp = num_from_u32(-data_1 + 0x10000, 0)

			return num_negate(temp)
		else
			return num_from_u32(data_1, 0)
		end
	end

	function extend.i64_n32(num)
		local data_1, _ = num_into_u32(num)

		if data_1 >= 0x80000000 then
			local temp = num_from_u32(-data_1 + 0x100000000, 0)

			return num_negate(temp)
		else
			return num_from_u32(data_1, 0)
		end
	end

	function extend.i64_i32(num)
		if num >= 0x80000000 then
			local temp = num_from_u32(-num + 0x100000000, 0)

			return num_negate(temp)
		else
			return num_from_u32(num, 0)
		end
	end

	function extend.i64_u32(num)
		return num_from_u32(num, 0)
	end

	convert.f32_i32 = to_i32
	convert.f32_u32 = no_op

	function convert.f32_i64(num)
		if num_is_negative(num) then
			local temp = num_negate(num)

			return -num_into_u64(temp)
		else
			return num_into_u64(num)
		end
	end

	convert.f32_u64 = num_into_u64
	convert.f64_i32 = to_i32
	convert.f64_u32 = no_op
	convert.f64_i64 = convert.f32_i64
	convert.f64_u64 = num_into_u64

	demote.f32_f64 = no_op

	promote.f64_f32 = no_op

	function reinterpret.i32_f32(num)
		local packed = string_pack("f", num)

		return string_unpack("I4", packed)
	end

	function reinterpret.i64_f64(num)
		local packed = string_pack("d", num)
		local data_1, data_2 = string_unpack("I4I4", packed)

		return num_from_u32(data_1, data_2)
	end

	function reinterpret.f32_i32(num)
		local packed = string_pack("I4", num)

		return string_unpack("f", packed)
	end

	function reinterpret.f64_i64(num)
		local data_1, data_2 = num_into_u32(num)
		local packed = string_pack("I4I4", data_1, data_2)

		return string_unpack("d", packed)
	end

	module.wrap = wrap
	module.truncate = truncate
	module.saturate = saturate
	module.extend = extend
	module.convert = convert
	module.demote = demote
	module.promote = promote
	module.reinterpret = reinterpret
end

do
	local load = {}
	local store = {}
	local allocator = {}

	local bit_extract = bit32.extract
	local bit_replace = bit32.replace

	local math_floor = math.floor

	local string_byte = string.byte
	local string_unpack = string.unpack

	local reinterpret_f32_i32 = module.reinterpret.f32_i32
	local reinterpret_f64_i64 = module.reinterpret.f64_i64
	local reinterpret_i32_f32 = module.reinterpret.i32_f32
	local reinterpret_i64_f64 = module.reinterpret.i64_f64

	local function load_byte(data, addr)
		local value = data[math_floor(addr / 4)] or 0

		return bit_extract(value, addr % 4 * 8, 8)
	end

	local function store_byte(data, addr, value)
		local adjust = math_floor(addr / 4)

		data[adjust] = bit_replace(data[adjust] or 0, value, addr % 4 * 8, 8)
	end

	function load.i32_i8(memory, addr)
		local temp = load_byte(memory.data, addr)

		if temp >= 0x80 then
			return to_u32(temp - 0x100)
		else
			return temp
		end
	end

	function load.i32_u8(memory, addr)
		return load_byte(memory.data, addr)
	end

	function load.i32_i16(memory, addr)
		local data = memory.data
		local temp

		if addr % 4 == 0 then
			temp = bit_and(data[addr / 4] or 0, 0xFFFF)
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)

			temp = bit_or(b1, b2)
		end

		if temp >= 0x8000 then
			return to_u32(temp - 0x10000)
		else
			return temp
		end
	end

	function load.i32_u16(memory, addr)
		local data = memory.data

		if addr % 4 == 0 then
			return bit_and(data[addr / 4] or 0, 0xFFFF)
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)

			return bit_or(b1, b2)
		end
	end

	function load.i32(memory, addr)
		local data = memory.data

		if addr % 4 == 0 then
			-- aligned read
			return data[addr / 4] or 0
		else
			-- unaligned read
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)
			local b3 = bit_lshift(load_byte(data, addr + 2), 16)
			local b4 = bit_lshift(load_byte(data, addr + 3), 24)

			return bit_or(b1, b2, b3, b4)
		end
	end

	function load.i64_i8(memory, addr)
		local data_1 = load_byte(memory.data, addr)
		local data_2

		if data_1 >= 0x80 then
			data_1 = to_u32(data_1 - 0x100)
			data_2 = 0xFFFFFFFF
		else
			data_2 = 0
		end

		return num_from_u32(data_1, data_2)
	end

	function load.i64_u8(memory, addr)
		local temp = load_byte(memory.data, addr)

		return num_from_u32(temp, 0)
	end

	function load.i64_i16(memory, addr)
		local data = memory.data
		local data_1, data_2

		if addr % 4 == 0 then
			data_1 = bit_and(data[addr / 4] or 0, 0xFFFF)
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)

			data_1 = bit_or(b1, b2)
		end

		if data_1 >= 0x8000 then
			data_1 = to_u32(data_1 - 0x10000)
			data_2 = 0xFFFFFFFF
		else
			data_2 = 0
		end

		return num_from_u32(data_1, data_2)
	end

	function load.i64_u16(memory, addr)
		local data = memory.data
		local temp

		if addr % 4 == 0 then
			temp = bit_and(data[addr / 4] or 0, 0xFFFF)
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)

			temp = bit_or(b1, b2)
		end

		return num_from_u32(temp, 0)
	end

	function load.i64_i32(memory, addr)
		local data = memory.data
		local data_1, data_2

		if addr % 4 == 0 then
			data_1 = data[addr / 4] or 0
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)
			local b3 = bit_lshift(load_byte(data, addr + 2), 16)
			local b4 = bit_lshift(load_byte(data, addr + 3), 24)

			data_1 = bit_or(b1, b2, b3, b4)
		end

		if data_1 >= 0x80000000 then
			data_1 = to_u32(data_1 - 0x100000000)
			data_2 = 0xFFFFFFFF
		else
			data_2 = 0
		end

		return num_from_u32(data_1, data_2)
	end

	function load.i64_u32(memory, addr)
		local data = memory.data
		local temp

		if addr % 4 == 0 then
			temp = data[addr / 4] or 0
		else
			local b1 = load_byte(data, addr)
			local b2 = bit_lshift(load_byte(data, addr + 1), 8)
			local b3 = bit_lshift(load_byte(data, addr + 2), 16)
			local b4 = bit_lshift(load_byte(data, addr + 3), 24)

			temp = bit_or(b1, b2, b3, b4)
		end

		return num_from_u32(temp, 0)
	end

	local load_i32 = load.i32

	function load.i64(memory, addr)
		local data_1 = load_i32(memory, addr)
		local data_2 = load_i32(memory, addr + 4)

		return num_from_u32(data_1, data_2)
	end

	local load_i64 = load.i64

	function load.f32(memory, addr)
		local raw = load_i32(memory, addr)

		return reinterpret_f32_i32(raw)
	end

	function load.f64(memory, addr)
		local raw = load_i64(memory, addr)

		return reinterpret_f64_i64(raw)
	end

	function store.i32_n8(memory, addr, value)
		store_byte(memory.data, addr, value)
	end

	local store_i8 = store.i32_n8

	function store.i32_n16(memory, addr, value)
		store_byte(memory.data, addr, value)
		store_byte(memory.data, addr + 1, bit_rshift(value, 8))
	end

	function store.i32(memory, addr, value)
		local data = memory.data

		if addr % 4 == 0 then
			-- aligned write
			data[addr / 4] = value
		else
			-- unaligned write
			store_byte(data, addr, value)
			store_byte(data, addr + 1, bit_rshift(value, 8))
			store_byte(data, addr + 2, bit_rshift(value, 16))
			store_byte(data, addr + 3, bit_rshift(value, 24))
		end
	end

	local store_i32 = store.i32
	local store_i32_n8 = store.i32_n8
	local store_i32_n16 = store.i32_n16

	function store.i64_n8(memory, addr, value)
		local data_1, _ = num_into_u32(value)

		store_i32_n8(memory, addr, data_1)
	end

	function store.i64_n16(memory, addr, value)
		local data_1, _ = num_into_u32(value)

		store_i32_n16(memory, addr, data_1)
	end

	function store.i64_n32(memory, addr, value)
		local data_1, _ = num_into_u32(value)

		store_i32(memory, addr, data_1)
	end

	function store.i64(memory, addr, value)
		local data_1, data_2 = num_into_u32(value)

		store_i32(memory, addr, data_1)
		store_i32(memory, addr + 4, data_2)
	end

	local store_i64 = store.i64

	function store.f32(memory, addr, value)
		store_i32(memory, addr, reinterpret_i32_f32(value))
	end

	function store.f64(memory, addr, value)
		store_i64(memory, addr, reinterpret_i64_f64(value))
	end

	function store.string(memory, addr, data, len)
		len = len or #data

		local rem = len % 4

		for i = 1, len - rem, 4 do
			local v = string_unpack("<I4", data, i)

			store_i32(memory, addr + i - 1, v)
		end

		for i = len - rem + 1, len do
			local v = string_byte(data, i)

			store_i8(memory, addr + i - 1, v)
		end
	end

	function allocator.new(min, max)
		return { min = min, max = max, data = {} }
	end

	function allocator.grow(memory, num)
		local old = memory.min
		local new = old + num

		if new > memory.max then
			return to_u32(-1)
		else
			memory.min = new

			return old
		end
	end

	module.load = load
	module.store = store
	module.allocator = allocator
end

return module

end)()
local add_i32 = rt.add.i32 local add_i64 = rt.add.i64 local band_i32 = bit32.band local bor_i32 = bit32.bor local bxor_i32 = bit32.bxor local div_u32 = rt.div.u32 local div_u64 = rt.div.u64 local eq_i64 = rt.eq.i64 local extend_i64_u32 = rt.extend.i64_u32 local ge_u64 = rt.ge.u64 local gt_i32 = rt.gt.i32 local gt_u64 = rt.gt.u64 local i64_ONE = rt.i64.ONE local i64_ZERO = rt.i64.ZERO local i64_from_u32 = rt.i64.from_u32 local le_i32 = rt.le.i32 local load_i32 = rt.load.i32 local load_i32_i8 = rt.load.i32_i8 local load_i32_u16 = rt.load.i32_u16 local load_i32_u8 = rt.load.i32_u8 local load_i64 = rt.load.i64 local load_i64_u32 = rt.load.i64_u32 local lt_i32 = rt.lt.i32 local mul_i32 = rt.mul.i32 local mul_i64 = rt.mul.i64 local ne_i64 = rt.ne.i64 local shl_i32 = rt.shl.i32 local shr_u32 = rt.shr.u32 local shr_u64 = rt.shr.u64 local store_i32 = rt.store.i32 local store_i32_n16 = rt.store.i32_n16 local store_i32_n8 = rt.store.i32_n8 local store_i64 = rt.store.i64 local sub_i32 = rt.sub.i32 local sub_i64 = rt.sub.i64 local wrap_i32_i64 = rt.wrap.i32_i64 local memory_at_0 local FUNC_LIST = table.create(151)local TABLE_LIST = table.create(0)local MEMORY_LIST = table.create(0)local GLOBAL_LIST = table.create(2)FUNC_LIST[4] =--[[ _ZN3std2rt10lang_start17h7dd11bcd763eff1eE ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 12, param_0 )reg_0 = FUNC_LIST[78](add_i32(loc_0 , 12 ), 1048576 , param_1 , param_2 , param_3 )param_0 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_0 break end return reg_0 end FUNC_LIST[5] =--[[ _ZN3std2rt10lang_start28_$u7b$$u7b$closure$u7d$$u7d$17h6c9ceb848cde7b32E.llvm.4982300217658313191 ]]function(param_0)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[8](load_i32(memory_at_0, param_0 ))store_i32_n8(memory_at_0, loc_0 + 15, 0 )reg_0 = FUNC_LIST[93](add_i32(loc_0 , 15 ))param_0 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_0 break end return reg_0 end FUNC_LIST[6] =--[[ _ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h3845759cba2a7af9E.llvm.4982300217658313191 ]]function(param_0)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 12, load_i32(memory_at_0, param_0 ))reg_0 = FUNC_LIST[5](add_i32(loc_0 , 12 ))param_0 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_0 break end return reg_0 end FUNC_LIST[7] =--[[ _ZN4core3ptr85drop_in_place$LT$std..rt..lang_start$LT$$LP$$RP$$GT$..$u7b$$u7b$closure$u7d$$u7d$$GT$17h62b77081a6261d3fE.llvm.4982300217658313191 ]]function(param_0)while true do break end end FUNC_LIST[8] =--[[ _ZN3std10sys_common9backtrace28__rust_begin_short_backtrace17hbbb2ed59a3c0ab73E ]]function(param_0)while true do TABLE_LIST[0].data[param_0 ]()break end end FUNC_LIST[9] =--[[ _ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17h489b279a702b2e8dE ]]function(param_0)while true do FUNC_LIST[40](param_0 )FUNC_LIST[36](param_0 )break end end FUNC_LIST[10] =--[[ _ZN4core5alloc6global11GlobalAlloc12alloc_zeroed17hafc4585eb4e8f428E ]]function(param_0, param_1, param_2)local reg_0 local desired while true do while true do reg_0 = FUNC_LIST[58](param_0 , param_1 , param_2 )param_1 = reg_0 if param_1 == 0 then break end reg_0 = FUNC_LIST[133](param_1 , 0 , param_2 )break end reg_0 = param_1 break end return reg_0 end FUNC_LIST[11] =--[[ _ZN4core5alloc6global11GlobalAlloc7realloc17hf67c68f85c90ffeeE ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0 = 0  local reg_0 local desired while true do while true do reg_0 = FUNC_LIST[58](param_0 , param_2 , param_4 )loc_0 = reg_0 if loc_0 == 0 then break end reg_0 = FUNC_LIST[132](loc_0 , param_1 , (param_3 < param_4 and param_3 or param_4 ))FUNC_LIST[59](param_0 , param_1 , param_2 , param_3 )break end reg_0 = loc_0 break end return reg_0 end FUNC_LIST[12] =--[[ _ZN6lua_sb4main17h16b5670a981040c1E ]]function()local loc_0, loc_1, loc_2 = 0 , 0 , 0  local reg_0, reg_1 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 reg_1 = FUNC_LIST[23]()store_i32(memory_at_0, loc_0 + 12, reg_1 )FUNC_LIST[29](loc_0 , 18 , 0 )loc_1 = load_i32(memory_at_0, loc_0 + 4)loc_2 = load_i32(memory_at_0, loc_0 )store_i64(memory_at_0, loc_2 , load_i64(memory_at_0, 0 + 1048600))store_i32_n16(memory_at_0, add_i32(loc_2 , 16 ), load_i32_u16(memory_at_0, 0 + 1048616))store_i64(memory_at_0, add_i32(loc_2 , 8 ), load_i64(memory_at_0, 0 + 1048608))store_i32(memory_at_0, loc_0 + 24, 18 )store_i32(memory_at_0, loc_0 + 20, loc_1 )store_i32(memory_at_0, loc_0 + 16, loc_2 )FUNC_LIST[0](loc_2 , 18 )FUNC_LIST[9](add_i32(loc_0 , 16 ))FUNC_LIST[24](add_i32(loc_0 , 12 ))GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[13] =--[[ __rg_alloc ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[58](1051648 , param_1 , param_0 )break end return reg_0 end FUNC_LIST[14] =--[[ __rg_dealloc ]]function(param_0, param_1, param_2)while true do FUNC_LIST[59](1051648 , param_0 , param_2 , param_1 )break end end FUNC_LIST[15] =--[[ __rg_realloc ]]function(param_0, param_1, param_2, param_3)local reg_0 while true do reg_0 = FUNC_LIST[11](1051648 , param_0 , param_2 , param_1 , param_3 )break end return reg_0 end FUNC_LIST[16] =--[[ __rg_alloc_zeroed ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[10](1051648 , param_1 , param_0 )break end return reg_0 end FUNC_LIST[17] =--[[ main ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[4](4 , param_0 , param_1 , 0 )break end return reg_0 end FUNC_LIST[18] =--[[ __rust_alloc ]]function(param_0, param_1)local loc_0 = 0  local reg_0 local desired while true do reg_0 = FUNC_LIST[13](param_0 , param_1 )loc_0 = reg_0 reg_0 = loc_0 break end return reg_0 end FUNC_LIST[19] =--[[ __rust_dealloc ]]function(param_0, param_1, param_2)local desired while true do FUNC_LIST[14](param_0 , param_1 , param_2 )break end end FUNC_LIST[20] =--[[ __rust_realloc ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 local desired while true do reg_0 = FUNC_LIST[15](param_0 , param_1 , param_2 , param_3 )loc_0 = reg_0 reg_0 = loc_0 break end return reg_0 end FUNC_LIST[21] =--[[ __rust_alloc_zeroed ]]function(param_0, param_1)local loc_0 = 0  local reg_0 local desired while true do reg_0 = FUNC_LIST[16](param_0 , param_1 )loc_0 = reg_0 reg_0 = loc_0 break end return reg_0 end FUNC_LIST[22] =--[[ __rust_alloc_error_handler ]]function(param_0, param_1)local desired while true do FUNC_LIST[94](param_0 , param_1 )break end end FUNC_LIST[23] =--[[ _ZN9roblox_rs9generated9DataModel8instance17h1ae7fd6140b5ec43E ]]function()local reg_0 while true do reg_0 = FUNC_LIST[2]()break end return reg_0 end FUNC_LIST[24] =--[[ _ZN67_$LT$roblox_rs..generated..Sky$u20$as$u20$core..ops..drop..Drop$GT$4drop17he6686ecf6d1bedecE ]]function(param_0)while true do FUNC_LIST[1](load_i32(memory_at_0, param_0 ))break end end FUNC_LIST[25] =--[[ _ZN5alloc5alloc6Global10alloc_impl17h2dafd55d05374e35E.llvm.14201643677092814246 ]]function(param_0, param_1, param_2, param_3)local reg_0 local desired while true do while true do if param_2 == 0 then break end while true do if param_3 ~= 0 then break end reg_0 = FUNC_LIST[18](param_2 , param_1 )param_1 = reg_0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end reg_0 = FUNC_LIST[21](param_2 , param_1 )param_1 = reg_0 break end store_i32(memory_at_0, param_0 + 4, param_2 )store_i32(memory_at_0, param_0 , param_1 )break end end FUNC_LIST[26] =--[[ _ZN5alloc7raw_vec11finish_grow17hbadf6044b02d0a4aE ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do if param_1 == 0 then break end while true do while true do while true do if le_i32(param_2 , 4294967295 )then break end if load_i32(memory_at_0, param_3 + 4)~= 0 then desired = 5 break end FUNC_LIST[27](loc_0 , param_1 , param_2 )loc_1 = load_i32(memory_at_0, loc_0 + 4)param_3 = load_i32(memory_at_0, loc_0 )desired = 4 break end if desired then if desired == 5 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )desired = 2 break end if desired then if desired == 4 then desired = nil end break end while true do loc_1 = load_i32(memory_at_0, add_i32(param_3 , 8 ))if loc_1 ~= 0 then break end FUNC_LIST[25](add_i32(loc_0 , 8 ), param_1 , param_2 , 0 )loc_1 = load_i32(memory_at_0, loc_0 + 12)param_3 = load_i32(memory_at_0, loc_0 + 8)desired = 4 break end if desired then if desired == 4 then desired = nil end break end reg_0 = FUNC_LIST[20](load_i32(memory_at_0, param_3 ), loc_1 , param_1 , param_2 )param_3 = reg_0 loc_1 = param_2 break end if desired then if desired == 3 then desired = nil end break end while true do if param_3 == 0 then break end store_i32(memory_at_0, param_0 + 4, param_3 )store_i32(memory_at_0, add_i32(param_0 , 8 ), loc_1 )param_2 = 0 desired = 1 break end if desired then if desired == 3 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, param_1 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )desired = 2 break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )break end if desired then if desired == 1 then desired = nil end break end param_2 = 1 break end store_i32(memory_at_0, param_0 , param_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[27] =--[[ _ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h14f49e0011641458E.llvm.14201643677092814246 ]]function(param_0, param_1, param_2)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[25](add_i32(loc_0 , 8 ), param_1 , param_2 , 0 )param_2 = load_i32(memory_at_0, loc_0 + 12)store_i32(memory_at_0, param_0 , load_i32(memory_at_0, loc_0 + 8))store_i32(memory_at_0, param_0 + 4, param_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[28] =--[[ _ZN5alloc7raw_vec14handle_reserve17h0e1a4b75bd0cf586E.llvm.14201643677092814246 ]]function(param_0, param_1)local desired while true do while true do while true do if param_0 == 2147483649 then break end if param_0 == 0 then desired = 1 break end FUNC_LIST[98](param_0 , param_1 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end end FUNC_LIST[29] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$11allocate_in17h05fe473388184edbE ]]function(param_0, param_1, param_2)local loc_0, loc_1 = 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do if param_1 ~= 0 then break end param_2 = 1 desired = 1 break end if desired then if desired == 1 then desired = nil end break end while true do loc_1 = (gt_i32(param_1 , 4294967295 )and 1 or 0)if loc_1 == 0 then break end while true do while true do if param_2 ~= 0 then break end FUNC_LIST[27](add_i32(loc_0 , 8 ), loc_1 , param_1 )param_2 = load_i32(memory_at_0, loc_0 + 8)desired = 3 break end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[30](loc_0 , loc_1 , param_1 )param_2 = load_i32(memory_at_0, loc_0 )break end if desired then if desired == 2 then desired = nil end break end if param_2 ~= 0 then desired = 1 break end FUNC_LIST[98](loc_1 , param_1 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end store_i32(memory_at_0, param_0 + 4, param_1 )store_i32(memory_at_0, param_0 , param_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[30] =--[[ _ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$15allocate_zeroed17h1b8e389c4e6165a0E.llvm.14201643677092814246 ]]function(param_0, param_1, param_2)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[25](add_i32(loc_0 , 8 ), param_1 , param_2 , 1 )param_2 = load_i32(memory_at_0, loc_0 + 12)store_i32(memory_at_0, param_0 , load_i32(memory_at_0, loc_0 + 8))store_i32(memory_at_0, param_0 + 4, param_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[31] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$11allocate_in17h071ced30baf8ffc2E ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do if param_1 ~= 0 then break end param_2 = 4 desired = 1 break end if desired then if desired == 1 then desired = nil end break end while true do if param_1 > 536870911 then break end loc_1 = shl_i32(param_1 , 2 )if le_i32(loc_1 , 4294967295 )then break end loc_2 = shl_i32((param_1 < 536870912 and 1 or 0), 2 )while true do while true do if param_2 ~= 0 then break end FUNC_LIST[27](add_i32(loc_0 , 8 ), loc_2 , loc_1 )param_2 = load_i32(memory_at_0, loc_0 + 8)desired = 3 break end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[30](loc_0 , loc_2 , loc_1 )param_2 = load_i32(memory_at_0, loc_0 )break end if desired then if desired == 2 then desired = nil end break end if param_2 ~= 0 then desired = 1 break end FUNC_LIST[98](loc_2 , loc_1 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end store_i32(memory_at_0, param_0 + 4, param_1 )store_i32(memory_at_0, param_0 , param_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[32] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$14grow_amortized17h1743d1142dedf24cE ]]function(param_0, param_1, param_2, param_3)local loc_0, loc_1 = 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 loc_1 = 0 while true do param_3 = add_i32(param_2 , param_3 )if param_3 < param_2 then break end param_2 = load_i32(memory_at_0, param_1 + 4)loc_1 = shl_i32(param_2 , 1 )param_3 = (loc_1 > param_3 and loc_1 or param_3 )param_3 = (param_3 > 8 and param_3 or 8 )loc_1 = shr_u32(bxor_i32(param_3 , 4294967295 ), 31 )while true do while true do if param_2 == 0 then break end store_i32(memory_at_0, loc_0 + 24, param_2 )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, load_i32(memory_at_0, param_1 ))desired = 2 break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, loc_0 + 20, 0 )break end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[26](loc_0 , loc_1 , param_3 , add_i32(loc_0 , 16 ), loc_0 )loc_1 = load_i32(memory_at_0, loc_0 + 4)while true do if load_i32(memory_at_0, loc_0 )== 0 then break end param_3 = load_i32(memory_at_0, add_i32(loc_0 , 8 ))desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, param_1 + 4, param_3 )store_i32(memory_at_0, param_1 , loc_1 )loc_1 = 2147483649 break end store_i32(memory_at_0, param_0 + 4, param_3 )store_i32(memory_at_0, param_0 , loc_1 )GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[33] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$16reserve_for_push17h072e32950560201cE ]]function(param_0, param_1)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[32](add_i32(loc_0 , 8 ), param_0 , param_1 , 1 )FUNC_LIST[28](load_i32(memory_at_0, loc_0 + 8), load_i32(memory_at_0, loc_0 + 12))GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[34] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$7reserve21do_reserve_and_handle17hbdf8a92e29d7d252E ]]function(param_0, param_1, param_2)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[32](add_i32(loc_0 , 8 ), param_0 , param_1 , param_2 )FUNC_LIST[28](load_i32(memory_at_0, loc_0 + 8), load_i32(memory_at_0, loc_0 + 12))GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[35] =--[[ _ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17h2e9501d1ae724a74E.llvm.14201643677092814246 ]]function(param_0, param_1, param_2)local desired while true do while true do if param_2 == 0 then break end FUNC_LIST[19](param_0 , param_2 , param_1 )break end break end end FUNC_LIST[36] =--[[ _ZN77_$LT$alloc..raw_vec..RawVec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h3b453ca22c959331E ]]function(param_0)local loc_0 = 0  local desired while true do while true do loc_0 = load_i32(memory_at_0, param_0 + 4)if loc_0 == 0 then break end FUNC_LIST[35](load_i32(memory_at_0, param_0 ), 1 , loc_0 )break end break end end FUNC_LIST[37] =--[[ _ZN132_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$alloc..vec..spec_extend..SpecExtend$LT$$RF$T$C$core..slice..iter..Iter$LT$T$GT$$GT$$GT$11spec_extend17he91777305342a611E ]]function(param_0, param_1, param_2)local loc_0 = 0  local reg_0 while true do param_2 = sub_i32(param_2 , param_1 )FUNC_LIST[38](param_0 , param_2 )loc_0 = load_i32(memory_at_0, param_0 + 8)reg_0 = FUNC_LIST[132](add_i32(load_i32(memory_at_0, param_0 ), loc_0 ), param_1 , param_2 )store_i32(memory_at_0, param_0 + 8, add_i32(loc_0 , param_2 ))break end end FUNC_LIST[38] =--[[ _ZN5alloc3vec16Vec$LT$T$C$A$GT$7reserve17h320c9464959cf3bdE ]]function(param_0, param_1)local loc_0 = 0  local desired while true do while true do loc_0 = load_i32(memory_at_0, param_0 + 8)if sub_i32(load_i32(memory_at_0, param_0 + 4), loc_0 )>= param_1 then break end FUNC_LIST[34](param_0 , loc_0 , param_1 )break end break end end FUNC_LIST[39] =--[[ _ZN5alloc3vec16Vec$LT$T$C$A$GT$17extend_from_slice17he55d1cda495ada9eE ]]function(param_0, param_1, param_2)while true do FUNC_LIST[37](param_0 , param_1 , add_i32(param_1 , param_2 ))break end end FUNC_LIST[40] =--[[ _ZN70_$LT$alloc..vec..Vec$LT$T$C$A$GT$$u20$as$u20$core..ops..drop..Drop$GT$4drop17h92d6fc6efb177f6bE ]]function(param_0)while true do break end end FUNC_LIST[41] =--[[ _ZN4core3ptr48drop_in_place$LT$wee_alloc..LargeAllocPolicy$GT$17h792c51f02281429dE ]]function(param_0)while true do break end end FUNC_LIST[42] =--[[ _ZN9wee_alloc12size_classes11SizeClasses3get17h73754e8e66f4735aE ]]function(param_0, param_1)local reg_0 local desired while true do while true do if param_1 == 0 then break end reg_0 = (param_1 < 257 and add_i32(add_i32(shl_i32(param_1 , 2 ), param_0 ), 4294967292 )or 0 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1048784 , 33 , 1048952 )error("out of code bounds")end return reg_0 end FUNC_LIST[43] =--[[ _ZN88_$LT$wee_alloc..size_classes..SizeClassAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$22new_cell_for_free_list17h271283570b1c8278E ]]function(param_0, param_1, param_2, param_3)local loc_0, loc_1 = 0 , 0  local loc_2 = i64_ZERO  local reg_0, reg_1 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do reg_1 = FUNC_LIST[63](8 )loc_1 = add_i32(param_2 , reg_1 )if loc_1 < param_2 then break end loc_2 = extend_i64_u32(loc_1 )loc_2 = mul_i64(loc_2 , loc_2 )if wrap_i32_i64(shr_u64(loc_2 , i64_from_u32(32, 0) ))~= 0 then desired = 3 break end reg_0 = FUNC_LIST[63](8192 )param_2 = reg_0 param_1 = load_i32(memory_at_0, param_1 )store_i32(memory_at_0, loc_0 + 12, load_i32(memory_at_0, param_1 ))loc_1 = wrap_i32_i64(loc_2 )loc_1 = (loc_1 > param_2 and loc_1 or param_2 )reg_0 = FUNC_LIST[56](loc_1 , 4 , add_i32(loc_0 , 12 ), 1048968 , 1048968 )param_2 = reg_0 store_i32(memory_at_0, param_1 , load_i32(memory_at_0, loc_0 + 12))while true do while true do if param_2 ~= 0 then break end loc_1 = 1 desired = 5 break end if desired then if desired == 5 then desired = nil end break end if loc_1 >= 1073741824 then desired = 2 break end if loc_1 <= 1 then desired = 1 break end store_i64(memory_at_0, param_2 + 4, i64_ZERO )store_i32(memory_at_0, param_2 , bor_i32(add_i32(param_2 , shl_i32(loc_1 , 2 )), 2 ))loc_1 = 0 break end if desired then if desired == 4 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, param_2 )store_i32(memory_at_0, param_0 , loc_1 )GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )desired = 0 break end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[109](1048832 , 28 , 1048704 )error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[109](1048720 , 33 , 1048704 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[109](1048720 , 33 , 1048704 )error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1048784 , 33 , 1048756 )error("out of code bounds")end end FUNC_LIST[44] =--[[ _ZN88_$LT$wee_alloc..size_classes..SizeClassAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$13min_cell_size17hc52b4239b506d7d3E ]]function(param_0, param_1)local reg_0 while true do reg_0 = param_1 break end return reg_0 end FUNC_LIST[45] =--[[ _ZN88_$LT$wee_alloc..size_classes..SizeClassAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$32should_merge_adjacent_free_cells17h2c24af81e2115050E ]]function(param_0)local reg_0 while true do reg_0 = 0 break end return reg_0 end FUNC_LIST[46] =--[[ _ZN4core3ptr42drop_in_place$LT$wee_alloc..CellHeader$GT$17hdf7330384fec52a7E ]]function(param_0)while true do break end end FUNC_LIST[47] =--[[ _ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17hb45ff3d7fbc62f54E ]]function(param_0)local reg_0 local desired while true do while true do if param_0 < 1073741824 then break end FUNC_LIST[109](1049104 , 33 , 1049140 )error("out of code bounds")end reg_0 = shl_i32(param_0 , 2 )break end return reg_0 end FUNC_LIST[48] =--[[ _ZN70_$LT$memory_units..Bytes$u20$as$u20$core..ops..arith..Sub$LT$T$GT$$GT$3sub17h86298b31808af062E ]]function(param_0)local desired while true do while true do if param_0 < 8 then break end desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049200 )error("out of code bounds")end end FUNC_LIST[49] =--[[ _ZN9wee_alloc9neighbors18Neighbors$LT$T$GT$6remove17haf49e843462ba391E ]]function(param_0)local loc_0, loc_1 = 0 , 0  local desired while true do while true do loc_0 = load_i32(memory_at_0, param_0 )loc_1 = band_i32(loc_0 , 4294967292 )if loc_1 == 0 then break end if band_i32(loc_0 , 2 )~= 0 then break end store_i32(memory_at_0, loc_1 + 4, bor_i32(band_i32(load_i32(memory_at_0, loc_1 + 4), 3 ), band_i32(load_i32(memory_at_0, param_0 + 4), 4294967292 )))break end while true do loc_1 = load_i32(memory_at_0, param_0 + 4)loc_0 = band_i32(loc_1 , 4294967292 )if loc_0 == 0 then break end store_i32(memory_at_0, loc_0 , bor_i32(band_i32(load_i32(memory_at_0, loc_0 ), 3 ), band_i32(load_i32(memory_at_0, param_0 ), 4294967292 )))loc_1 = load_i32(memory_at_0, param_0 + 4)break end store_i32(memory_at_0, param_0 + 4, band_i32(loc_1 , 3 ))store_i32(memory_at_0, param_0 , band_i32(load_i32(memory_at_0, param_0 ), 3 ))break end end FUNC_LIST[50] =--[[ _ZN9wee_alloc10CellHeader4size17hc3d6d68139eb9e2aE ]]function(param_0)local loc_0 = 0  local reg_0 local desired while true do while true do loc_0 = add_i32(param_0 , 8 )param_0 = band_i32(load_i32(memory_at_0, param_0 ), 4294967292 )if loc_0 > param_0 then break end reg_0 = sub_i32(param_0 , loc_0 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049364 )error("out of code bounds")end return reg_0 end FUNC_LIST[51] =--[[ _ZN70_$LT$wee_alloc..LargeAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$22new_cell_for_free_list17h600799de054e5c2aE ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 local desired while true do reg_0 = FUNC_LIST[47](param_2 )loc_0 = reg_0 while true do while true do while true do while true do param_2 = add_i32(param_3 , 2048 )if param_2 < param_3 then break end if param_2 >= 536870912 then desired = 3 break end param_3 = shl_i32(param_2 , 3 )param_3 = (loc_0 > param_3 and loc_0 or param_3 )param_2 = add_i32(param_3 , 8 )if param_2 < param_3 then desired = 2 break end while true do while true do reg_0 = FUNC_LIST[62](param_2 )param_2 = reg_0 reg_0 = FUNC_LIST[60](param_2 )param_3 = reg_0 if param_3 ~= 0 then break end param_2 = 1 desired = 5 break end if desired then if desired == 5 then desired = nil end break end if param_2 >= 65536 then desired = 1 break end param_2 = shl_i32(param_2 , 16 )FUNC_LIST[48](param_2 )store_i64(memory_at_0, param_3 + 4, i64_ZERO )store_i32(memory_at_0, param_3 , bor_i32(add_i32(param_3 , param_2 ), 2 ))param_2 = 0 break end if desired then if desired == 4 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, param_3 )store_i32(memory_at_0, param_0 , param_2 )desired = 0 break end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[109](1049216 , 28 , 1049200 )error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[109](1049104 , 33 , 1049200 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[109](1049216 , 28 , 1049200 )error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1049104 , 33 , 1049076 )error("out of code bounds")end end FUNC_LIST[52] =--[[ _ZN70_$LT$wee_alloc..LargeAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$13min_cell_size17hcb74ad39f1f287daE ]]function(param_0, param_1)local reg_0 while true do reg_0 = 512 break end return reg_0 end FUNC_LIST[53] =--[[ _ZN70_$LT$wee_alloc..LargeAllocPolicy$u20$as$u20$wee_alloc..AllocPolicy$GT$32should_merge_adjacent_free_cells17ha5c3ad45dcdaef3cE ]]function(param_0)local reg_0 while true do reg_0 = 1 break end return reg_0 end FUNC_LIST[54] =--[[ _ZN9wee_alloc15alloc_first_fit17h79ea1af50e7a1467E.llvm.11868136739520158798 ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6, loc_7, loc_8 = 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0 local desired while true do loc_0 = add_i32(param_1 , 4294967295 )loc_1 = 0 loc_2 = sub_i32(0 , param_1 )loc_3 = load_i32(memory_at_0, param_2 )while true do while true do if loc_3 == 0 then desired = 1 break end while true do while true do while true do while true do while true do while true do while true do while true do while true do while true do while true do while true do loc_4 = load_i32(memory_at_0, loc_3 + 8)if band_i32(loc_4 , 1 )~= 0 then break end loc_4 = add_i32(loc_3 , 8 )reg_0 = FUNC_LIST[47](param_0 )loc_5 = reg_0 reg_0 = FUNC_LIST[50](loc_3 )if reg_0 < loc_5 then desired = 5 break end loc_6 = band_i32(load_i32(memory_at_0, loc_3 ), 4294967292 )if loc_6 < loc_5 then desired = 11 break end if param_1 == 0 then desired = 10 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_4 + 16)](param_3 , param_0 )reg_0 = FUNC_LIST[47](reg_0 )loc_7 = reg_0 loc_8 = add_i32(loc_4 , 8 )if loc_8 < loc_4 then desired = 9 break end loc_7 = add_i32(loc_8 , loc_7 )if loc_7 < loc_8 then desired = 8 break end while true do loc_5 = band_i32(sub_i32(loc_6 , loc_5 ), loc_2 )if loc_7 <= loc_5 then break end if band_i32(loc_0 , loc_4 )~= 0 then desired = 5 break end store_i32(memory_at_0, param_2 , band_i32(load_i32(memory_at_0, loc_3 + 8), 4294967292 ))param_2 = load_i32(memory_at_0, loc_3 )loc_4 = loc_3 desired = 12 break end if desired then if desired == 14 then desired = nil end break end if loc_5 < 8 then desired = 7 break end param_2 = add_i32(loc_5 , 4294967288 )reg_0 = FUNC_LIST[55](param_2 )loc_4 = reg_0 while true do if loc_6 < param_2 then break end FUNC_LIST[48](sub_i32(loc_6 , param_2 ))loc_5 = 0 store_i32(memory_at_0, loc_4 + 8, 0 )store_i64(memory_at_0, loc_4 , i64_ZERO )store_i32(memory_at_0, loc_4 , band_i32(load_i32(memory_at_0, loc_3 ), 4294967292 ))while true do loc_8 = load_i32(memory_at_0, loc_3 )param_0 = band_i32(loc_8 , 4294967292 )if param_0 == 0 then break end if band_i32(loc_8 , 2 )~= 0 then break end store_i32(memory_at_0, param_0 + 4, bor_i32(band_i32(load_i32(memory_at_0, param_0 + 4), 3 ), param_2 ))loc_5 = band_i32(load_i32(memory_at_0, loc_4 + 4), 3 )break end if desired then if desired == 15 then desired = nil end break end store_i32(memory_at_0, loc_4 + 4, bor_i32(loc_5 , loc_3 ))store_i32(memory_at_0, loc_3 + 8, band_i32(load_i32(memory_at_0, loc_3 + 8), 4294967294 ))param_2 = bor_i32(band_i32(load_i32(memory_at_0, loc_3 ), 3 ), param_2 )store_i32(memory_at_0, loc_3 , param_2 )if band_i32(param_2 , 2 )~= 0 then desired = 13 break end param_2 = load_i32(memory_at_0, loc_4 )desired = 12 break end if desired then if desired == 14 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049444 )error("out of code bounds")end if desired then if desired == 13 then desired = nil end break end store_i32(memory_at_0, loc_3 + 8, band_i32(loc_4 , 4294967294 ))loc_4 = band_i32(load_i32(memory_at_0, loc_3 + 4), 4294967292 )if loc_4 == 0 then desired = 6 break end if band_i32(load_i32_u8(memory_at_0, loc_4 ), 1 )~= 0 then desired = 6 break end FUNC_LIST[49](loc_3 )if band_i32(load_i32_u8(memory_at_0, loc_3 ), 2 )== 0 then desired = 4 break end store_i32(memory_at_0, loc_4 , bor_i32(load_i32(memory_at_0, loc_4 ), 2 ))desired = 4 break end if desired then if desired == 12 then desired = nil end break end store_i32(memory_at_0, loc_3 , band_i32(param_2 , 4294967293 ))param_2 = bor_i32(load_i32(memory_at_0, loc_4 ), 2 )break end if desired then if desired == 11 then desired = nil end break end store_i32(memory_at_0, loc_4 , bor_i32(param_2 , 1 ))loc_1 = add_i32(loc_4 , 8 )desired = 1 break end if desired then if desired == 10 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049380 )error("out of code bounds")end if desired then if desired == 9 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049396 )error("out of code bounds")end if desired then if desired == 8 then desired = nil end break end FUNC_LIST[109](1049216 , 28 , 1049412 )error("out of code bounds")end if desired then if desired == 7 then desired = nil end break end FUNC_LIST[109](1049216 , 28 , 1049412 )error("out of code bounds")end if desired then if desired == 6 then desired = nil end break end FUNC_LIST[109](1049248 , 33 , 1049428 )error("out of code bounds")end if desired then if desired == 5 then desired = nil end break end FUNC_LIST[109](1049156 , 43 , 1049508 )error("out of code bounds")end if desired then if desired == 4 then desired = nil end break end loc_3 = load_i32(memory_at_0, loc_4 )store_i32(memory_at_0, param_2 , loc_3 )desired = 2 break end if desired then if desired == 3 then desired = nil continue end break end store_i32(memory_at_0, param_2 , loc_4 )reg_0 = FUNC_LIST[50](loc_4 )loc_3 = loc_4 continue end if desired then if desired == 2 then desired = nil continue end break end break end if desired then if desired == 1 then desired = nil end break end break end reg_0 = loc_1 break end return reg_0 end FUNC_LIST[55] =--[[ _ZN9wee_alloc16unchecked_unwrap17he011e75cb67f4f7eE ]]function(param_0)local reg_0 local desired while true do while true do if param_0 ~= 0 then break end FUNC_LIST[109](1049156 , 43 , 1049508 )error("out of code bounds")end reg_0 = param_0 break end return reg_0 end FUNC_LIST[56] =--[[ _ZN9wee_alloc17alloc_with_refill17h54c8cc0e7a2611a1E ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do reg_0 = FUNC_LIST[54](param_0 , param_1 , param_2 , param_3 , param_4 )loc_1 = reg_0 if loc_1 ~= 0 then break end TABLE_LIST[0].data[load_i32(memory_at_0, param_4 + 12)](add_i32(loc_0 , 8 ), param_3 , param_0 , param_1 )loc_1 = 0 if load_i32(memory_at_0, loc_0 + 8)~= 0 then break end loc_1 = load_i32(memory_at_0, loc_0 + 12)store_i32(memory_at_0, loc_1 + 8, load_i32(memory_at_0, param_2 ))store_i32(memory_at_0, param_2 , loc_1 )reg_0 = FUNC_LIST[54](param_0 , param_1 , param_2 , param_3 , param_4 )loc_1 = reg_0 break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = loc_1 break end return reg_0 end FUNC_LIST[57] =--[[ _ZN9wee_alloc8WeeAlloc12dealloc_impl28_$u7b$$u7b$closure$u7d$$u7d$17h50f95c93303d7a91E ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 local desired while true do loc_0 = load_i32(memory_at_0, param_0 )param_0 = add_i32(loc_0 , 4294967288 )store_i32(memory_at_0, param_0 , band_i32(load_i32(memory_at_0, param_0 ), 4294967294 ))reg_0 = FUNC_LIST[50](param_0 )store_i32(memory_at_0, loc_0 , 0 )while true do reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_3 + 20)](param_2 )if reg_0 == 0 then break end while true do while true do while true do param_3 = band_i32(load_i32(memory_at_0, add_i32(loc_0 , 4294967292 )), 4294967292 )if param_3 == 0 then break end if band_i32(load_i32_u8(memory_at_0, param_3 ), 1 )~= 0 then break end FUNC_LIST[49](param_0 )if band_i32(load_i32_u8(memory_at_0, param_0 ), 2 )~= 0 then desired = 3 break end desired = 2 break end if desired then if desired == 3 then desired = nil end break end param_2 = load_i32(memory_at_0, param_0 )param_3 = band_i32(param_2 , 4294967292 )if param_3 == 0 then desired = 1 break end if band_i32(param_2 , 2 )~= 0 then desired = 1 break end if band_i32(load_i32_u8(memory_at_0, param_3 ), 1 )~= 0 then desired = 1 break end store_i32(memory_at_0, loc_0 , band_i32(load_i32(memory_at_0, param_3 + 8), 4294967292 ))store_i32(memory_at_0, param_3 + 8, bor_i32(param_0 , 1 ))desired = 0 break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, param_3 , bor_i32(load_i32(memory_at_0, param_3 ), 2 ))break end if desired then if desired == 1 then desired = nil end break end reg_0 = FUNC_LIST[50](param_3 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end store_i32(memory_at_0, loc_0 , load_i32(memory_at_0, param_1 ))store_i32(memory_at_0, param_1 , param_0 )break end end FUNC_LIST[58] =--[[ _ZN72_$LT$wee_alloc..WeeAlloc$u20$as$u20$core..alloc..global..GlobalAlloc$GT$5alloc17h54c6e74e0457c1baE ]]function(param_0, param_1, param_2)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do if param_2 == 0 then break end reg_0 = FUNC_LIST[63](param_2 )param_2 = reg_0 while true do if param_1 >= 5 then break end reg_0 = FUNC_LIST[42](param_0 , param_2 )loc_1 = reg_0 if loc_1 == 0 then break end store_i32(memory_at_0, loc_0 + 4, add_i32(param_0 , 1024 ))store_i32(memory_at_0, loc_0 + 12, load_i32(memory_at_0, loc_1 ))reg_0 = FUNC_LIST[56](param_2 , param_1 , add_i32(loc_0 , 12 ), add_i32(loc_0 , 4 ), 1049484 )param_1 = reg_0 store_i32(memory_at_0, loc_1 , load_i32(memory_at_0, loc_0 + 12))desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 8, load_i32(memory_at_0, param_0 + 1024))reg_0 = FUNC_LIST[56](param_2 , param_1 , add_i32(loc_0 , 8 ), 1049460 , 1049460 )param_1 = reg_0 store_i32(memory_at_0, param_0 + 1024, load_i32(memory_at_0, loc_0 + 8))break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_1 break end return reg_0 end FUNC_LIST[59] =--[[ _ZN72_$LT$wee_alloc..WeeAlloc$u20$as$u20$core..alloc..global..GlobalAlloc$GT$7dealloc17hf94d98fa1384a360E ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do if param_1 == 0 then break end store_i32(memory_at_0, loc_0 + 4, param_1 )if param_3 == 0 then break end reg_0 = FUNC_LIST[63](param_3 )param_1 = reg_0 while true do if param_2 >= 5 then break end reg_0 = FUNC_LIST[42](param_0 , param_1 )param_1 = reg_0 if param_1 == 0 then break end store_i32(memory_at_0, loc_0 + 8, add_i32(param_0 , 1024 ))store_i32(memory_at_0, loc_0 + 12, load_i32(memory_at_0, param_1 ))FUNC_LIST[57](add_i32(loc_0 , 4 ), add_i32(loc_0 , 12 ), add_i32(loc_0 , 8 ), 1049484 )store_i32(memory_at_0, param_1 , load_i32(memory_at_0, loc_0 + 12))desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 12, load_i32(memory_at_0, param_0 + 1024))FUNC_LIST[57](add_i32(loc_0 , 4 ), add_i32(loc_0 , 12 ), 1049460 , 1049460 )store_i32(memory_at_0, param_0 + 1024, load_i32(memory_at_0, loc_0 + 12))break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )break end end FUNC_LIST[60] =--[[ _ZN9wee_alloc10imp_wasm3211alloc_pages17h4a466dcbb98d456dE ]]function(param_0)local reg_0 local desired while true do while true do reg_0 = rt.allocator.grow(memory_at_0, param_0 )param_0 = reg_0 if param_0 ~= 4294967295 then break end reg_0 = 0 desired = 0 break end if desired then if desired == 0 then desired = nil end break end while true do if param_0 > 65535 then break end reg_0 = FUNC_LIST[55](shl_i32(param_0 , 16 ))desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1049632 , 33 , 1049612 )error("out of code bounds")end return reg_0 end FUNC_LIST[61] =--[[ _ZN12memory_units11round_up_to17hc50a6c9a3cb97903E.llvm.4751424611206271077 ]]function(param_0, param_1)local loc_0 = 0  local reg_0 local desired while true do while true do while true do loc_0 = add_i32(param_0 , param_1 )if loc_0 < param_0 then break end if loc_0 == 0 then desired = 1 break end reg_0 = div_u32(add_i32(loc_0 , 4294967295 ), param_1 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[109](1049776 , 28 , 1049752 )error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[109](1049824 , 33 , 1049804 )error("out of code bounds")end return reg_0 end FUNC_LIST[62] =--[[ _ZN12memory_units6wasm3290_$LT$impl$u20$memory_units..RoundUpTo$LT$memory_units..wasm32..Pages$GT$$u20$for$u20$T$GT$11round_up_to17hfb61d3e0f0f2979fE ]]function(param_0)local reg_0 while true do reg_0 = FUNC_LIST[61](param_0 , 65536 )break end return reg_0 end FUNC_LIST[63] =--[[ _ZN12memory_units6wasm3290_$LT$impl$u20$memory_units..RoundUpTo$LT$memory_units..wasm32..Words$GT$$u20$for$u20$T$GT$11round_up_to17ha826a9d0cc6538e6E ]]function(param_0)local reg_0 while true do reg_0 = FUNC_LIST[61](param_0 , 4 )break end return reg_0 end FUNC_LIST[64] =--[[ _ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h1d641f32c254d6adE ]]function(param_0)local reg_0 while true do reg_0 = i64_from_u32(3441327041, 3248670876) break end return reg_0 end FUNC_LIST[65] =--[[ _ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h69045b7f074e68feE ]]function(param_0)local reg_0 while true do reg_0 = i64_from_u32(2806628161, 461491624) break end return reg_0 end FUNC_LIST[66] =--[[ _ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17h79426a9cdef4aa3fE ]]function(param_0)local reg_0 while true do reg_0 = i64_from_u32(3187869221, 1284456005) break end return reg_0 end FUNC_LIST[67] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$7reserve21do_reserve_and_handle17h06865a477901175cE ]]function(param_0, param_1, param_2)local loc_0, loc_1 = 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do param_2 = add_i32(param_1 , param_2 )if param_2 < param_1 then break end param_1 = load_i32(memory_at_0, add_i32(param_0 , 4 ))loc_1 = shl_i32(param_1 , 1 )param_2 = (loc_1 > param_2 and loc_1 or param_2 )param_2 = (param_2 > 8 and param_2 or 8 )loc_1 = shr_u32(bxor_i32(param_2 , 4294967295 ), 31 )while true do while true do if param_1 == 0 then break end store_i32(memory_at_0, loc_0 + 24, param_1 )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, load_i32(memory_at_0, param_0 ))desired = 3 break end if desired then if desired == 3 then desired = nil end break end store_i32(memory_at_0, loc_0 + 20, 0 )break end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[76](loc_0 , loc_1 , param_2 , add_i32(loc_0 , 16 ))param_1 = load_i32(memory_at_0, loc_0 + 4)while true do if load_i32(memory_at_0, loc_0 )~= 0 then break end store_i32(memory_at_0, param_0 , param_1 )store_i32(memory_at_0, add_i32(param_0 , 4 ), param_2 )desired = 1 break end if desired then if desired == 2 then desired = nil end break end if param_1 == 2147483649 then desired = 1 break end if param_1 == 0 then break end FUNC_LIST[98](param_1 , load_i32(memory_at_0, add_i32(loc_0 , 8 )))error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[68] =--[[ _ZN4core3ptr100drop_in_place$LT$$RF$mut$u20$std..io..Write..write_fmt..Adapter$LT$alloc..vec..Vec$LT$u8$GT$$GT$$GT$17hb7741be10ae71fc5E ]]function(param_0)while true do break end end FUNC_LIST[69] =--[[ _ZN3std9panicking11panic_count17is_zero_slow_path17ha8152572b5ae7ea0E ]]function()local reg_0 while true do reg_0 = (load_i32(memory_at_0, 0 + 1052752)== 0 and 1 or 0)break end return reg_0 end FUNC_LIST[70] =--[[ _ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17ha09c803d0c8d5b69E ]]function(param_0)local loc_0 = 0  local desired while true do while true do loc_0 = load_i32(memory_at_0, add_i32(param_0 , 4 ))if loc_0 == 0 then break end FUNC_LIST[19](load_i32(memory_at_0, param_0 ), loc_0 , 1 )break end break end end FUNC_LIST[71] =--[[ _ZN4core3ptr70drop_in_place$LT$std..panicking..begin_panic_handler..PanicPayload$GT$17hc065e3019730a3eaE ]]function(param_0)local loc_0 = 0  local desired while true do while true do loc_0 = load_i32(memory_at_0, param_0 + 4)if loc_0 == 0 then break end param_0 = load_i32(memory_at_0, add_i32(param_0 , 8 ))if param_0 == 0 then break end FUNC_LIST[19](loc_0 , param_0 , 1 )break end break end end FUNC_LIST[72] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$10write_char17ha1d11df153b63892E ]]function(param_0, param_1)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 param_0 = load_i32(memory_at_0, param_0 )while true do while true do if param_1 > 127 then break end while true do loc_1 = load_i32(memory_at_0, param_0 + 8)if loc_1 ~= load_i32(memory_at_0, param_0 + 4)then break end FUNC_LIST[73](param_0 , loc_1 )loc_1 = load_i32(memory_at_0, param_0 + 8)break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, param_0 + 8, add_i32(loc_1 , 1 ))store_i32_n8(memory_at_0, add_i32(load_i32(memory_at_0, param_0 ), loc_1 ), param_1 )desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 12, 0 )while true do while true do if param_1 < 2048 then break end while true do if param_1 < 65536 then break end store_i32_n8(memory_at_0, loc_0 + 15, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 12 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(band_i32(shr_u32(param_1 , 18 ), 7 ), 240 ))param_1 = 4 desired = 2 break end if desired then if desired == 3 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 12 ), 224 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))param_1 = 3 desired = 2 break end if desired then if desired == 2 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 6 ), 192 ))param_1 = 2 break end if desired then if desired == 1 then desired = nil end break end while true do loc_1 = load_i32(memory_at_0, param_0 + 8)if sub_i32(load_i32(memory_at_0, param_0 + 4), loc_1 )>= param_1 then break end FUNC_LIST[67](param_0 , loc_1 , param_1 )loc_1 = load_i32(memory_at_0, param_0 + 8)break end if desired then if desired == 1 then desired = nil end break end reg_0 = FUNC_LIST[132](add_i32(load_i32(memory_at_0, param_0 ), loc_1 ), add_i32(loc_0 , 12 ), param_1 )store_i32(memory_at_0, param_0 + 8, add_i32(loc_1 , param_1 ))break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = 0 break end return reg_0 end FUNC_LIST[73] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$16reserve_for_push17he555a757605ad552E ]]function(param_0, param_1)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do param_1 = add_i32(param_1 , 1 )if param_1 == 0 then break end loc_1 = load_i32(memory_at_0, add_i32(param_0 , 4 ))loc_2 = shl_i32(loc_1 , 1 )param_1 = (loc_2 > param_1 and loc_2 or param_1 )param_1 = (param_1 > 8 and param_1 or 8 )loc_2 = shr_u32(bxor_i32(param_1 , 4294967295 ), 31 )while true do while true do if loc_1 == 0 then break end store_i32(memory_at_0, loc_0 + 24, loc_1 )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, load_i32(memory_at_0, param_0 ))desired = 3 break end if desired then if desired == 3 then desired = nil end break end store_i32(memory_at_0, loc_0 + 20, 0 )break end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[76](loc_0 , loc_2 , param_1 , add_i32(loc_0 , 16 ))loc_1 = load_i32(memory_at_0, loc_0 + 4)while true do if load_i32(memory_at_0, loc_0 )~= 0 then break end store_i32(memory_at_0, param_0 , loc_1 )store_i32(memory_at_0, add_i32(param_0 , 4 ), param_1 )desired = 1 break end if desired then if desired == 2 then desired = nil end break end if loc_1 == 2147483649 then desired = 1 break end if loc_1 == 0 then break end FUNC_LIST[98](loc_1 , load_i32(memory_at_0, add_i32(loc_0 , 8 )))error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[74] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_fmt17hdb87f1534fbfde3dE ]]function(param_0, param_1)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 param_0 = load_i32(memory_at_0, param_0 )store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 16 ), load_i64(memory_at_0, add_i32(param_1 , 16 )))store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 8 ), load_i64(memory_at_0, add_i32(param_1 , 8 )))store_i64(memory_at_0, loc_0 + 8, load_i64(memory_at_0, param_1 ))store_i32(memory_at_0, loc_0 + 4, param_0 )reg_0 = FUNC_LIST[111](add_i32(loc_0 , 4 ), 1049900 , add_i32(loc_0 , 8 ))param_1 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )reg_0 = param_1 break end return reg_0 end FUNC_LIST[75] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_str17h55ba2d6aa1e90a91E ]]function(param_0, param_1, param_2)local loc_0 = 0  local reg_0 local desired while true do while true do param_0 = load_i32(memory_at_0, param_0 )loc_0 = load_i32(memory_at_0, param_0 + 8)if sub_i32(load_i32(memory_at_0, param_0 + 4), loc_0 )>= param_2 then break end FUNC_LIST[67](param_0 , loc_0 , param_2 )loc_0 = load_i32(memory_at_0, param_0 + 8)break end reg_0 = FUNC_LIST[132](add_i32(load_i32(memory_at_0, param_0 ), loc_0 ), param_1 , param_2 )store_i32(memory_at_0, param_0 + 8, add_i32(loc_0 , param_2 ))reg_0 = 0 break end return reg_0 end FUNC_LIST[76] =--[[ _ZN5alloc7raw_vec11finish_grow17h5cd33ab5b82d7fd5E ]]function(param_0, param_1, param_2, param_3)local loc_0 = 0  local reg_0 local desired while true do while true do while true do if param_1 == 0 then break end while true do while true do while true do while true do while true do if le_i32(param_2 , 4294967295 )then break end if load_i32(memory_at_0, param_3 + 4)== 0 then desired = 5 break end loc_0 = load_i32(memory_at_0, add_i32(param_3 , 8 ))if loc_0 ~= 0 then desired = 6 break end if param_2 ~= 0 then desired = 4 break end param_3 = param_1 desired = 3 break end if desired then if desired == 6 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )desired = 1 break end if desired then if desired == 5 then desired = nil end break end reg_0 = FUNC_LIST[20](load_i32(memory_at_0, param_3 ), loc_0 , param_1 , param_2 )param_3 = reg_0 desired = 3 break end if desired then if desired == 4 then desired = nil end break end if param_2 ~= 0 then break end param_3 = param_1 desired = 3 break end if desired then if desired == 3 then desired = nil end break end reg_0 = FUNC_LIST[18](param_2 , param_1 )param_3 = reg_0 break end if desired then if desired == 2 then desired = nil end break end while true do if param_3 == 0 then break end store_i32(memory_at_0, param_0 + 4, param_3 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )store_i32(memory_at_0, param_0 , 0 )desired = 0 break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, param_1 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )break end if desired then if desired == 0 then desired = nil end break end store_i32(memory_at_0, param_0 , 1 )break end end FUNC_LIST[77] =--[[ _ZN3std3sys4wasm4once4Once4call17ha9fe4ce984d31724E ]]function(param_0)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local desired local br_map = {} while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do while true do while true do while true do if not br_map[1] then br_map[1] = (function() return {[0] =0,2,6,1,} end)()end local temp = br_map[1][load_i32_u8(memory_at_0, 0 + 1052677)] or 0 if temp < 2 then if temp < 1 then break else desired = 6 break end elseif temp > 2 then desired = 1 break else desired = 5 break end end if desired then if desired == 6 then desired = nil end break end store_i32_n8(memory_at_0, 0 + 1052677, 2 )loc_1 = load_i32_u8(memory_at_0, param_0 )store_i32_n8(memory_at_0, param_0 , 0 )if loc_1 == 0 then desired = 4 break end store_i32_n8(memory_at_0, loc_0 + 31, 0 )while true do while true do if load_i32_u8(memory_at_0, 0 + 1052712)== 3 then break end FUNC_LIST[80](add_i32(loc_0 , 31 ))if load_i32_u8(memory_at_0, loc_0 + 31)~= 0 then desired = 7 break end break end if desired then if desired == 7 then desired = nil end break end while true do while true do if load_i32(memory_at_0, 0 + 1052680)== 1052764 then break end loc_1 = load_i32_u8(memory_at_0, 0 + 1052708)param_0 = 1 store_i32_n8(memory_at_0, 0 + 1052708, 1 )if loc_1 ~= 0 then desired = 7 break end store_i32(memory_at_0, 0 + 1052680, 1052764 )desired = 8 break end if desired then if desired == 8 then desired = nil end break end param_0 = add_i32(load_i32(memory_at_0, 0 + 1052684), 1 )if param_0 == 0 then desired = 3 break end break end if desired then if desired == 7 then desired = nil end break end store_i32(memory_at_0, 0 + 1052684, param_0 )if load_i32(memory_at_0, 0 + 1052688)~= 0 then desired = 2 break end store_i32(memory_at_0, 0 + 1052688, 4294967295 )while true do if load_i32_u8(memory_at_0, 0 + 1052704)~= 0 then break end if load_i32(memory_at_0, 0 + 1052700)== 0 then break end store_i32(memory_at_0, 0 + 1052700, 0 )store_i32_n8(memory_at_0, 0 + 1052704, 0 )break end if desired then if desired == 7 then desired = nil end break end loc_1 = 0 while true do loc_2 = load_i32(memory_at_0, 0 + 1052696)if loc_2 == 0 then break end FUNC_LIST[19](load_i32(memory_at_0, 0 + 1052692), loc_2 , 1 )loc_1 = add_i32(load_i32(memory_at_0, 0 + 1052688), 1 )param_0 = load_i32(memory_at_0, 0 + 1052684)break end if desired then if desired == 7 then desired = nil end break end store_i64(memory_at_0, 0 + 1052696, i64_ZERO )store_i32(memory_at_0, 0 + 1052692, 1 )store_i32(memory_at_0, 0 + 1052688, loc_1 )param_0 = add_i32(param_0 , 4294967295 )store_i32(memory_at_0, 0 + 1052684, param_0 )store_i32_n8(memory_at_0, 0 + 1052704, 0 )if param_0 ~= 0 then break end store_i32_n8(memory_at_0, 0 + 1052708, 0 )store_i32(memory_at_0, 0 + 1052680, 0 )break end if desired then if desired == 6 then desired = nil end break end store_i32_n8(memory_at_0, 0 + 1052677, 3 )break end if desired then if desired == 5 then desired = nil end break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )desired = 0 break end if desired then if desired == 4 then desired = nil end break end store_i64(memory_at_0, add_i32(loc_0 , 12 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 4, 1 )store_i32(memory_at_0, loc_0 , 1050800 )store_i32(memory_at_0, loc_0 + 8, 1049924 )FUNC_LIST[107](loc_0 , 1049952 )error("out of code bounds")end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[109](1049857 , 43 , 1050180 )error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[116](1050228 , 38 , 1050300 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[115](1050076 , 16 , loc_0 , 1050092 , 1050136 )error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end store_i64(memory_at_0, add_i32(loc_0 , 12 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 4, 1 )store_i32(memory_at_0, loc_0 , 1050748 )store_i32(memory_at_0, loc_0 + 8, 1049924 )FUNC_LIST[107](loc_0 , 1049952 )error("out of code bounds")end end FUNC_LIST[78] =--[[ _ZN3std2rt19lang_start_internal17h219d1396b3281d48E ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6 = 0 , 0 , 0 , 0 , 0 , 0 , 0  local loc_7, loc_8, loc_9 = i64_ZERO , i64_ZERO , i64_ZERO  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[102](add_i32(loc_0 , 16 ), 1049924 , 4 )while true do while true do if load_i32(memory_at_0, loc_0 + 16)~= 0 then break end loc_1 = load_i32(memory_at_0, add_i32(add_i32(loc_0 , 16 ), 8 ))loc_2 = load_i32(memory_at_0, loc_0 + 20)FUNC_LIST[104](add_i32(loc_0 , 8 ), 8 , 16 )loc_3 = load_i32(memory_at_0, loc_0 + 12)loc_4 = load_i32(memory_at_0, loc_0 + 8)FUNC_LIST[104](loc_0 , 8 , 16 )loc_5 = load_i32(memory_at_0, loc_0 )while true do loc_6 = load_i32(memory_at_0, loc_0 + 4)if loc_6 == 0 then break end reg_0 = FUNC_LIST[18](loc_6 , loc_5 )loc_5 = reg_0 break end if desired then if desired == 2 then desired = nil end break end while true do while true do if loc_5 == 0 then break end store_i64(memory_at_0, loc_5 , i64_from_u32(1, 1) )store_i32(memory_at_0, loc_5 + 20, loc_1 )store_i32(memory_at_0, add_i32(loc_5 , 16 ), loc_2 )loc_7 = load_i64(memory_at_0, 0 + 1052744)while true do loc_8 = add_i64(loc_7 , i64_ONE )if eq_i64(loc_8 , i64_ZERO )then desired = 1 break end loc_9 = load_i64(memory_at_0, 0 + 1052744)loc_1 = (eq_i64(loc_9 , loc_7 )and 1 or 0)store_i64(memory_at_0, 0 + 1052744, (loc_1 ~= 0 and loc_8 or loc_9 ))loc_7 = loc_9 if loc_1 == 0 then continue end break end if desired then if desired == 4 then desired = nil end break end store_i64(memory_at_0, loc_5 + 8, loc_8 )if load_i32(memory_at_0, 0 + 1052756)~= 0 then desired = 3 break end store_i32(memory_at_0, 0 + 1052756, 4294967295 )if load_i32(memory_at_0, 0 + 1052760)~= 0 then desired = 2 break end store_i32(memory_at_0, 0 + 1052760, loc_5 )store_i32(memory_at_0, 0 + 1052756, 0 )reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, add_i32(param_1 , 20 ))](param_0 )loc_1 = reg_0 while true do if load_i32_u8(memory_at_0, 0 + 1052677)== 3 then break end store_i32_n8(memory_at_0, loc_0 + 16, 1 )FUNC_LIST[77](add_i32(loc_0 , 16 ))break end if desired then if desired == 4 then desired = nil end break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )reg_0 = loc_1 desired = 0 break end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[98](loc_4 , loc_3 )error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[115](1050076 , 16 , add_i32(loc_0 , 16 ), 1050092 , 1050360 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[79]()error("out of code bounds")end return reg_0 end FUNC_LIST[79] =--[[ _ZN3std6thread8ThreadId3new9exhausted17h0fdfe9709b60ae75E ]]function()local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 store_i64(memory_at_0, add_i32(loc_0 , 20 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 12, 1 )store_i32(memory_at_0, loc_0 + 8, 1050052 )store_i32(memory_at_0, loc_0 + 16, 1049924 )FUNC_LIST[107](add_i32(loc_0 , 8 ), 1050060 )error("out of code bounds")end end FUNC_LIST[80] =--[[ _ZN3std4sync9once_lock17OnceLock$LT$T$GT$10initialize17h03474e12629de1f7E ]]function(param_0)local loc_0 = 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do if load_i32_u8(memory_at_0, 0 + 1052712)== 3 then break end store_i32(memory_at_0, loc_0 + 12, 1052680 )store_i32(memory_at_0, loc_0 + 8, param_0 )store_i32(memory_at_0, loc_0 + 16, add_i32(loc_0 , 24 ))FUNC_LIST[81](add_i32(loc_0 , 8 ))break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[81] =--[[ _ZN3std3sys4wasm4once4Once4call17h049a7c5ff46526b3E ]]function(param_0)local loc_0, loc_1 = 0 , 0  local desired local br_map = {} while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do loc_1 = load_i32_u8(memory_at_0, 0 + 1052712)if loc_1 < 2 then break end if not br_map[1] then br_map[1] = (function() return {[0] =3,1,} end)()end local temp = br_map[1][add_i32(loc_1 , 4294967294 )] or 3 if temp < 3 then desired = 3 break else desired = 1 break end end if desired then if desired == 3 then desired = nil end break end store_i32_n8(memory_at_0, 0 + 1052712, 2 )loc_1 = load_i32(memory_at_0, param_0 )store_i32(memory_at_0, param_0 , 0 )if loc_1 == 0 then desired = 2 break end param_0 = load_i32(memory_at_0, param_0 + 4)store_i32_n8(memory_at_0, loc_1 , 1 )store_i64(memory_at_0, param_0 + 16, i64_ZERO )store_i64(memory_at_0, param_0 + 8, i64_from_u32(0, 1) )store_i64(memory_at_0, param_0 , i64_ZERO )store_i32_n8(memory_at_0, add_i32(param_0 , 24 ), 0 )store_i32_n8(memory_at_0, param_0 + 28, 0 )store_i32_n8(memory_at_0, 0 + 1052712, 3 )break end if desired then if desired == 2 then desired = nil end break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[109](1049857 , 43 , 1050212 )error("out of code bounds")end if desired then if desired == 0 then desired = nil end break end store_i64(memory_at_0, add_i32(loc_0 , 20 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 12, 1 )store_i32(memory_at_0, loc_0 + 8, 1050748 )store_i32(memory_at_0, loc_0 + 16, 1049924 )FUNC_LIST[107](add_i32(loc_0 , 8 ), 1050196 )error("out of code bounds")end end FUNC_LIST[82] =--[[ _ZN3std10sys_common9backtrace26__rust_end_short_backtrace17hef39a150fc1412aeE ]]function(param_0)while true do FUNC_LIST[83](param_0 )error("out of code bounds")end end FUNC_LIST[83] =--[[ _ZN3std9panicking19begin_panic_handler28_$u7b$$u7b$closure$u7d$$u7d$17h7ee15b9d8cb7799aE ]]function(param_0)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local reg_0, reg_1, reg_2, reg_3, reg_4 local desired local br_map = {} while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 loc_1 = load_i32(memory_at_0, param_0 )loc_2 = load_i32(memory_at_0, add_i32(loc_1 , 12 ))while true do while true do while true do while true do if not br_map[1] then br_map[1] = (function() return {[0] =0,1,} end)()end local temp = br_map[1][load_i32(memory_at_0, loc_1 + 4)] or 3 if temp < 1 then break elseif temp > 1 then desired = 1 break else desired = 3 break end end if desired then if desired == 3 then desired = nil end break end if loc_2 ~= 0 then desired = 1 break end loc_1 = 1049924 loc_2 = 0 desired = 2 break end if desired then if desired == 2 then desired = nil end break end if loc_2 ~= 0 then desired = 1 break end loc_1 = load_i32(memory_at_0, loc_1 )loc_2 = load_i32(memory_at_0, loc_1 + 4)loc_1 = load_i32(memory_at_0, loc_1 )break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 4, loc_2 )store_i32(memory_at_0, loc_0 , loc_1 )loc_1 = load_i32(memory_at_0, param_0 + 4)reg_2 = FUNC_LIST[118](loc_1 )reg_3 = load_i32(memory_at_0, param_0 + 8)reg_4 = FUNC_LIST[120](loc_1 )FUNC_LIST[91](loc_0 , 1050656 , reg_2 , reg_3 , reg_4 )error("out of code bounds")end store_i32(memory_at_0, loc_0 + 4, 0 )store_i32(memory_at_0, loc_0 , loc_1 )loc_1 = load_i32(memory_at_0, param_0 + 4)reg_2 = FUNC_LIST[118](loc_1 )reg_3 = load_i32(memory_at_0, param_0 + 8)reg_4 = FUNC_LIST[120](loc_1 )FUNC_LIST[91](loc_0 , 1050636 , reg_2 , reg_3 , reg_4 )error("out of code bounds")end end FUNC_LIST[84] =--[[ _ZN3std5alloc24default_alloc_error_hook17h77183bbe18529594E ]]function(param_0, param_1)local loc_0 = 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 48 )GLOBAL_LIST[0].value = loc_0 while true do if load_i32_u8(memory_at_0, 0 + 1052676)== 0 then break end store_i64(memory_at_0, add_i32(loc_0 , 20 ), i64_ONE )store_i32(memory_at_0, loc_0 + 12, 2 )store_i32(memory_at_0, loc_0 + 8, 1050412 )store_i32(memory_at_0, loc_0 + 36, 13 )store_i32(memory_at_0, loc_0 + 44, param_1 )store_i32(memory_at_0, loc_0 + 16, add_i32(loc_0 , 32 ))store_i32(memory_at_0, loc_0 + 32, add_i32(loc_0 , 44 ))FUNC_LIST[107](add_i32(loc_0 , 8 ), 1050452 )error("out of code bounds")end GLOBAL_LIST[0].value = add_i32(loc_0 , 48 )break end end FUNC_LIST[85] =--[[ _ZN3std9panicking8set_hook17h85785d01aafb8d25E ]]function(param_0, param_1)local loc_0, loc_1, loc_2, loc_3 = 0 , 0 , 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do while true do while true do if band_i32(load_i32(memory_at_0, 0 + 1052736), 2147483647 )== 0 then break end reg_0 = FUNC_LIST[69]()if reg_0 == 0 then desired = 5 break end break end if desired then if desired == 5 then desired = nil end break end loc_1 = load_i32(memory_at_0, 0 + 1052720)store_i32(memory_at_0, 0 + 1052720, 4294967295 )if loc_1 ~= 0 then desired = 1 break end if band_i32(load_i32(memory_at_0, 0 + 1052736), 2147483647 )~= 0 then desired = 4 break end loc_2 = load_i32(memory_at_0, 0 + 1052732)store_i32(memory_at_0, 0 + 1052732, param_1 )loc_1 = load_i32(memory_at_0, 0 + 1052728)store_i32(memory_at_0, 0 + 1052728, param_0 )desired = 3 break end if desired then if desired == 4 then desired = nil end break end store_i64(memory_at_0, add_i32(loc_0 , 20 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 12, 1 )store_i32(memory_at_0, loc_0 + 8, 1050520 )store_i32(memory_at_0, loc_0 + 16, 1049924 )FUNC_LIST[107](add_i32(loc_0 , 8 ), 1050556 )error("out of code bounds")end if desired then if desired == 3 then desired = nil end break end reg_0 = FUNC_LIST[69]()loc_3 = reg_0 loc_2 = load_i32(memory_at_0, 0 + 1052732)store_i32(memory_at_0, 0 + 1052732, param_1 )loc_1 = load_i32(memory_at_0, 0 + 1052728)store_i32(memory_at_0, 0 + 1052728, param_0 )if loc_3 == 0 then desired = 2 break end break end if desired then if desired == 2 then desired = nil end break end if band_i32(load_i32(memory_at_0, 0 + 1052736), 2147483647 )== 0 then break end reg_0 = FUNC_LIST[69]()if reg_0 ~= 0 then break end store_i32_n8(memory_at_0, 0 + 1052724, 1 )break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, 0 + 1052720, 0 )while true do if loc_1 == 0 then break end TABLE_LIST[0].data[load_i32(memory_at_0, loc_2 )](loc_1 )param_1 = load_i32(memory_at_0, add_i32(loc_2 , 4 ))if param_1 == 0 then break end FUNC_LIST[19](loc_1 , param_1 , load_i32(memory_at_0, add_i32(loc_2 , 8 )))break end if desired then if desired == 1 then desired = nil end break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end error("out of code bounds")end end FUNC_LIST[86] =--[[ rust_begin_unwind ]]function(param_0)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do reg_0 = FUNC_LIST[119](param_0 )loc_1 = reg_0 if loc_1 == 0 then break end reg_0 = FUNC_LIST[118](param_0 )loc_2 = reg_0 if loc_2 == 0 then desired = 1 break end store_i32(memory_at_0, loc_0 + 8, loc_1 )store_i32(memory_at_0, loc_0 + 4, param_0 )store_i32(memory_at_0, loc_0 , loc_2 )FUNC_LIST[82](loc_0 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[109](1049857 , 43 , 1050588 )error("out of code bounds")end FUNC_LIST[109](1049857 , 43 , 1050572 )error("out of code bounds")end end FUNC_LIST[87] =--[[ _ZN90_$LT$std..panicking..begin_panic_handler..PanicPayload$u20$as$u20$core..panic..BoxMeUp$GT$8take_box17h30b8e19bf9b49b80E ]]function(param_0, param_1)local loc_0, loc_1, loc_2, loc_3 = 0 , 0 , 0 , 0  local loc_4 = i64_ZERO  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 48 )GLOBAL_LIST[0].value = loc_0 loc_1 = add_i32(param_1 , 4 )while true do if load_i32(memory_at_0, param_1 + 4)~= 0 then break end loc_2 = load_i32(memory_at_0, param_1 )loc_3 = add_i32(add_i32(loc_0 , 32 ), 8 )store_i32(memory_at_0, loc_3 , 0 )store_i64(memory_at_0, loc_0 + 32, i64_ONE )store_i32(memory_at_0, loc_0 + 44, add_i32(loc_0 , 32 ))reg_0 = FUNC_LIST[111](add_i32(loc_0 , 44 ), 1049900 , loc_2 )loc_2 = load_i32(memory_at_0, loc_3 )store_i32(memory_at_0, add_i32(add_i32(loc_0 , 16 ), 8 ), loc_2 )loc_4 = load_i64(memory_at_0, loc_0 + 32)store_i64(memory_at_0, loc_0 + 16, loc_4 )store_i32(memory_at_0, add_i32(loc_1 , 8 ), loc_2 )store_i64(memory_at_0, loc_1 , loc_4 )break end loc_2 = add_i32(loc_0 , 8 )store_i32(memory_at_0, loc_2 , load_i32(memory_at_0, add_i32(loc_1 , 8 )))store_i32(memory_at_0, add_i32(param_1 , 12 ), 0 )loc_4 = load_i64(memory_at_0, loc_1 )store_i64(memory_at_0, param_1 + 4, i64_ONE )store_i64(memory_at_0, loc_0 , loc_4 )while true do reg_0 = FUNC_LIST[18](12 , 4 )param_1 = reg_0 if param_1 ~= 0 then break end FUNC_LIST[98](4 , 12 )error("out of code bounds")end store_i64(memory_at_0, param_1 , load_i64(memory_at_0, loc_0 ))store_i32(memory_at_0, add_i32(param_1 , 8 ), load_i32(memory_at_0, loc_2 ))store_i32(memory_at_0, param_0 + 4, 1050604 )store_i32(memory_at_0, param_0 , param_1 )GLOBAL_LIST[0].value = add_i32(loc_0 , 48 )break end end FUNC_LIST[88] =--[[ _ZN90_$LT$std..panicking..begin_panic_handler..PanicPayload$u20$as$u20$core..panic..BoxMeUp$GT$3get17h9b7f0328ded5da8fE ]]function(param_0, param_1)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local loc_3 = i64_ZERO  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 loc_1 = add_i32(param_1 , 4 )while true do if load_i32(memory_at_0, param_1 + 4)~= 0 then break end param_1 = load_i32(memory_at_0, param_1 )loc_2 = add_i32(add_i32(loc_0 , 16 ), 8 )store_i32(memory_at_0, loc_2 , 0 )store_i64(memory_at_0, loc_0 + 16, i64_ONE )store_i32(memory_at_0, loc_0 + 28, add_i32(loc_0 , 16 ))reg_0 = FUNC_LIST[111](add_i32(loc_0 , 28 ), 1049900 , param_1 )param_1 = load_i32(memory_at_0, loc_2 )store_i32(memory_at_0, add_i32(loc_0 , 8 ), param_1 )loc_3 = load_i64(memory_at_0, loc_0 + 16)store_i64(memory_at_0, loc_0 , loc_3 )store_i32(memory_at_0, add_i32(loc_1 , 8 ), param_1 )store_i64(memory_at_0, loc_1 , loc_3 )break end store_i32(memory_at_0, param_0 + 4, 1050604 )store_i32(memory_at_0, param_0 , loc_1 )GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[89] =--[[ _ZN93_$LT$std..panicking..begin_panic_handler..StrPanicPayload$u20$as$u20$core..panic..BoxMeUp$GT$8take_box17h2ef4b96e88e5e539E ]]function(param_0, param_1)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = load_i32(memory_at_0, param_1 + 4)loc_1 = load_i32(memory_at_0, param_1 )while true do reg_0 = FUNC_LIST[18](8 , 4 )param_1 = reg_0 if param_1 ~= 0 then break end FUNC_LIST[98](4 , 8 )error("out of code bounds")end store_i32(memory_at_0, param_1 + 4, loc_0 )store_i32(memory_at_0, param_1 , loc_1 )store_i32(memory_at_0, param_0 + 4, 1050620 )store_i32(memory_at_0, param_0 , param_1 )break end end FUNC_LIST[90] =--[[ _ZN93_$LT$std..panicking..begin_panic_handler..StrPanicPayload$u20$as$u20$core..panic..BoxMeUp$GT$3get17h5b7c223fa2ad50d2E ]]function(param_0, param_1)while true do store_i32(memory_at_0, param_0 + 4, 1050620 )store_i32(memory_at_0, param_0 , param_1 )break end end FUNC_LIST[91] =--[[ _ZN3std9panicking20rust_panic_with_hook17h244f69deb1e6118bE ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0, loc_1 = 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 loc_1 = load_i32(memory_at_0, 0 + 1052736)store_i32(memory_at_0, 0 + 1052736, add_i32(loc_1 , 1 ))while true do while true do if lt_i32(loc_1 , 0 )then break end loc_1 = add_i32(load_i32(memory_at_0, 0 + 1052752), 1 )store_i32(memory_at_0, 0 + 1052752, loc_1 )if loc_1 > 2 then break end store_i32(memory_at_0, loc_0 + 20, param_2 )store_i32(memory_at_0, loc_0 + 12, 1050676 )store_i32(memory_at_0, loc_0 + 8, 1049924 )store_i32_n8(memory_at_0, loc_0 + 24, param_4 )store_i32(memory_at_0, loc_0 + 16, param_3 )param_3 = load_i32(memory_at_0, 0 + 1052720)if le_i32(param_3 , 4294967295 )then break end store_i32(memory_at_0, 0 + 1052720, add_i32(param_3 , 1 ))while true do if load_i32(memory_at_0, 0 + 1052728)== 0 then break end TABLE_LIST[0].data[load_i32(memory_at_0, param_1 + 16)](loc_0 , param_0 )store_i64(memory_at_0, loc_0 + 8, load_i64(memory_at_0, loc_0 ))TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, 0 + 1052732)+ 20)](load_i32(memory_at_0, 0 + 1052728), add_i32(loc_0 , 8 ))param_3 = add_i32(load_i32(memory_at_0, 0 + 1052720), 4294967295 )break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, 0 + 1052720, param_3 )if loc_1 > 1 then break end if param_4 ~= 0 then desired = 1 break end break end if desired then if desired == 1 then desired = nil end break end error("out of code bounds")end FUNC_LIST[92](param_0 , param_1 )error("out of code bounds")end end FUNC_LIST[92] =--[[ rust_panic ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[95](param_0 , param_1 )error("out of code bounds")end end FUNC_LIST[93] =--[[ _ZN3std3sys4wasm7process8ExitCode6as_i3217h058d6808ffe7a27eE ]]function(param_0)local reg_0 while true do reg_0 = load_i32_u8(memory_at_0, param_0 )break end return reg_0 end FUNC_LIST[94] =--[[ __rg_oom ]]function(param_0, param_1)local loc_0 = 0  while true do loc_0 = load_i32(memory_at_0, 0 + 1052716)TABLE_LIST[0].data[(loc_0 ~= 0 and loc_0 or 14 )](param_1 , param_0 )error("out of code bounds")end end FUNC_LIST[95] =--[[ __rust_start_panic ]]function(param_0, param_1)while true do error("out of code bounds")end return reg_0 end FUNC_LIST[96] =--[[ _ZN4core3ptr26drop_in_place$LT$usize$GT$17he768bb3cc0b4f695E ]]function(param_0)while true do break end end FUNC_LIST[97] =--[[ _ZN5alloc7raw_vec11finish_grow17h5adb3aef355678deE ]]function(param_0, param_1, param_2, param_3)local reg_0 local desired while true do while true do while true do if param_1 == 0 then break end while true do while true do while true do while true do while true do while true do if le_i32(param_2 , 4294967295 )then break end if load_i32(memory_at_0, param_3 + 4)~= 0 then desired = 7 break end if param_2 ~= 0 then desired = 6 break end param_1 = 1 desired = 4 break end if desired then if desired == 7 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )desired = 1 break end if desired then if desired == 6 then desired = nil end break end while true do param_1 = load_i32(memory_at_0, add_i32(param_3 , 8 ))if param_1 ~= 0 then break end while true do if param_2 ~= 0 then break end param_1 = 1 desired = 4 break end if desired then if desired == 7 then desired = nil end break end reg_0 = FUNC_LIST[18](param_2 , 1 )param_1 = reg_0 desired = 5 break end if desired then if desired == 6 then desired = nil end break end reg_0 = FUNC_LIST[20](load_i32(memory_at_0, param_3 ), param_1 , 1 , param_2 )param_1 = reg_0 desired = 5 break end if desired then if desired == 5 then desired = nil end break end reg_0 = FUNC_LIST[18](param_2 , 1 )param_1 = reg_0 break end if desired then if desired == 4 then desired = nil end break end if param_1 == 0 then desired = 3 break end break end if desired then if desired == 3 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, param_1 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )store_i32(memory_at_0, param_0 , 0 )desired = 0 break end if desired then if desired == 2 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 1 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )store_i32(memory_at_0, param_0 , 1 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, 0 )store_i32(memory_at_0, add_i32(param_0 , 8 ), param_2 )break end if desired then if desired == 0 then desired = nil end break end store_i32(memory_at_0, param_0 , 1 )break end end FUNC_LIST[98] =--[[ _ZN5alloc5alloc18handle_alloc_error17h99f159a3f7e65d4dE ]]function(param_0, param_1)while true do FUNC_LIST[101](param_0 , param_1 )error("out of code bounds")end end FUNC_LIST[99] =--[[ _ZN5alloc7raw_vec17capacity_overflow17he0cacb761dc6b3afE ]]function()local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 store_i64(memory_at_0, add_i32(loc_0 , 20 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 12, 1 )store_i32(memory_at_0, loc_0 + 8, 1050856 )store_i32(memory_at_0, loc_0 + 16, 1050808 )FUNC_LIST[107](add_i32(loc_0 , 8 ), 1050864 )error("out of code bounds")end end FUNC_LIST[100] =--[[ _ZN5alloc7raw_vec19RawVec$LT$T$C$A$GT$16reserve_for_push17h2a8afbe053fee724E ]]function(param_0, param_1)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do param_1 = add_i32(param_1 , 1 )if param_1 == 0 then break end loc_1 = load_i32(memory_at_0, add_i32(param_0 , 4 ))loc_2 = shl_i32(loc_1 , 1 )param_1 = (loc_2 > param_1 and loc_2 or param_1 )param_1 = (param_1 > 8 and param_1 or 8 )loc_2 = shr_u32(bxor_i32(param_1 , 4294967295 ), 31 )while true do while true do if loc_1 == 0 then break end store_i32(memory_at_0, loc_0 + 24, loc_1 )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, load_i32(memory_at_0, param_0 ))desired = 3 break end if desired then if desired == 3 then desired = nil end break end store_i32(memory_at_0, loc_0 + 20, 0 )break end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[97](loc_0 , loc_2 , param_1 , add_i32(loc_0 , 16 ))loc_1 = load_i32(memory_at_0, loc_0 + 4)while true do if load_i32(memory_at_0, loc_0 )~= 0 then break end store_i32(memory_at_0, param_0 , loc_1 )store_i32(memory_at_0, add_i32(param_0 , 4 ), param_1 )desired = 1 break end if desired then if desired == 2 then desired = nil end break end if loc_1 == 2147483649 then desired = 1 break end if loc_1 == 0 then break end FUNC_LIST[98](loc_1 , load_i32(memory_at_0, add_i32(loc_0 , 8 )))error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[101] =--[[ _ZN5alloc5alloc18handle_alloc_error8rt_error17h5678f12f18b1296bE ]]function(param_0, param_1)while true do FUNC_LIST[22](param_1 , param_0 )error("out of code bounds")end end FUNC_LIST[102] =--[[ _ZN72_$LT$$RF$str$u20$as$u20$alloc..ffi..c_str..CString..new..SpecNewImpl$GT$13spec_new_impl17h8e7ce13361d0ee2dE ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2, loc_3, loc_4 = 0 , 0 , 0 , 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do while true do loc_1 = add_i32(param_2 , 1 )if loc_1 == 0 then break end if le_i32(loc_1 , 4294967295 )then desired = 4 break end reg_0 = FUNC_LIST[18](loc_1 , 1 )loc_2 = reg_0 if loc_2 == 0 then desired = 3 break end reg_0 = FUNC_LIST[132](loc_2 , param_1 , param_2 )loc_3 = reg_0 while true do if param_2 < 8 then break end FUNC_LIST[128](add_i32(loc_0 , 8 ), 0 , param_1 , param_2 )loc_4 = load_i32(memory_at_0, loc_0 + 12)loc_2 = load_i32(memory_at_0, loc_0 + 8)desired = 1 break end if desired then if desired == 5 then desired = nil end break end while true do if param_2 ~= 0 then break end loc_4 = 0 loc_2 = 0 desired = 1 break end if desired then if desired == 5 then desired = nil end break end while true do if load_i32_u8(memory_at_0, param_1 )~= 0 then break end loc_2 = 1 loc_4 = 0 desired = 1 break end if desired then if desired == 5 then desired = nil end break end loc_2 = 1 if param_2 == 1 then desired = 2 break end while true do if load_i32_u8(memory_at_0, param_1 + 1)~= 0 then break end loc_4 = 1 desired = 1 break end if desired then if desired == 5 then desired = nil end break end loc_4 = 2 if param_2 == 2 then desired = 2 break end if load_i32_u8(memory_at_0, param_1 + 2)== 0 then desired = 1 break end loc_4 = 3 if param_2 == 3 then desired = 2 break end if load_i32_u8(memory_at_0, param_1 + 3)== 0 then desired = 1 break end loc_4 = 4 if param_2 == 4 then desired = 2 break end if load_i32_u8(memory_at_0, param_1 + 4)== 0 then desired = 1 break end loc_4 = 5 if param_2 == 5 then desired = 2 break end if load_i32_u8(memory_at_0, param_1 + 5)== 0 then desired = 1 break end loc_4 = param_2 loc_2 = 0 if param_2 == 6 then desired = 1 break end param_1 = load_i32_u8(memory_at_0, param_1 + 6)loc_4 = (param_1 ~= 0 and param_2 or 6 )loc_2 = (param_1 == 0 and 1 or 0)desired = 1 break end if desired then if desired == 4 then desired = nil end break end FUNC_LIST[109](1050880 , 43 , 1050956 )error("out of code bounds")end if desired then if desired == 3 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[98](1 , loc_1 )error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end loc_4 = param_2 loc_2 = 0 break end while true do while true do if loc_2 ~= 0 then break end store_i32(memory_at_0, loc_0 + 24, param_2 )store_i32(memory_at_0, loc_0 + 20, loc_1 )store_i32(memory_at_0, loc_0 + 16, loc_3 )FUNC_LIST[103](loc_0 , add_i32(loc_0 , 16 ))store_i64(memory_at_0, param_0 + 4, load_i64(memory_at_0, loc_0 ))store_i32(memory_at_0, param_0 , 0 )desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, param_0 + 8, param_2 )store_i32(memory_at_0, param_0 + 4, loc_1 )store_i32(memory_at_0, param_0 , loc_3 )store_i32(memory_at_0, param_0 + 12, loc_4 )break end GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )break end end FUNC_LIST[103] =--[[ _ZN5alloc3ffi5c_str7CString19_from_vec_unchecked17h1c8633b16b50d34aE ]]function(param_0, param_1)local loc_0, loc_1, loc_2, loc_3 = 0 , 0 , 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 while true do while true do while true do while true do while true do loc_1 = load_i32(memory_at_0, add_i32(param_1 , 4 ))loc_2 = load_i32(memory_at_0, param_1 + 8)if loc_1 ~= loc_2 then break end loc_1 = add_i32(loc_2 , 1 )if loc_1 == 0 then desired = 3 break end loc_3 = shr_u32(bxor_i32(loc_1 , 4294967295 ), 31 )while true do while true do if loc_2 == 0 then break end store_i32(memory_at_0, loc_0 + 24, loc_2 )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, load_i32(memory_at_0, param_1 ))desired = 6 break end if desired then if desired == 6 then desired = nil end break end store_i32(memory_at_0, loc_0 + 20, 0 )break end if desired then if desired == 5 then desired = nil end break end FUNC_LIST[97](loc_0 , loc_3 , loc_1 , add_i32(loc_0 , 16 ))loc_3 = load_i32(memory_at_0, loc_0 + 4)if load_i32(memory_at_0, loc_0 )~= 0 then desired = 4 break end store_i32(memory_at_0, param_1 , loc_3 )store_i32(memory_at_0, add_i32(param_1 , 4 ), loc_1 )break end if desired then if desired == 4 then desired = nil end break end if loc_2 ~= loc_1 then desired = 1 break end desired = 2 break end if desired then if desired == 3 then desired = nil end break end if loc_3 == 2147483649 then desired = 2 break end if loc_3 == 0 then break end FUNC_LIST[98](loc_3 , load_i32(memory_at_0, add_i32(loc_0 , 8 )))error("out of code bounds")end if desired then if desired == 2 then desired = nil end break end FUNC_LIST[99]()error("out of code bounds")end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[100](param_1 , loc_2 )loc_1 = load_i32(memory_at_0, add_i32(param_1 , 4 ))loc_2 = load_i32(memory_at_0, param_1 + 8)break end if desired then if desired == 0 then desired = nil end break end loc_3 = add_i32(loc_2 , 1 )store_i32(memory_at_0, param_1 + 8, loc_3 )param_1 = load_i32(memory_at_0, param_1 )store_i32_n8(memory_at_0, add_i32(param_1 , loc_2 ), 0 )while true do while true do while true do if loc_1 > loc_3 then break end loc_2 = param_1 desired = 2 break end if desired then if desired == 2 then desired = nil end break end while true do if loc_3 ~= 0 then break end loc_2 = 1 FUNC_LIST[19](param_1 , loc_1 , 1 )desired = 2 break end if desired then if desired == 2 then desired = nil end break end reg_0 = FUNC_LIST[20](param_1 , loc_1 , 1 , loc_3 )loc_2 = reg_0 if loc_2 == 0 then desired = 1 break end break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, param_0 + 4, loc_3 )store_i32(memory_at_0, param_0 , loc_2 )GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[98](1 , loc_3 )error("out of code bounds")end end FUNC_LIST[104] =--[[ _ZN5alloc4sync32arcinner_layout_for_value_layout17hc76b51503e7fc54eE ]]function(param_0, param_1, param_2)local loc_0, loc_1 = 0 , 0  local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do loc_1 = band_i32(add_i32(param_1 , 7 ), sub_i32(0 , param_1 ))if loc_1 < add_i32(loc_1 , 4294967288 )then break end param_2 = add_i32(loc_1 , param_2 )if param_2 < loc_1 then break end param_1 = (param_1 > 4 and param_1 or 4 )if param_2 > sub_i32(2147483648 , param_1 )then break end store_i32(memory_at_0, param_0 , param_1 )store_i32(memory_at_0, param_0 + 4, band_i32(add_i32(add_i32(param_1 , param_2 ), 4294967295 ), sub_i32(0 , param_1 )))GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[115](1050972 , 43 , add_i32(loc_0 , 8 ), 1051016 , 1051060 )error("out of code bounds")end end FUNC_LIST[105] =--[[ _ZN4core3ops8function6FnOnce9call_once17h97156c953a23b85fE ]]function(param_0, param_1)local reg_0 local desired while true do while true do continue end break end return reg_0 end FUNC_LIST[106] =--[[ _ZN4core3ptr102drop_in_place$LT$$RF$core..iter..adapters..copied..Copied$LT$core..slice..iter..Iter$LT$u8$GT$$GT$$GT$17ha0d2399e57118f20E ]]function(param_0)while true do break end end FUNC_LIST[107] =--[[ _ZN4core9panicking9panic_fmt17hd7b054421d5b8f68E ]]function(param_0, param_1)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 20, param_0 )store_i32(memory_at_0, loc_0 + 12, 1051160 )store_i32(memory_at_0, loc_0 + 8, 1051076 )store_i32_n8(memory_at_0, loc_0 + 24, 1 )store_i32(memory_at_0, loc_0 + 16, param_1 )FUNC_LIST[86](add_i32(loc_0 , 8 ))error("out of code bounds")end end FUNC_LIST[108] =--[[ _ZN4core3fmt9Formatter3pad17h3ebc74892bcc62c2E ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6, loc_7 = 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0 local desired local br_map = {} while true do while true do while true do loc_0 = load_i32(memory_at_0, param_0 )loc_1 = load_i32(memory_at_0, param_0 + 8)if bor_i32(loc_0 , loc_1 )== 0 then break end while true do if loc_1 == 0 then break end loc_2 = add_i32(param_1 , param_2 )loc_3 = add_i32(load_i32(memory_at_0, add_i32(param_0 , 12 )), 1 )loc_4 = 0 loc_5 = param_1 while true do while true do loc_1 = loc_5 loc_3 = add_i32(loc_3 , 4294967295 )if loc_3 == 0 then desired = 4 break end if loc_1 == loc_2 then desired = 3 break end while true do while true do loc_6 = load_i32_i8(memory_at_0, loc_1 )if le_i32(loc_6 , 4294967295 )then break end loc_5 = add_i32(loc_1 , 1 )loc_6 = band_i32(loc_6 , 255 )desired = 6 break end if desired then if desired == 6 then desired = nil end break end loc_7 = band_i32(load_i32_u8(memory_at_0, loc_1 + 1), 63 )loc_5 = band_i32(loc_6 , 31 )while true do if loc_6 > 4294967263 then break end loc_6 = bor_i32(shl_i32(loc_5 , 6 ), loc_7 )loc_5 = add_i32(loc_1 , 2 )desired = 6 break end if desired then if desired == 6 then desired = nil end break end loc_7 = bor_i32(shl_i32(loc_7 , 6 ), band_i32(load_i32_u8(memory_at_0, loc_1 + 2), 63 ))while true do if loc_6 >= 4294967280 then break end loc_6 = bor_i32(loc_7 , shl_i32(loc_5 , 12 ))loc_5 = add_i32(loc_1 , 3 )desired = 6 break end if desired then if desired == 6 then desired = nil end break end loc_6 = bor_i32(bor_i32(shl_i32(loc_7 , 6 ), band_i32(load_i32_u8(memory_at_0, loc_1 + 3), 63 )), band_i32(shl_i32(loc_5 , 18 ), 1835008 ))if loc_6 == 1114112 then desired = 3 break end loc_5 = add_i32(loc_1 , 4 )break end if desired then if desired == 5 then desired = nil continue end break end loc_4 = add_i32(sub_i32(loc_4 , loc_1 ), loc_5 )if loc_6 ~= 1114112 then continue end desired = 3 break end if desired then if desired == 4 then desired = nil end break end break end if desired then if desired == 3 then desired = nil end break end if loc_1 == loc_2 then break end while true do loc_5 = load_i32_i8(memory_at_0, loc_1 )if gt_i32(loc_5 , 4294967295 )then break end if loc_5 < 4294967264 then break end if loc_5 < 4294967280 then break end if bor_i32(bor_i32(bor_i32(shl_i32(band_i32(load_i32_u8(memory_at_0, loc_1 + 2), 63 ), 6 ), shl_i32(band_i32(load_i32_u8(memory_at_0, loc_1 + 1), 63 ), 12 )), band_i32(load_i32_u8(memory_at_0, loc_1 + 3), 63 )), band_i32(shl_i32(band_i32(loc_5 , 255 ), 18 ), 1835008 ))== 1114112 then desired = 3 break end break end if desired then if desired == 3 then desired = nil end break end while true do while true do if loc_4 == 0 then break end while true do if loc_4 < param_2 then break end loc_1 = 0 if loc_4 == param_2 then desired = 5 break end desired = 4 break end if desired then if desired == 5 then desired = nil end break end loc_1 = 0 if lt_i32(load_i32_i8(memory_at_0, add_i32(param_1 , loc_4 )), 4294967232 )then desired = 4 break end break end if desired then if desired == 4 then desired = nil end break end loc_1 = param_1 break end if desired then if desired == 3 then desired = nil end break end param_2 = (loc_1 ~= 0 and loc_4 or param_2 )param_1 = (loc_1 ~= 0 and loc_1 or param_1 )break end if desired then if desired == 2 then desired = nil end break end while true do if loc_0 ~= 0 then break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_0 , 24 ))+ 12)](load_i32(memory_at_0, param_0 + 20), param_1 , param_2 )desired = 0 break end if desired then if desired == 2 then desired = nil end break end loc_4 = load_i32(memory_at_0, param_0 + 4)while true do while true do if param_2 < 16 then break end reg_0 = FUNC_LIST[126](param_1 , param_2 )loc_5 = reg_0 desired = 3 break end if desired then if desired == 3 then desired = nil end break end while true do if param_2 ~= 0 then break end loc_5 = 0 desired = 3 break end if desired then if desired == 3 then desired = nil end break end loc_6 = band_i32(param_2 , 3 )while true do while true do if param_2 >= 4 then break end loc_5 = 0 loc_1 = param_1 desired = 4 break end if desired then if desired == 4 then desired = nil end break end loc_3 = band_i32(param_2 , 4294967292 )loc_5 = 0 loc_1 = param_1 while true do loc_5 = add_i32(add_i32(add_i32(add_i32(loc_5 , (gt_i32(load_i32_i8(memory_at_0, loc_1 ), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_1 + 1), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_1 + 2), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_1 + 3), 4294967231 )and 1 or 0))loc_1 = add_i32(loc_1 , 4 )loc_3 = add_i32(loc_3 , 4294967292 )if loc_3 ~= 0 then continue end break end if desired then if desired == 4 then desired = nil end break end break end if desired then if desired == 3 then desired = nil end break end if loc_6 == 0 then break end while true do loc_5 = add_i32(loc_5 , (gt_i32(load_i32_i8(memory_at_0, loc_1 ), 4294967231 )and 1 or 0))loc_1 = add_i32(loc_1 , 1 )loc_6 = add_i32(loc_6 , 4294967295 )if loc_6 ~= 0 then continue end break end if desired then if desired == 3 then desired = nil end break end break end if desired then if desired == 2 then desired = nil end break end while true do if loc_4 <= loc_5 then break end loc_1 = 0 loc_5 = sub_i32(loc_4 , loc_5 )loc_4 = loc_5 while true do while true do while true do if not br_map[1] then br_map[1] = (function() return {[0] =2,0,1,2,} end)()end local temp = br_map[1][load_i32_u8(memory_at_0, param_0 + 32)] or 2 if temp < 1 then break elseif temp > 1 then desired = 4 break else desired = 5 break end end if desired then if desired == 5 then desired = nil end break end loc_4 = 0 loc_1 = loc_5 desired = 4 break end if desired then if desired == 4 then desired = nil end break end loc_1 = shr_u32(loc_5 , 1 )loc_4 = shr_u32(add_i32(loc_5 , 1 ), 1 )break end if desired then if desired == 3 then desired = nil end break end loc_1 = add_i32(loc_1 , 1 )loc_6 = load_i32(memory_at_0, add_i32(param_0 , 24 ))loc_3 = load_i32(memory_at_0, add_i32(param_0 , 20 ))loc_5 = load_i32(memory_at_0, param_0 + 16)while true do while true do loc_1 = add_i32(loc_1 , 4294967295 )if loc_1 == 0 then desired = 4 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_6 + 16)](loc_3 , loc_5 )if reg_0 == 0 then continue end break end if desired then if desired == 4 then desired = nil end break end reg_0 = 1 desired = 0 break end if desired then if desired == 3 then desired = nil end break end loc_1 = 1 if loc_5 == 1114112 then desired = 1 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_6 + 12)](loc_3 , param_1 , param_2 )if reg_0 ~= 0 then desired = 1 break end loc_1 = 0 while true do while true do if loc_4 ~= loc_1 then break end reg_0 = (loc_4 < loc_4 and 1 or 0)desired = 0 break end if desired then if desired == 4 then desired = nil continue end break end loc_1 = add_i32(loc_1 , 1 )reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_6 + 16)](loc_3 , loc_5 )if reg_0 == 0 then continue end break end if desired then if desired == 3 then desired = nil end break end reg_0 = (add_i32(loc_1 , 4294967295 )< loc_4 and 1 or 0)desired = 0 break end if desired then if desired == 2 then desired = nil end break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_0 , 24 ))+ 12)](load_i32(memory_at_0, param_0 + 20), param_1 , param_2 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_0 , 24 ))+ 12)](load_i32(memory_at_0, param_0 + 20), param_1 , param_2 )loc_1 = reg_0 break end if desired then if desired == 0 then desired = nil end break end reg_0 = loc_1 break end return reg_0 end FUNC_LIST[109] =--[[ _ZN4core9panicking5panic17h57d0c7f2c1a3f934E ]]function(param_0, param_1, param_2)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 store_i64(memory_at_0, add_i32(loc_0 , 12 ), i64_ZERO )store_i32(memory_at_0, loc_0 + 4, 1 )store_i32(memory_at_0, loc_0 + 8, 1051076 )store_i32(memory_at_0, loc_0 + 28, param_1 )store_i32(memory_at_0, loc_0 + 24, param_0 )store_i32(memory_at_0, loc_0 , add_i32(loc_0 , 24 ))FUNC_LIST[107](loc_0 , param_2 )error("out of code bounds")end end FUNC_LIST[110] =--[[ _ZN4core3fmt3num3imp52_$LT$impl$u20$core..fmt..Display$u20$for$u20$u32$GT$3fmt17h2c88f662495599f4E ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[129](load_i64_u32(memory_at_0, param_0 ), 1 , param_1 )break end return reg_0 end FUNC_LIST[111] =--[[ _ZN4core3fmt5write17h85a9a90ef8695166E ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6, loc_7, loc_8, loc_9 = 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0 local desired local br_map = {} while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 48 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, add_i32(loc_0 , 32 ), param_1 )store_i32_n8(memory_at_0, loc_0 + 40, 3 )store_i32(memory_at_0, loc_0 + 24, 32 )loc_1 = 0 store_i32(memory_at_0, loc_0 + 36, 0 )store_i32(memory_at_0, loc_0 + 28, param_0 )store_i32(memory_at_0, loc_0 + 16, 0 )store_i32(memory_at_0, loc_0 + 8, 0 )while true do while true do while true do while true do loc_2 = load_i32(memory_at_0, param_2 + 16)if loc_2 ~= 0 then break end param_0 = load_i32(memory_at_0, add_i32(param_2 , 12 ))if param_0 == 0 then desired = 3 break end param_1 = load_i32(memory_at_0, param_2 + 8)loc_3 = shl_i32(param_0 , 3 )loc_1 = add_i32(band_i32(add_i32(param_0 , 4294967295 ), 536870911 ), 1 )param_0 = load_i32(memory_at_0, param_2 )while true do while true do loc_4 = load_i32(memory_at_0, add_i32(param_0 , 4 ))if loc_4 == 0 then break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, loc_0 + 32)+ 12)](load_i32(memory_at_0, loc_0 + 28), load_i32(memory_at_0, param_0 ), loc_4 )if reg_0 ~= 0 then desired = 2 break end break end if desired then if desired == 5 then desired = nil continue end break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, add_i32(param_1 , 4 ))](load_i32(memory_at_0, param_1 ), add_i32(loc_0 , 8 ))if reg_0 ~= 0 then desired = 2 break end param_1 = add_i32(param_1 , 8 )param_0 = add_i32(param_0 , 8 )loc_3 = add_i32(loc_3 , 4294967288 )if loc_3 ~= 0 then continue end desired = 3 break end if desired then if desired == 4 then desired = nil end break end break end if desired then if desired == 3 then desired = nil end break end param_1 = load_i32(memory_at_0, add_i32(param_2 , 20 ))if param_1 == 0 then break end loc_5 = shl_i32(param_1 , 5 )loc_1 = add_i32(band_i32(add_i32(param_1 , 4294967295 ), 134217727 ), 1 )param_0 = load_i32(memory_at_0, param_2 )loc_3 = 0 while true do while true do param_1 = load_i32(memory_at_0, add_i32(param_0 , 4 ))if param_1 == 0 then break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, loc_0 + 32)+ 12)](load_i32(memory_at_0, loc_0 + 28), load_i32(memory_at_0, param_0 ), param_1 )if reg_0 ~= 0 then desired = 2 break end break end if desired then if desired == 4 then desired = nil continue end break end param_1 = add_i32(loc_2 , loc_3 )store_i32(memory_at_0, loc_0 + 24, load_i32(memory_at_0, add_i32(param_1 , 16 )))store_i32_n8(memory_at_0, loc_0 + 40, load_i32_u8(memory_at_0, add_i32(param_1 , 28 )))store_i32(memory_at_0, loc_0 + 36, load_i32(memory_at_0, add_i32(param_1 , 24 )))loc_6 = load_i32(memory_at_0, add_i32(param_1 , 12 ))loc_7 = load_i32(memory_at_0, param_2 + 8)loc_8 = 0 loc_4 = 0 while true do while true do while true do if not br_map[1] then br_map[1] = (function() return {[0] =1,0,2,} end)()end local temp = br_map[1][load_i32(memory_at_0, add_i32(param_1 , 8 ))] or 1 if temp < 1 then break elseif temp > 1 then desired = 5 break else desired = 6 break end end if desired then if desired == 6 then desired = nil end break end loc_9 = shl_i32(loc_6 , 3 )loc_4 = 0 loc_9 = add_i32(loc_7 , loc_9 )if load_i32(memory_at_0, loc_9 + 4)~= 31 then desired = 5 break end loc_6 = load_i32(memory_at_0, load_i32(memory_at_0, loc_9 ))break end if desired then if desired == 5 then desired = nil end break end loc_4 = 1 break end if desired then if desired == 4 then desired = nil continue end break end store_i32(memory_at_0, loc_0 + 12, loc_6 )store_i32(memory_at_0, loc_0 + 8, loc_4 )loc_4 = load_i32(memory_at_0, add_i32(param_1 , 4 ))while true do while true do while true do if not br_map[2] then br_map[2] = (function() return {[0] =1,0,2,} end)()end local temp = br_map[2][load_i32(memory_at_0, param_1 )] or 1 if temp < 1 then break elseif temp > 1 then desired = 5 break else desired = 6 break end end if desired then if desired == 6 then desired = nil end break end loc_6 = shl_i32(loc_4 , 3 )loc_6 = add_i32(loc_7 , loc_6 )if load_i32(memory_at_0, loc_6 + 4)~= 31 then desired = 5 break end loc_4 = load_i32(memory_at_0, load_i32(memory_at_0, loc_6 ))break end if desired then if desired == 5 then desired = nil end break end loc_8 = 1 break end if desired then if desired == 4 then desired = nil continue end break end store_i32(memory_at_0, loc_0 + 20, loc_4 )store_i32(memory_at_0, loc_0 + 16, loc_8 )param_1 = add_i32(loc_7 , shl_i32(load_i32(memory_at_0, add_i32(param_1 , 20 )), 3 ))reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_1 + 4)](load_i32(memory_at_0, param_1 ), add_i32(loc_0 , 8 ))if reg_0 ~= 0 then desired = 2 break end param_0 = add_i32(param_0 , 8 )loc_3 = add_i32(loc_3 , 32 )if loc_5 ~= loc_3 then continue end break end if desired then if desired == 3 then desired = nil end break end break end if desired then if desired == 2 then desired = nil end break end while true do if loc_1 >= load_i32(memory_at_0, param_2 + 4)then break end param_1 = add_i32(load_i32(memory_at_0, param_2 ), shl_i32(loc_1 , 3 ))reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, loc_0 + 32)+ 12)](load_i32(memory_at_0, loc_0 + 28), load_i32(memory_at_0, param_1 ), load_i32(memory_at_0, param_1 + 4))if reg_0 ~= 0 then desired = 2 break end break end if desired then if desired == 2 then desired = nil end break end param_1 = 0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end param_1 = 1 break end GLOBAL_LIST[0].value = add_i32(loc_0 , 48 )reg_0 = param_1 break end return reg_0 end FUNC_LIST[112] =--[[ _ZN4core3fmt9Formatter12pad_integral17h97ced6c471291764E ]]function(param_0, param_1, param_2, param_3, param_4, param_5)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6 = 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0 local desired local br_map = {} while true do while true do while true do if param_1 == 0 then break end loc_0 = load_i32(memory_at_0, param_0 + 28)param_1 = band_i32(loc_0 , 1 )loc_1 = (param_1 ~= 0 and 43 or 1114112 )loc_2 = add_i32(param_1 , param_5 )desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_2 = add_i32(param_5 , 1 )loc_0 = load_i32(memory_at_0, param_0 + 28)loc_1 = 45 break end if desired then if desired == 0 then desired = nil end break end while true do while true do if band_i32(loc_0 , 4 )~= 0 then break end param_2 = 0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end while true do while true do if param_3 < 16 then break end reg_0 = FUNC_LIST[126](param_2 , param_3 )loc_3 = reg_0 desired = 2 break end if desired then if desired == 2 then desired = nil end break end while true do if param_3 ~= 0 then break end loc_3 = 0 desired = 2 break end if desired then if desired == 2 then desired = nil end break end loc_4 = band_i32(param_3 , 3 )while true do while true do if param_3 >= 4 then break end loc_3 = 0 param_1 = param_2 desired = 3 break end if desired then if desired == 3 then desired = nil end break end loc_5 = band_i32(param_3 , 4294967292 )loc_3 = 0 param_1 = param_2 while true do loc_3 = add_i32(add_i32(add_i32(add_i32(loc_3 , (gt_i32(load_i32_i8(memory_at_0, param_1 ), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_1 + 1), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_1 + 2), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_1 + 3), 4294967231 )and 1 or 0))param_1 = add_i32(param_1 , 4 )loc_5 = add_i32(loc_5 , 4294967292 )if loc_5 ~= 0 then continue end break end if desired then if desired == 3 then desired = nil end break end break end if desired then if desired == 2 then desired = nil end break end if loc_4 == 0 then break end while true do loc_3 = add_i32(loc_3 , (gt_i32(load_i32_i8(memory_at_0, param_1 ), 4294967231 )and 1 or 0))param_1 = add_i32(param_1 , 1 )loc_4 = add_i32(loc_4 , 4294967295 )if loc_4 ~= 0 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end loc_2 = add_i32(loc_3 , loc_2 )break end if desired then if desired == 0 then desired = nil end break end while true do while true do if load_i32(memory_at_0, param_0 )~= 0 then break end param_1 = 1 loc_3 = load_i32(memory_at_0, add_i32(param_0 , 20 ))param_0 = load_i32(memory_at_0, add_i32(param_0 , 24 ))reg_0 = FUNC_LIST[127](loc_3 , param_0 , loc_1 , param_2 , param_3 )if reg_0 ~= 0 then desired = 1 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_0 + 12)](loc_3 , param_4 , param_5 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end while true do while true do while true do while true do while true do loc_5 = load_i32(memory_at_0, param_0 + 4)if loc_5 <= loc_2 then break end if band_i32(loc_0 , 8 )~= 0 then desired = 2 break end loc_3 = sub_i32(loc_5 , loc_2 )loc_2 = loc_3 param_1 = load_i32_u8(memory_at_0, param_0 + 32)if not br_map[1] then br_map[1] = (function() return {[0] =3,1,2,1,} end)()end local temp = br_map[1][param_1 ] or 3 if temp < 2 then desired = 5 break elseif temp > 2 then desired = 3 break else desired = 4 break end end if desired then if desired == 5 then desired = nil end break end param_1 = 1 loc_3 = load_i32(memory_at_0, add_i32(param_0 , 20 ))param_0 = load_i32(memory_at_0, add_i32(param_0 , 24 ))reg_0 = FUNC_LIST[127](loc_3 , param_0 , loc_1 , param_2 , param_3 )if reg_0 ~= 0 then desired = 1 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_0 + 12)](loc_3 , param_4 , param_5 )desired = 0 break end if desired then if desired == 4 then desired = nil end break end loc_2 = 0 param_1 = loc_3 desired = 3 break end if desired then if desired == 3 then desired = nil end break end param_1 = shr_u32(loc_3 , 1 )loc_2 = shr_u32(add_i32(loc_3 , 1 ), 1 )break end if desired then if desired == 2 then desired = nil end break end param_1 = add_i32(param_1 , 1 )loc_4 = load_i32(memory_at_0, add_i32(param_0 , 24 ))loc_5 = load_i32(memory_at_0, add_i32(param_0 , 20 ))loc_3 = load_i32(memory_at_0, param_0 + 16)while true do while true do param_1 = add_i32(param_1 , 4294967295 )if param_1 == 0 then desired = 3 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_4 + 16)](loc_5 , loc_3 )if reg_0 == 0 then continue end break end if desired then if desired == 3 then desired = nil end break end reg_0 = 1 desired = 0 break end if desired then if desired == 2 then desired = nil end break end param_1 = 1 if loc_3 == 1114112 then desired = 1 break end reg_0 = FUNC_LIST[127](loc_5 , loc_4 , loc_1 , param_2 , param_3 )if reg_0 ~= 0 then desired = 1 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_4 + 12)](loc_5 , param_4 , param_5 )if reg_0 ~= 0 then desired = 1 break end param_1 = 0 while true do while true do while true do if loc_2 ~= param_1 then break end param_1 = loc_2 desired = 3 break end if desired then if desired == 4 then desired = nil continue end break end param_1 = add_i32(param_1 , 1 )reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_4 + 16)](loc_5 , loc_3 )if reg_0 == 0 then continue end break end if desired then if desired == 3 then desired = nil end break end param_1 = add_i32(param_1 , 4294967295 )break end if desired then if desired == 2 then desired = nil end break end param_1 = (param_1 < loc_2 and 1 or 0)desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_0 = load_i32(memory_at_0, param_0 + 16)store_i32(memory_at_0, param_0 + 16, 48 )loc_6 = load_i32_u8(memory_at_0, param_0 + 32)param_1 = 1 store_i32_n8(memory_at_0, param_0 + 32, 1 )loc_3 = load_i32(memory_at_0, add_i32(param_0 , 20 ))loc_4 = load_i32(memory_at_0, add_i32(param_0 , 24 ))reg_0 = FUNC_LIST[127](loc_3 , loc_4 , loc_1 , param_2 , param_3 )if reg_0 ~= 0 then break end param_1 = add_i32(sub_i32(loc_5 , loc_2 ), 1 )while true do while true do param_1 = add_i32(param_1 , 4294967295 )if param_1 == 0 then desired = 2 break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_4 + 16)](loc_3 , 48 )if reg_0 == 0 then continue end break end if desired then if desired == 2 then desired = nil end break end reg_0 = 1 desired = 0 break end if desired then if desired == 1 then desired = nil end break end param_1 = 1 reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, loc_4 + 12)](loc_3 , param_4 , param_5 )if reg_0 ~= 0 then break end store_i32_n8(memory_at_0, param_0 + 32, loc_6 )store_i32(memory_at_0, param_0 + 16, loc_0 )reg_0 = 0 desired = 0 break end if desired then if desired == 0 then desired = nil end break end reg_0 = param_1 break end return reg_0 end FUNC_LIST[113] =--[[ _ZN36_$LT$T$u20$as$u20$core..any..Any$GT$7type_id17hb410880f3274c2bbE ]]function(param_0)local reg_0 while true do reg_0 = i64_from_u32(2806628161, 461491624) break end return reg_0 end FUNC_LIST[114] =--[[ _ZN63_$LT$core..cell..BorrowMutError$u20$as$u20$core..fmt..Debug$GT$3fmt17h7131c0eee6e24791E ]]function(param_0, param_1)local reg_0 while true do reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_1 , 24 ))+ 12)](load_i32(memory_at_0, param_1 + 20), 1051076 , 14 )break end return reg_0 end FUNC_LIST[115] =--[[ _ZN4core6result13unwrap_failed17h097db8465a47b18cE ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 64 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 12, param_1 )store_i32(memory_at_0, loc_0 + 8, param_0 )store_i32(memory_at_0, loc_0 + 20, param_3 )store_i32(memory_at_0, loc_0 + 16, param_2 )store_i64(memory_at_0, add_i32(add_i32(loc_0 , 24 ), 12 ), i64_from_u32(2, 0) )store_i32(memory_at_0, add_i32(add_i32(loc_0 , 48 ), 12 ), 32 )store_i32(memory_at_0, loc_0 + 28, 2 )store_i32(memory_at_0, loc_0 + 24, 1051180 )store_i32(memory_at_0, loc_0 + 52, 33 )store_i32(memory_at_0, loc_0 + 32, add_i32(loc_0 , 48 ))store_i32(memory_at_0, loc_0 + 56, add_i32(loc_0 , 16 ))store_i32(memory_at_0, loc_0 + 48, add_i32(loc_0 , 8 ))FUNC_LIST[107](add_i32(loc_0 , 24 ), param_4 )error("out of code bounds")end end FUNC_LIST[116] =--[[ _ZN4core6option13expect_failed17h4f520cb1e67fd1bdE ]]function(param_0, param_1, param_2)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 48 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 12, param_1 )store_i32(memory_at_0, loc_0 + 8, param_0 )store_i64(memory_at_0, add_i32(loc_0 , 28 ), i64_ONE )store_i32(memory_at_0, loc_0 + 20, 1 )store_i32(memory_at_0, loc_0 + 16, 1051092 )store_i32(memory_at_0, loc_0 + 44, 33 )store_i32(memory_at_0, loc_0 + 24, add_i32(loc_0 , 40 ))store_i32(memory_at_0, loc_0 + 40, add_i32(loc_0 , 8 ))FUNC_LIST[107](add_i32(loc_0 , 16 ), param_2 )error("out of code bounds")end end FUNC_LIST[117] =--[[ _ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17haa70c1d879ff3142E ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[108](param_1 , load_i32(memory_at_0, param_0 ), load_i32(memory_at_0, param_0 + 4))break end return reg_0 end FUNC_LIST[118] =--[[ _ZN4core5panic10panic_info9PanicInfo7message17h9e6623653f75fb2aE ]]function(param_0)local reg_0 while true do reg_0 = load_i32(memory_at_0, param_0 + 12)break end return reg_0 end FUNC_LIST[119] =--[[ _ZN4core5panic10panic_info9PanicInfo8location17h823b06af86391ad7E ]]function(param_0)local reg_0 while true do reg_0 = load_i32(memory_at_0, param_0 + 8)break end return reg_0 end FUNC_LIST[120] =--[[ _ZN4core5panic10panic_info9PanicInfo10can_unwind17h7ed2b080ddb24d58E ]]function(param_0)local reg_0 while true do reg_0 = load_i32_u8(memory_at_0, param_0 + 16)break end return reg_0 end FUNC_LIST[121] =--[[ _ZN73_$LT$core..panic..panic_info..PanicInfo$u20$as$u20$core..fmt..Display$GT$3fmt17h72987c98bef3d849E ]]function(param_0, param_1)local loc_0, loc_1, loc_2, loc_3 = 0 , 0 , 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 64 )GLOBAL_LIST[0].value = loc_0 loc_1 = 1 while true do loc_2 = load_i32(memory_at_0, param_1 + 20)param_1 = load_i32(memory_at_0, add_i32(param_1 , 24 ))reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_1 + 12)](loc_2 , 1051128 , 12 )if reg_0 ~= 0 then break end while true do while true do loc_3 = load_i32(memory_at_0, param_0 + 12)if loc_3 == 0 then break end store_i32(memory_at_0, loc_0 + 12, loc_3 )store_i32(memory_at_0, loc_0 + 20, 34 )store_i32(memory_at_0, loc_0 + 16, add_i32(loc_0 , 12 ))store_i64(memory_at_0, loc_0 + 52, i64_ONE )store_i32(memory_at_0, loc_0 + 44, 2 )store_i32(memory_at_0, loc_0 + 40, 1051144 )store_i32(memory_at_0, loc_0 + 48, add_i32(loc_0 , 16 ))reg_0 = FUNC_LIST[111](loc_2 , param_1 , add_i32(loc_0 , 40 ))if reg_0 == 0 then desired = 2 break end desired = 1 break end if desired then if desired == 2 then desired = nil end break end loc_3 = load_i32(memory_at_0, param_0 )reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, add_i32(load_i32(memory_at_0, param_0 + 4), 12 ))](loc_3 )if ne_i64(reg_0 , i64_from_u32(3441327041, 3248670876) )then break end store_i32(memory_at_0, loc_0 + 12, loc_3 )store_i32(memory_at_0, loc_0 + 20, 35 )store_i32(memory_at_0, loc_0 + 16, add_i32(loc_0 , 12 ))store_i64(memory_at_0, loc_0 + 52, i64_ONE )store_i32(memory_at_0, loc_0 + 44, 2 )store_i32(memory_at_0, loc_0 + 40, 1051144 )store_i32(memory_at_0, loc_0 + 48, add_i32(loc_0 , 16 ))reg_0 = FUNC_LIST[111](loc_2 , param_1 , add_i32(loc_0 , 40 ))if reg_0 ~= 0 then desired = 1 break end break end if desired then if desired == 1 then desired = nil end break end loc_1 = load_i32(memory_at_0, param_0 + 8)store_i32(memory_at_0, add_i32(loc_0 , 36 ), 13 )store_i32(memory_at_0, add_i32(add_i32(loc_0 , 16 ), 12 ), 13 )store_i32(memory_at_0, loc_0 + 32, add_i32(loc_1 , 12 ))store_i32(memory_at_0, loc_0 + 24, add_i32(loc_1 , 8 ))store_i32(memory_at_0, loc_0 + 20, 33 )store_i32(memory_at_0, loc_0 + 16, loc_1 )store_i64(memory_at_0, loc_0 + 52, i64_from_u32(3, 0) )store_i32(memory_at_0, loc_0 + 44, 3 )store_i32(memory_at_0, loc_0 + 40, 1051104 )store_i32(memory_at_0, loc_0 + 48, add_i32(loc_0 , 16 ))reg_0 = FUNC_LIST[111](loc_2 , param_1 , add_i32(loc_0 , 40 ))loc_1 = reg_0 break end GLOBAL_LIST[0].value = add_i32(loc_0 , 64 )reg_0 = loc_1 break end return reg_0 end FUNC_LIST[122] =--[[ _ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h79de601cf007b9bfE ]]function(param_0, param_1)local reg_0 while true do reg_0 = FUNC_LIST[111](load_i32(memory_at_0, param_1 + 20), load_i32(memory_at_0, add_i32(param_1 , 24 )), load_i32(memory_at_0, param_0 ))break end return reg_0 end FUNC_LIST[123] =--[[ _ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h04b1f732eaaa8361E ]]function(param_0, param_1)local reg_0 while true do param_0 = load_i32(memory_at_0, param_0 )reg_0 = FUNC_LIST[108](param_1 , load_i32(memory_at_0, param_0 ), load_i32(memory_at_0, param_0 + 4))break end return reg_0 end FUNC_LIST[124] =--[[ _ZN42_$LT$$RF$T$u20$as$u20$core..fmt..Debug$GT$3fmt17h72fd019a025a9f45E ]]function(param_0, param_1)local reg_0 while true do reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, param_0 + 4)+ 12)](load_i32(memory_at_0, param_0 ), param_1 )break end return reg_0 end FUNC_LIST[125] =--[[ _ZN4core3fmt9Formatter3new17h1e5ff75bacec31bdE ]]function(param_0, param_1, param_2)while true do store_i32_n8(memory_at_0, param_0 + 32, 3 )store_i32(memory_at_0, param_0 + 16, 32 )store_i32(memory_at_0, param_0 + 28, 0 )store_i32(memory_at_0, param_0 + 20, param_1 )store_i32(memory_at_0, param_0 + 8, 0 )store_i32(memory_at_0, param_0 , 0 )store_i32(memory_at_0, add_i32(param_0 , 24 ), param_2 )break end end FUNC_LIST[126] =--[[ _ZN4core3str5count14do_count_chars17h34fe08ccf7b231f6E ]]function(param_0, param_1)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6, loc_7, loc_8 = 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0, reg_1, reg_2 local desired while true do while true do while true do loc_0 = band_i32(add_i32(param_0 , 3 ), 4294967292 )loc_1 = sub_i32(loc_0 , param_0 )if loc_1 > param_1 then break end loc_2 = sub_i32(param_1 , loc_1 )if loc_2 < 4 then break end loc_3 = band_i32(loc_2 , 3 )loc_4 = 0 param_1 = 0 while true do if loc_0 == param_0 then break end loc_5 = band_i32(loc_1 , 3 )while true do while true do if add_i32(loc_0 , bxor_i32(param_0 , 4294967295 ))>= 3 then break end param_1 = 0 loc_0 = param_0 desired = 4 break end if desired then if desired == 4 then desired = nil end break end loc_6 = band_i32(loc_1 , 4294967292 )param_1 = 0 loc_0 = param_0 while true do param_1 = add_i32(add_i32(add_i32(add_i32(param_1 , (gt_i32(load_i32_i8(memory_at_0, loc_0 ), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_0 + 1), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_0 + 2), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, loc_0 + 3), 4294967231 )and 1 or 0))loc_0 = add_i32(loc_0 , 4 )loc_6 = add_i32(loc_6 , 4294967292 )if loc_6 ~= 0 then continue end break end if desired then if desired == 4 then desired = nil end break end break end if desired then if desired == 3 then desired = nil end break end if loc_5 == 0 then break end while true do param_1 = add_i32(param_1 , (gt_i32(load_i32_i8(memory_at_0, loc_0 ), 4294967231 )and 1 or 0))loc_0 = add_i32(loc_0 , 1 )loc_5 = add_i32(loc_5 , 4294967295 )if loc_5 ~= 0 then continue end break end if desired then if desired == 3 then desired = nil end break end break end if desired then if desired == 2 then desired = nil end break end param_0 = add_i32(param_0 , loc_1 )while true do if loc_3 == 0 then break end loc_0 = add_i32(param_0 , band_i32(loc_2 , 4294967292 ))loc_4 = (gt_i32(load_i32_i8(memory_at_0, loc_0 ), 4294967231 )and 1 or 0)if loc_3 == 1 then break end loc_4 = add_i32(loc_4 , (gt_i32(load_i32_i8(memory_at_0, loc_0 + 1), 4294967231 )and 1 or 0))if loc_3 == 2 then break end loc_4 = add_i32(loc_4 , (gt_i32(load_i32_i8(memory_at_0, loc_0 + 2), 4294967231 )and 1 or 0))break end if desired then if desired == 2 then desired = nil end break end loc_1 = shr_u32(loc_2 , 2 )loc_5 = add_i32(loc_4 , param_1 )while true do loc_4 = param_0 if loc_1 == 0 then desired = 1 break end loc_2 = (loc_1 < 192 and loc_1 or 192 )loc_3 = band_i32(loc_2 , 3 )loc_7 = shl_i32(loc_2 , 2 )while true do while true do loc_8 = band_i32(loc_2 , 252 )if loc_8 ~= 0 then break end loc_0 = 0 desired = 4 break end if desired then if desired == 4 then desired = nil end break end loc_6 = add_i32(loc_4 , shl_i32(loc_8 , 2 ))loc_0 = 0 param_0 = loc_4 while true do if param_0 == 0 then desired = 4 break end param_1 = load_i32(memory_at_0, add_i32(param_0 , 12 ))reg_0 = band_i32(bor_i32(shr_u32(bxor_i32(param_1 , 4294967295 ), 7 ), shr_u32(param_1 , 6 )), 16843009 )param_1 = load_i32(memory_at_0, add_i32(param_0 , 8 ))reg_1 = band_i32(bor_i32(shr_u32(bxor_i32(param_1 , 4294967295 ), 7 ), shr_u32(param_1 , 6 )), 16843009 )param_1 = load_i32(memory_at_0, add_i32(param_0 , 4 ))reg_2 = band_i32(bor_i32(shr_u32(bxor_i32(param_1 , 4294967295 ), 7 ), shr_u32(param_1 , 6 )), 16843009 )param_1 = load_i32(memory_at_0, param_0 )loc_0 = add_i32(reg_0 , add_i32(reg_1 , add_i32(reg_2 , add_i32(band_i32(bor_i32(shr_u32(bxor_i32(param_1 , 4294967295 ), 7 ), shr_u32(param_1 , 6 )), 16843009 ), loc_0 ))))param_0 = add_i32(param_0 , 16 )if param_0 ~= loc_6 then continue end break end if desired then if desired == 4 then desired = nil end break end break end if desired then if desired == 3 then desired = nil continue end break end loc_1 = sub_i32(loc_1 , loc_2 )param_0 = add_i32(loc_4 , loc_7 )loc_5 = add_i32(shr_u32(mul_i32(add_i32(band_i32(shr_u32(loc_0 , 8 ), 16711935 ), band_i32(loc_0 , 16711935 )), 65537 ), 16 ), loc_5 )if loc_3 == 0 then continue end break end if desired then if desired == 2 then desired = nil end break end while true do while true do if loc_4 ~= 0 then break end param_0 = 0 desired = 3 break end if desired then if desired == 3 then desired = nil end break end loc_0 = add_i32(loc_4 , shl_i32(loc_8 , 2 ))param_0 = load_i32(memory_at_0, loc_0 )param_0 = band_i32(bor_i32(shr_u32(bxor_i32(param_0 , 4294967295 ), 7 ), shr_u32(param_0 , 6 )), 16843009 )if loc_3 == 1 then break end param_1 = load_i32(memory_at_0, loc_0 + 4)param_0 = add_i32(band_i32(bor_i32(shr_u32(bxor_i32(param_1 , 4294967295 ), 7 ), shr_u32(param_1 , 6 )), 16843009 ), param_0 )if loc_3 == 2 then break end loc_0 = load_i32(memory_at_0, loc_0 + 8)param_0 = add_i32(band_i32(bor_i32(shr_u32(bxor_i32(loc_0 , 4294967295 ), 7 ), shr_u32(loc_0 , 6 )), 16843009 ), param_0 )break end if desired then if desired == 2 then desired = nil end break end reg_0 = add_i32(shr_u32(mul_i32(add_i32(band_i32(shr_u32(param_0 , 8 ), 459007 ), band_i32(param_0 , 16711935 )), 65537 ), 16 ), loc_5 )desired = 0 break end if desired then if desired == 1 then desired = nil end break end while true do if param_1 ~= 0 then break end reg_0 = 0 desired = 0 break end if desired then if desired == 1 then desired = nil end break end loc_0 = band_i32(param_1 , 3 )while true do while true do if param_1 >= 4 then break end loc_5 = 0 desired = 2 break end if desired then if desired == 2 then desired = nil end break end param_1 = band_i32(param_1 , 4294967292 )loc_5 = 0 while true do loc_5 = add_i32(add_i32(add_i32(add_i32(loc_5 , (gt_i32(load_i32_i8(memory_at_0, param_0 ), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_0 + 1), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_0 + 2), 4294967231 )and 1 or 0)), (gt_i32(load_i32_i8(memory_at_0, param_0 + 3), 4294967231 )and 1 or 0))param_0 = add_i32(param_0 , 4 )param_1 = add_i32(param_1 , 4294967292 )if param_1 ~= 0 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end if loc_0 == 0 then break end while true do loc_5 = add_i32(loc_5 , (gt_i32(load_i32_i8(memory_at_0, param_0 ), 4294967231 )and 1 or 0))param_0 = add_i32(param_0 , 1 )loc_0 = add_i32(loc_0 , 4294967295 )if loc_0 ~= 0 then continue end break end if desired then if desired == 1 then desired = nil end break end break end if desired then if desired == 0 then desired = nil end break end reg_0 = loc_5 break end return reg_0 end FUNC_LIST[127] =--[[ _ZN4core3fmt9Formatter12pad_integral12write_prefix17he1c339465beb40e8E ]]function(param_0, param_1, param_2, param_3, param_4)local loc_0 = 0  local reg_0 local desired while true do while true do while true do while true do if param_2 == 1114112 then break end loc_0 = 1 reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_1 + 16)](param_0 , param_2 )if reg_0 ~= 0 then desired = 2 break end break end if desired then if desired == 2 then desired = nil end break end if param_3 ~= 0 then desired = 1 break end loc_0 = 0 break end if desired then if desired == 1 then desired = nil end break end reg_0 = loc_0 desired = 0 break end if desired then if desired == 0 then desired = nil end break end reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, param_1 + 12)](param_0 , param_3 , param_4 )break end return reg_0 end FUNC_LIST[128] =--[[ _ZN4core5slice6memchr14memchr_aligned17h6c15952605a5d320E ]]function(param_0, param_1, param_2, param_3)local loc_0, loc_1, loc_2, loc_3, loc_4 = 0 , 0 , 0 , 0 , 0  local desired while true do while true do while true do while true do while true do loc_0 = band_i32(add_i32(param_2 , 3 ), 4294967292 )if loc_0 == param_2 then break end loc_0 = sub_i32(loc_0 , param_2 )loc_0 = (loc_0 < param_3 and loc_0 or param_3 )if loc_0 == 0 then break end loc_1 = 0 loc_2 = band_i32(param_1 , 255 )loc_3 = 1 while true do if load_i32_u8(memory_at_0, add_i32(param_2 , loc_1 ))== loc_2 then desired = 1 break end loc_1 = add_i32(loc_1 , 1 )if loc_0 ~= loc_1 then continue end break end if desired then if desired == 4 then desired = nil end break end loc_4 = add_i32(param_3 , 4294967288 )if loc_0 > loc_4 then desired = 2 break end desired = 3 break end if desired then if desired == 3 then desired = nil end break end loc_4 = add_i32(param_3 , 4294967288 )loc_0 = 0 break end if desired then if desired == 2 then desired = nil end break end loc_1 = mul_i32(band_i32(param_1 , 255 ), 16843009 )while true do loc_3 = add_i32(param_2 , loc_0 )loc_2 = bxor_i32(load_i32(memory_at_0, loc_3 ), loc_1 )if band_i32(band_i32(bxor_i32(loc_2 , 4294967295 ), add_i32(loc_2 , 4278124287 )), 2155905152 )~= 0 then desired = 2 break end loc_2 = bxor_i32(load_i32(memory_at_0, add_i32(loc_3 , 4 )), loc_1 )if band_i32(band_i32(bxor_i32(loc_2 , 4294967295 ), add_i32(loc_2 , 4278124287 )), 2155905152 )~= 0 then desired = 2 break end loc_0 = add_i32(loc_0 , 8 )if loc_0 <= loc_4 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end loc_3 = 0 while true do if loc_0 == param_3 then break end loc_1 = band_i32(param_1 , 255 )while true do while true do if load_i32_u8(memory_at_0, add_i32(param_2 , loc_0 ))~= loc_1 then break end loc_1 = loc_0 loc_3 = 1 desired = 1 break end if desired then if desired == 3 then desired = nil continue end break end loc_0 = add_i32(loc_0 , 1 )if param_3 ~= loc_0 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end loc_1 = param_3 break end store_i32(memory_at_0, param_0 + 4, loc_1 )store_i32(memory_at_0, param_0 , loc_3 )break end end FUNC_LIST[129] =--[[ _ZN4core3fmt3num3imp7fmt_u6417h53fa5a065a51ff4cE ]]function(param_0, param_1, param_2)local loc_0, loc_1 = 0 , 0  local loc_2 = i64_ZERO  local loc_3, loc_4, loc_5 = 0 , 0 , 0  local reg_0, reg_1 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 48 )GLOBAL_LIST[0].value = loc_0 loc_1 = 39 while true do while true do if ge_u64(param_0 , i64_from_u32(10000, 0) )then break end loc_2 = param_0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_1 = 39 while true do loc_3 = add_i32(add_i32(loc_0 , 9 ), loc_1 )loc_2 = div_u64(param_0 , i64_from_u32(10000, 0) )loc_4 = wrap_i32_i64(sub_i64(param_0 , mul_i64(loc_2 , i64_from_u32(10000, 0) )))loc_5 = div_u32(band_i32(loc_4 , 65535 ), 100 )store_i32_n16(memory_at_0, add_i32(loc_3 , 4294967292 ), load_i32_u16(memory_at_0, add_i32(shl_i32(loc_5 , 1 ), 1051196 )))store_i32_n16(memory_at_0, add_i32(loc_3 , 4294967294 ), load_i32_u16(memory_at_0, add_i32(shl_i32(band_i32(sub_i32(loc_4 , mul_i32(loc_5 , 100 )), 65535 ), 1 ), 1051196 )))loc_1 = add_i32(loc_1 , 4294967292 )loc_3 = (gt_u64(param_0 , i64_from_u32(99999999, 0) )and 1 or 0)param_0 = loc_2 if loc_3 ~= 0 then continue end break end if desired then if desired == 1 then desired = nil end break end break end while true do loc_3 = wrap_i32_i64(loc_2 )if loc_3 <= 99 then break end loc_1 = add_i32(loc_1 , 4294967294 )loc_3 = wrap_i32_i64(loc_2 )reg_1 = loc_3 loc_3 = div_u32(band_i32(loc_3 , 65535 ), 100 )store_i32_n16(memory_at_0, add_i32(add_i32(loc_0 , 9 ), loc_1 ), load_i32_u16(memory_at_0, add_i32(shl_i32(band_i32(sub_i32(reg_1 , mul_i32(loc_3 , 100 )), 65535 ), 1 ), 1051196 )))break end while true do while true do if loc_3 < 10 then break end loc_1 = add_i32(loc_1 , 4294967294 )store_i32_n16(memory_at_0, add_i32(add_i32(loc_0 , 9 ), loc_1 ), load_i32_u16(memory_at_0, add_i32(shl_i32(loc_3 , 1 ), 1051196 )))desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_1 = add_i32(loc_1 , 4294967295 )store_i32_n8(memory_at_0, add_i32(add_i32(loc_0 , 9 ), loc_1 ), add_i32(loc_3 , 48 ))break end reg_0 = FUNC_LIST[112](param_2 , param_1 , 1051076 , 0 , add_i32(add_i32(loc_0 , 9 ), loc_1 ), sub_i32(39 , loc_1 ))loc_1 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 48 )reg_0 = loc_1 break end return reg_0 end FUNC_LIST[130] =--[[ _ZN53_$LT$core..fmt..Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h19ff99ce888a9250E ]]function(param_0, param_1)local reg_0 while true do reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_1 , 24 ))+ 12)](load_i32(memory_at_0, param_1 + 20), 1051396 , 5 )break end return reg_0 end FUNC_LIST[131] =--[[ _ZN69_$LT$core..alloc..layout..LayoutError$u20$as$u20$core..fmt..Debug$GT$3fmt17hc7cd1c2ff1e8a326E ]]function(param_0, param_1)local reg_0 while true do reg_0 = TABLE_LIST[0].data[load_i32(memory_at_0, load_i32(memory_at_0, add_i32(param_1 , 24 ))+ 12)](load_i32(memory_at_0, param_1 + 20), 1051401 , 11 )break end return reg_0 end FUNC_LIST[132] =--[[ memcpy ]]function(param_0, param_1, param_2)local reg_0 while true do reg_0 = FUNC_LIST[134](param_0 , param_1 , param_2 )break end return reg_0 end FUNC_LIST[133] =--[[ memset ]]function(param_0, param_1, param_2)local reg_0 while true do reg_0 = FUNC_LIST[135](param_0 , param_1 , param_2 )break end return reg_0 end FUNC_LIST[134] =--[[ _ZN17compiler_builtins3mem6memcpy17ha1338d2d3041a583E ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2, loc_3, loc_4, loc_5, loc_6, loc_7 = 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0  local reg_0, reg_1 local desired while true do while true do while true do if param_2 > 15 then break end loc_0 = param_0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_1 = band_i32(sub_i32(0 , param_0 ), 3 )loc_2 = add_i32(param_0 , loc_1 )while true do if loc_1 == 0 then break end loc_0 = param_0 loc_3 = param_1 while true do store_i32_n8(memory_at_0, loc_0 , load_i32_u8(memory_at_0, loc_3 ))loc_3 = add_i32(loc_3 , 1 )loc_0 = add_i32(loc_0 , 1 )if loc_0 < loc_2 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end loc_4 = sub_i32(param_2 , loc_1 )loc_5 = band_i32(loc_4 , 4294967292 )loc_0 = add_i32(loc_2 , loc_5 )while true do while true do loc_6 = add_i32(param_1 , loc_1 )loc_3 = band_i32(loc_6 , 3 )if loc_3 == 0 then break end if lt_i32(loc_5 , 1 )then desired = 2 break end loc_7 = band_i32(loc_6 , 4294967292 )param_1 = add_i32(loc_7 , 4 )param_2 = shl_i32(loc_3 , 3 )loc_1 = band_i32(sub_i32(0 , param_2 ), 24 )loc_3 = load_i32(memory_at_0, loc_7 )while true do reg_1 = shr_u32(loc_3 , param_2 )loc_3 = load_i32(memory_at_0, param_1 )store_i32(memory_at_0, loc_2 , bor_i32(reg_1 , shl_i32(loc_3 , loc_1 )))param_1 = add_i32(param_1 , 4 )loc_2 = add_i32(loc_2 , 4 )if loc_2 < loc_0 then continue end desired = 2 break end if desired then if desired == 3 then desired = nil end break end break end if desired then if desired == 2 then desired = nil end break end if lt_i32(loc_5 , 1 )then break end param_1 = loc_6 while true do store_i32(memory_at_0, loc_2 , load_i32(memory_at_0, param_1 ))param_1 = add_i32(param_1 , 4 )loc_2 = add_i32(loc_2 , 4 )if loc_2 < loc_0 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end param_2 = band_i32(loc_4 , 3 )param_1 = add_i32(loc_6 , loc_5 )break end while true do if param_2 == 0 then break end loc_2 = add_i32(loc_0 , param_2 )while true do store_i32_n8(memory_at_0, loc_0 , load_i32_u8(memory_at_0, param_1 ))param_1 = add_i32(param_1 , 1 )loc_0 = add_i32(loc_0 , 1 )if loc_0 < loc_2 then continue end break end if desired then if desired == 1 then desired = nil end break end break end reg_0 = param_0 break end return reg_0 end FUNC_LIST[135] =--[[ _ZN17compiler_builtins3mem6memset17h5a9fd781a1d5ee99E ]]function(param_0, param_1, param_2)local loc_0, loc_1, loc_2 = 0 , 0 , 0  local reg_0 local desired while true do while true do while true do if param_2 > 15 then break end loc_0 = param_0 desired = 1 break end if desired then if desired == 1 then desired = nil end break end loc_1 = band_i32(sub_i32(0 , param_0 ), 3 )loc_2 = add_i32(param_0 , loc_1 )while true do if loc_1 == 0 then break end loc_0 = param_0 while true do store_i32_n8(memory_at_0, loc_0 , param_1 )loc_0 = add_i32(loc_0 , 1 )if loc_0 < loc_2 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end loc_1 = sub_i32(param_2 , loc_1 )param_2 = band_i32(loc_1 , 4294967292 )loc_0 = add_i32(loc_2 , param_2 )while true do if lt_i32(param_2 , 1 )then break end param_2 = mul_i32(band_i32(param_1 , 255 ), 16843009 )while true do store_i32(memory_at_0, loc_2 , param_2 )loc_2 = add_i32(loc_2 , 4 )if loc_2 < loc_0 then continue end break end if desired then if desired == 2 then desired = nil end break end break end if desired then if desired == 1 then desired = nil end break end param_2 = band_i32(loc_1 , 3 )break end while true do if param_2 == 0 then break end loc_2 = add_i32(loc_0 , param_2 )while true do store_i32_n8(memory_at_0, loc_0 , param_1 )loc_0 = add_i32(loc_0 , 1 )if loc_0 < loc_2 then continue end break end if desired then if desired == 1 then desired = nil end break end break end reg_0 = param_0 break end return reg_0 end FUNC_LIST[136] =--[[ _ZN4core3fmt5Write9write_fmt17hf849e6d9541e7988E ]]function(param_0, param_1)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 4, param_0 )store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 16 ), load_i64(memory_at_0, add_i32(param_1 , 16 )))store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 8 ), load_i64(memory_at_0, add_i32(param_1 , 8 )))store_i64(memory_at_0, loc_0 + 8, load_i64(memory_at_0, param_1 ))reg_0 = FUNC_LIST[111](add_i32(loc_0 , 4 ), 1051412 , add_i32(loc_0 , 8 ))param_1 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )reg_0 = param_1 break end return reg_0 end FUNC_LIST[137] =--[[ _ZN4core3ptr54drop_in_place$LT$$RF$mut$u20$alloc..string..String$GT$17hc5b066e15459ed65E ]]function(param_0)while true do break end end FUNC_LIST[138] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$10write_char17ha52600710543be24E ]]function(param_0, param_1)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 param_0 = load_i32(memory_at_0, param_0 )while true do while true do if param_1 > 127 then break end while true do loc_1 = load_i32(memory_at_0, param_0 + 8)if loc_1 ~= load_i32(memory_at_0, param_0 + 4)then break end FUNC_LIST[33](param_0 , loc_1 )loc_1 = load_i32(memory_at_0, param_0 + 8)break end if desired then if desired == 2 then desired = nil end break end store_i32_n8(memory_at_0, add_i32(load_i32(memory_at_0, param_0 ), loc_1 ), param_1 )store_i32(memory_at_0, param_0 + 8, add_i32(load_i32(memory_at_0, param_0 + 8), 1 ))desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 12, 0 )while true do while true do if param_1 < 2048 then break end while true do if param_1 < 65536 then break end store_i32_n8(memory_at_0, loc_0 + 15, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 12 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(band_i32(shr_u32(param_1 , 18 ), 7 ), 240 ))param_1 = 4 desired = 2 break end if desired then if desired == 3 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 12 ), 224 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))param_1 = 3 desired = 2 break end if desired then if desired == 2 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 6 ), 192 ))param_1 = 2 break end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[39](param_0 , add_i32(loc_0 , 12 ), param_1 )break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = 0 break end return reg_0 end FUNC_LIST[139] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_fmt17hcf245b3f50afdf19E ]]function(param_0, param_1)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 32 )GLOBAL_LIST[0].value = loc_0 param_0 = load_i32(memory_at_0, param_0 )store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 16 ), load_i64(memory_at_0, add_i32(param_1 , 16 )))store_i64(memory_at_0, add_i32(add_i32(loc_0 , 8 ), 8 ), load_i64(memory_at_0, add_i32(param_1 , 8 )))store_i64(memory_at_0, loc_0 + 8, load_i64(memory_at_0, param_1 ))reg_0 = FUNC_LIST[136](param_0 , add_i32(loc_0 , 8 ))param_1 = reg_0 GLOBAL_LIST[0].value = add_i32(loc_0 , 32 )reg_0 = param_1 break end return reg_0 end FUNC_LIST[140] =--[[ _ZN50_$LT$$RF$mut$u20$W$u20$as$u20$core..fmt..Write$GT$9write_str17hd36a1b2be8682a8cE ]]function(param_0, param_1, param_2)local reg_0 while true do FUNC_LIST[39](load_i32(memory_at_0, param_0 ), param_1 , param_2 )reg_0 = 0 break end return reg_0 end FUNC_LIST[141] =--[[ _ZN45_$LT$T$u20$as$u20$alloc..string..ToString$GT$9to_string17h088b16f087eb58a7E ]]function(param_0, param_1)local loc_0 = 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 64 )GLOBAL_LIST[0].value = loc_0 store_i32(memory_at_0, loc_0 + 8, 0 )store_i64(memory_at_0, loc_0 , i64_ONE )FUNC_LIST[125](add_i32(loc_0 , 16 ), loc_0 , 1051492 )while true do reg_0 = FUNC_LIST[121](param_1 , add_i32(loc_0 , 16 ))if reg_0 ~= 0 then break end store_i64(memory_at_0, param_0 , load_i64(memory_at_0, loc_0 ))store_i32(memory_at_0, add_i32(param_0 , 8 ), load_i32(memory_at_0, add_i32(loc_0 , 8 )))GLOBAL_LIST[0].value = add_i32(loc_0 , 64 )desired = 0 break end if desired then if desired == 0 then desired = nil end break end FUNC_LIST[115](1051436 , 55 , add_i32(loc_0 , 56 ), 1051516 , 1051608 )error("out of code bounds")end end FUNC_LIST[142] =--[[ _ZN4core3ops8function6FnOnce40call_once$u7b$$u7b$vtable.shim$u7d$$u7d$17h48d4cc2ff355a649E ]]function(param_0, param_1)while true do FUNC_LIST[143](param_1 , param_1 )error("out of code bounds")end end FUNC_LIST[143] =--[[ _ZN9roblox_rs4hook28_$u7b$$u7b$closure$u7d$$u7d$17h0441735338d2a87dE ]]function(param_0, param_1)local loc_0 = 0  while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[141](loc_0 , param_1 )FUNC_LIST[3](load_i32(memory_at_0, loc_0 ), load_i32(memory_at_0, loc_0 + 8))error("out of code bounds")end end FUNC_LIST[144] =--[[ _ZN4core3ptr37drop_in_place$LT$core..fmt..Error$GT$17h739cd3f864b2dc9cE ]]function(param_0)while true do break end end FUNC_LIST[145] =--[[ _ZN4core3ptr42drop_in_place$LT$alloc..string..String$GT$17hda7bd4ac0331d1c8E ]]function(param_0)while true do FUNC_LIST[36](param_0 )break end end FUNC_LIST[146] =--[[ _ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$10write_char17h9269691ba1082bdcE ]]function(param_0, param_1)local loc_0, loc_1 = 0 , 0  local reg_0 local desired while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 while true do while true do if param_1 > 127 then break end while true do loc_1 = load_i32(memory_at_0, param_0 + 8)if loc_1 ~= load_i32(memory_at_0, param_0 + 4)then break end FUNC_LIST[33](param_0 , loc_1 )loc_1 = load_i32(memory_at_0, param_0 + 8)break end if desired then if desired == 2 then desired = nil end break end store_i32_n8(memory_at_0, add_i32(load_i32(memory_at_0, param_0 ), loc_1 ), param_1 )store_i32(memory_at_0, param_0 + 8, add_i32(load_i32(memory_at_0, param_0 + 8), 1 ))desired = 1 break end if desired then if desired == 1 then desired = nil end break end store_i32(memory_at_0, loc_0 + 12, 0 )while true do while true do if param_1 < 2048 then break end while true do if param_1 < 65536 then break end store_i32_n8(memory_at_0, loc_0 + 15, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 12 ), 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(band_i32(shr_u32(param_1 , 18 ), 7 ), 240 ))param_1 = 4 desired = 2 break end if desired then if desired == 3 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 14, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 12 ), 224 ))store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(shr_u32(param_1 , 6 ), 63 ), 128 ))param_1 = 3 desired = 2 break end if desired then if desired == 2 then desired = nil end break end store_i32_n8(memory_at_0, loc_0 + 13, bor_i32(band_i32(param_1 , 63 ), 128 ))store_i32_n8(memory_at_0, loc_0 + 12, bor_i32(shr_u32(param_1 , 6 ), 192 ))param_1 = 2 break end if desired then if desired == 1 then desired = nil end break end FUNC_LIST[39](param_0 , add_i32(loc_0 , 12 ), param_1 )break end GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = 0 break end return reg_0 end FUNC_LIST[147] =--[[ _ZN58_$LT$alloc..string..String$u20$as$u20$core..fmt..Write$GT$9write_str17hc2f8a85a53d6c0c4E ]]function(param_0, param_1, param_2)local reg_0 while true do FUNC_LIST[39](param_0 , param_1 , param_2 )reg_0 = 0 break end return reg_0 end FUNC_LIST[148] =--[[ hook ]]function()while true do FUNC_LIST[85](1 , 1051624 )break end end FUNC_LIST[149] =--[[ __heap_alloc_string ]]function(param_0)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[29](add_i32(loc_0 , 8 ), param_0 , 0 )param_0 = load_i32(memory_at_0, loc_0 + 8)GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_0 break end return reg_0 end FUNC_LIST[150] =--[[ __heap_alloc_vec ]]function(param_0)local loc_0 = 0  local reg_0 while true do loc_0 = sub_i32(GLOBAL_LIST[0].value , 16 )GLOBAL_LIST[0].value = loc_0 FUNC_LIST[31](add_i32(loc_0 , 8 ), param_0 , 0 )param_0 = load_i32(memory_at_0, loc_0 + 8)GLOBAL_LIST[0].value = add_i32(loc_0 , 16 )reg_0 = param_0 break end return reg_0 end FUNC_LIST[151] =--[[ __drop_box_dyn_fn ]]function(param_0, param_1)local loc_0 = 0  local desired while true do TABLE_LIST[0].data[load_i32(memory_at_0, param_1 )](param_0 )while true do loc_0 = load_i32(memory_at_0, param_1 + 4)if loc_0 == 0 then break end FUNC_LIST[19](param_0 , loc_0 , load_i32(memory_at_0, param_1 + 8))break end break end end local function run_init_code()TABLE_LIST[0] = { min = 50, max = 50, data = {} }MEMORY_LIST[0] = rt.allocator.new(17, 65535)GLOBAL_LIST[0] = { value =1048576 }GLOBAL_LIST[1] = { value =1052765 }GLOBAL_LIST[2] = { value =1052768 }do local target = TABLE_LIST[0].data local offset =1 local data = {FUNC_LIST[7],FUNC_LIST[6],FUNC_LIST[5],FUNC_LIST[12],FUNC_LIST[41],FUNC_LIST[51],FUNC_LIST[52],FUNC_LIST[53],FUNC_LIST[46],FUNC_LIST[43],FUNC_LIST[44],FUNC_LIST[45],FUNC_LIST[110],FUNC_LIST[84],FUNC_LIST[68],FUNC_LIST[75],FUNC_LIST[72],FUNC_LIST[74],FUNC_LIST[114],FUNC_LIST[70],FUNC_LIST[66],FUNC_LIST[64],FUNC_LIST[71],FUNC_LIST[87],FUNC_LIST[88],FUNC_LIST[89],FUNC_LIST[90],FUNC_LIST[65],FUNC_LIST[96],FUNC_LIST[131],FUNC_LIST[105],FUNC_LIST[124],FUNC_LIST[117],FUNC_LIST[122],FUNC_LIST[123],FUNC_LIST[106],FUNC_LIST[113],FUNC_LIST[137],FUNC_LIST[140],FUNC_LIST[138],FUNC_LIST[139],FUNC_LIST[145],FUNC_LIST[147],FUNC_LIST[146],FUNC_LIST[136],FUNC_LIST[144],FUNC_LIST[130],FUNC_LIST[142],FUNC_LIST[143],}table.move(data, 1, #data, offset, target)end rt.store.string(MEMORY_LIST[0],1048576 ,"\x01\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x02\x00\x00\x00\x03\x00\x00\x00\x03\x00\x00\x00Hello from wasm!!!~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/memory_units-0.4.0/src/lib.rs\x00\x00*\x00\x10\x00T\x00\x00\x00\xae\x00\x00\x00\x05\x00\x00\x00attempt to multiply with overflow\x00\x00\x00*\x00\x10\x00T\x00\x00\x00\xa6\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00attempt to subtract with overflow\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00attempt to add with overflow~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/wee_alloc-0.4.5/src/size_classes.rs\x00\x00\x1c\x01\x10\x00Z\x00\x00\x00\x17\x00\x00\x00\x14\x00\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x06\x00\x00\x00\x07\x00\x00\x00\x08\x00\x00\x00~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/memory_units-0.4.0/src/lib.rs\xa0\x01\x10\x00T\x00\x00\x00\xb3\x00\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00attempt to multiply with overflow\x00\x00\x00\xa0\x01\x10\x00T\x00\x00\x00\xae\x00\x00\x00\x05\x00\x00\x00called `Option::unwrap()` on a `None` value\x00\xa0\x01\x10\x00T\x00\x00\x00\xa6\x00\x00\x00\x01\x00\x00\x00attempt to add with overflow\x00\x00\x00\x00attempt to subtract with overflow~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/wee_alloc-0.4.5/src/lib.rs\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00\x9e\x01\x00\x00\x0f\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00\x19\x02\x00\x00!\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00\x19\x02\x00\x004\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00\x1c\x02\x00\x00\x0c\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00\x1d\x02\x00\x00#\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x00!\x02\x00\x00\x1b\x00\x00\x00\t\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x06\x00\x00\x00\x07\x00\x00\x00\x08\x00\x00\x00\t\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\n\x00\x00\x00\x0b\x00\x00\x00\x0c\x00\x00\x00\xc1\x02\x10\x00Q\x00\x00\x003\x03\x00\x00\x0f\x00\x00\x00~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/wee_alloc-0.4.5/src/imp_wasm32.rs\xb4\x03\x10\x00X\x00\x00\x00\x0c\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00attempt to multiply with overflow~/.cargo/registry/src/index.crates.io-6f17d22bba15001f/memory_units-0.4.0/src/lib.rs\x00\x00\x00A\x04\x10\x00T\x00\x00\x00\x8f\x00\x00\x00\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00attempt to add with overflowA\x04\x10\x00T\x00\x00\x00\x8f\x00\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00attempt to subtract with overflowcalled `Option::unwrap()` on a `None` value\x0f\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\x10\x00\x00\x00\x11\x00\x00\x00\x12\x00\x00\x00mainlibrary/std/src/rt.rs\x00\x00\x00H\x05\x10\x00\x15\x00\x00\x00r\x00\x00\x00\r\x00\x00\x00library/std/src/thread/mod.rsfailed to generate unique thread ID: bitspace exhausted\x8d\x05\x10\x007\x00\x00\x00p\x05\x10\x00\x1d\x00\x00\x00@\x04\x00\x00\r\x00\x00\x00already borrowed\x0f\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x13\x00\x00\x00library/std/src/io/stdio.rs\x00\xfc\x05\x10\x00\x1b\x00\x00\x00}\x02\x00\x00\x13\x00\x00\x00library/std/src/sync/once.rs(\x06\x10\x00\x1c\x00\x00\x00\x95\x00\x00\x002\x00\x00\x00(\x06\x10\x00\x1c\x00\x00\x00\xd0\x00\x00\x00\x14\x00\x00\x00(\x06\x10\x00\x1c\x00\x00\x00\xd0\x00\x00\x001\x00\x00\x00lock count overflow in reentrant mutexlibrary/std/src/sync/remutex.rs\x00\x00\x00\x9a\x06\x10\x00\x1f\x00\x00\x00\x91\x00\x00\x00\x0e\x00\x00\x00library/std/src/sys_common/thread_info.rs\x00\x00\x00\xcc\x06\x10\x00)\x00\x00\x00+\x00\x00\x00+\x00\x00\x00memory allocation of  bytes failed\x00\x00\x08\x07\x10\x00\x15\x00\x00\x00\x1d\x07\x10\x00\r\x00\x00\x00library/std/src/alloc.rs<\x07\x10\x00\x18\x00\x00\x00U\x01\x00\x00\t\x00\x00\x00cannot modify the panic hook from a panicking threadd\x07\x10\x004\x00\x00\x00library/std/src/panicking.rs\xa0\x07\x10\x00\x1c\x00\x00\x00\x87\x00\x00\x00\t\x00\x00\x00\xa0\x07\x10\x00\x1c\x00\x00\x00A\x02\x00\x00\x1e\x00\x00\x00\xa0\x07\x10\x00\x1c\x00\x00\x00@\x02\x00\x00\x1f\x00\x00\x00\x14\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00\x15\x00\x00\x00\x0f\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00\x16\x00\x00\x00\x17\x00\x00\x00\x10\x00\x00\x00\x04\x00\x00\x00\x18\x00\x00\x00\x19\x00\x00\x00\x0f\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00\x1a\x00\x00\x00\x1b\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x1c\x00\x00\x00one-time initialization may not be performed recursivelyD\x08\x10\x008\x00\x00\x00Once instance has previously been poisoned\x00\x00\x84\x08\x10\x00*\x00\x00\x00library/alloc/src/raw_vec.rscapacity overflow\x00\x00\x00\xd4\x08\x10\x00\x11\x00\x00\x00\xb8\x08\x10\x00\x1c\x00\x00\x00\x0c\x02\x00\x00\x05\x00\x00\x00called `Option::unwrap()` on a `None` valuelibrary/alloc/src/ffi/c_str.rs\x00\x00\x00+\t\x10\x00\x1e\x00\x00\x00\x1b\x01\x00\x007\x00\x00\x00called `Result::unwrap()` on an `Err` value\x00\x1d\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x1e\x00\x00\x00library/alloc/src/sync.rs\x00\x00\x00\x98\t\x10\x00\x19\x00\x00\x00[\x01\x00\x002\x00\x00\x00BorrowMutError\x00\x00\xc4\t\x10\x00\x00\x00\x00\x00:\x00\x00\x00\xc4\t\x10\x00\x00\x00\x00\x00\xdc\t\x10\x00\x01\x00\x00\x00\xdc\t\x10\x00\x01\x00\x00\x00panicked at \'\', \x04\n\x10\x00\x01\x00\x00\x00\x05\n\x10\x00\x03\x00\x00\x00$\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00%\x00\x00\x00: \x00\x00\xc4\t\x10\x00\x00\x00\x00\x00(\n\x10\x00\x02\x00\x00\x0000010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899ErrorLayoutError&\x00\x00\x00\x04\x00\x00\x00\x04\x00\x00\x00\'\x00\x00\x00(\x00\x00\x00)\x00\x00\x00a Display implementation returned an error unexpectedly\x00*\x00\x00\x00\x0c\x00\x00\x00\x04\x00\x00\x00+\x00\x00\x00,\x00\x00\x00-\x00\x00\x00.\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00/\x00\x00\x00/rustc/e9e1bbc7a820c472b39d3de54b3049bf14050655/library/alloc/src/string.rs\x00\x8c\x0b\x10\x00K\x00\x00\x00\xdc\t\x00\x00\x0e\x00\x00\x00.\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x000\x00\x00\x001\x00\x00\x001\x00\x00\x00")end return function(wasm)FUNC_LIST[0] = wasm["env"].func_list["print"]FUNC_LIST[1] = wasm["env"].func_list["drop_pointer"]FUNC_LIST[2] = wasm["env"].func_list["get_game"]FUNC_LIST[3] = wasm["env"].func_list["error"]run_init_code()memory_at_0 = MEMORY_LIST[0]return {func_list = {["main"] = FUNC_LIST[17],["__heap_alloc_string"] = FUNC_LIST[149],["__heap_alloc_vec"] = FUNC_LIST[150],["__drop_box_dyn_fn"] = FUNC_LIST[151],["hook"] = FUNC_LIST[148],},table_list = {},memory_list = {["memory"] = MEMORY_LIST[0],},global_list = {["__data_end"] = GLOBAL_LIST[1],["__heap_base"] = GLOBAL_LIST[2],},} end 