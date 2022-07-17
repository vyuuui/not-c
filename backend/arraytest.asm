.sub main
local _pos float
local _test_x float
temp t0 float
temp t1 float
temp t2 float
.endframe
.label main
inttofloat t0 5::int64
mov _test_x t0
div t0 4::float 2::float
mul t1 t0 _test_x
inttofloat t0 3::int64
add t2 t1 t0
mov _pos t2
print _pos
return _pos
.endsub
