.sub findValue
in _root int64
in _value int64
temp t0 int64
temp t1 int8
temp t2 int8
temp t3 int8
temp t4 int8
.endframe
.label findValue
mov t0 0::int64
mov t1 0::int8
cmp _root t0
jeq l0
mov t1 1::int8
.label l0
mov t3 t1
cmp t1 0::int8
jeq l4
mov t2 1::int8
cmp [_root]::int64 _value
jeq l1
mov t2 0::int8
.label l1
mov t4 t2
cmp t2 1::int8
jeq l2
param [_root + 8]::int64 int64
param _value int64
call findValue t3
mov t4 t3
.label l2
mov t2 t4
cmp t4 1::int8
jeq l3
param [_root + 16]::int64 int64
param _value int64
call findValue t3
mov t2 t3
.label l3
mov t3 t2
.label l4
return t3
.endsub
.sub main
local _a int8 24
local _b int8 24
local _c int8 24
local _d int8 24
local _e int8 24
local _f int8 24
temp t0 int64
temp t1 int64
temp t2 int8
temp t3 int32
.endframe
.label main
mov [&_a]::int64 0::int64
mov [&_b]::int64 4::int64
mov [&_c]::int64 10::int64
mov [&_d]::int64 7::int64
mov [&_e]::int64 11::int64
mov [&_f]::int64 21::int64
mov [&_a + 8]::int64 &_b
mov [&_a + 16]::int64 &_c
mov [&_b + 8]::int64 &_d
mov [&_b + 16]::int64 &_e
mov [&_c + 8]::int64 &_f
mov t0 0::int64
mov [&_c + 16]::int64 t0
mov t0 0::int64
mov [&_d + 8]::int64 t0
mov t0 0::int64
mov [&_d + 16]::int64 t0
mov t0 0::int64
mov [&_e + 8]::int64 t0
mov t0 0::int64
mov [&_e + 16]::int64 t0
mov t0 0::int64
mov [&_f + 8]::int64 t0
mov t0 0::int64
mov [&_f + 16]::int64 t0
param &_a int64
param 21::int64 int64
call findValue t2
cmp t2 0::int8
jeq l6
print 1::int64
jmp l5
.label l6
print 2::int64
.label l5
param &_a int64
param 999::int64 int64
call findValue t2
cmp t2 0::int8
jeq l8
print 3::int64
jmp l7
.label l8
print 4::int64
.label l7
mov t3 0::int64
return t3
.endsub
