.sub main
local t0 int8 10
local t1 int64
local t2 int64
.endframe
.label main

mov t1 0::int64
mov t2 &t0
.label main_l0
mul [t2]::int8 t1 3::int8
add t1 t1 1::int64
add t2 t2 1::int64
cmp t1 10::int64
jlt main_l0

mov t1 0::int64
mov t2 &t0
.label main_l1
print [t2]::int8
add t1 t1 1::int64
add t2 t2 1::int64
cmp t1 10::int64
jlt main_l1
return [&t0 + 2]::int8

.endsub
