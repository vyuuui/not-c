.sub proof_my_compiler_works
in _fac int64
local _i int64
local _out int64
temp t0 int8
temp t1 int32
.endframe
.label proof_my_compiler_works
mov _out 1::int64
mov _i 1::int64
.label l2
mov t0 0::int8
cmp _i _fac
jgt l0
mov t0 1::int8
.label l0
cmp t0 0::int8
jeq l1
mul _out _out _i
.label l3
add _i _i 1::int64
jmp l2
.label l1
mov t1 _out
return t1
.endsub
.sub main
temp t0 int32
.endframe
.label main
param 10::int64 int64
call proof_my_compiler_works t0
return t0
.endsub
