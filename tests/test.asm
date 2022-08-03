.sub main
local _c int64
temp t0 int64
temp t1 int64
.endframe
.label main
mul t1 20::int64 28::int64
dynalloc t0 t1
mov _c t0
dynfree [_c + 20]::int64
return 102::int8
.endsub

