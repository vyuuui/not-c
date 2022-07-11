.sub main
local test int32 3
local test2 int32 2
local fe int64
local fe_ptr int64
.endframe
.label main
mov [&test + 0]::int32 20::int32
mov [&test + 4]::int32 21::int32
mov [&test + 8]::int32 22::int32
add fe &test 4::int32
mov fe_ptr &fe
arraycopy &test2 fe 8
return [&test2 + 4]::int32
.endsub 
