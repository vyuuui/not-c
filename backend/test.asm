beginsubroutine add
beginframeinfo
in t0 int64
in t1 int64
endframeinfo
label add
mul t0 t1 t0
return t0
endsubroutine

beginsubroutine main
beginframeinfo
local t0 int64
endframeinfo
label main
param 15::int8 int64
param 2::int8 int64
call add t0
return t0
endsubroutine