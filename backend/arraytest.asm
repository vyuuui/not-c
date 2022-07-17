.sub sam
local _uhh int64
temp t0 int64
.endframe
.label sam
mul t0 1::int64 4::int64
add t0 _uhh t0
mov _uhh t0
.endsub
.sub main
temp t0 int32
.endframe
.label main
call sam $nil
mov t0 0::int64
return t0
.endsub
