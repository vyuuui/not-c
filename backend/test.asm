mov r0 123i64
mov ti64_abc 321i64
add r0 r0 ti64_abc
sub r0 r0 5
cmp r0 439i64
je 2
mov r0 0i64
mov r1 1i32
mov r2 99i8
pushs
mov ti64_abc 9999i32
cmp ti64_abc 9999i32
je 1
pops
mov r7 64i64
print 1i64
print r7
print ti64_abc
print r0