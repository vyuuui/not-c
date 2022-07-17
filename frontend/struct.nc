struct test2 {
    int abc;
}
struct test1 {
    int def;
    test2 ghi;
    int x;
    int y;
    int z;
}
struct test0 {
    test1 jkl[3];
    int bunch;
    int of;
    int vars;
}

void sam() {
    test0 x;
    int abc[10];
    int def[10] = abc;
}



int main() {
    sam();
    return 0;
}
