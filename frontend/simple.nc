bool test(int* out) {
    *out = 5/4+2;
    return *out == 3;
}

short main() {
    int x = 0;
    x += 1;
    int*[10] a;
    char[4] str;
    str = "test";
    
    int* y = &x;
    int** z = &y;
    a[0] = y;
    while (y == *z) {
        test(*(z+x)) == false;
    }
    for (;;) {
        
    }
    for (int q; ; q += 1) {
        q = 30;
    }
}