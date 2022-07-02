struct test {
    int mem1;
    float mem2;
}

int main() {
    int x;
    test t;
    t.mem1 = x;
    test* t2;
    t2->mem1 = 1.0 * x;
    return 0;
}
