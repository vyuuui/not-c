int add(int x, int y) {
    return x + y;
}

bool check(float x, float y) {
    if (x > y) {
        return true;
    } else {
        return false;
    }
}

int mult(float z) {
    z *= 6.0;
    return z;
}

void main() {
    if (check(1.5, 2.1)) {
        check(mult(5), 5);
    } else {
        add(0, 1);
    }
}