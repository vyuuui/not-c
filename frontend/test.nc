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
    z *= 5.0;
    return z;
}

void main() {
    if (check(0.5, 2.1)) {
        check((4), 5.0);
    } else {
        mult(9);
    }
}