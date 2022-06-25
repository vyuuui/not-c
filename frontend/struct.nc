struct a {
    int x;
}

struct b {
    a bacb;
}

int main() {
    b b;
    *b->x;
}