struct a {
    int[5500] x;
    int y;
}

int main() {
    a a;
    for (int x = 0; x < 500; x+=1) {
        a.x[x] = x;
    }
    return 0;
}