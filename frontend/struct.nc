int proof_my_compiler_works(int fac) {
    long i;
    long out = 1;
    for (i = 1; i <= fac; i+=1) {
        out *= i;
    }
    return out;
}

int main() {
    return proof_my_compiler_works(10);
}
