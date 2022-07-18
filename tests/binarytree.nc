struct BinaryNode {
    long value;
    BinaryNode* left;
    BinaryNode* right;
}
bool findValue(BinaryNode* root, long value) {
    return root != no && (root->value == value || findValue(root->left, value) || findValue(root->right, value));
} 

int main() {
    BinaryNode a;
    BinaryNode b;
    BinaryNode c;
    BinaryNode d;
    BinaryNode e;
    BinaryNode f;

    a.value = 0;
    b.value = 4;
    c.value = 10;
    d.value = 7;
    e.value = 11;
    f.value = 21;
    a.left = &b;
    a.right = &c;
    b.left = &d;
    b.right = &e;
    c.left = &f;
    c.right = no;
    d.left = no;
    d.right = no;
    e.left = no;
    e.right = no;
    f.left = no;
    f.right = no;

    if (findValue(&a, 21)) {
        print 1;
    } else {
        print 2;
    }
    if (findValue(&a, 999)) {
        print 3;
    } else {
        print 4;
    }
    return 0;
}