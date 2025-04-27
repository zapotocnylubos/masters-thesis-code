struct S {
    char c;
};

void calc(struct S *p) {
    p->c = -1;
    p->c = 0;
    p->c = 1;
    p->c = 2;
    //@ assert p->c == 2;
}
