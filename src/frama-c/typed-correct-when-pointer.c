void calc() {
    long long a;
    int xw = 0;
    int *p = &xw;

    *p = 1;
    //@ assert xw == 1;
}
