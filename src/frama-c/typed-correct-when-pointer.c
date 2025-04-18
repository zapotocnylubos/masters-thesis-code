void calc() {
    int x = 0;
    int *p = &x;

    *p = 1;
    //@ assert x == 1;
}
