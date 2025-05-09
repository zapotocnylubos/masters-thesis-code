void calc(int x) {
    L0:
    x++;
    L1:
    x += 2;
    //@ assert x >= \at(x, L0) + 3;
}