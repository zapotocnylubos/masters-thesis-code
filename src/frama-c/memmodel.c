void example_if(int c, int x) {
    if (c) {
        x += 1;
    } else {
        x += 2;
    }

    //@ assert x <= \at(x, Pre) + 2;
}