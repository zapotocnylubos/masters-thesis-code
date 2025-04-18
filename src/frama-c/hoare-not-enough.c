/*@
    requires \valid(x);

    ensures \at(*x, Post) == 1;
 */
void calc(int *x) {
    *x = 1;
}
