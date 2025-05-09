// demonstrate problem, where two pointers point to the same location

// requires \separated(x, y); is crucial for a correct reasoning about the code
// if x == y, then the result would not be as ensures specifies

/*@
    requires \valid(x);
    requires \valid(y);
    requires \separated(x, y);

    ensures \at(*x, Post) == \old(*y) + 1;
    ensures \at(*y, Post) == \old(*y);
 */
void calc(int *x, int *y) {
    *x = *y + 1;
}
