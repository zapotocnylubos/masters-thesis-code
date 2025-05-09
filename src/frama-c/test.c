/*@
    predicate P{A,B}(int x) = x > 0;
 */

int increment(int x) {
    L0:
    x = 1;
    L1:
    x = x + 1;
    //@ assert P{L0,L1}(x);
    return x + 1;
}