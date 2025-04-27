/*@
    requires n >= 0;
*/
void loop_invariant(int n) {
    while (n > 0) {
        n--;
    }
    //@ assert n == 0;
}