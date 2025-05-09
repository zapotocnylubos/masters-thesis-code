/*@
    requires n >= 0;
*/
void loop_invariant(int n) {
    /*@
        loop invariant n >= 0;
        loop variant n;
    */
    while (n > 0) {
        n--;
    }
    //@ assert n == 0;
}