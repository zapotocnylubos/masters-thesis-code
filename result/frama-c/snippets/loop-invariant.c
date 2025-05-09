/*@
    requires n >= 0;
*/
void loop_invariant(int n) {
    /*@
        loop invariant n >= 0;
    */
    while (n > 0) {
        n--;
    }
    //@ assert n == 0;
}