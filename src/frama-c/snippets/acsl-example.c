/*@ requires x > 0;
    assigns \result;
    ensures \result == x + 2;
*/
int increment(int x) {
    //@ assert x >= 1;
    x = x + 1;
    //@ assert x >= 2;
    return x + 1;
}