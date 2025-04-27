/*@ 
  requires 0 ≤ n;
  ensures  \result ≥ 0;
*/
int abs(int n) {
  return n < 0 ? -n : n;
}
