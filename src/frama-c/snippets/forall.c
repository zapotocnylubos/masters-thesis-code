/*@
    requires \valid(arr);
    requires n > 0;
    requires
        \forall integer i;
            0 <= i < n
                ==> arr[i] >= 0;
*/
int only_nonnegative(int *arr, int n) {
}