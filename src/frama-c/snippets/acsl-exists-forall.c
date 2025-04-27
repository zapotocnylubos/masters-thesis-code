/*@
    requires \valid(arr);
    requires n > 0;

    requires
        \forall integer i;
            0 <= i < n
                ==> 0 <= arr[i];

    ensures
        \exists integer i;
            0 <= i < n
                ==> arr[i] == \result
                && \forall integer j;
                    0 <= j < n
                        ==> arr[i] <= arr[j];
*/
int find_min(int *arr, int n) {
    int min = arr[0];

    /*@
        loop invariant 0 <= i <= n;
        loop invariant
            \forall integer j;
                0 <= j < i
                    ==> arr[j] >= min;
        loop assigns i, min;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (arr[i] < min) {
            min = arr[i];
        }
    }

    return min;
}