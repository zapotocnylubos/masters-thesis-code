#include <stdlib.h>

void test_malloc() {
  int *pi = (int *)malloc(sizeof(int));
    if (pi == NULL) {
        return;
    }
    //@ admit \valid(pi);
    //@ assert \valid(pi);
}
