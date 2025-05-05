#include <stdlib.h>

void test_malloc() {
  int *pi = (int *)malloc(sizeof(int));
    if (pi == NULL) {
        return;
    }
    //@ assert \valid(pi);
}
