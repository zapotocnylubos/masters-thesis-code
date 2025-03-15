#include <stdlib.h>

// https://stackoverflow.com/questions/78862966/copy-a-singly-linked-list-with-frama-c
// ACSL Mini-Tutorial Virgile Prevosto1 1 CEA LIST, Software Security Laboratory, Saclay, F-91191

/*@
    ensures \result >= x && \result >= y;
    ensures \result == x || \result == y;
*/
int max (int x, int y) { return (x > y) ? x : y; }

///*@
//    requires \valid(p) && \valid(q);
//    ensures *p<=*q;
//*/

/*@ requires \valid(p) && \valid(q);
    ensures *p <= *q;
    ensures
        (*p == \old(*p) && *q == \old(*q)) ||
        (*p == \old(*q) && *q == \old(*p));
*/
void max_ptr(int*p, int*q) {
    if (*p > *q) {
        int tmp = *p;
        *p = *q;
        *q = tmp;
    }
}

typedef struct _list { int element; struct _list* next; } list;

/*@
    inductive reachable{L} (list* root, list* node) {
        case root_reachable{L}:
            \forall list* root; reachable(root,root);
        case next_reachable{L}:
            \forall list* root, *node;
                \valid(root) ==>
                    reachable(root->next, node) ==>
                        reachable(root,node);
    }
*/

/*@
    predicate finite{L}(list* root) = reachable(root,\null);
*/

/*@ axiomatic Length {
    logic integer length{L}(list* l);

    axiom length_nil{L}: length(\null) == 0;

    axiom length_cons{L}:
        \forall list* l, integer n;
            finite(l) && \valid(l) ==>
                length(l) == length(l->next) + 1;
    }
*/

/*@
    requires \valid(root);
    terminates finite(root);
    assigns \nothing;
    ensures
        \forall list* l;
            \valid(l) && reachable(root,l) ==>
                \result >= l->element;
    ensures
        \exists list* l;
            \valid(l) && reachable(root,l) && \result == l->element;
*/
int max_list(list* root) {
    int max = root->element;

    while(root->next) {
        root = root->next;

        if (root->element > max) {
            max = root->element;
        }
    }

    return max;
}