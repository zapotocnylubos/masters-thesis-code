#include <stddef.h>

typedef struct list {
    struct list *next;
    int value;
} List;

/*@
    inductive reachable(List *root, List *node) {
        case root_reachable:
            \forall List *root;
                reachable(root, root);

        case next_reachable:
            \forall List *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    predicate finite(List *root) = reachable(root, \null);
*/

/*@ axiomatic Length {
    logic integer length(List *head);

    axiom length_null:
        length(\null) == 0;

    axiom length_list:
        \forall List *head;
            \valid_read(head)
            && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative:
        \forall List *l;
            finite(l)
              ==> length(l) >= 0;
}
*/

/*
      axiomatic PrependLemma {
        axiom prepend_keeps_finite{L1, L2}:
          \forall List *head, *new_node;
            \valid{L1}(head)
            && \valid{L1}(new_node)
            && finite{L1}(head)
            && \at(new_node->next, L2) == head ==>
              finite{L2}(new_node);
      }
*/

/*
    axiomatic PrependLemma {
        axiom prepend_keeps_finite{L1, L2}:
          \forall List *head, *new_node;
            \valid{L1}(head)
            && \valid{L1}(new_node)
            && finite{L1}(head)
            && !reachable{L1}(head, new_node)
            && \at(new_node->next, L2) == head ==>
              finite{L2}(new_node);
      }
*/

//    requires length(head) < 100;
/*@
    requires \valid(head);
    requires finite(head);

    requires \valid(new_node);
    requires !reachable(head, new_node);

    ensures finite(\result);
*/
List *prepend(List *head, List *new_node) {
    new_node->next = head;
    return new_node;
}
