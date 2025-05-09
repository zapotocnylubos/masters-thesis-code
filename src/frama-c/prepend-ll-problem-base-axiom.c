#include <stddef.h>

typedef struct list {
    struct list *next;
    int value;
} List;

/*@
    inductive reachable{L}(List *root, List *node) {
        case root_reachable{L}:
            \forall List *root;
                reachable(root, root);

        case next_reachable{L}:
            \forall List *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    predicate finite{L}(List *root) = reachable{L}(root, \null);
*/

/*@ axiomatic Length {
    logic integer length{L}(List *head);

    axiom length_null{L}:
        length(\null) == 0;

    axiom length_list{L}:
        \forall List *head;
            \valid_read(head)
            && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall List *l;
            finite(l)
              ==> length(l) >= 0;
}
*/

/*
    axiomatic PrependLemma {
        axiom prepend_keeps_finite{L1, L2}:
            \forall List *head, *new_node;
                \at(new_node->next, L2) == head &&
                finite{L1}(head) ==>
                    finite{L2}(new_node);
    }
*/

/*@
    requires \valid(head);
    requires finite(head);
    requires length(head) < 100;

    requires \valid(new_node);
    requires !reachable(head, new_node);

    assigns new_node->next \from head;

    ensures finite(\result);
 */
List *prepend(List *head, List *new_node) {
    new_node->next = head;
    return new_node;
}
