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
                \valid(root)
                && reachable(root->next, node) ==>
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
            \valid_read(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall List *l;
            finite(l) ==> length(l) >= 0;
}
*/

/*@
    requires \valid(head);
    requires finite(head);
    requires length(head) <= 3;

    requires \valid(new_node);
    requires \separated(new_node, {
        node | List *node; reachable(head, node)
    });

    ensures finite(\result);
*/
List *prepend(List *head, List *new_node) {
    new_node->next = head;
    return new_node;
}
