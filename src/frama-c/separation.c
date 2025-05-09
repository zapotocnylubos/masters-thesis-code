#include <stddef.h>

typedef struct list {
    struct list *next;
    int value;
};

/*@
    inductive reachable{L}(struct list *root, struct list *node) {
        case root_reachable{L}:
            \forall struct list *root;
                reachable(root, root);

        case next_reachable{L}:
            \forall struct list *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    predicate finite{L}(struct list *root) = reachable{L}(root, \null);
*/

/*@ axiomatic Length {
    logic integer length{L}(struct list *head);

    axiom length_null{L}:
        length(\null) == 0;

    axiom length_list{L}:
        \forall struct list *head;
            \valid_read(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall struct list *l;
            finite(l) ==> length(l) >= 0;
}
*/

// length(head) < 3, timeout 5 -> ok
// length(head) < 4, timout 5 -> not ok
// length(head) < 4, timout 10 -> ok
// length(head) < 5 -> not ok

/*@
    requires finite(head);
    requires length(head) < 5;

    requires \valid(new_node);
    requires \separated(new_node, { node | struct list *node; reachable(head, node) });

    ensures finite(\result);
 */
struct list *prepend(struct list *head, struct list *new_node) {
    //@ assert \separated(new_node, head);
    new_node->next = new_node;
    //@ assert head == \at(head, Pre);
    //@ assert \separated(new_node, head);
    //@ assert finite(\at(head, Pre));
    //@ assert finite(head);

    //@ assert \false;
    return head;
}
