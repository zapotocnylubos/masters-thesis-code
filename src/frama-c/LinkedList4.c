#include <stdlib.h>

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

    predicate finite{L}(List *root) = reachable(root, \null);
*/

/*@ axiomatic Length {
    logic integer length(List *head);

    axiom length_null: length(\null) == 0;

    axiom length_list:
        \forall List *head;
            \valid(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative:
        \forall List *l;
            finite(l) ==> length(l) >= 0;
}
*/

/*@
    requires finite(head);

    terminates \true;
    assigns \nothing;
 */
void list_iteration(List *head) {
    List *p = head;

    /*@
        loop invariant finite(p);
        loop assigns p;
        loop variant length(p);
     */
    while (p != NULL) {
        p = p->next;
    }
}

/*@
    requires finite(head);

    assigns \nothing;

    ensures \result == length(head);
 */
int list_length(List *head) {
    int len = 0;
    List *p = head;

    /*@
        loop invariant finite(p);
        loop invariant len >= 0;
        loop invariant len + length(p) == length(head);

        loop assigns len, p;
        loop variant length(p);
     */
    while (p != NULL) {
        len++;
        p = p->next;
    }

    return len;
}

/* axiomatic PrependLemma {
    axiom prepend_keeps_finite{L1, L2}:
        \forall List *head, *new_node;
            \at(new_node->next, L2) == head &&
            finite{L1}(head) ==>
                finite{L2}(new_node);
}
*/

/*@ requires finite(head);
    requires \valid(new_node);
    requires \separated(new_node, { node | List *node; reachable(head, node) });

    assigns new_node->next;
 */
List *prepend(List *head, List *new_node) {
    //@ assert finite(head);

    //@ assert !reachable(head, new_node);

    new_node->next = NULL;

    //@ assert !reachable(head, new_node);

    //@ assert head == \at(head, Pre);

    //@ assert finite(\at(head, Pre));
    //@ assert finite(head);

    //@ assert finite(new_node);

    //@ assert \false;

    return new_node;
}