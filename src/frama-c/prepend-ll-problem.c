#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>

typedef struct list {
    int value;
    struct list *next;
} List;

/*@
    inductive linked{L}(List *root) {
        case root_linked{L}:
            \forall List *root;
                linked(root);

        case next_linked{L}:
            \forall List *root;
                \valid(root) &&
                    linked(root->next) ==>
                        linked(root);
    }
*/

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
            \valid(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall List *l;
            finite(l) ==> length(l) >= 0;
}
*/

/*@
    requires \valid(head);
    requires finite(head);
    requires length(head) == 1;

    assigns \nothing;
*/
void test_reachable(List *head) {
    //@ assert reachable(head, head);
    //@ assert reachable(head, head->next);
    // assert !reachable(head->next, head);
    //@ assert head->next == \null;
}


/*@
    requires \valid(head);
    requires finite(head);

    requires \valid(new_node);
    requires \separated(new_node, { node | List *node; reachable(head, node) });

    assigns \nothing;
 */
List prepend(List *head, List *new_node) {
    //@ assert finite(head);
    List new_head;
    new_head.value = new_node->value;
    new_head.next = head;

    //@ assert reachable(\at(head, Pre), \null);

    //@ assert finite(head);
    //@ assert finite(&new_head);
    return new_head;
}

int main() {
    List *head;
    //@ assert finite(head);

    List *new_node = (List *) malloc(sizeof(List));
    if (!new_node) {
        return 1;
    }
    new_node->value = 10;

    List new_head = prepend(head, new_node);

    return 0;
}