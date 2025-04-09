#include <stddef.h>
//#include <stdlib.h>
//#include <stdio.h>

typedef struct list {
    struct list *next;
    int value;
} List;

/*
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
            \valid_read(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall List *l;
            finite(l) ==> length(l) >= 0;
}
*/

///*@
//    requires \valid_read(head);
//    requires finite(head);
//    requires length(head) == 1;
//
//    assigns \nothing;
//*/
//void test_reachable(List *head) {
//    //@ assert reachable(head, head);
//    //@ assert reachable(head, head->next);
//    // assert !reachable(head->next, head);
//    //@ assert head->next == \null;
//}

//    requires \separated(new_node, { node | List *node; reachable(head, node) });
//    requires \separated(&new_node->next, { node | List *node; reachable(head, node) });

/*@
    requires finite(*head);

    requires finite(new_node);
    requires length(new_node) == 1;
    requires !reachable(*head, new_node);
    requires !reachable(new_node, *head);

    assigns *head;

    ensures finite(*head);
 */
void prepend(List **head, List *new_node) {
    //new_node->next = *head;
    new_node->next = NULL;
    *head = new_node;
}

///*@
//    requires \valid_read(head);
//    requires finite(head);
//
//    requires \valid_read(new_node);
//    requires \separated(new_node, { node | List *node; reachable(head, node) });
//    requires \separated(&new_node->next, { node | List *node; reachable(head, node) });
//
//    assigns { node->next | List *node; reachable(head, node) };
//
//    ensures finite(\result);
// */
//List *append(List *head, List *new_node) {
//    if (!head) {
//        head = new_node;
//        return head;
//    }
//
//    List *current = head;
//    while (current->next) {
//        current = current->next;
//    }
//
//    current->next = new_node;
//
//    return head;
//}

void test_hardcoded_prepend_pointers() {
    List a, b, c;
    a.value = 1;
    b.value = 2;
    c.value = 3;

    List *ap = &a, *bp = &b, *cp = &c;
    ap->next = bp;
    bp->next = cp;
    cp->next = NULL;

    List *head = ap;

    //@ assert finite(head);
    //@ assert length(head) == 3;

    List d;
    d.value = 4;
    List *dp = &d;

    dp->next = ap;
    head = dp;

    //@ assert finite(head);
    //@ assert length(head) == 4;
}

//int main() {
//    List *head = NULL;
//    //@ assert finite(head);
//
//    List *new_node = (List *) malloc(sizeof(List));
//    if (!new_node) {
//        return 1;
//    }
//    new_node->value = 10;
//
//    head = prepend(head, new_node);
//
//    return 0;
//}

// TODO: jak modelovat LL/Strom/Graf jednoduse? 2D pole - pripadne N*N 1D pole reprezentujici 2D pole
// TODO: to by pak mohlo byt v ghost promenne a delat se dukazy na tom?