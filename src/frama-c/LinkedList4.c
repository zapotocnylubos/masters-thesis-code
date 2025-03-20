#include <stdlib.h>

typedef struct list {
    int value;
    struct list *next;
} List;

/*@
    logic set<List*> footprint{L}(List *root) =
        \union({ root }, (root == \null) ? \empty : footprint{L}(root->next));
 */

/*@
    predicate reachable{L}(List *root, List *node) =
        root == node || (\valid(root) && reachable{L}(root->next, node));

    predicate finite{L}(List *root) = reachable{L}(root, \null);
 */

/*
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
    logic integer length{L}(List *head);

    axiom length_null{L}: length(\null) == 0;

    axiom length_list{L}:
        \forall List *head;
            \valid(head) && finite(head) ==>
                length(head) == 1 + length(head->next);

    axiom length_nonnegative{L}:
        \forall List *l;
            finite(l) ==> length(l) >= 0;
}
*/

/*
    predicate is_same_list{L1, L2}(List *head) =
        \forall List *node;
            reachable{L1}(head, node) <==> reachable{L2}(head, node);
 */

///*@
//    requires finite(head);
//
//    terminates \true;
//    assigns \nothing;
// */
//void list_iteration(List *head) {
//    List *p = head;
//
//    /*@
//        loop invariant finite(p);
//        loop assigns p;
//        loop variant length(p);
//     */
//    while (p != NULL) {
//        p = p->next;
//    }
//}
//
///*@
//    requires finite(head);
//
//    assigns \nothing;
//
//    ensures \result == length(head);
// */
//int list_length(List *head) {
//    int len = 0;
//    List *p = head;
//
//    /*@
//        loop invariant finite(p);
//        loop invariant len >= 0;
//        loop invariant len + length(p) == length(head);
//
//        loop assigns len, p;
//        loop variant length(p);
//     */
//    while (p != NULL) {
//        len++;
//        p = p->next;
//    }
//
//    return len;
//}

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
    requires \separated(new_node, head);
    requires \separated(new_node, { node | List *node; reachable(head, node) });

    assigns new_node->next \from head;
    assigns \result \from head, new_node;

    ensures finite(\result);
 */
List *prepend(List *head, List *new_node) {
    //@ assert finite(head);

    //@ assert !reachable(head, new_node);

    //@ assert \separated(new_node, { node | List *node; reachable(head, node) });

    //@ assert reachable(head, \null);

    //@ assert \forall List* node; reachable(head, node) ==> node != new_node;

    // assert \subset(footprint{Here}(head), footprint{Pre}(head));

    // assert footprint{Here}(new_node) == footprint{Pre}(new_node);

    new_node->next = head;

    // assert footprint{Here}(new_node) == footprint{Pre}(new_node);


    //@ assert head == \at(head, Pre);
    //@ assert head != \null ==> head->next == \at(head->next, Pre);
    //@ assert head != \null && head->next != \null ==> head->next->next == \at(head->next->next, Pre);
    //@ assert \separated(new_node, head);

    //@ assert head != \null ==> \separated(new_node, head->next);
    //@ assert head != \null && head->next != \null ==> \separated(new_node, head->next->next);

    //@ assert head != \null ==> reachable(new_node, head);
    //@ assert head != \null && head->next != \null ==> reachable(new_node, head->next);

    //@ assert finite(head);

    //@ assert head != \null ==> \separated(new_node, { node | List *node; reachable(head->next, node) });

    // assert is_same_list{Pre, Here}(head);

    // assert \forall List* node; reachable{Pre}(head, node) ==> reachable{Pre}(head, node);
    // assert \forall List* node; reachable{Pre}(head, node) ==> reachable{Here}(head, node);

    // assert \separated(new_node, { node | List *node; reachable(\at(head->next, Pre), node) });


    // assert length{Pre}(head) == length(head);
    // assert length(new_node) == 1 + length(head);

    // assert \forall List *node; reachable{Pre}(head, node) ==> reachable(head, node);

    // assert head != \null ==> \separated(new_node, head->next);

    // assert new_node == \at(new_node, Pre);

    // assert \separated(new_node, { node | List *node; reachable(\at(head, Pre), node) });

    // assert !reachable(head, new_node);


    // assert finite(\at(head, Pre));
    // assert finite(head);

    //@ assert finite(new_node);

    //@ assert \false;

    return new_node;
}

//int main() {
//    List *head = NULL;
//    //@ assert finite(head);
//
//    List *new_node = malloc(sizeof(List));
//    if (!new_node) {
//        return 1;
//    }
//
//    List * new_head = prepend(head, new_node);
//    int len = list_length(new_head);
//
//    printf("Length: %d\n", len);
//
//    free(new_node);
//    free(head);
//
//    return 0;
//}


///*@
//    requires finite(head);
//    requires length(head) == 0;
// */
//void test_list_footprint(
//        List *head
//) {
//    //@ assert \empty == \empty;
//    //@ assert footprint(\null) == footprint(\null);
//    //@ assert footprint(\null) == \empty;
//    //@ assert footprint(head) == footprint(head);
//    //@ assert \null \in { \null };
//    //@ assert \null \in \empty;
//    //@ assert \null \in footprint(\null);
//}
