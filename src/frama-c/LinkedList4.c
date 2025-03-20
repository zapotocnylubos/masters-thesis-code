#include <stdlib.h>

typedef struct list {
    int value;
    struct list *next;
} List;

/*@
    logic set<List*> footprint{L}(List *root) =
        root == \null ?
            \union({ root }, footprint{L}(root->next)) :
            { (List *)\null };
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

//    requires \valid(new_node);
//    requires \separated(new_node, head);
//    requires \separated(new_node, { node | List *node; reachable(head, node) });
//    assigns new_node->next \from head;
//    assigns \result \from head, new_node;
//    ensures finite(\result);



/*@
    requires finite(head);
    assigns \nothing;
 */
List prepend(List *head) {
    List a;
    a.value = 0;
    a.next = head;

    //@ assert finite(&a);

    return a;
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
//    requires length(head) == 1;
//    requires head->next == \null;
// */
//void test_list_footprint(
//        List *head
//) {
//    // assert \empty == \empty;
//    // assert footprint(\null) == footprint(\null);
//    // assert footprint(\null) == \empty;
//    // assert footprint(head) == footprint(head);
//    // assert \null \in { \null };
//    // assert \null \in \empty;
//    // assert \null \in footprint(\null);
//
//    // assert \null \in footprint(head);
//
//    // can not have a set of void pointers. Ignoring code annotation
//    // assert \null \in { head, head->next, \null};
//
//    // -> true
//    // assert \null \in { head, head->next, (List *)\null};
//
//    // -> unknown
//    // assert \null \in { head, (List *)head->next};
//
//    // -> true, unknown
//    // assert head->next == \null;
//    // assert \null \in { (List *)head, (List *)head->next };
//
//
//    /*?? assert \null ∈ {(void *)head, (List *)\null}; */
//    // assert \null \in { (List *)head, (List *)\null };
//
//    // assert \null ∈ {(List *)head, (List *)\null};
//
//    // -> unknown
//    // assert \subset(\null, footprint(\null));
//
//    // -> true
//    // assert \subset(\null, { \null });
//
//    //@ assert \subset(\null, footprint(\null));
//}
