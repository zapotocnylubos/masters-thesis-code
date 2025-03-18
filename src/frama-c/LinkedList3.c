#include <stdlib.h>

struct node {
    int value;
    struct node *next;
};

/*@
    logic integer length(struct node *head) =
      head == \null ? 0 : 1 + length(head->next);
*/

/*@
    inductive linked_list{L}(struct node *head) {
      case empty{L}:
        linked_list(\null);

      case node{L}:
        \forall struct node *n;
          \valid(n) &&
              linked_list(n->next) ==> linked_list(n);
    }
*/


/*@
    inductive reachable{L}(struct node *root, struct node *node) {
        case root_reachable{L}:
            \forall struct node *root;
                reachable(root, root);

        case next_reachable{L}:
            \forall struct node *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }

    predicate finite(struct node *root) = reachable(root, \null);
*/

/*@
    predicate finite_linked_list(struct node *head) =
        linked_list(head) && finite(head);
 */


/*@ lemma length_nonnegative:
      \forall struct node *l;
          \valid(l) && linked_list(l) ==>
              length(l) >= 0;
*/

/*@
    requires finite_linked_list(head);

    assigns \nothing;

    ensures \result == length(head);
*/
int length(struct node *head) {
    int len = 0;
    struct node *p = head;

    /*@
      loop invariant finite_linked_list(p);
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



/*
    requires finite_linked_list(head);
    requires \valid(new_node);
    requires \valid(head);

    assigns new_node->next;

    ensures \valid(head);
    ensures \valid(head->next);
    ensures linked_list(head->next);

    ensures finite_linked_list(new_node);
    ensures new_node->next == \old(head);
    ensures \result == new_node;
    ensures length(new_node) == length(head) + 1;
*/

// not working
// requires \separated(\union(new_node, { q | struct node *q; reachable(head, q) }));
// working
// requires \separated(new_node, head);
// not working
// requires \separated({new_node, head});

/*@
    requires linked_list(head);
    requires finite(head);
    requires length(head) == 3;

    requires \valid(new_node);
    requires \separated(new_node, { node | struct node *node; reachable(head, node) });
    requires \separated(new_node->next, { node | struct node *node; reachable(head, node) });


    assigns new_node->next;
 */
struct node *prepend(struct node *head, struct node *new_node) {
    // assert finite_linked_list(head);

    //@ assert head != new_node;
    //@ assert head != new_node->next;

    //@ assert !reachable(head, new_node);

    //@ assert linked_list(head);
    //@ assert finite(head);

    new_node->next = head;

    // may be needed, that new_node is not in the list??

    //@ assert linked_list(head);
    //@ assert finite(head);

    //@ assert linked_list(new_node);
    //@ assert finite(new_node);

    // assert head != new_node;
    // assert !reachable(head, new_node);
    // assert finite_linked_list(head);

    // ?? aaa -> asserting false is proven :)
    //@ assert \false;
    return new_node;
}


/*@
    requires \valid(p);

    assigns *p;

    ensures \valid(p);
 */
void can_ensure_valid_pointer(char *p) {
    *p = 1;
}

/*@
    requires finite_linked_list(head);

    assigns \nothing;

    ensures finite_linked_list(head);
 */
void can_ensure_not_broken_linked_list(struct node *head) {
}

void null_pointer_is_valid() {
    // only in Z3
    char *p = NULL;
    //@ assert \valid(p);
}


/*@
    requires \valid(n0);
    requires \valid(n1);
    requires \valid(n2);
    requires \valid(n3);
 */
void test_prepend_reachability_speed(
        struct node *n0,
        struct node *n1,
        struct node *n2,
        struct node *n3
) {
    n1->next = n2;
    n2->next = n3;
    n3->next = NULL;

    // assert linked_list(n1);
    // assert finite(n1);
    // separatelly provable, in a predicate, not

    //@ assert linked_list(n1);
    //@ assert finite(n1);

    // together using && not working??
    // assert linked_list(n1) && finite(n1);
    //@ assert finite_linked_list(n1);

    //@ assert reachable(n1, n1);

    //@ assert \valid(n1);
    //@ assert \valid(n1->next);
    //@ assert reachable(n1->next, n2);

    //@ assert reachable(n1, n2);
    //@ assert reachable(n1, n3);
    // assert !reachable(n1, n0);

    n0->next = n1;

    // assert finite_linked_list(n0);
    //@ assert reachable(n0, n0);
    //@ assert reachable(n0, n1);
    //@ assert reachable(n0, n2);
    //@ assert reachable(n0, n3);
}

/*@
    requires \valid(a);
    requires \valid(b);

    requires \separated(a, b);
 */
void test_separation_two(char *a, char *b) {
    //@ assert a != b;
}


// tset == sets of values
// \separated ( location , locations-list )
// location ::= tset
// locations-list ::= location (, location)*

/*@
    requires \valid(a);
    requires \valid(b);

    requires \separated(a, {b});
 */
void test_separation_tset(char *a, char *b) {
    //@ assert a != b;
}

/*@
    requires \valid(a);
    requires \valid(b);
    requires \valid(c);

    requires \separated(a, {b, c});
 */
void test_separation_tset_3(char *a, char *b, char *c) {
    //@ assert a != b;
    //@ assert a != c;

    // this is not defined by this \separated
    // -> its not all-pairs separation clause
    // assert b != c;
}

/*@
    requires linked_list(head);
    requires finite(head);

    requires \valid(new_node);
    requires \separated(new_node, { node | struct node *node; reachable(head, node) });
 */
void test_separation_linked_list(
        struct node *head,
        struct node *new_node
) {
    //@ assert head != new_node;
    //@ assert !reachable(head, new_node);
}