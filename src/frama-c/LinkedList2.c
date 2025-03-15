#include <stdlib.h>

struct node {
    int value;
    struct node *next;
};

/*@ inductive linked_list{L}(struct node *head) {
      case empty{L}:
        linked_list(\null);

      case nonempty{L}:
        \forall struct node *n;
          \valid(n) && linked_list(n->next) ==> linked_list(n);
    }
*/


/*@ logic integer length(struct node *head) =
      head == \null ? 0 : 1 + length(head->next);
*/

/*@
    inductive reachable(struct node *root, struct node *node) {
        case root_reachable:
            \forall struct node *root;
                reachable(root, root);

        case next_reachable:
            \forall struct node *root, *node;
                \valid(root) ==>
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    predicate finite(struct node *root) = reachable(root, \null);
*/

/* lemma finite_list_length:
      \forall struct node *l;
        linked_list(l) ==> finite(l);
*/

/* lemma length_null_zero:
      length(\null) == 0;
*/

/* lemma length_nonnull:
      \forall struct node *l;
        linked_list(l) && l != \null ==> length(l) > 0;
*/

/* axiomatic LengthProperties {
      axiom length_null_zero:
        length(\null) == 0;

      axiom length_nonnegative:
        \forall struct node *l;
          linked_list(l) ==> length(l) >= 0;
    }
*/

/*@
    requires linked_list(head);
    requires finite(head);

    assigns \nothing;

    ensures \result == length(head);
*/
int length(struct node *head) {
    int len = 0;
    struct node *p = head;

    /*@
      loop invariant linked_list(p);
      loop invariant len >= 0;
      loop invariant len + length(p) == length(head);
      loop assigns len, p;
      loop variant length(p);
    */
    while (p != NULL) {
        len++;
        p = p->next;
    }

    //@ assert \false;
    return len;
}