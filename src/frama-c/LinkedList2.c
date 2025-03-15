#include <stdlib.h>

struct node {
    int value;
    struct node *next;
};

/*@
    logic integer length(struct node *head) = 1 + length(head->next);
*/

/*@
    inductive linked_list(struct node *head) {
      case empty:
        linked_list(\null);

      case node:
        \forall struct node *n;
          linked_list(n->next) ==> linked_list(n);
    }
*/


/*@
    inductive reachable(struct node *root, struct node *node) {
        case root_reachable:
            \forall struct node *root;
                reachable(root, root);

        case next_reachable:
            \forall struct node *root, *node;
                reachable(root->next, node) ==>
                    reachable(root, node);
    }

    predicate finite(struct node *root) = reachable(root, \null);
*/

// TODO: add finite into definition of linked_list?

/* lemma finite_list_length:
      \forall struct node *l;
        finite(l) ==> linked_list(l);
*/

/* lemma length_null_zero:
      length(\null) == 0;
*/

/*@ lemma length_nonnegative:
      \forall struct node *l;
        length(l) >= 0;
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

    //@ assert len <= length(head);
    //@ assert len >= 0;

    return len;
}

void test() {
    struct node *head = malloc(sizeof(struct node));
    struct node *n1 = malloc(sizeof(struct node));
    struct node *n2 = malloc(sizeof(struct node));

    if (head == NULL || n1 == NULL || n2 == NULL) {
        return;
    }

    head->value = 1;
    head->next = n1;
    n1->value = 2;
    n1->next = n2;
    n2->value = 3;
    n2->next = NULL;

    //@ assert linked_list(NULL);
    //@ assert linked_list(n2);
    //@ assert linked_list(n1);
    //@ assert linked_list(head);

    //@ assert finite(head);

    //@ assert length(head) == 3;

    free(n2);
    free(n1);
    free(head);
}