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
    inductive linked_list(struct node *head) {
      case empty:
        linked_list(\null);

      case node:
        \forall struct node *n;
          \valid(n) && \valid(n->next) &&
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
                \valid(root) && \valid(root->next) &&
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


/*@
    requires finite_linked_list(head);
    requires \valid(head);
    requires \valid(new_node);

    assigns new_node->next;

    ensures \valid(new_node);
    ensures \valid(new_node->next);
    ensures new_node->next == \old(head);
    ensures \result == new_node;
    ensures finite_linked_list(head);
 */
struct node *prepend(struct node *head, struct node *new_node) {
    //new_node->next = head;
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