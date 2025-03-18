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

/*
    lemma prepend_lemma:
        \forall struct node *head, *new_node;
            linked_list(head) &&
            !reachable(head, new_node) &&
            new_node->next == head ==>
                linked_list(new_node);
 */

/*@
    requires linked_list(head);

    requires \valid(new_node);
    requires \separated(new_node, { node | struct node *node; reachable(head, node) });

    assigns new_node->next;
 */
struct node *prepend(
        struct node *const head,
        struct node *new_node
) {
    //@ assert linked_list(head);

    new_node->next = head;

    //@ assert linked_list(head);
    //@ assert linked_list(new_node);

    //@ assert \false;

    return new_node;
}

void test_contradiction() {
    //@ assert \false;
}