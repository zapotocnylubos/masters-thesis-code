#include <stdlib.h>

typedef struct list {
    struct list *next;
    int value;
} List;

/*@
    inductive reachable(List *root, List *node) {
        case root_reachable:
            \forall List *root;
                reachable(root, root);

        case next_reachable:
            \forall List *root, *node;
                \valid(root)
                && reachable(root->next, node)
                    ==> reachable(root, node);
  }
*/

/*@
    predicate finite(List *root) =
        reachable(root, \null);
 */

/*
    axiomatic finite_lemma {
        axiom finite_chain:
            \forall List *node, *children;
                \valid(node)
                && finite(node)
                && reachable(node, children)
                ==>
                    finite(children);
    }
 */

/*@
    requires \valid(head);
    requires finite(head);

    ensures finite(\result);
 */
List *prepend(List *head, int value) {
    List *new_node = (List *) malloc(sizeof(List));
    if (!new_node) {
        return NULL; // Handle memory allocation failure
    }
    //@ admit \valid(new_node);
    /*@
        admit \forall List *node;
            reachable(head, node)
                ==> \separated(new_node, node);
     */

    new_node->value = value;
    L0:
    new_node->next = head;
    /*@
        admit \forall List *node;
            reachable{L0}(head, node)
            && finite{L0}(node)
            && \separated(new_node, node)
                ==> finite(node);
    */

    return new_node;
}
