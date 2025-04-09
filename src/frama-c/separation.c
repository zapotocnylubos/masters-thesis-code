#include <stddef.h>

typedef struct list {
    struct list *next;
    int value;
};

/*@
    inductive reachable{L}(struct list *root, struct list *node) {
        case root_reachable{L}:
            \forall struct list *root;
                reachable(root, root);

        case next_reachable{L}:
            \forall struct list *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    predicate finite{L}(struct list *root) = reachable{L}(root, \null);
*/

/*@
    requires finite(head);

    requires \valid(new_node);
    requires new_node->next == \null;
    requires \separated(new_node, head);

    ensures finite(\result);
 */
struct list *prepend(struct list *head, struct list *new_node) {
    //@ assert \separated(new_node, head);
    new_node->next = new_node;
    //@ assert head == \at(head, Pre);
    //@ assert \separated(new_node, head);
    //@ assert finite(\at(head, Pre));
    //@ assert finite(head);

    //@ assert \false;
    return head;
}
