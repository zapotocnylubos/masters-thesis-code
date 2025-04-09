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
    requires !reachable(head, new_node);
    requires \separated(
        {new_node, &new_node->next},
        { node | struct list *node; reachable(head, node) },
        { &node->next | struct list *node; reachable(head, node) }
    );

    ensures finite(\result);
 */
struct list *prepend(struct list *head, struct list *new_node) {
    new_node->next = new_node;
    //@ assert finite(\at(head, Pre));
    //@ assert finite(head);

    //@ assert \false;
    return head;
}
