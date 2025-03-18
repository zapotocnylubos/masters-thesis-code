#include <stdlib.h>

typedef struct _Node {
    int value;

    struct _Node *next;
} Node;

typedef struct {
    Node *head;
} MyList;

/*@
    logic integer length(MyList list) =
        list.head == \null ? 0 : 1 + length((MyList){list.head->next});
*/


/*@
    inductive reachable{L}(Node *root, Node *node) {
        case root_reachable{L}:
            \forall Node *root;
                reachable(root, root);

        case next_reachable{L}:
            \forall Node *root, *node;
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }

    predicate finite(MyList list) = reachable(list.head, \null);
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
    requires finite(list);

    ensures finite(\result);
 */
MyList prepend(
        MyList list,
        int value
) {
    Node *new_node = (Node *) malloc(sizeof(Node));

    new_node->value = value;
    new_node->next = list.head;

    return (MyList){new_node};
}
