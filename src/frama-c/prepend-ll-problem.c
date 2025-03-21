typedef struct list {
    struct list *next;
} List;

/*@
    predicate reachable{L}(List *root, List *node) =
        root == node || (\valid(root) && reachable{L}(root->next, node));

    predicate finite{L}(List *root) = reachable{L}(root, \null);
*/

/*@
    requires finite(head);
    requires \valid(new_node);
    requires \separated(new_node, { node | List *node; reachable(head, node) });

    assigns \nothing;
 */
List *prepend(List *head, List *new_node) {
    //@ assert finite(head);

    List a;

    //@ assert finite(head);

    //@ assert finite(&a);

    //@ assert finite(head);

    return new_node;
}
