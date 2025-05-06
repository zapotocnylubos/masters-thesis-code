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
                \valid(root) &&
                    reachable(root->next, node) ==>
                        reachable(root, node);
    }
*/

/*@
    inductive finite(List *root) {
        case null_finite:
            finite(\null);

        case node_finite:
            \forall List *node;
                \valid(node)
                && finite(node->next)
                ==>
                    finite(node);
    }
 */

/*
    predicate finite(List *root) = reachable(root, \null);
*/

/*@
    inductive SameLists(List *root1, List *root2) {
        case null_same:
            \forall List *root1, *root2;
                root1 == \null
                && root2 == \null
                ==>
                    SameLists(root1, root2);

        case node_same:
            \forall List *root1, *root2;
                \valid(root1)
                && \valid(root2)
                && root1 == root2
                && SameLists(root1->next, root2->next)
                ==>
                    SameLists(root1, root2);
    }
 */

/*@
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
    axiomatic Length {
        logic integer length(List *head);

        axiom length_null:
            length(\null) == 0;

        axiom length_list:
            \forall List *head;
                \valid_read(head)
                && finite(head) ==>
                    length(head) == 1 + length(head->next);

        axiom length_nonnegative:
            \forall List *l;
                finite(l)
                  ==> length(l) >= 0;
    }
*/

/*@
    logic set<List*> footprint(List *head) = \union(head, footprint(head->next));
 */

/*
    axiomatic LinkedListMemoryFootprint {
        logic set<List*> footprint(List *root);

        axiom footprint_null: footprint(\null) == \empty;

        axiom footprint_node:
            \forall List *node;
                \valid(node)
                && finite(node)
                ==>
                    (footprint(node) == \union({ node }, footprint(node->next)));
    }
*/


/*@
    axiomatic separated_lemma {
        lemma a:
            \forall int *a, *b, c;
                \valid(a) && \valid(b)
                && \separated(a, b)
                && *a == c
                && *b != c
                  ==> a != b;
    }
 */

/*@
    requires \valid(head);
    requires finite(head);
    requires length(head) < 100;

    ensures finite(\result);
 */
List *prepend(List *head, int value) {
    List *new_node = (List *)malloc(sizeof(List));
    if (!new_node) {
        return NULL; // Handle memory allocation failure
    }
    //@ admit \valid(new_node);

    //@ admit \forall List *node; reachable(head, node) ==> \separated(new_node, node);
    //@ admit \forall List *node; reachable(head, node) ==> new_node != node;
    // admit \forall List *node; reachable(head, node) ==> new_node->next != node;

    // admit !(new_node \in footprint(head));
    // admit \subset(\inter({new_node}, footprint(head)), \inter({new_node}, footprint(head)));
    // admit \separated(new_node, footprint(head));
    // admit new_node != head;

    // assert finite(head);
//    new_node->value = value;
    // assert finite(head);
    //new_node->next = NULL;
    // admit \separated(new_node, footprint(head));
    // assert finite(new_node);
    // assert finite(head);

    // assert finite(head);
    // assert \forall List *node; reachable(head, node) ==> finite(node);

    //@ assert head != \null ==> footprint(head) == \union({ head }, footprint(head->next));
    // assert SameLists(head, head);

    L0:
    new_node->next = head;

    // admit head != \null ==> footprint{L0}(head) == \union({ head }, footprint(head->next));
    // assert head != \null ==> footprint(head) == \union({ head }, footprint(head->next));

    // assert head == \at(head, L0);
    // admit \forall List *node; reachable{L0}(head, node) <==> reachable(head, node);

    // assert SameLists(head, \at(head, L0));


    // assert \forall List *node; reachable(head, node) ==> node == \at(node, L0);
    // assert finite(head);

    // ---- this is the one
    // admit \forall List *node; reachable{L0}(head, node) ==> finite(node);
    // admit \forall List *node; reachable(head, node) ==> finite(node);
    //@ admit \forall List *node; reachable{L0}(head, node) && finite{L0}(node) ==> finite(node);
    // ---- this is the one

    // assert \forall List *node; reachable(head, node) ==> finite(node);

    // admit \forall List *node; reachable(head, node) ==> \separated(new_node, node);
    // admit \forall List *node; reachable(head, node) ==> new_node != node;

    // admit \forall List *node; reachable(head, node) ==> \separated(new_node, node);
    // admit \forall List *node; reachable{L0}(head, node) ==> \separated(new_node->next, node);
    // admit \forall List *node; reachable(head, node) ==> new_node != node;
    // admit \forall List *node; reachable(head->next, node) ==> new_node->next != node;

    // admit !(new_node \in footprint(head));
    // admit \subset(\inter({new_node}, footprint(head)), \inter({new_node}, footprint(head)));
    // admit \separated(new_node, footprint(head));
    // admit new_node != head;
    // admit finite(head->next);

    // assert finite{L0}(head) && (\forall List *node; reachable(head, node) ==> \separated(new_node, node)) ==> finite(head);
    //@ assert finite(head);
    // assert finite(new_node);

    //@ assert \false;

    return new_node;
}
