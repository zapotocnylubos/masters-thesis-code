#include <stdlib.h>
#include <stdbool.h>

typedef struct binary_search_tree {
    struct binary_search_tree *left;
    struct binary_search_tree *right;
    int value;
} BinarySearchTree;

/*@
    inductive hasBinarySearchTreeStructure(BinarySearchTree *node) {
        case null_hasBinarySearchTreeStructure:
            hasBinarySearchTreeStructure(\null);

        case leaf_hasBinarySearchTreeStructure:
            \forall BinarySearchTree *node;
                \valid(node)
                && node->left == \null
                && node->right == \null
                ==>
                    hasBinarySearchTreeStructure(node);

        case node_hasBinarySearchTreeStructure:
            \forall BinarySearchTree *node, integer value;
                \valid(node)
                && hasBinarySearchTreeStructure(node->left)
                && hasBinarySearchTreeStructure(node->right)
                && node->value  == value
                && (node->left  == \null || node->left->value < value)
                && (node->right == \null || node->right->value > value)
                ==>
                    hasBinarySearchTreeStructure(node);
    }
*/

/*
    logic set<BinarySearchTree*> footprint(BinarySearchTree *root) =
        root == \null ? \empty :
            \union({ root }, footprint(root->left), footprint(root->right));

    logic set<integer> content(BinarySearchTree *root) =
        root == \null ? \empty :
            \union({ root->value }, content(root->left), content(root->right));
 */

/*@
    axiomatic BinaryTreeFootprint {
        logic set<BinarySearchTree*> footprint(BinarySearchTree *root);

        axiom footprint_null: footprint(\null) == \empty;

        axiom footprint_node:
            \forall BinarySearchTree *node;
                \valid(node)
                ==>
                    footprint(node) == \union({ node }, footprint(node->left), footprint(node->right));
    }
 */

/*@
    predicate reachable(BinarySearchTree *root, BinarySearchTree *node) =
        root == node
        || (
            \valid(root)
            && (
                reachable(root->left, node)
                || reachable(root->right, node)
            )
        );
 */

/*@
    predicate acyclic(BinarySearchTree *root) =
        root == \null
        || (
            \valid(root)
            && acyclic(root->left)
            && acyclic(root->right)
            && !reachable(root->left, root)
            && !reachable(root->right, root)
        );
 */

/*@
    predicate acyclic_mem(BinarySearchTree *root) =
        root == \null
        || (
            \valid(root)
            && acyclic_mem(root->left)
            && acyclic_mem(root->right)
            && \inter(footprint(root->left), footprint(root->right)) == \empty
            && \inter(footprint(root->left), footprint(root)) == \empty
            && \inter(footprint(root->right), footprint(root)) == \empty
        );
 */

/*@
    logic integer height(BinarySearchTree *node) = (node == \null) ? 0 :
        \max(1 + height(node->left), 1 + height(node->right));
 */

/*@
    requires hasBinarySearchTreeStructure(root);
    requires acyclic(root);
    requires acyclic_mem(root);

    ensures hasBinarySearchTreeStructure(\result);
    ensures acyclic(\result);
*/
BinarySearchTree *insert(BinarySearchTree *root, int value) {
    if (root == NULL) {
        BinarySearchTree *new_node = (BinarySearchTree *) malloc(sizeof(BinarySearchTree));
        if (new_node == NULL) {
            return NULL; // Memory allocation failed
        }
        //@ admit \valid(new_node);
        //@ assert !reachable(root, new_node);

        new_node->left = NULL;
        new_node->right = NULL;
        new_node->value = value;

        //@ assert hasBinarySearchTreeStructure(new_node);
        return new_node;
    }

    BinarySearchTree *current = root;
    BinarySearchTree *parent = root;

    /*@
        loop invariant hasBinarySearchTreeStructure(root);
        loop invariant hasBinarySearchTreeStructure(current);
        loop invariant hasBinarySearchTreeStructure(parent);
        loop assigns parent, current;
        loop variant height(current);
     */
    while (current != NULL) {
        parent = current;
        if (value < current->value) {
            current = current->left;
        } else if (value > current->value) {
            current = current->right;
        } else {
            // Value already exists in the tree
            //@ assert hasBinarySearchTreeStructure(root);
            return root;
        }
    }

    BinarySearchTree *new_node = (BinarySearchTree *) malloc(sizeof(BinarySearchTree));
    if (new_node == NULL) {
        return NULL; // Memory allocation failed
    }
    //@ admit \valid(new_node);
    /*@
        admit \separated(new_node, {
            node | BinarySearchTree *node; reachable(root, node)
        });
     */

    new_node->left = NULL;
    new_node->right = NULL;
    new_node->value = value;

    if (value < parent->value) {
        parent->left = new_node;
    } else {
        parent->right = new_node;
    }

    // assert hasBinarySearchTreeStructure(parent);
    //@ assert hasBinarySearchTreeStructure(root);

    return root;
}


