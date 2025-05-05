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

/* axiomatic Length {
    logic integer height(BinarySearchTree *node);

    axiom height_null: height(\null) == 0;

    axiom height_node:
        \forall BinarySearchTree *node;
            \valid(node)
            && hasBinarySearchTreeStructure(node) ==>
                height(node) == 1 + \max(height(node->left), height(node->right));

    axiom height_nonnegative:
        \forall BinarySearchTree *node;
            hasBinarySearchTreeStructure(node) ==>
                0 <= height(node);
}
*/

/*
    axiomatic HeightProperties {
      axiom height_nonnegative:
        \forall BinarySearchTree *node;
            hasBinarySearchTreeStructure(node) ==>
                0 <= height(node);

      axiom height_strict_higher_than_left:
        \forall BinarySearchTree *node;
            \valid(node)
            && hasBinarySearchTreeStructure(node)
            ==>
                height(node->left) < height(node);

      axiom height_strict_higher_than_right:
        \forall BinarySearchTree *node;
            \valid(node)
            && hasBinarySearchTreeStructure(node)
            ==>
                height(node->right) < height(node);
    }
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

//    BinarySearchTree *parent = NULL;
//    BinarySearchTree *current = root;

//    /*@
//        loop invariant hasBinarySearchTreeStructure(root);
//        loop invariant hasBinarySearchTreeStructure(current);
//        loop invariant hasBinarySearchTreeStructure(parent);
//        loop assigns parent, current;
//        loop variant height(current);
//     */
//    while (current != NULL) {
//        parent = current;
//        if (value < current->value) {
//            current = current->left;
//        } else if (value > current->value) {
//            current = current->right;
//        } else {
//            // Value already exists in the tree
//            //@ assert hasBinarySearchTreeStructure(root);
//            return root;
//        }
//    }

    //@ assert hasBinarySearchTreeStructure(root);
    root->left = NULL;
    //root->right = NULL;

    //@ assert \valid(root);
    //@ assert hasBinarySearchTreeStructure(root->left);
    //@ assert hasBinarySearchTreeStructure(root->right);
    //@ assert (root->left  == \null || root->left->value < root->value);
    //@ assert (root->right == \null || root->right->value > root->value);

    // assert \valid(root);
    // assert root->left  == \null;
    // assert root->right == \null;
    //@ assert hasBinarySearchTreeStructure(root);

    BinarySearchTree *new_node = (BinarySearchTree *) malloc(sizeof(BinarySearchTree));
    if (new_node == NULL) {
        return NULL; // Memory allocation failed
    }
    // admit \valid(new_node);
    // admit !reachable(root, new_node);
    // assert !reachable(root, new_node);


    /*
        admit \separated(new_node, {
            node | BinarySearchTree *node; reachable(root, node)
        });
     */
    /*
        admit \separated(new_node->left, {
            node | BinarySearchTree *node; reachable(root, node)
        });
     */

    // assert \separated(new_node, root);
    // assert hasBinarySearchTreeStructure(root);
    new_node->left = NULL;

    // assert \separated(new_node, root);
    //@ assert hasBinarySearchTreeStructure(root);
    new_node->right = NULL;

    //@ assert hasBinarySearchTreeStructure(new_node);
    // assert hasBinarySearchTreeStructure(root);
    new_node->value = value;

    //@ assert hasBinarySearchTreeStructure(new_node);
    // assert hasBinarySearchTreeStructure(parent);

//    if (value < parent->value) {
//        parent->left = new_node;
//    } else {
//        parent->right = new_node;
//    }

    // assert hasBinarySearchTreeStructure(parent);
    //@ assert hasBinarySearchTreeStructure(root);

    return root;
}


