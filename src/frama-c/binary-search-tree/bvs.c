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
                && node->right == \null ==>
                    hasBinarySearchTreeStructure(node);

        case node_hasBinarySearchTreeStructure:
            \forall BinarySearchTree *node, integer value;
                \valid(node)
                && hasBinarySearchTreeStructure(node->left)
                && hasBinarySearchTreeStructure(node->right)
                && node->value == value
                && (node->left == \null
                    || node->left->value < value)
                && (node->right == \null
                    || node->right->value > value)
                ==>
                    hasBinarySearchTreeStructure(node);
    }
*/

/*@
    logic integer height(BinarySearchTree *node) = (node == \null) ? 0 :
        \max(1 + height(node->left), 1 + height(node->right));
 */

/*@
    axiomatic HeightProperties {
      axiom height_null_zero:
        height(\null) == 0;

      axiom height_nonnegative:
        \forall BinarySearchTree *l;
            hasBinarySearchTreeStructure(l) ==>
                0 <= height(l);

      axiom height_strict_higher:
        \forall BinarySearchTree *node;
            hasBinarySearchTreeStructure(node) ==>
               height(node) > height(node->left)
               && height(node) > height(node->right);
    }
*/

/*@
    requires \valid(*root);
    requires hasBinarySearchTreeStructure(*root);

    ensures hasBinarySearchTreeStructure(\at(*root, Post));
*/
bool insert(BinarySearchTree **root, int value) {
    BinarySearchTree *currentRoot = *root;

    // check if the tree is empty
    // if the tree is empty, create a single node
    // and return it
    if (currentRoot == NULL) {
        BinarySearchTree *new_node = (BinarySearchTree *)malloc(sizeof(BinarySearchTree));
        if (new_node == NULL) {
            // Memory allocation failed
            return false;
        }
        // mini-axiomatic hint
        //@ admit \valid(new_node);

        new_node->left = NULL;
        new_node->right = NULL;
        new_node->value = value;
        *root = new_node;
        return true;
    }

    BinarySearchTree *parent = NULL;

    /*@
         loop assigns currentRoot, parent;
         loop variant height(currentRoot);
     */
    while (currentRoot != NULL) {
        parent = currentRoot;
        if (value < currentRoot->value) {
            currentRoot = currentRoot->left;
        } else if (value > currentRoot->value) {
            currentRoot = currentRoot->right;
        } else {
            // Value already exists in the tree
            return false;
        }
    }

    // create a new node
    BinarySearchTree *new_node = (BinarySearchTree *)malloc(sizeof(BinarySearchTree));
    if (new_node == NULL) {
        // Memory allocation failed
        return false;
    }
    //@ admit \valid(new_node);

    new_node->left = NULL;
    new_node->right = NULL;
    new_node->value = value;

    if (value < parent->value) {
        parent->left = new_node;
    } else {
        parent->right = new_node;
    }

    //@ assert \false;
    return true;
}