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

      axiom height_strict_higher_than_left:
        \forall BinarySearchTree *node;
            \valid(node)
            && hasBinarySearchTreeStructure(node) ==>
               height(node) > height(node->left);

      axiom height_strict_higher_than_right:
        \forall BinarySearchTree *node;
            \valid(node)
            && hasBinarySearchTreeStructure(node) ==>
               height(node) > height(node->right);
    }
*/

/*@
    requires hasBinarySearchTreeStructure(root);
    ensures hasBinarySearchTreeStructure(\result);
*/
BinarySearchTree *insert(BinarySearchTree *root, int value) {
    BinarySearchTree *result = root;

    // check if the tree is empty
    // if the tree is empty, create a single node
    // and return it
    if (root == NULL) {
        BinarySearchTree *result = (BinarySearchTree *)malloc(sizeof(BinarySearchTree));
        if (result != NULL) {
            result->left = NULL;
            result->right = NULL;
            result->value = value;
        }
    } else {
        // Otherwise, recur down the tree
        BinarySearchTree *currentRoot = root;
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
                return root;
            }
        }

        BinarySearchTree *new_node = (BinarySearchTree *)malloc(sizeof(BinarySearchTree));
        if (new_node == NULL) {
            return NULL; // Memory allocation failed
        }
        // mini-axiomatic hint for provers
        // admit \valid(new_node);

        new_node->left = NULL;
        new_node->right = NULL;
        new_node->value = value;

        if (value < parent->value) {
            parent->left = new_node;
        } else {
            parent->right = new_node;
        }
    }

    return result;
}