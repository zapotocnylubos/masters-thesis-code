#include <stddef.h>
#include <limits.h>

typedef struct list {
    /*@ ghost int id; */
    struct list *next;
    int value;
} List;

/*@ ghost int graph[INT_MAX][INT_MAX]; */

List *prepend(
        List *head,
        List *new_node
) {
    new_node->next = head;
    return new_node;
}