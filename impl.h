#ifndef HYBRID_HASH
#define HYBRID_HASH
#define HSIZE 1024

// Define linked-list chaining as a collision solution
typedef struct node_t {
	char *value;
	struct node_t *next;
} node_t;

// Assume a hash-table with a linked-list for collision solving

// Add to hash table
// Provide two arguments, the value and the position of the value in the linked-list
int add(char* key, char* value, unsigned int list_pos);

// Lookup in hash table
// Provide two arguments, the key, and the position of the value in the linked-list
char* get(char *key, unsigned int list_pos);

#endif

