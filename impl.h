#ifndef HYBRID_HASH
#define HYBRID_HASH
#include<stdlib.h>

#define HSIZE 1024
#define INITSIZE 16

// Implement collision chaining with an array-list
typedef struct array_t {
	unsigned int size;
	char **val;
} array_t;

array_t makeArray() {
	array_t retval;
	retval.size = INITSIZE;
	retval.val = (char**) malloc(INITSIZE * sizeof(char*));
	return retval;	
}

void doubleArray(array_t *ar) {
	char **buffer = (char**) malloc(INITSIZE * 2 * sizeof(char*));
	for (int i = 0; i < ar->size; ++i) {
		buffer[i] = ar->val[i];
	}
	ar->size = ar->size * 2;
	free(ar->val);
	ar->val = buffer;
}

// Assume a hash-table with an array-list for collision solving
// Add to hash table
// Provide two arguments, the value and the position of the value in the linked-list
int add(array_t *table, char* key, char* value, unsigned int pos);

// Lookup in hash table
// Provide two arguments, the key, and the position of the value in the linked-list
char* get(array_t *table, char *key, unsigned int pos);

#endif

