#include<stdio.h>
#include<assert.h>
#include "impl.h"

// Hash function djb2
// http://www.cse.yorku.ca/~oz/hash.html
unsigned long hash_str(const char *str)
{
	unsigned long hash = 5381;
	int c;
	while (c = *str++)
		hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
	return hash % HSIZE;
}

// Assume a hash-table with a array-list for collision solving
// Provide three arguments, the key, the value and the position of the value in the array-list
int add(array_t *table, char* key, char* value, unsigned int pos) {
	array_t *row = &table[hash_str(key)];
	if (pos >= row->size) {
		doubleArray(row);
	}

	if (pos >= row->size) {
		printf("ERROR: pos to write outside bounds even after doubling the array\n");
		return -1;
	}
	row->val[pos] = value;
	return 0;
}

// Assume a hash-table with a array-list for collision solving
// Provide two arguments, the key, and the position of the value in the array-list
char* get(array_t *table, char *key, unsigned int pos) {
	array_t *row = &table[hash_str(key)];
	if (pos >= row->size) {
		printf("ERROR: pos outside bounds when fetching from the array\n");
		return NULL;
	}
	return row->val[pos];
}

void init(array_t *table) {
	for (int i = 0; i < HSIZE; ++i) {
		table[i] = makeArray();
	}

}

void test(array_t *table, char *key, char * s, unsigned int pos) {
	// add phase
	assert(add(table, key, s, pos) == 0);
	// Get phase
	char *value = get(table, key, pos);
	// Test phase
	assert(value == s);
}

int main() {

	// Define and init the hash table
	array_t table[HSIZE];
	init(table);

	// Test the implementation
	printf("Starting hybrid hash table test...\n");
	test(table, "foo", "One string", 0);
	test(table, "foo", "Another string", 1);
	test(table, "foo", "Yet one more", 2);
	test(table, "foo", "Maybe the last?", 3);
	test(table, "bar", "Ah another key!", 0);
	printf("Done inserting, all pass!\n");

	return 0;
}

