#include<stdio.h>
#include<stdlib.h>
#include<assert.h>
#include "impl.h"

// Define global table
node_t table[HSIZE];

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

// Assume a hash-table with a linked-list for collision solving
// Provide three arguments, the key, the value and the position of the value in the linked-list
int add(char* key, char* value, unsigned int list_pos) {
	node_t *head = &table[hash_str(key)];
	node_t *last = NULL;

	// Bounded loop to confirm to first-order logic
	for (unsigned int i = 0; i < list_pos; ++i) {
		if (head == NULL) { return -1; }
		last = head;
		head = head->next;
	}

	// Allocate head if it doesn't exist
	if (head == NULL){	
		head = (node_t*) calloc(1, sizeof(node_t));
	}

	// Assign head's father to point to head
	if (last != NULL){
		last->next = head;		
	}

	printf("head is: 0x%x, last is 0x%x\n", head, last);
	head->value = value;
	return 0;
}

// Assume a hash-table with a linked-list for collision solving
// Provide two arguments, the key, and the position of the value in the linked-list
char* get(char *key, unsigned int list_pos) {
	node_t *head = &table[hash_str(key)];
	for (unsigned int i = 0; i < list_pos; ++i) {
		if (head == NULL) { return NULL; }
		head = head->next;
	}
	return head->value;
}

void test(char *key, char * s, unsigned int list_pos) {
	// add phase
	assert(add(key, s, list_pos) == 0);
	// Get phase
	char *value = get(key, list_pos);
	// Test phase
	assert(value == s);
}

int main() {
	// Test the implementation
	printf("Starting hybrid hash table test...\n");
	test("foo", "One string", 0);
	test("foo", "Another string", 1);
	test("foo", "Yet one more", 2);
	test("foo", "Maybe the last?", 3);
	test("bar", "Ah another key!", 0);
	printf("Done inserting, all pass!\n");

	return 0;
}

