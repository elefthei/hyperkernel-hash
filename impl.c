#include<stdio.h>
#include<stdlib.h>
#include<assert.h>

#ifndef HYBRID_HASH_IMPL
#define HYBRID_HASH_IMPL
#define HSIZE 1024

// Define linked-list chaining as a collision solution
typedef struct node_t {
	char *value;
	struct node_t *next;
} node_t;

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
// Provide two arguments, the value and the position of the value in the linked-list
int add(char* value, unsigned int list_pos) {
	node_t *head = &table[hash_str(value)];
	node_t *last = NULL;

	// Bounded loop to confirm to first-order logic
	for (unsigned int i = 0; i < list_pos; ++i) {
		if (head == NULL) { return -1; }
		last = head;
		head = head->next;
	}

	// Allocate head if it doesn't exist
	if (head == NULL){	
		head = (node_t*) malloc(sizeof(node_t));
	}

	// Assign head's father to point to head
	if (last != NULL){
		last->next = head;		
	}

	printf("head is: 0x%x, last is 0x%x\n", head, last);
	head->value = value;
	return 0;
}

void test(char * s, unsigned int list_pos) {
	assert(add(s, list_pos) == 0);
	unsigned long pos = hash_str(s);
	node_t *elem = &table[pos];

	for(int i = 0; i < list_pos; ++i) {
		elem = elem->next;
	}
	assert(elem->value == s);
}

int main() {
	// Test the implementation
	printf("Starting hybrid hash table test...\n");
	test("foo", 0);
	test("foo", 1);
	test("foo", 2);
	test("foo", 3);
	test("bar", 0);
	printf("Done inserting, all pass!\n");


	return 0;
}

#endif

