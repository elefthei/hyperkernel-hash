.PHONY: all

LIBS  = 
CFLAGS = -Wno-parentheses -Wno-format
LDFLAGS = 

SRC=$(wildcard *.c)
OBJ=$(SRC:.c=.o)

all: impl

%.o: %.c
	gcc -o $@ -c $^ $(CFLAGS) $(LIBS)
	
impl: $(OBJ)
	gcc -o $@ $^ $(LDFLAGS)

clean-lib:
	-rm *.o

clean: clean-lib
	rm impl
