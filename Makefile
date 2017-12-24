.PHONY: irpy all

CC       = clang-5.0
MAKE     = make
CFLAGS   = -g -Wno-parentheses -Wno-format -mno-sse -mno-sse2 -nostdlib -O0
LDFLAGS  =
LIBS	 =

SRC		 = $(wildcard *.c)
OBJ		 = o.x86_64/$(SRC:.c=.o)
LLS		 = o.x86_64/$(SRC:.c=.ll)
PYS		 = o.x86_64/$(SRC:.c=.py)

all: o.x86_64 o.x86_64/impl irpy $(PYS)

irpy:
	cd irpy-z3 && $(MAKE) DEBUG=$(DEBUG) compiler/irpy

o.x86_64/%.py: $(LLS)
	./irpy-z3/compiler/irpy $^ > $@
	
o.x86_64:
	mkdir -p o.x86_64

o.x86_64/%.ll: %.c
	$(CC) $(CFLAGS) -S -emit-llvm -o $@ -c $^ $(LIBS)

o.x86_64/%.o: $(LLS)
	$(CC) $(CFLAGS) -o $@ -c $^ $(LIBS)

o.x86_64/impl: $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS)

clean-lib:
	-rm o.x86_64/*.o
	-cd irpy-z3 && $(MAKE) clean

clean: clean-lib
	rm -rf o.x86_64



.SECONDARY: $(LLS)
