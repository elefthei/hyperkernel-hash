.PHONY: irpy all

LLVM_CONFIG = llvm-config
CC       = $(shell "$(LLVM_CONFIG)" --bindir)/clang
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
	cd hv6 && $(MAKE) DEBUG=1 irpy/compiler/irpy

o.x86_64/%.py: $(LLS)
	./hv6/irpy/compiler/irpy $^ > $@
	
o.x86_64:
	mkdir -p o.x86_64

o.x86_64/%.ll: %.c
	clang $(CFLAGS) -S -emit-llvm -o $@ -c $^ $(LIBS)

o.x86_64/%.o: $(LLS)
	clang $(CFLAGS) -o $@ -c $^ $(LIBS)

o.x86_64/impl: $(OBJ)
	clang -o $@ $^ $(LDFLAGS)

clean-lib:
	-rm o.x86_64/*.o
	-rm hv6/irpy/compiler/irpy

clean: clean-lib
	rm -rf o.x86_64


.SECONDARY: $(LLS)
