.PHONY: irpy all

CC       = clang
MAKE     = make
CFLAGS   = -Wno-parentheses -Wno-format -mno-sse -mno-sse2 -nostdlib -O0
LDFLAGS  =
LIBS	 =

SRC		 = $(wildcard *.c)
OBJ		 = o.x86_64/$(SRC:.c=.o)
LLS		 = o.x86_64/$(SRC:.c=.ll)
PYS		 = o.x86_64/pyimpl/$(SRC:.c=.py)

all: o.x86_64 o.x86_64/impl irpy $(PYS)

irpy:
	cd irpy && \
		$(MAKE) DEBUG=$(DEBUG) compiler/irpy && \
		cp -r libirpy ../o.x86_64/ && \
		cp -r ../spec/* ../o.x86_64/

o.x86_64/pyimpl/%.py: $(LLS)
	./irpy/compiler/irpy $^ > $@

o.x86_64:
	mkdir -p $@/pyimpl
	touch $@/pyimpl/__init__.py

o.x86_64/%.ll: %.c
	$(CC) $(CFLAGS) -S -emit-llvm -o $@ -c $^ $(LIBS)

o.x86_64/%.o: $(LLS)
	$(CC) $(CFLAGS) -o $@ -c $^ $(LIBS)

o.x86_64/impl: $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS)

verify: all
	python o.x86_64/main.py

clean-lib:
	-rm o.x86_64/*.o
	-cd irpy && $(MAKE) clean

clean: clean-lib
	rm -rf o.x86_64


.SECONDARY: $(LLS)
