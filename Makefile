.PHONY: all

SRC = impl.c
ELF = impl

all: $(ELF)

$(ELF): $(SRC)
	clang -Wno-parentheses -Wno-format $(SRC) -o $(ELF)

clean: 
	rm impl
