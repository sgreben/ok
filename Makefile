.PHONY: all clean k

all: k

k:
	ocamlbuild k.native

clean:
	ocamlbuild -clean