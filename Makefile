.PHONY: all clean k test-e2e

all: k

k:
	ocamlbuild k.native

clean:
	ocamlbuild -clean

test-e2e:
	echo "\\\\\\" | ./k.native end_to_end_test.k