# What

Here's a WIP implementation of the [K 2.0 language](http://en.wikipedia.org/wiki/K_(programming_language)) in OCaml (4.02.3). Some basic things already work. A whole bunch of things does not (yet).


# Why

fun, practice etc

# How

[Kona wiki](https://github.com/kevinlawler/kona/wiki), [K 2.0 reference](http://web.archive.org/web/20050504070651/http://www.kx.com/technical/documents/kreflite.pdf) and [manual](http://web.archive.org/web/20041022042401/http://www.kx.com/technical/documents/kusrlite.pdf).

# Examples

The [Islands](https://github.com/kevinlawler/kona/wiki/Islands) example from the Kona wiki (Given a binary matrix, identifies "islands" of 1's and sequentially numbers them):

~~~~
  grid:(1 0 0 0 1
        1 1 1 0 0
        0 0 0 0 1
        0 0 0 1 1
        1 0 1 1 1
        0 0 1 0 1)
  col:  {x*(^x)#1+!*/^x}                   / give each 1 a unique id
  ab:   {e:{(0,)'x};+(e(+e x))}            / add a border of zeroes
  rb:   {(1_)'1_ x}                        / remove the border of zeroes
  adj:  {(,x),(-1 1!'\:x),(-1 1)!\:x}      / adjacent cells
  mrg:  {(~~x)*|/adj x}                    / merge neighboring ids
  rc:   {l:0,,/x;g:=l;l[g]:!#g;(^x)#1_ l}  / renumber ids sequentially
  isl:  {rc rb(mrg/col ab x)}              / find islands
  isl grid
(1 0 0 0 2
 1 1 1 0 0
 0 0 0 0 3
 0 0 0 3 3
 4 0 3 3 3
 0 0 3 0 3)
~~~~

Short examples from [Ninety-Nine K problems](https://github.com/kevinlawler/kona/wiki/K-99%3A-Ninety-Nine-K-Problems) and [K idioms](https://github.com/kevinlawler/kona/wiki/Idioms):

~~~~
  compress:{x@&1,~=':x}
  compress "aaaaabbbccdddeee"
"abcde"
  ? "aaaaabbbccdddeee"  /same result using the range operator
"abcde"
  powerset:{x@&:'!2+&#x}
  powerset (`a;1;"test")
(()
 ,"test"
 ,1
 (1;"test")
 ,`a
 (`a;"test")
 (`a;1)
 (`a;1;"test"))
~~~~

Loading a CSV file as a column dictionary:

~~~~
$ cat test.csv
symbols,strings,integers,floats
"abc","def 123",4,5.6
"ghi","ijk 456",7,89.10

$ ./k.native
  table:.{(x;y)}'.("SCIF";,",") 0: "test.csv"
.((`symbols
   `abc `ghi
   )
  (`strings
   ("def 123";"ijk 456")
   )
  (`integers
   4 7
   )
  (`floats
   5.6 89.1
   ))
~~~~

# Current status & notes

Messy, but getting there. *ok* currently implements just enough to "play around with K". Many features essential to a production system are missing.

The core language is covered almost entirely, while the standard library is quite incomplete.

- Entirely missing: FFI, IPC, networking, date/time ops, attributes, UI.
- Functions can be serialized, but neither their source nor their AST is preserved.
- K-tree namespaces are not faithfully implemented yet. In particular, assignments to the current directory do not have the desired effect (a separate copy is created on writes).
As a special-case workaround, the current workspace (entire K-tree) can be saved/loaded to/from disk using the (non-standard) "\load" and "\save" commands:

        $ ./k.native
        ┌──────────┐
        │ok console│
        └──────────┘
          test:123
          \save "my_workspace"
        "my_workspace"
          \\

        $ ./k.native
        ┌──────────┐
        │ok console│
        └──────────┘
          \load "my_workspace"
        "my_workspace"
          test
        123

- Performance is currently terrible. In particular, `Amend[;;]` always creates a deep copy, even if the structure is only being referenced once.
- Compiler warnings: many partial patterns. Mainly due to infeasible cases omitted for brevity.