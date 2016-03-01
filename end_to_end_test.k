\l ansicolor
test:{`0:(:[y;c.apply[c.green;"OK"];c.apply[c.red;"FAILED"]],"\t",x,"\n")}
test_eq:{test[x;y[]~z]}
tests:{`0:"\n\t",x,"\n";(test_eq .)'y}

/ (* Self-test *)
tests["should";(("fail";{1 0};0 1);
                ("succeed";{0 1};0 1))]

/ (* Scope *)
\d scope_test
f:{. `abc}
g:{f[]}
abc:123
\d .k
abc:_n
tests["scope/sym";(("test.f[]";{scope_test.f[]};_n)
                   ("test.g[]";{scope_test.g[]};_n))]
abc:456
tests["scope/sym[abc=456]";(("test.f[]";{scope_test.f[]};456)
                            ("test.g[]";{scope_test.g[]};456))]
f:{`def}
tests["scope/sym[abc=456;f:{`def}]";(("test.f[]";{scope_test.f[]};456)
                                     ("test.g[]";{scope_test.g[]};456))]
abc:_n
tests["scope/sym[abc=_n]";(("test.f[]";{scope_test.f[]};_n)
                           ("test.g[]";{scope_test.g[]};_n))]
tests["scope/fun";,("{abc:123;{abc,(abc:10),{abc*x}[2],{abc:1}[],abc}[]}"
                    {abc:123;{abc,(abc:10),{abc*x}[2],{abc:1}[],abc}[]}
                    10 10 246 1 123)]
scope_test.f:{"TEST_STRING"}
tests["scope/fun-replace";(("test.f[]";{scope_test.f[]};"TEST_STRING")
                           ("test.g[]";{scope_test.g[]};"TEST_STRING"))]

/ (* Islands *)
\d islands
grid:(1 0 0 0 1
      1 1 1 0 0
      0 0 0 0 1
      0 0 0 1 1
      1 0 1 1 1
      0 0 1 0 1)
col:  {x*(^x)#1+!*/^x}
ab:   {e:{(0,)'x};+(e(+e x))}
rb:   {(1_)'1_ x}
adj:  {(,x),(-1 1!'\:x),(-1 1)!\:x}
mrg:  {(~~x)*|/adj x}
rc:   {.[x;(;);(?0,,/x)?]}
isl:  {rc rb(mrg/col ab x)}
\d .k
tests["islands";,("1  ";{islands.isl islands.grid};(1 0 0 0 2
                                                    1 1 1 0 0
                                                    0 0 0 0 3
                                                    0 0 0 3 3
                                                    4 0 3 3 3
                                                    0 0 3 0 3))]
\d islands
rc: {l:0,,/x;g:=l;l[g]:!#g;(^x)#1_ l}  / original version from Kona wiki
\d .k
tests["islands";,("2  ";{islands.isl islands.grid};(1 0 0 0 2
                                                    1 1 1 0 0
                                                    0 0 0 0 3
                                                    0 0 0 3 3
                                                    4 0 3 3 3
                                                    0 0 3 0 3))]

/ (* Idioms *)
leapyear:{(+/~x!'4 100 400)!2}
tests["leap year";,("1699-1712";{leapyear' 1699+!14};0 0 0 0 0 1 0 0 0 1 0 0 0 1)]
factorial:{*/1+!:x}
tests["factorial";,("1-8";{factorial' (1+!8)};1 2 6 24 120 720 5040 40320)]
eye:{a=/:a:!x}
tests["identity matrix";(("0";{eye 0};())
                         ("1";{eye 1};,,1)
                         ("3";{eye 3};(1 0 0;0 1 0;0 0 1))
                         ("4";{eye 4};(1 0 0 0;0 1 0 0;0 0 1 0;0 0 0 1)))]
dot:{+/x*y}
tests["dot product";(("builtin";{1 2 3 _dot 123 456 789};3402)
                     ("manual";{dot[1 2 3;123 456 789]};3402))]
range:{x[*:'=x]}
tests["range";(("builtin";{? "abracadabra"};"abrcd")
               ("manual";{range "abracadabra"};"abrcd"))]
dlb:{x@&|\~x=" "}
tests["delete leading blanks";(("\"   abc\"";{dlb "   abc"};"abc")
                               ("\" abc\"";{dlb " abc"};"abc")
                               ("\"abc\"";{dlb "abc"};"abc"))]
diag:{x ./:n,'n:!#x}
tests["diag";(("123";{diag(1 0 0;0 2 0;0 0 3)};1 2 3)
              ("987";{diag(9 0 0;0 8 0;0 0 7)};9 8 7))]
powerset:{x[&:'!2+&#x]}
tests["powerset";(("`a`b";{powerset `a`b};(0#`;,`b;,`a;`a `b))
                  ("1 2 3";{powerset 1 2 3};(!0;,3;,2;2 3;,1;1 3;1 2;1 2 3))
                  ("abc";{powerset "abc"};("";,"c";,"b";"bc";,"a";"ac";"ab";"abc"))
                  ("ab cd ef";{powerset("ab";"cd";"ef")};(();,"ef";,"cd";("cd"; "ef");,"ab";("ab"; "ef");("ab"; "cd");("ab"; "cd";"ef")))
                  ("ab,`cd,3";{powerset("ab";`cd;3)};(();,3;,`cd;(`cd; 3);,"ab";("ab"; 3);("ab"; `cd);("ab"; `cd;3))))]
compress:{x@&1,~=':x}
tests["compress";(("aaaaabbbccdddeee";{compress "aaaaabbbccdddeee"};"abcde")
                 (("ooonnkkkkkmmlll");{compress "ooonnkkkkkmmlll"};"onkml"))]
tests["left-justify";,("\"  abc \"";{{(+/&\x=" ")!x} ("  abc ")};"abc   ")]
freqtbl:{b@<b:(x@*:'a),'#:'a:=x}
tests["freq table";(("1 1 2 3";{freqtbl 1 1 2 3};(1 2;2 1;3 1))
                    ("\"bxyaba\"";{freqtbl "bxyaba"};(("a";2);("b";2);("x";1);("y";1)))
                    ("mixed";{freqtbl(`a;"b";123;(1 2);(1 2);`a)};(("b";1);(`a;2);123 1;1 2 2)))]

tests["rule104";,("kona example";"_X"@{2=+/(0,x,0)@(!#x)+/:!3}\0 1 1 1 0 1 1 0 1 0 1 0 1 0 1 0 0 1 0 0;("_X_XXXXX_X_X_X______"
                                                                                                        "__XX___XX_X_X_______"
                                                                                                        "__XX___XXX_X________"
                                                                                                        "__XX___X_XX_________"
                                                                                                        "__XX____XXX_________"
                                                                                                        "__XX____X_X_________"
                                                                                                        "__XX_____X__________"
                                                                                                        "__XX________________"
                                                                                                        "__XX________________"))]
tests["csv";,("test.csv";.{(x;y)}'.("SCIF";,",") 0: "test.csv";.((`symbols;`abc `ghi)
                                                                 (`strings;("def 123";"ijk 456"))
                                                                 (`integers;4 7)
                                                                 (`floats;5.6 89.1)))]