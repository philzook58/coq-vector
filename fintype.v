(*

https://www.ps.uni-saarland.de/~menz/finalTalktex.pdf
Why am I even fighting the a -> R form of vectors.
It's kind of nice.


https://github.com/bmsherman/finite
https://github.com/tchajed/cardinality

There is of course the Fin n type. That'll probably suck to use

uustalu firsov agda
http://firsov.ee/finset/finset.pdf

https://math-comp.github.io/htmldoc/mathcomp.ssreflect.fintype.html

 *)

Class BEnum a := {
                  enumAll : list a
                }.

Instance unitbenum : BEnum unit := {| enumAll := cons tt nil |}.
Instance boolbenum : BEnum bool := {| enumAll := (cons true  ( cons false nil)) |}.


Instance pairbenum `{BEnum a} `{BEnum b} : BEnum (a * b) :=
  {| enumAll :=
      |}.
Instance unitbenum : BEnum unit := {| enumAll := cons tt nil |}.
