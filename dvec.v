

Require Import Ring.
Definition v2 (A : Type) := A -> A -> A.
(* Really it should be a linear function. *)

Definition xhat {A : Type} : v2 A := fun  x y => x.
Definition yhat {A : Type} : v2 A := fun  x y => y.
 
Class SemiRing (A : Type) :=
  {
    plus : A -> A -> A ;
    one : A ;
    zero : A ;
    times : A -> A -> A ;
    (* Plus all the laws. *)
                             
  }.

Search Nat.add.
Locate "+".
Instance seminat : SemiRing nat := {
                        plus := Nat.add;
                        one := 1;
                        zero := 0;
                        times := Nat.mul
                                }.
Definition vadd {A : Type} {ringa : SemiRing A} (v : v2 A) (w : v2 A) : v2 A :=
  fun x1 y1 => plus (v x1 y1) (w x1 y1).

Compute vadd xhat yhat 1 2.

Definition smul {A : Type} {ringa : SemiRing A} (s : A) (v : v2 A) : v2 A :=
  fun x1 y1 => times s (v x1 y1).

Definition dot {A : Type} {ringa : SemiRing A} (v : v2 A) (w : v2 A) : A :=
  plus (times (v one zero) (w one zero)) (times (v zero one ) (w zero one)).

Compute dot xhat yhat.
Compute dot xhat xhat.

