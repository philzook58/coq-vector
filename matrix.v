(*Require Import stdpp.base stdpp.numbers.
*)
Require Import QArith.
Record V2 (a : Type) := {
                         x2 : a;
                         y2 : a
                       }.

Arguments x2 {a}.
Arguments y2 {a}.



Record M2 := {
              c1 : V2 Q;
              c2 : V2 Q
              }.

Open Scope Q_scope.
Definition vadd v w : V2 Q := {| x2 := v.(x2) + w.(x2) ; y2 := v.(y2) + w.(y2)  |}.

Definition smul s v : V2 Q := {| x2 := s * v.(x2) ; y2 := s * v.(y2)   |}.

Definition dot v w : Q := v.(x2) * w.(x2) + v.(y2) * w.(y2).

Definition mapply m v := vadd (smul v.(x2) m.(c1)) (smul v.(y2) m.(c2)).



Require Import Ring.
Require Import Psatz.
Require Import Lqa.

Goal forall x y , x + y == x + y. intros. lra. Qed.

Definition VEq v w := v.(x2) == w.(x2)  /\ v.(y2) == w.(y2).
Notation "x == y" := (VEq x y).
Notation " x + y " := (vadd x  y).
Notation " s * y " := (smul s y).



Definition vzero := {| x2 := 0 ; y2 := 0 |}.

Definition xhat := {| x2 := 1 ; y2 := 0 |}.

Definition yhat := {| x2 := 0 ; y2 := 1 |}.
Check vzero.
Check vzero == vzero.
Theorem vadd_comm : forall v w, v + w == w + v. Proof. intros. split; simpl; lra. Qed.

(* This is a setoid equality. :/   Does lra not work on Qc? *)

Theorem linop : forall v w m, mapply m (vadd v w) == (vadd (mapply m v)  (mapply m w)).
  intros. unfold mapply. unfold vadd. simpl. split; simpl; lra. Qed.

Theorem linop2 : forall s v m, mapply m (smul s v) == smul s (mapply m v).
  intros. unfold mapply. unfold smul. simpl. split; simpl; lra. Qed.

Definition mcompose m n :=  {|
                            c1 := mapply m n.(c1);
                            c2 := mapply m n.(c2)

                            |}.

Notation " m @@ n " := (mcompose m n) (at level 50) .
Notation " m @ v " := (mapply m v) (at level 50) .



Theorem matrixgood : forall m n v, mapply m (mapply n v) == mapply ( mcompose m n ) v.
   intros. unfold mapply. unfold mcompose. simpl. split; simpl; lra. Qed.

Definition madd m n := {|
                        c1 := vadd m.(c1) n.(c1);
                        c2 := vadd m.(c2) n.(c2)
                      |}.

Notation "<< a b >>" := {| x2 := a ; y2 := b |}.
Notation "<< a b , c d >>" := {| c1 := {| x2 := a ; y2 := c|} ; c2 := {| x2 := b ; y2 := d |} |}.

Check << 1 0 >> .

(*

https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
He does a 2x2 matrix type
*)

Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlNatInt  Coq.extraction.ExtrOcamlZInt.
Recursive Extraction vadd.
Recursive Extraction smul.

Goal dot vzero vzero <= 1. cbn. unfold dot. simpl. lra. Qed.




Theorem vadd_comm : forall v w, vadd v w = vadd w v. Proof.
                                                  intros v w. destruct v. destruct w. unfold vadd. cbn.  assert (x3 + x4 = x4 + x3). ring.  assert (y3 + y4 = y4 + y3). ring.  rewrite H. rewrite H0. auto. Qed.

Theorem smul_assoc : forall a b v, smul a (smul b v)  = smul (a * b) v. Proof.
     intros. destruct v.  unfold smul. cbn.  assert (a * (b * x3) = a * b * x3). ring.  assert (a * (b * y3) = a * b * y3). ring.  rewrite H. rewrite H0. auto. Qed.


