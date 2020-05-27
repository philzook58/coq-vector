Require Import QArith.

Require Import Psatz.

Require Import Ring.


Definition dt := (1 # 100).

Definition step x := x + dt * x.

Definition step2 x := step (step x).

Goal forall x, x >= 0 -> x <= 2 * x + 1. intros. lra. Qed.

Definition step2' x := (1 + 3 * dt) * x.
Goal forall x, 0 <= x -> step2 x <= step2' x.  unfold step2. unfold step2'. unfold step.  unfold dt.  intros. lra. Qed.


Goal forall x, x >= 0 -> step x >= x. intros. unfold step. unfold dt. lra. Qed.

(* Induction 


Manual building the proof for individual guys.
*)

