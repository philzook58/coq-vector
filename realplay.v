Require Import Reals.
Require Import ZArith.


Open Scope Z_scope.

Goal forall x y, x + y = y + x. debug auto with zarith. Qed.
(* ok the next one basically did it by omega *)
Goal forall x y z, (x + y) + z = y + (x + z). debug auto with zarith. Qed.

Goal forall x y z, x * (y + z) = x * y + x * z. debug auto with zarith. Qed.


Open Scope R_scope.
Require Import Psatz.

About R.
Goal 1 + 1 = 2. lra. Qed.
Variable x y z : R.

Goal x + y = y + x. lra. Qed.
Goal (x + y) + z = x + (y + z). lra. Qed.
Goal x - x  = 0. lra. Qed.
Goal (x + 0 = x). lra. Qed.
Goal x*x >= 0. nra. Qed.

Locate "<=?".

Inductive abs : Prop -> R -> R -> Prop :=
  | LE0 : abs (x <= 0) x (-x)
  | GE0 : abs (x >= 0) x x
.

(* Theorem zsplit :  (x <= 0) + (x >= 0). assert ((x <= 0) \/ (x >= 0)). lra. 
*)

Record I {a} := mk_I { l : a; r : a}.

Require Import QArith.
Definition IQ := I (a := Q).

Check (mk_I Q 0 0).
Definition iadd (x : IQ)  (y : IQ) : IQ :=
  mk_I Q (x.(l) + y.(l) ) ( x.(r) + y.(r)) .
(* Search (R -> R -> ). *)

Definition ilift (x : Q) : IQ := {| l := x ; r := x |}. 

Definition i0 := ilift 0.
Definition i1 := ilift 1.
Definition iu := {|  l := 0 ; r := 1 |}.
Compute iadd i1 i0.
Compute iadd iu iu. 
Open Scope Q_scope.
Print Scope Q_scope.


  
Locate "&&".

Definition ile  (x : IQ) (y : IQ) :=
  Qle_bool x.(l)  y.(l) && Qle_bool y.(r)  x.(r) 
.

(* Theorem iadd_iso : forall ia ib, ile (iadd ia ib)  *)
Close Scope Q_scope.
Definition baby_iter (x : R) (y : R) := (x / y + y) / 2%R.

Compute baby_iter 3 7.

Goal Rabs 3 = 3. Proof.  unfold Rabs.  destruct (Rcase_abs 3); lra. Qed.


Definition near eps x y := (x - y < eps) /\ (y - x < eps).


Definition cont f := forall x y del, del > 0 -> exists eps, R_dist x y < eps -> R_dist (f x) (f y) < del.
(* using near is more automatable that R_dist which ises Rabs which is a branch  *)
Definition cont2 f := forall x del, del > 0 -> exists eps, forall y, near eps x y -> near del (f x) (f y).

Goal cont2 (fun x => x). unfold cont2. unfold near. intros. eexists. intros. eauto.
Qed.
                      (* exists del. intros. lra. Qed. *)
Goal cont2 (fun x => 2*x). unfold cont2. unfold near. intros.  exists (del / 2). intros. lra. Qed.
Theorem relabs x : exists z, z >= 0 /\ ((z = x) \/ z = -x). assert ((x >= 0) \/ (x <= 0)). lra. destruct H. exists x. lra. exists (-x). lra. Qed.

Theorem relmax x y : exists z, z >= x /\ z >= y /\ (z = x \/ z = y). assert ((x >= y) \/ (y >= x)). lra. destruct H. exists x; lra. exists y; lra. Qed.  


Theorem relabs2 x : { z | z >= 0 /\ ((z = x) \/ z = -x)}. destruct (total_order_T x (-x)). destruct s. exists (-x). lra. exists 0. lra. exists x. lra. Qed.
                                                      
(* can't destruct H because H is prop. Tougher to prove assert, can't use lra. *)


(* 

The subset type notation. 
Check {  | e >= 0 }.

These existential things are a lot like 
return z, cs

 *)

Locate "exists".
Print ex.
Locate "/\".
Print and.
Locate ",".
Locate "&".
Print R.
Print prod.
Definition R2 : Set := R * R.
Theorem reflAbs :  forall x, (Rabs x = x) \/ (Rabs x = -x).  intros. unfold Rabs. destruct (Rcase_abs x0); lra. Qed.

Definition proj1 : forall A P, { x : A | P x} -> A := fun A P z => let (x, pf) := z in x.



Theorem norm  (x : R2) : {z | z = relmax (relabs (fst x)) (relabs (snd x)) }.

  {z | z >= (relabs (fst x))  }    let (z1, pf1) := (relabs2 (fst x)) in
                            let (z2, pf2) := (relabs2 (snd x)) in
                            let (z3, pf3) := relmax z1 z2 in
                            { z3 |  pf1 /\ pf2 /\ pf3}.
                            


(*
https://github.com/coq/coq/wiki/Talkin'-with-the-Rooster

eexists
eauto
replace
info auto
debug eauto
specialize
congruence
ring field
firstorder
cut
autorewrite
fourier

intuition? 
Hint Resolve
Hint 

info auto
debug eauto


https://github.com/VERIMAG-Polyhedra/VplTactic



 *)

Print Hint *. (* Prints all hints *)
Print HintDb real.
Print HintDb arith.
Print HintDb zarith.

(*


core:	This special database is automatically used by auto, except when pseudo-database nocore is given to auto. The core database contains only basic lemmas about negation, conjunction, and so on. Most of the hints in this database come from the Init and Logic directories.
arith:	This database contains all lemmas about Peano’s arithmetic proved in the directories Init and Arith.
zarith:	contains lemmas about binary signed integers from the directories theories/ZArith. When required, the module Omega also extends the database zarith with a high-cost hint that calls omega on equations and inequalities in nat or Z.
bool:	contains lemmas about booleans, mostly from directory theories/Bool.
datatypes:	is for lemmas about lists, streams and so on that are mainly proved in the Lists subdirectory.
sets:	contains lemmas about sets and relations from the directories Sets and Relations.
typeclass_instances:
 	contains all the typeclass instances declared in the environment, including those used for setoid_rewrite, from the Classes directory.
fset:


*)

(*
Theorem between x y : exists z, (y <= z /\ z <= x) \/ (x <= z /\ z <= y).
*)


(* a piecewise function that is relationally defined. 
Take in a list of intervals. default value.
Theorem piecewise ls : exists z,  ( -1 <= x <= 2  /\  z = 3 * x )  \/

Or should we take a reflect style approach?
Instance {Reflect 


*)


Locate Rsqrt.

Goal cont (fun x => x). unfold cont. intros. exists del. auto. Qed.
Goal cont (fun x => 2*x). unfold cont. intros. exists (del / 2). Search R_dist. intros. rewrite R_dist_mult_l. assert  (2 * R_dist x0 y0 < del). lra. unfold Rabs. destruct (Rcase_abs 2); lra.  Qed.


Goal cont (fun x => x * x). unfold cont. intros. exists (del / (Rabs x + Rabs y)). intros. unfold R_dist. unfold Rabs. destruct RCase_abs .  Qed.

Record ContLens a b := { f : a -> (b * (b -> a))   } .
Check Build_ContLens.
Check {| f := fun x => (x , fun _ => x ) |}.

(** BEGIN **)
Require Import Reals.
Require Import Interval.Interval_tactic.

Open Scope R_scope.

Goal
  forall x, -1 <= x <= 1 ->
       sqrt (1 - x) <= 3/2.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval_intro (sqrt (1 - x)) upper as H'.
  apply Rle_trans with (1 := H').
  interval.
Qed.

Goal
  forall x, 3/2 <= x <= 2 ->
  forall y, 1 <= y <= 33/32 ->
  Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768.
Proof.
  intros.
  interval with (i_prec 19, i_bisect x).
Qed.

Goal
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
Proof.
  intros.
  interval with (i_bisect_taylor x 3).
Qed.

Goal
  forall x, -1 <= x ->
  x < 1 + powerRZ x 3.
Proof.
  intros.
  interval with (i_bisect_diff x).
Qed.

Require Import Coquelicot.Coquelicot.

Goal
  Rabs (RInt (fun x => atan (sqrt (x*x + 2)) / (sqrt (x*x + 2) * (x*x + 1))) 0 1
        - 5/96*PI*PI) <= 1/1000.
Proof.
  interval with (i_integral_prec 9, i_integral_depth 1, i_integral_deg 5).
Qed.

Goal
  RInt_gen (fun x => 1 * (powerRZ x 3 * ln x^2))
           (at_right 0) (at_point 1) = 1/32.
Proof.
  refine ((fun H => Rle_antisym _ _ (proj2 H) (proj1 H)) _).
  interval.
Qed.

Goal
  Rabs (RInt_gen (fun t => 1/sqrt t * exp (-(1*t)))
                 (at_point 1) (Rbar_locally p_infty)
        - 2788/10000) <= 1/1000.
Proof.
  interval.
Qed.
(*** END ***)





Definition abs x := if zsplit then -x else x .

(*

Continuity Lens
Differentiation and continuity aren't all that different.
In each case we're describing something about how a function is in the neighborhood of a point

A traditional definition of continuity is using the epsilon-delta definition. 


 *)



Definition cont (f : R -> R) : forall del x y, exists eps, abs (x - y) < eps -> abs (f x) - (f y) < del

                                                                                  (*
We can skolemize this definition however, to bring a new fresh function out front 
exists f, forall del, 

f is now a function of del, x, y


(f, c)
a -> (b, b -> a)
evauate the function, and give a pull back of nerughborhoods as described by radii, or as described by l1 norm.
Along with a proof
forall x y del, |x - y| <  (snd (f x) del)   ->  (fst f x) - (fst f y) < del
and vice verse for y.

Record ContLens a b := { f : a -> (b, b -> a)   ;  pf :   } 

*)
