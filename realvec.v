Require Import Reals.
Compute (1)%R.
Compute (1 + 1)%R.
Local Open Scope R_scope.

Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof.
  destruct 1. red. auto with real. auto with real.
Qed.

Lemma Rle_refl : forall r, r <= r.
Proof.
  intro. red. right. reflexivity.
Qed.


Lemma Rge_refl : forall r, r <= r.
Proof. intro. right. reflexivity. Qed.
(* Proof. exact Rle_refl. Qed. *)

Print Rlt_asym.
Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  intros r H. eapply Rlt_asym. apply H. apply H. 
Qed.Lemma Rlt_irrefl : forall r, ~ r < r.

  

(* Solution at https://github.com/coq/coq/blob/master/theories/Reals/RIneq.v
I should try to do them on my own
*)
Theorem square_pos : forall (x : R),  0 <= Rmult x x.
Proof.
  (*
  apply Rle_0_sqr. 
  Qed. *)
  intros r.
  Print Hint.
  case (Rlt_le_dec r 0).
  intro H.
  replace (r * r) with (- r * - r).
  auto with real. (* This is not working *)
  
  About Rlt_le_dec.
  auto with real.
  
  destruct (total_order_T x 0).
  destruct s.
  
  
  Rmult_lt_compat_l.
  

  (**
  
  Define LinOp
  record LinOp

  define contractive as
  |A v| <= |v|

  prove using complete basis
  Chain them

  Define polytope region using corner
  show that goes inside region in fitie time

  Define V1 V2 Product and Compose

  define Vector space type class
  vadd
  smul
  



  *)