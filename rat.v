
Compute 1 + 1.
Require Import ZArith. 

Compute 2 + 3.
Compute (2+3)%Z.

Require Import QArith.
Compute 1 # 2.
Compute 7 # 8.

Compute (1 # 2 == 2 # 4). 
(* https://coq.inria.fr/distrib/current/stdlib/Coq.QArith.QArith_base.html# *)


Theorem simplq : (1 # 2 == 2 # 4).
Proof.
  reflexivity.
Qed.

Theorem simpq2 (x : Q) : x + 1 ==  x + 1.
Proof.
   reflexivity.
  Qed.

Record V2 : Set := V2make {x : Q; y : Q }.
Record V2' (a : Set) : Set := V2make' {x' : a; y' : a}.

Definition V2'' := V2' Q.

Definition xhat := V2make 1 0.
Definition yhat := V2make 0 1.

Compute x xhat.

Definition vsum (v1 v2 : V2) := V2make (x v1 + x v2) (y v1 + y v2).
Compute vsum xhat yhat.
Definition dot  (v1 v2 : V2) := (x v1 * x v2) + (y v1 * y v2).
Compute dot xhat yhat.
Compute dot xhat xhat.



Definition smul ( s : Q) (v : V2) :=  V2make (s * x v) (s * y v).

Definition vnegate (v : V2) := V2make  (Qopp (x v)) (Qopp (y v)).



Definition vsub (v1 v2 : V2) := vsum v1 (vnegate v2).
(* or define vsub via an entirely new definition? using Qminus *)
Definition vEq (v1 v2 : V2) := (x v1) == (x v2) /\ (y v1) == (y v2).

Theorem negatedist (v1 v2 : V2) : vEq (vnegate (vsum v1 v2)) (vsum (vnegate v1) (vnegate v2)).
Admitted.


Theorem symvEq (v1 v2 : V2) (e : vEq v1 v2) : (vEq v2 v1).
Proof.
  unfold vEq.  unfold vEq in e. destruct e. split. apply Qeq_sym. rewrite H. reflexivity.  apply Qeq_sym. rewrite H0. reflexivity.
Qed.



Theorem smuldist (s : Q) (v1 v2 : V2) : vEq (smul s (vsum v1 v2)) (vsum (smul s v1) (smul s v2)).
Proof.
  unfold vEq. simpl.  split. rewrite Qmult_plus_distr_r. reflexivity.
  rewrite Qmult_plus_distr_r. reflexivity.
Qed.

Definition Pos a := exists b, a = Zpos b. 
Definition NonNeg a :=  (a = Z0) \/ Pos a.

Theorem squarenonneg  (x : Z) : NonNeg (x * x).
Proof.
  unfold NonNeg. destruct x. left. reflexivity. right. unfold Pos. simpl. eauto. simpl. unfold Pos. right. eauto. Qed.


Definition QNonNeg x := exists b, exists c, NonNeg b /\  x = Qmake b c.


Theorem squarenonnegQ (x : Q) : QNonNeg (x * x).
Proof.
  unfold QNonNeg. destruct x as [ n d ]. unfold Qmult. simpl. unfold Qmult.
  exists (Zmult n n). exists (Pmult d d). split. apply squarenonneg. reflexivity. Qed.

Theorem QNonNegSum (x y : Q) (p1 : QNonNeg x) (p2 : QNonNeg y) : QNonNeg (x + y).
Proof.
Admitted.

 (* unfold QNonNeg. unfold QNonNeg in p1. *)

Theorem dotpos (v : V2) : QNonNeg (dot v v).
Proof.
Admitted.

Definition project (v1 v2 : V2) := vsub v1 (smul (Qdiv (dot v1 v2) (dot v1 v1))  v2).

Definition vzero : V2 := V2make 0 0.

Theorem projectgone (v1 v2 : V2) : (dot v1 (project v2 v1)) == 0.
unfold dot. unfold project. unfold vsub. unfold vnegate. unfold vsum. unfold dot. unfold smul. simpl.  Abort.


(* I need to introduce a new variable for x v1.  Then it hsould be obvious by the ring solver. *)

Definition InHalfSpace (l v : V2) := QNonNeg (dot l v).


(*

 Definition Cone (P : V2 -> Prop) := forall x1 x2 : V2, forall NonNeg l, NonNeg l2,   P x1 -> P x2 -> P (l * x1 + l * x2)

Definition Support (l : V2) P := forall x, P x -> InHalfSpace l x   
 
Definition 

forall x1 x2

*)
 

(* normsquare -> positive rational 
Should we perhaps make a positive rationals type? 
QPos = {N , positive} 

 Leading to the obvious question : how to abstract over V2
 how to abtract over Q
 how to write automation for these proofs. because they are mega trivial.

projection
gram schmidt
cuachy-schwartz

 *)

(*
Theorem qpos  (x : Q) : x * x >= 0.
Proof.
  destruct x. destruct Qnum.   rewrite Qmult_0_l.


  
Compute V2make 1 0.
Compute V2make 0 1.


Require Import Reals.
Print Z_scope.
Compute Z0.
Compute 0.

Compute QArith.
*)