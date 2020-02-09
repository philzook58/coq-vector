Require Import Reals.

Open Scope R_scope.
Inductive V0 (A : Type) : Type := V0Make.
(* Inductive V1 (A : Type) : Type := V1Make : A -> V1 A. *)

Record V1 {A : Type} := { v : A }.
Check Build_V1 R 3.
Hint Constructors V1.

Class Count (a : Type) := {
       count :  nat
                         }.
Open Scope nat.
Instance unitCount : Count unit := {
                                    count := 1%nat
                                  }.

Instance sumCount a b `{Count a} `{Count b}  : Count (a + b) :=
  {
   count := count + count
    }.

Instance prodCount a b `{Count a} `{Count b}  : Count (a * b) :=
  {
   count  := count * count
  }.
Instance boolCount  : Count bool :=
  {
   count  := 2
  }.


Class Enum (a : Type) `{c : Count a} :=  {
        toNat : a -> nat
      }.

Instance unitEnum : Enum unit := {
                                    toNat := fun _ => 0
                                 }.
Print sum.
Instance plusEnum {a b : Type} `{ea : Enum a} `{eb : Enum b} : Enum (a + b) :=
  {      toNat := fun x => match x with
                        | inl a => toNat a
                        | inr b => (toNat b) + count (a := a)
                        end
                                                                               
        }.

Compute toNat (a := (unit + unit)) (inr tt).

Check @count.
Compute count (a := unit * unit).
(* Compute count unitCount. *)

Open Scope nat.
Definition isdiv f := forall x y z, z * y <= x <-> z <= f x y.
Definition isdivy f y := forall x z, z * y <= x <-> z <= f x.
(*
It's strange. it's a spec for div. We don't need to assume a unique div op.


 *)
Require Import Psatz.

Goal forall x y, x <= y <= x -> x = y. intros. destruct H. Search ( _ <= _ -> _ <= _ -> _ = _). apply Nat.le_antisymm; auto. Qed.

Definition islog f := forall x z, 2 ^ z <= x <-> z <= f x.
Goal forall f, islog f -> f 1 = 0. intros. apply Nat.le_antisymm. unfold islog in H. auto with arith. Focus 2. unfold islog in H. apply H. simpl. constructor. assert (f 1 <= f 1). lia. apply H in H0. assert (forall x, 2 ^ x >= 1). intros. auto with arith. induction x. simpl. lia. simpl. lia.  destruct (f 1). lia.  simpl in H0. assert False. ring_simplify in H0. assert (2 * 1 <= 2 * 2^n ) . Search (_ * _ <= _ * _). apply Nat.mul_le_mono_l. apply H1. lia. destruct H2. Qed.

(* what a mess *)

Theorem pospow : forall y, 1 <= 2 ^ y. intros. auto with arith. Search (_ ^ _). assert (1 ^ y <= 2 ^ y). apply Nat.pow_le_mono_l. lia. Search (1 ^ _). rewrite Nat.pow_1_l in H. auto. Qed.

Goal forall f y, islog f -> (y <= f 1 <-> y <= 0). intros. unfold islog in H. split. intros. apply H in H0.  destruct y. lia. simpl in H0. pose (pospow y). lia. intros. apply H. assert ( y = 0). lia. rewrite H1. simpl. lia. Qed.

(*
Ok, a key fact is that 2^n is monotonic. That makes sense.

2^x <= 



 *)


Record Iso {A} {B} (f : A -> B) (g : B -> A) := { to : forall x, f (g x) = x ;
                    from : forall y,  g (f y) = y
                                              }.
Definition id {A : Type} (x : A) := x.

Goal forall A, Iso (A:= A) id id. constructor; intros; unfold id; reflexivity. Qed.




Theorem thingo : {n : nat | n <= 0}. exists 0. auto. Qed.
(*
Goal Iso (A := unit) (B := {n : nat |  Nat.le n 0}) (fun _ => thingo ) (fun _ => tt). constructor. intros. destruct x. destruct x. destruct thingo. destruct x.
*)

(*


isomorphism between n <= m and 

Program Instance let's you fill in partial typeclasses

*)

Compute count.
Compute count.

(*  I'm of half a mind to just use pair. *)
Close Scope nat.

Inductive V2 (A : Type) : Type := V2Make : A -> A -> V2 A.
Inductive Kron (f : Type -> Type) (g : Type -> Type) (a : Type) := MkKron : (f (g a)) -> Kron f g a.
Inductive DSum (f : Type -> Type) (g : Type -> Type) (a : Type) := MkDSum : f a -> g a -> DSum f g a.
(* Definition kron f g a := f ( g a) 
Definition V2 a := (a,a)

*)

Require Import Psatz.
Definition convex f := forall x y l, 0 <= l <= 1 -> f((1 - l) *  x + l * y) <= (1 - l) * f x + l * f y.
Goal convex (fun x => x). unfold convex. intros. lra. Qed.

Theorem cert1 : forall a x l c, a * x >= 0 -> l >= 0 -> l * a = c -> c * x >= 0.
  Proof. intros. assert (l * (a * x) >= l * 0). Search (_ * _ >= _ * _). apply Rmult_ge_compat_l; auto. ring_simplify in H2. rewrite H1 in H2. auto. Qed.

Definition convex2 f := forall x y lx ly, 0 <= lx <= 1 -> 0 <= ly <= 1 -> lx + ly = 1 ->  f(lx *  x + ly * y) <= lx * f x + ly * f y.
(* Definition convex f := forall x y l, 0 <= l <= 1 -> f((1 - l) *  x + l * y) <= (1 - l) * f x + l * f y. *)
Goal convex (fun x => x * x). unfold convex. intros. psatz R . Qed.
(*   Note on compling csdp for mac os x. i had to remove static flag from flags
and export CC=gcc-9
 *)

Goal forall x, (x * x - 7 * x + 9) ^ 2 >= 0. intros. ring_simplify. (* blow it up *)
                                       try nia. try psatz R. Qed.

                           
Goal convex (fun x => x * x). unfold convex. intros. ring_simplify. assert (l ^ 2 <= l). nra. assert ((x - y)^2 >= 0). assert (Rsqr (x - y) = (x - y)^2). unfold Rsqr. simpl. ring. rewrite <- H1. auto with real. nra. Qed.

Definition epigraph (f : R -> R) (x : R)  y := (f x) <= y.
 

(* 
 compositional rules of convexity
  
positive Scalar multiples are convex
composition rule



*)
Goal forall a f, a >= 0 -> convex f -> convex (fun x => a * (f x)). Abort.

(* quite an opaque proof as written
https://math.stackexchange.com/questions/580856/proof-of-convexity-of-fx-x2




                                                                                                                                                                                                                        *)



                           (* Search (_ + _ <= _ + _). apply Rplus_le_compat_r.  assert (lx * x * ly * y <= 0).   psatz R 2.
                            *)


(*

Definition min 


Given a dual certificate
prove minimality of 

we can do the 1d version, and the 2d version. 
cert : A * x >= 0 -> l >= 0 -> l * A = c -> c x >= l a 

ocaml-python
sympy tactic

find formula using sympy, assert it's truth.

use python solve.
esympy 

*)

Definition vsumv1 x y := Build_V1 (v x + v y).
Definition smulv1 s x := Build_V1 (s *(v x)).
Definition vzerov1 : V1 := Build_V1 R 0.
Check vzerov1.
Check vzerov1.
(* Check vsumv1 vzerov1 vzerov1. *)




(* We need to get the ring theory in there. *)
(* 
Class Linear (f : Type -> Type) := {
                                   vsum : f R -> f R -> f R ;
                                   smul : R -> f R -> f R;
                                   vzero : f R;
           
                                             
                                 }.
*)


Class LinOps (v : Type) := {
                                   vsum : v -> v -> v;
                                   smul : R -> v -> v;
                                   vzero : v;
           
                                             
                          }.
Require Import Program.Tactics.
Class Linear (a : Type) `{l : LinOps a} := {
       dist_smul : forall x y s, smul s (vsum x y) = vsum (smul s x) (smul s y);
       assoc_vsum : forall x y z, vsum (vsum x y) z = vsum x (vsum y z);
       assoc_smul : forall s s' v, smul s (smul s' v) = smul (s * s') v;
       dist_smul2 : forall s s' v, smul (s + s') v = vsum (smul s v) (smul s' v);
       vsum_comm : forall x y, vsum x y = vsum y x;
       smul_id : forall v, smul 1 v = v;
       vzero_id : forall v, vsum v vzero = v  
                             }.
  
Print Linear.

Notation "s *^ v" := (smul s v) (at level 75, right associativity).
Notation "v ^+^ w" := (vsum v w) (at level 70, right associativity).
Locate "+".
Locate "*".
Instance linOpsR : (LinOps R) := {
                      vsum := Rplus;
                      smul := Rmult;
                      vzero := 0%R
                                
                                }.

Instance linearR : (Linear R). split; intros; simpl; lra.  Qed.

                                         
Print linearR.
Print vsum. 
(* Print HintDb typeclass_instances. *)


(*
Set Typeclasses Debug.

a -> Prop is morally very much like a -> bool
The difference is in decidability questions, which aren't really where I play
Coq has way more introspection into a -> bool than a runtime/haskell/evulation only model does. It can see the textual definition.


Definition MySet a := a -> Prop
Definition MyRel a b := (a -> Prop) -> (b -> Prop) -> Prop
Definition MyPro a b := (a -> bool) -> list b ->  
(a -> Prop) -> Prop  ? Partialy applied 
(a -> bool) -> bool -- finitely probing?
(a -> Prop) -> a


class Canon a where
   canon :: a -> a

canonicalizing a relationship for quotienting. Very natrual



DSum f g = (f,g) -- no i already did this.

Solving systems -- QR is easiest.

Duality
A x == 0
A^T l == 0

[x,y,z...] = 0


 f f = identity matrix


Class basisOps v := {
      basis : list v {- list is a little weak
}
Laws?
Class basis v := {
      complete : forall v, exists l, v = vsum smul l basis
      independnet : not (exists l vsum basis = head basis)      
}


complete : sum u <u,x> u = x
orthonormal : 


instance basis R {
         basis = [1]
}

instance basis unit {
    basis = []
}
instance basis (x,y) {
    basis = (map dsum vzero basis) append (map dsum x  vzero basis)
    orthonormal = forall u1 u2, u1 elem basis, u2 elem basis, Reflect (dot u1 u2 ?= 1) (u1 = u2)

}



instance Outer R x := x

instance Outer Unit x = Unit

instance Outer (a,b) x := Outer a x, Outer ta x := 





class Scalar {}






*)

Instance linopsunit : (LinOps unit) := {
                                        vsum := fun _ _ => tt;
                                        smul := fun _ _ => tt;
                                        vzero := tt
                                      }.

Instance linearunit : (Linear unit). split; intros; simpl; auto; destruct v0. auto. auto. Qed.



Instance linopspair a b `{LinOps a} `{LinOps b}  : LinOps (a * b) :=
  {

    vsum := fun v1 v2 => ( (fst v1) ^+^ (fst v2) , (snd v1) ^+^ (snd v2 ));
    smul := fun s v => ( s *^ (fst v) , s *^ (snd v));
    vzero := (vzero, vzero)
    }.


Instance linearpair a b `{lina : Linear a} `{ linb : Linear b}  : Linear (a * b).  destruct lina. destruct linb. split; intros; simpl; try congruence.
- destruct v0. simpl. rewrite smul_id1; rewrite smul_id0; auto.
- destruct v0. simpl.  rewrite vzero_id1; rewrite vzero_id0; auto. 
Qed.

Print nat.



Fixpoint V (n : nat) := match n with
                      | O => unit
                      | S n' => prod R (V n')
                      end.

Compute (vzero : (V 4)).
Compute (vzero : (V 5)).                      

Theorem vzero_id_l A  `{l : Linear A} (v : A) :  vsum vzero v = v.
  Proof. rewrite vsum_comm. rewrite vzero_id. auto. Qed.


(*
Norm?
Metric

I shouldn't call these metric. Hilbert maybe?

*)

 Class MetricOps v `{LinOps v} := {
                      dot : v -> v -> R
                      }.

 Class Metric v `{MetricOps v} `{Linear v} := {
                  pos_dot : forall v, 0 <= dot v v;
                  sym_dot : forall v w, dot v w = dot w v;
                  lin_dot : forall v w u, dot v (w ^+^ u) = (dot v w) + (dot v u);
                  lin_dot2 : forall v w s, dot v (s *^ w) = s * (dot v w)

                                             }.

 Instance metopunit : MetricOps unit := {
   dot := fun _ _ => 0
                                       }.

 Instance metopreal : MetricOps R := { dot := fun x y => x * y }.

 Instance metoprod a b `{MetricOps a} `{MetricOps b} : MetricOps (a * b) := {
    dot := fun x y => (dot (fst x) (fst y)) + (dot (snd x) (snd y)) }.

 Instance metricunit : Metric unit.
 split; auto with real. Qed.

Search (0 <= Rsqr _).



Instance metricreal : Metric R.
split; intros; simpl; nra. Qed.

Instance metricprod a b `{ma : Metric a} `{mb : Metric b} : Metric (a * b).
Proof. 
  destruct ma. destruct mb. split; intros; simpl.
  - simpl. Search (0 <= _ + _). apply Rplus_le_le_0_compat; auto.
  - simpl. rewrite sym_dot0. rewrite sym_dot1. auto. 
  - simpl. rewrite lin_dot0. rewrite lin_dot1. simpl. lra.
  - simpl. rewrite lin_dot3. rewrite lin_dot4. simpl. lra.
Qed.


Definition Cone {A} `{Linear A} (P : A -> Prop) := forall l v, P v -> l >= 0 -> P (smul l v).
Goal Cone (fun x => x >= 0). unfold Cone. intros. simpl. nra. Qed.
Goal Cone (fun (v : R*R) => let ( x, y ) := v in x >= 0 /\ y >= 0). unfold Cone. simpl. intros. destruct v0. simpl. nra. Qed.
Goal forall {a} `{la : Metric a} (w : a), Cone (fun v => dot w v >= 0).
  intros. unfold Cone. intros. rewrite lin_dot2. nra. Qed.


Class Quadrant a  `{Linear a} := {  quadrant : a -> Prop; conequad : Cone quadrant}.
Instance quadr : Quadrant R := {  quadrant := fun x => x >= 0}.
unfold Cone. intros. simpl. nra. Qed.

Instance quadprod a b `{Quadrant a} `{Quadrant b} : Quadrant (a * b) := {quadrant := fun x => quadrant (fst x) /\  quadrant (snd x)  }.
unfold Cone. intros. simpl.  destruct H3. split; apply conequad; auto.  Qed.

Theorem cone_conj : forall P Q, Cone P -> Cone Q -> Cone (fun x => P x /\ Q x).
  intros. unfold Cone. intros. destruct H1. split; auto. Qed.

Definition DualCone {A} `{Metric A} (P : A -> Prop) := fun w => forall x, P x -> dot w x >= 0.

Theorem dcone : forall A `{Metric A} (P : A -> Prop), Cone (DualCone P). intros. unfold Cone. intros. unfold DualCone. intros. rewrite sym_dot. rewrite lin_dot2. rewrite sym_dot. 

(*

Contlens
| _ => : Is this constructive point-wise continuity?

Contructive cones. 
(a -> Prop) -> Prop 
feels rather non contrusctive (I wouldn't necessarily want this in Haskell)
cone :: (a -> Bool) -> Bool would never be a function I write

Why not list?
Need to trim upper zeros. That's not so bad







*)

Search R.
Require Import QArith.
Search (Q -> Q -> bool).
Print Scope Q_scope.
Print Qeq.
Print Qeq_bool.
Search nil.
Print list.
Close Scope R.

Fixpoint trimzero (l : list Q) : list Q  := match l with
             | List.cons x xs => if (Qeq_bool 0 x)%Q then trimzero xs else l 
             | List.nil     =>  List.nil
             end.
Definition canonlist l : list Q := List.rev (trimzero (List.rev l)).

Compute canonlist (List.cons 1 (List.cons 0 (List.nil))).


Fixpoint vsumlist l l' := match l, l' with
                            | List.cons x xs, List.cons y ys => List.cons (x + y) (vsumlist xs ys) 
                            | List.nil, ys => ys
                            | xs, List.nil => xs
                            end.
Definition vzerolist {A} := @List.nil A.

Definition smullist s l := List.map (fun x => s * x) l.

(*

list is ambiently in an infinite dimensional space with finite nonzeros.

*)

Compute trimzero (List.cons 0 List.nil).



(*

Quadrant
Elementwise
Functor

*)

                                                                  
  


Compute ((1,2), 4) ^+^ ((1,3), 8).

Goal forall x y : R, (x ^+^ y) = (y ^+^ x). intros. auto with real. Qed.
Goal forall x y : R * R, (x ^+^ y) = (y ^+^ x). intros. destruct x. destruct y. unfold vsum. simpl.   auto with real.

(*
    Definition LinFun {Linear a} {Linear b} a b := {f : a -> b | f (vsum a a') = vsum (f a) (f a') /\
                             f (smul x a) = smul x (f a) } 
*)


(*
     dist_smul : forall x y s, smul s (vsum x y) = vsum (smul s x) (smul s y);
        assoc_vsum : forall x y z, (vsum (vsum x y) z) = vsum (vsum x y) z;
            assoc_smul : forall s s' v, smul s (smul s' v) = smul (s * s') v;
       dist_smul2 : forall s s'smul (s + s') v = vsum (smul s v) (smul s' v);
         vsum_comm : vsum x y = vsum y x;
        smul_id : smul 1 v = v;
        vzero_id : vsum v vzero = v  
*)





Definition cone P := forall l, l >= 0 -> P x -> P (l ^* x). 

Program Instance linearV1 : Linear V1 := {
                         
                         smul s v := match v with
                                     | (V1Make _ x) => V1Make _ (s * x)
                                     end;
                         vzero := V1Make _ 0
                         dist_smul := 
                                        }.



Instance linearDSum (f : Type -> Type) (g : Type -> Type) `{Linear f} `{Linear g}  : Linear (DSum f g) nat := {
                         vsum := fun v w => match v,w with
                                         | (MkDSum _ _ _ f g), (MkDSum _ _ _ f' g') => MkDSum _ _ _ (f ^+^ f') (g ^+^ g')
                                         end;
                         smul s v := match v with
                                     | (MkDSum _ _ _ f g) => MkDSum _ _ _ (s *^ f) (s *^ g)
                                     end;
                         vzero := MkDSum _ _ _ vzero vzero
                                  }.

Definition v1one := V1Make _ 1.
Compute v1one ^+^ v1one.
Definition v2one := MkDSum _ _ _ v1one v1one.
Compute v2one ^+^ v2one.


(*


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
  
  *)
