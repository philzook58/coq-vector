From stdpp Require Import base numbers.

(*
The spec of a "differentail" equation

Defining what differentiation means is difficilt.

We're better off with difference equations

This is a matter of spec choice. If your spec TRULY requires a differential equation rather than a difference equation of dt = 10^-100000000, I am very suspicious that you are in a physically relevant regime of that differential equation.

Differential equations are only used in physics and engineering so far as they are usefl. They compactly describe systems and have occasional useful closed form solutions. Other times they are discretized in some manner for numerical simulation.

If the differential equation is not numerically simulatable, then it is highly suspicious.

For the purspoes of usage inside a system like Coq, the differential equation is no longer convenenitn. To explcility state what differentiation means makes things very difficult.

A mathemticaitica may be interested in a differential equaiton for it's own sake




Ok

I really want somewhat autmated lia/lra.
But

Q can be basically fixed point arithmetic. If the denominator is static and the numerator is dynamic.

I'd have to overload all the operations.
And then I'd use lia to discharge facts.
Maybe sometimes one could use lra too.

Record Qa := {  nominal : Q; err : nat }.

I feel like we kind of want err to be a Qa also...?

Maybe err is with resepct to the same system of denominatrs. That makes sense.

Qa.plus (x y) 


It would be kind of nice for a good denominator to be inferred.



The error term would then also be static.

We'd also probably want to be able to bound 

This seems fun. MetaOcaml for fixed poit

The point of Qc is
1. keep the numbers from getting out of control
2. Being able to use actual equality

1. Could build a correspondence system of some kinf/ reflection between Q and Qc.
2. 
3.


The analog in Z3 might be to use an Int64 symbol with a python int as a denominator

The python in lives at the meta level and can be lifted to z3 level but not vice versa.


Yeah, If you make x dynamic and err static, then err is related to uniform continuity, unifrom error bounds.

 *)

(*
Definition example (x : bool) : nat := 4 + (if x then 2 else 3).
Definition example_cps (b : Type) (x : bool) (k : nat -> b) : b :=
  let k' := fun n => k (4 + n) in                                                         if x then k' 2 else k' 3.

Eval cbv in example.
  (*   = λ x : bool, S (S (S (S (if x then 2 else 3))))
     : bool → nat *)

Eval cbv in example_cps.
*)



(*
     = λ (b : Type) (x : bool) (k : nat → b), if x then k 6 else k 7
     : ∀ b : Type, bool → (nat → b) → b
*)

(*
Inductive my_gadt (o : Type) : Type :=
  | myint : nat -> my_gadt nat
  | mybool : bool -> my_gadt bool.


Definition thing {a} (x : my_gadt a) :=
  match x in my_gadt a  return (a -> a) -> a with
  | myint x => fun f => f x
  | mybool x => fun f => f x
  end.

Definition thing {a} (x : my_gadt a) (f : a -> a) : a:=
  match x in my_gadt b return nat with
  | myint x => f (x + 1)
  | mybool x => f (negb x)
  end.
*)
Require Import QArith.
Require Import QArith.Qcanon.
Search Qc.
Print Scope Q_scope.

(*Print Scope Qc_scope.*)
Check Q2Qc.

Require Import Ascii.
Print ascii.

Require Import ZArith.

Open Scope Z_scope.

Goal forall x, x < x + 1. lia. Qed.

Compute 1 / 2.
Compute 2/2.

(* Goal forall x, 2 * (x / 2) <= x. Aborted. *)
Print Scope Q_scope.
Print Qle.
Goal forall (x y : Z) (z : positive),  (x <= y) -> ((x # z) <= (y # z))%Q. intros.  unfold Qle. simpl. nia. Qed.
Search "div".
Compute -8 / 4.
Search Z.div.
Print Hint *.
Goal forall n m c, n > 0 -> m <= c * n ->  (m / n) <= c. intros.  Search ((_ / _) <= _). apply Z.div_le_upper_bound. lia. lia. Qed.


Search (positive -> Z).
Definition approx ( x : Q) (d : positive) : Q := ((x.(Qnum) * (Zpos d)) / Zpos (x.(Qden))) # d.
| _ => 
Compute approx (1 # 4) 8.
Compute approx (1 # 4) 13.
Search Z.div.

Lemma div_lemma : forall x y z, y > 0 -> z * y <= x + y ->  z  <= 1 + x / y. intros. pose Z.mul_div_le.

Lemma appox_lemma : forall x d, (x - (1 # d)  <= (approx x d) <= x )%Q.
Proof.
  intros. split. Focus 2.
  unfold approx. unfold Qle. simpl. Search Z.div.  Search ( _ * _  = _ * _ ). rewrite ( Z.mul_comm _ (Z.pos (Qden x))).

Require Import Psatz.
  Search ( _ * (_ / _) ).  apply Z.mul_div_le. Search (0 < Zpos _). auto with zarith.
  Search Qle. assert ( forall x y z, x <= z + y  ->  x - y <= z)%Q. intros. lra. apply H. unfold Qle. unfold approx. simpl . clear H.  assert ((((Qnum x) * Z.pos d) `div` Z.pos (Qden x)) * Z.pos (Qden x) <= ((Qnum x) * Z.pos d)). Search Z.div.
  
 
   Check Z.div_le_lower_bound. pose (Z.div_le_lower_bound  (x.(Qnum) * (Zpos d))  (Zpos (x.(Qden)))      . unfold Qle. unfold Qge. split. simpl. 


Compute (div 1 2).


forall x,



Open Scope Q_scope.
Print Q.
Locate positive.

Require Import Ring.
Print Scope positive_scope.
(*  If you need more than 1/ 2^128 sized dt, what are you even doing?   *)
Print Module QArith.
Definition dt_spec := Eval cbv in Qinv (Qmake (Z.shiftl 1 128) 1).
Print dt_spec.
(* Definition dt_spec : Q := ( 1  # 100 ). *)
Print dt_spec.
(* The differnetial equations xdot = x *)
Definition next_spec (x : Q) := (1 + dt_spec) * x.
Definition step2 (x : Q) : Q := next_spec (next_spec x).
Search (Q -> Q).
Definition approx (x : Q) : Q :=  (Pos.shiftl 1 128) * x

Definition step2' (x : Q) : {z : Q|  exists e, 0 <= e /\  z <= (step2 x) + e /\ (step2 x) - e  <= z }.  {| Qnum :=  _  ; Qden := (Pos.shiftl 1 128) |}.
Compute next_spec 1.
Eval cbn in  fun x => next_spec (next_spec x).





Check  {x : Q | x.(Qden) = 100%positive}.

Definition Fixed n := {x : Q | x.(QDen) = n}.

Definition approx_add (x y : Fixed 100) : {z : Fixed 100 | exists e,
                                                           x + y == z * (1 + e)}.

Definition approx_add (x y : Q) (p : x.(Qden) = 100%positive): {z : Q | exists e, x + y == z * (1 + e) (* /\ z.(Qden) = 100%positive *) }. eexists. exists 0. cbn. ring_simplify. auto. unfold "==". auto. Qed.

Definition approx_add x y : {z : Q | exists e, x + y == z * (1 + e) }.


Print Z.
Print Q.

Search (Z -> _ -> Z).
Eval cbv in Z.shiftl 1 8.
Definition dt_spec := Eval cbv in Qinv (Qmake (Z.shiftl 1 8) 1).
Print dt_spec.
Definition dt_spec : Q := ( 1  # 100 ).

Print Q.
Require Import Ascii.

let branch t = if t = 'a' then 'a'
                else if t = 'b' then 'b'
                else if t = 'c' then b
                else failwith "unexpected token"
let fast_branch = if ('a' <= t  && t <= 'c' the return t else failwith "unexpected token" 

                      

                                                                     

(* The differnetial equations xdot = x *)
Definition next_spec (x : Q) := x + x * dt_spec.

(* This is the recursion principle for nat *)
Fixpoint iterate {a} (n : nat) (f : a -> a) (x0 : a) :=
  match n with
  | O => x0
  | S n' => iterate n' f (f x0)
  end.


Eval vm_compute in iterate 9 next_spec 1. (* getting slow around 10
    The exponential is doubling with every op. *)

Close Scope Q_scope.

Definition dt_spec : Q := ( 1  # 100 ).

Print Q.







(* The differnetial equations xdot = x *)
Definition next_spec (x : Q) := x + x * dt_spec.

(* This is the recursion principle for nat *)
Fixpoint iterate {a} (n : nat) (f : a -> a) (x0 : a) :=
  match n with
  | O => x0
  | S n' => iterate n' f (f x0)
  end.


Eval vm_compute in iterate 9 next_spec 1. (* getting slow around 10
    The exponential is doubling with every op. *)

Close Scope Q_scope.
Open Scope Qc_scope.

Definition dt_spec : Qc := Q2Qc ( 1  # 100 ).


(* The differnetial equations xdot = x *)
Definition next_spec (x : Qc) := x + x * dt_spec.

(* This is the recursion principle for nat *)
Fixpoint iterate {a} (n : nat) (f : a -> a) (x0 : a) :=
  match n with
  | O => x0
  | S n' => iterate n' f (f x0)
  end.




Search (nat -> (_ -> _) -> _).
Search (Q -> Q).

Eval vm_compute in decide (0 <= dt_spec).
Eval vm_compute in decide (0 = dt_spec).



Require  Import Psatz.

Goal (0 <= 1)%Q. lra. Qed.
Goal (0 <= 1). fourier.  Abort. (* lra doesn't work on Qc? That super sucks. *)


Definition myabs x := if decide (0 <= x) then x else - x.
Search Qc.



Goal forall x, (myabs (myabs x)) = x. intros. unfold myabs. destruct (decide (0 <= x)). destruct (decide (0 <= x)). auto. apply n in q. destruct q. destruct (decide (0 <= -x)). Search (- _ <= - _).  apply Qcopp_le_compat in q. Search (- 0). Search (- - _). rewrite Qcopp_involutive in q.


(*

Approximate by epsilon
Qabs


*)


(* If we parametrize over dt, we are in some ense allowing the differential limit 


*)


                                 p_count_as_opt = 
(λ (st : () * ()) (input : stream (ocaml_stream ascii) ascii),
   let
   '(_, m_st', st') :=
    ocaml_peek (ascii * () * ocaml_stream ascii) (let (state, _, _, _) := input in state)
      (λ ot : option ascii,
         match ot with
         | Some t =>
             if ocaml_eq t "a"%char
             then
              ocaml_drop (ascii * () * ocaml_stream ascii) (let (state, _, _, _) := input in state)
                (λ state_str : ocaml_stream ascii, ("a"%char, let (x, _) := st in x, state_str))
             else failwith "parse_exact: Unexpected Token!"
         | None => failwith "Unexpected EOF!"
         end) in
    (fix
     rec_v (n : nat) (H : Type) (k' : nat → () → option as_tok * () * ocaml_stream ascii → H)
           (m_st : ()) (stream_st : option as_tok * () * ocaml_stream ascii) {struct n} : H :=
       match n with
       | 0 => failwith "out of gas!"
       | S m =>
           match stream_st with
           | (Some t, _, _) =>
               if ocaml_eq t A
               then
                let
                '(_, m_st'0, st'0) :=
                 let
                 '(_, m_st0, str') := stream_st in
                  ocaml_peek (as_tok * () * (option as_tok * () * ocaml_stream ascii)) str'
                    (λ ot : option ascii,
                       match ot with
                       | Some _ =>
                           let
                           '(_, m_st'0, st'0) :=
                            ocaml_peek (ascii * () * ocaml_stream ascii) st'
                              (λ ot0 : option ascii,
                                 match ot0 with
                                 | Some t1 =>
                                     if ocaml_eq t1 "a"%char
                                     then
                                      ocaml_drop (ascii * () * ocaml_stream ascii) st'
                                        (λ state_str : ocaml_stream ascii,
                                           ("a"%char, m_st0, state_str))
                                     else failwith "parse_exact: Unexpected Token!"
                                 | None => failwith "Unexpected EOF!"
                                 end) in (A, m_st, (Some A, m_st'0, st'0))
                       | None => (A, m_st, (None, m_st0, str'))
                       end) in
                 let
                 '(o2, m_st'1, st'1) :=
                  rec_v m (nat * () * (option as_tok * () * ocaml_stream ascii))%type
                    (λ (o2 : nat) (m_st'1 : ()) (st'1 : option as_tok * () * ocaml_stream ascii),
                       (o2, m_st'1, st'1)) m_st'0 st'0 in k' (S o2) m_st'1 st'1
               else k' 0 m_st stream_st
           | (None, _, _) => k' 0 m_st stream_st
           end
       end) max_int nat (λ (o0 : nat) (_ : ()) (_ : option as_tok * () * ocaml_stream ascii), o0)
      (let (_, y) := st in y) (Some A, m_st', st'))
