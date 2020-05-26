From stdpp Require Import finite vector numbers.

Locate vec.
Compute vec.
Compute vec bool 1.
Compute [# true ; false ].

Class Vector (v : Type) (s : Type) :=
  {
    vsum : v -> v -> v;
    smul : s -> v -> v;
    vzero : v;
    dist : forall s x y, smul s (vsum x y) = vsum (smul s x) (smul s y)
            
  }.
Print Vector.

Require Import QArith.
Search Q.
Print Qmult.
Print Qmult'.
Print Scope Q_scope.
 
Instance zerovect {a} : Vector unit a. refine  {|
                                          vsum x y := tt;
                                          smul _ _ := tt;
                                          vzero := tt
                                          
                                                       
                                         |}.
intros. auto. Qed.


Search ring_theory.

Goal forall y z,  (Qplus y z) = (Qplus z y). intros. Search (_ + _). apply Qplus_comm.


                                            
Instance qvect : Vector Q Q. refine {|
                                vsum := Qplus;
                                smul := Qmult;
                                vzero := 0
                               |}.
intros. ring.

Instance tupvect `{Vector v s}  : Vector (v * v) s := {|
                                                       vsum u w := match u,w with (x,y), (a,b) => (vsum x a, vsum y b) end;
                                                       smul s v := match v with (x,y) => (smul s x, smul s y) end;
                                                       vzero := (vzero, vzero)
 
                                                     |}.
(* 
Instance arrvect {a} `{Vector s s} : Vector (a -> s) s := {|
                                                vsum u w := fun z => vsum (u z) (w z) ;
                                                smul s v := fun z => smul s (v z) ;
                                                vzero := ?

                                                |}.
*)
Class Norm (v : Type) (s : Type) :=
  {
    norm : v -> s
    }.

Search Q.
(* Instance qnorm : Norm Q Q :=
  {|
    norm := Qabs 
    |}.
 *)

Class Inner (v : Type) (s : Type) :=
  {
    dot : v -> v ->  s
  }.

 Instance dotQ : Inner Q Q :=
  {|
    dot := Qmult 
    |}.

 Instance tupQ `{Inner a Q} `{Inner b Q} : Inner (a * b) Q :=
  {|
    dot x y := match x, y with | (a,b),(c,d) => (dot a c) + (dot b d) end
  |}.

Print nat.
 
Fixpoint vec n a : Type := match n with | S n' => (a * (vec n' a)) | O => unit end.  

Compute vec 10 Q.



Definition norm2 `{Inner v s} (x : v) := dot x x.

(* Instance sumvect `{Vector v s} `{Vector w s} := Vector (v + w) s := {|
                                                                    vsum    

                                                                    |}.
Nope, that's silly.

Thes definitions make it rather difficult to define kroncker product.
I guess 
class Kron a b c s := {
   kron : a -> b -> c
}

 *)
Class Kron (a b c : Type) := {
   kron : a -> b -> c
                              }.

Instance scalarkron `{Vector b s} : Kron  s b b := {|
                                      kron := smul
                                                    |}.

Instance dsumkron `{Kron a c d} `{Kron b c e} :  Kron (prod a  b) c (d * e) := {|
                                kron x y := match x with | (a,b) => (kron a y, kron b y) end  
                                (* : Vector d s *)           
                                                                              |}.

Compute kron (vzero : (Q * Q) ) (vzero : (Q * Q)). 


 Fixpoint e {a} n : vec n a. := match n with  




(*

I definitely want to use the decidable typeclass technology.
???

Can I get psatz to fire on this stuff?

Decidable (a = a) for  

What about Decision (smul s (vsum ) = ) 


We could write a Ring normalizer using typeclases

Class Ring a {
   mul : a -> a -> a;
   plus : a -> a -> a;
   zero : a -> a -> a;
   one : a -> a -> a;
   negate : a -> a
}


*)
