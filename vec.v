Require Import Ring_theory.
Print ring_theory.

Inductive V0 (A : Type) : Type := V0Make.
Inductive V1 (A : Type) : Type := V1Make : A -> V1 A.
Inductive V2 (A : Type) : Type := V2Make : A -> A -> V2 A.
Inductive Kron (f : Type -> Type) (g : Type -> Type) (a : Type) := MkKron : (f (g a)) -> Kron f g a.
Inductive DSum (f : Type -> Type) (g : Type -> Type) (a : Type) := MkDSum : f a -> g a -> DSum f g a.
(* We need to get the ring theory in there. *)
Class Linear (f : Type -> Type) (A : Type) := {
                                   vsum : f A -> f A -> f A ;
                                   smul : A -> f A -> f A;
                                   vzero : f A
                                            }.

Notation "s *^ v" := (smul s v) (at level 75, right associativity).
Notation "v ^+^ w" := (vsum v w) (at level 70, right associativity).

Instance linearV1 : Linear V1 nat := {
                         vsum := fun v w => match v,w with
                                         | (V1Make _ x), (V1Make _ y) => V1Make _ (x + y)
                                         end;
                         smul s v := match v with
                                     | (V1Make _ x) => V1Make _ (s * x)
                                     end;
                         vzero := V1Make _ 0
                                  }.
Instance linearDSum (f : Type -> Type) (g : Type -> Type) `{Linear f nat} `{Linear g nat}  : Linear (DSum f g) nat := {
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
Class Ring (A : Type) := {
           eq :
           plus 
           theory : ring_theory eq 


}

Record LinOp (f : v A -> w A) {
       is_linear : f (v ^+^ w) = (f v) ^+^ (f w)
        

}

*)
(*
                                   dist_smul : smul s (vsum x y) = vsum (smul s x) (smul s y);
                                   assoc_vsum : (vsum (vsum x y) z) = vsum (vsum x y) z;
                                   assoc_smul : smul s (smul s' v) = smul (s * s') v;
                                   dist_smul : smul (s + s') v = vsum (smul s v) (smul s' v);
                                   vsum_comm : vsum x y = vsum y x;
                                   smul_id : smul 1 v = v;
                                   vzero_id : vsum v vzero = v                                                                                
                                                        
                                 *)
