Require Import NatFinSubsets.Prelude.
Import ListNotations.


(* -----------------------------------------------------------------------------
   The predicate for recognising lists of natural numbers has been sorted by
   increasing. -------------------------------------------------------------- *)
Inductive increasing : list nat → Prop :=
  | inc0 : increasing []
  | inc1 : ∀ n, increasing [n]
  | incS : ∀ n m ns, 
      n < m → increasing (m :: ns) → increasing (n :: m :: ns). (*
----------------------------------------------------------------------------- *)

(* -----------------------------------------------------------------------------
   The type 'NatFinSubset' is used for modelling finite subsets of natural
   numbers, with the coercion 'toList' ensuring to operate with inhabitants of 
   this type as with lists. ------------------------------------------------- *)
Definition NatFinSubset : Set := {lst : list nat | increasing lst}.
Coercion toList := fun ns : NatFinSubset => proj1_sig ns. (*
----------------------------------------------------------------------------- *)
