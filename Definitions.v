(* -----------------------------------------------------------------------------
   The definitions for names and finite sets of names are here.
   We assume that there is an enumerable set of names and a computable method 
   for distinguishing two different names.
================================================================================
   Used Libraries
============================================================================= *)
Require Export Utf8.
Require Import Lists.List.
Import ListNotations.
(* ========================================================================== *)

(* -----------------------------------------------------------------------------
   Type Name
----------------------------------------------------------------------------- *)
Inductive Name : Set := name : nat → Name.

Definition name_id : Name → nat :=
  (* the function returns identifier of its argument ------------------------ *)
  fun n => let 'name id := n in id.
(* -------------------------------------------------------------------------- *)

(* -----------------------------------------------------------------------------
   The type 'NameSet' is used for modeling finite sets of atoms, with 
   the coercion 'toList' ensuring to operate with inhabitants of 
   this type as with lists.
   The idea of modeling is to use lists of terms inhabiting type 'Name' 
   sorted by increasing name identifiers.
----------------------------------------------------------------------------- *)
Inductive increasing : list Name → Prop  (* the property 'to be increasing' *)
  := inc0 : increasing []
   | inc1 : ∀ n, increasing [n]
   | incS : ∀ n1 n2 ns,
              name_id n1 < name_id n2 → 
              increasing (n2 :: ns) → 
                increasing (n1 :: n2 :: ns).

Definition NameSet : Set := {ns : list Name | increasing ns}.
Coercion to_list := fun ns : NameSet => proj1_sig ns.

Example noName : NameSet.
(* Empty name set ----------------------------------------------------------- *)
Proof. exists []. constructor. Defined.
(* -------------------------------------------------------------------------- *)
