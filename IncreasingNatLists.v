(* =============================================================================
   Used Libraries
============================================================================= *)
Require Import Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.
(* ========================================================================== *)

(* -----------------------------------------------------------------------------
   The predicate for recognising lists of atoms has been sorted by
   increasing their identifiers. 
----------------------------------------------------------------------------- *)
Inductive increasing : list nat → Prop :=
  | inc0 : increasing []
  | inc1 : ∀ n, increasing [n]
  | incS : ∀ n m ns,
      n < m → increasing (m :: ns) → increasing (n :: m :: ns).

Definition increasing_dec :
  (* the predicate increasing is decidable ---------------------------------- *)
  ∀ lst : list nat, {increasing lst} + {¬ increasing lst}.
Proof.
  intro.
  destruct lst as [| n lst'].
  - left. constructor.
  - revert n. induction lst' as [| m lst'' IHlst'']; intro.
    + left. constructor.
    + destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      * { elim (IHlst'' m); intro H.
        - left. now constructor.
        - right. intro H1. apply H. now inversion_clear H1. }
      * right. intro H. inversion_clear H. rewrite Heq in H0.
        now apply Nat.lt_irrefl with m.
      * right. intro H. inversion_clear H.
        apply Nat.lt_irrefl with m. now apply Nat.lt_trans with n.
Defined.
(* -------------------------------------------------------------------------- *)
