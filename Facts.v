Require Import NatFinSubsets.Prelude.
Import ListNotations.
Require Import NatFinSubsets.Definitions.


Section Auxiliaries.

  (* If a list of natural numbers has been sorted by increasing, then its tail
     is sorted by increasing too.
     This lemma is used to define and certify the function 'inject'. -------- *)
  Lemma tail_increasing : ∀ n lst, increasing (n :: lst) → increasing lst.
  Proof.
    intros. inversion H; [ constructor | assumption ].
  Qed. (*
  --------------------------------------------------------------------------- *)

  (* If removing the after-head member from a natural numbers list has been
     sorted by increasing, then the obtained list is sorted by increasing too.
     This lemma is used to define and certify the function 'inject'. -------- *)
  Lemma remove_increasing :
    ∀ n m lst, increasing (n :: m :: lst) → increasing (n :: lst).
  Proof.
    intros.
    inversion_clear H.
    destruct lst as [| k lst'].
    - constructor.
    - inversion_clear H1.
      assert (H3 : n < k). { now apply Nat.lt_trans with m. }
      now constructor.
  Qed. (*
  --------------------------------------------------------------------------- *)

  Fixpoint aux_inject (n : nat) (lst : list nat) : list nat :=
  (* The auxiliary function for injecting a natural number 'n' into a list of
     natural numbers 'lst' before the first member of the list that is greater 
     than 'n'. -------------------------------------------------------------- *)
    match lst with
    | []        => [n]
    | m :: lst' => match (lt_eq_lt_dec n m) with
        | inleft Hle => match Hle with
            | left _  => n :: m :: lst'
            | right _ => m :: lst'
            end
        | inright _  => m :: (aux_inject n lst')
        end
    end.
  (* Check function beahaviour ---------------------------------------------- *)
  Eval simpl in aux_inject 5 [].
  Eval simpl in aux_inject 5 [2].
  Eval simpl in aux_inject 2 [2]. 
  Eval simpl in aux_inject 1 [2].
  Eval simpl in aux_inject 5 [2; 7; 9]. (*
  --------------------------------------------------------------------------- *)

  (* The following lemmas
       'aux_inject_eq', 
       'aux_inject_less', and
       'aux_inject_greater'
     are used for defining the function 'inject', which adds a natural number 
     to a finite set of natural numbers. ------------------------------------ *)
  Lemma aux_inject_eq : ∀ n lst, aux_inject n (n :: lst) = n :: lst.
  Proof.
    intros. simpl.
    destruct (lt_eq_lt_dec n n) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    - exfalso. revert Hlt. apply Nat.lt_irrefl.
    - reflexivity.
    - exfalso. revert Hgt. apply Nat.lt_irrefl.
  Qed.

  Lemma aux_inject_less :
    ∀ n lst, increasing (n :: lst) → aux_inject n lst = n :: lst.
  Proof.
    intros.
    induction lst as [| m lst' IHlst'].
    - trivial.
    - simpl. destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + trivial.
      + rewrite Heq in H. inversion_clear H. exfalso. revert H0.
        apply Nat.lt_irrefl.
      + inversion_clear H. 
        assert (m < m). { now apply Nat.lt_trans with (m := n). }
        exfalso. revert H. apply Nat.lt_irrefl.
  Qed.

  Lemma aux_inject_greater : ∀ n m lst,
    increasing (m :: lst) → m < n 
      → aux_inject n (m :: lst) = m :: aux_inject n lst.
  Proof.
    intros. simpl.
    destruct (lt_eq_lt_dec n m) as [Hle | Hgt]; try destruct Hle as [Hlt | Heq];
    induction lst as [| k lst' IHlst'].
    - exfalso.
      assert (m < m). { now apply Nat.lt_trans with (m := n). }
      revert H1; apply Nat.lt_irrefl.
    - exfalso.
      assert (m < m). { now apply Nat.lt_trans with (m := n). }
      revert H1; apply Nat.lt_irrefl.
    - exfalso. rewrite Heq in H0. revert H0. apply Nat.lt_irrefl.
    - exfalso. rewrite Heq in H0. revert H0. apply Nat.lt_irrefl.
    - trivial.
    - assert (m :: aux_inject n lst' = m :: aux_inject n lst'). {
        apply IHlst'. now apply remove_increasing with (m := k). }
    reflexivity.
  Qed. (*
  --------------------------------------------------------------------------- *)
End Auxiliaries.

Definition inject (n : nat) (ns : NatFinSubset) : NatFinSubset.
(* The function Injects a natural number 'n' into a finite set of natural
   numbers 'ns'. ------------------------------------------------------------ *)
Proof.
  destruct ns as (lst, H).
  pose (aux_inject n lst) as nlst.
  exists nlst.
  induction lst as [| m lst' IHlst'].
  - constructor.
  - simpl in nlst.
    destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now constructor.
    + assumption.
    + simpl in IHlst'. subst nlst.
      assert (IH : increasing (aux_inject n lst')). {
        apply IHlst'. now apply tail_increasing with m. }
      destruct lst' as [| k lst''].
      * simpl. constructor; [ assumption | constructor ].
      * inversion_clear H. simpl. {
        destruct (lt_eq_lt_dec n k) as [Hle | Hgt'];
        try destruct Hle as [Hlt | Heq].
        - constructor; [ assumption | now constructor ].
        - rewrite <- Heq in IH. rewrite <- Heq in H0, H1.
          rewrite (aux_inject_eq n) in IH.
          rewrite <- Heq. now constructor.
        - constructor.
          + assumption.
          + assert (aux_inject n (k :: lst'') = k :: aux_inject n lst''). {
              now apply aux_inject_greater. }
            rewrite <- H. now apply IHlst'. }
Defined.
Notation "'injecting' x 'into' y" := (inject x y)
  (at level 70).
(* Check operation behaviour ------------------------------------------------ *)
Example ns1245 : NatFinSubset.
Proof. exists [1; 2; 4; 5]. repeat constructor. Defined.
Eval simpl in toList (injecting 3 into ns1245).

(*
removing 'x' from 'A'
'A' excluding 'B'
uniting 'A' and 'B'
*)

Fixpoint union (ns ms : NatFinSubset) : NatFinSubset.
Proof.
  destruct ns as (nlst, _).
  induction nlst as [| n].
  - exact ms.
  - exact (injecting n into IHnlst).
Defined.
Notation "'uniting' x 'and' y" := (union x y)
  (at level 70, left associativity).

Fixpoint segment (base off : nat) : NatFinSubset.
Proof.
  induction off as [| off' IHoff'].
  - exists []. constructor.
  - exact (injecting (base + off') into IHoff').
Defined.
Eval simpl in toList (segment 3 5).


Lemma in_segment : ∀ n base off : nat,
  base ≤ n → n < base + off → In n (segment base off).
Proof.
Admitted.

Lemma out_segment : ∀ n base off : nat,
  n < base ∨ n ≥ base + off → ¬ In n (segment base off).
Proof.
Admitted.
