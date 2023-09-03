(* -----------------------------------------------------------------------------
   This library contains definitions, properties, and certificates for
   atomic entities.
   We assume that there is an enumerable set of names and a computable method 
   for distinguishing two different names.
   Therefore, natural numbers are used as names in the library.
   -------------------------------------------------------------------------- *)

Require Export Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.

Inductive atom : Set := a : nat → atom.
Definition aid : atom → nat :=
(* the function returns identifier of its argument -------------------------- *)
  fun n => let 'a idn := n in idn.
  
Lemma aid_inj : ∀ n m, aid n = aid m → n = m.
Proof.
  intros. destruct n as [idn], m as [idm]. simpl in H. now rewrite H.
Qed.

Lemma aid_surj : ∀ n, ∃ idn, n = a idn.
Proof.
  intro. destruct n as [idn]. now exists idn.
Qed.

(* -----------------------------------------------------------------------------
   The predicate for recognising lists of atoms has been sorted by
   increasing their identifiers. 
   -------------------------------------------------------------------------- *)
Inductive increasing : list atom → Prop :=
  | inc0 : increasing []
  | inc1 : ∀ n, increasing [n]
  | incS : ∀ n m ns,
      aid n < aid m → increasing (m :: ns) → increasing (n :: m :: ns).

Definition increasing_dec :
(* the predicate is decidable ----------------------------------------------- *)
  ∀ lst : list atom, {increasing lst} + {¬ increasing lst}.
Proof.
  intro.
  destruct lst as [| n lst'].
  - left. constructor.
  - revert n. induction lst' as [| m lst'' IHlst'']; intro.
    + left. constructor.
    + destruct (lt_eq_lt_dec (aid n) (aid m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      * { elim (IHlst'' m); intro H.
        - left. now constructor.
        - right. intro H1. apply H. now inversion_clear H1. }
      * right. intro H. inversion_clear H. rewrite Heq in H0.
        now apply Nat.lt_irrefl with (aid m).
      * right. intro H. inversion_clear H.
        apply Nat.lt_irrefl with (aid m). now apply Nat.lt_trans with (aid n).
Defined.
(* ========================================================================== *)

(* -----------------------------------------------------------------------------
   The type 'AtomSet' is used for modelling finite subsets of names,
   with the coercion 'toList' ensuring to operate with inhabitants of 
   this type as with lists. 
   -------------------------------------------------------------------------- *)
Definition AtomSet : Set := {lst : list atom | increasing lst}.
Coercion toList := fun ns : AtomSet => proj1_sig ns.
(* -------------------------------------------------------------------------- *)

Fixpoint aux_inject (n : atom) (lst : list atom) : list atom :=
(* the auxiliary function for injecting a natural number 'n' into a list of
   natural numbers 'lst' before the first member of the list that is greater 
   than 'n'.
   -------------------------------------------------------------------------- *)
    match lst with
    | []        => [n]
    | m :: lst' => match (lt_eq_lt_dec (aid n) (aid m)) with
        | inleft Hle => match Hle with
            | left _  => n :: m :: lst'
            | right _ => m :: lst'
            end
        | inright _  => m :: (aux_inject n lst')
        end
    end.

Definition inject (n : atom) (ns : AtomSet) : AtomSet.
(* the function injects an atom 'n' into a finite set of atoms 'ns'.
   -------------------------------------------------------------------------- *)
Proof.
  destruct ns as (lst, H). pose (aux_inject n lst) as nlst.
  exists nlst. subst nlst.
  destruct lst as [| m lst'].
  - constructor.
  - simpl. destruct (lt_eq_lt_dec (aid n) (aid m)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now constructor.
    + assumption.
    + revert n m H Hgt. induction lst' as [| k lst'' IHlst''].
      * constructor; [assumption | constructor].
      * intros. {
        simpl. destruct (lt_eq_lt_dec (aid n) (aid k)) as [Hle | Hgt'];
        try destruct Hle as [Hlt | Heq].
        - constructor; [ assumption | constructor ]; try assumption.
          now inversion_clear H.
        - assumption.
        - inversion_clear H.
          constructor; try assumption. now apply IHlst''. }
Defined.

Lemma post_inject : ∀ n ns, In n (inject n ns).
Proof.
  intros. revert n.
  destruct ns as (lst, H).
  induction lst as [| m lst' IHlst']; intro.
  - now left.
  - simpl.
    destruct (lt_eq_lt_dec (aid n) (aid m)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now left.
    + left. now apply aid_inj.
    + right.
      assert (increasing lst'). { 
        inversion_clear H; [ constructor | assumption ]. }
      now apply IHlst'.
Qed.

Lemma post_inject_discr : ∀ n m ns, In m (inject n ns) → m = n ∨ In m ns.
Proof.
  intros until ns. revert m n.
  destruct ns as (lst, H).
  induction lst as [| k lst' IHlst']; intros * H1.
  - elim H1; intro H2; [ now left | contradiction ].
  - simpl in H1 |-*.
    assert (H2 : increasing lst'). { 
      inversion_clear H; [ constructor | assumption ]. }
    simpl in IHlst'. pose (IH := IHlst' H2).
    destruct (lt_eq_lt_dec (aid n) (aid k)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + elim H1; intro H3.
      * left. now symmetry.
      * destruct H3 as [HL | HR]; right; [ now left | now right ].
    + destruct (lt_eq_lt_dec (aid k) (aid m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq'];
      try (right; inversion_clear H1; [ now left | now right ]).
    + inversion_clear H1.
      * right. now left.
      * elim (IH m n H0); intro; [ now left | right ]; now right.
Qed.

Fixpoint aux_segment (base len : nat) {struct len} : list atom :=
(* the function generates the list [base; ..., base + len - 1].
   -------------------------------------------------------------------------- *)
  match len with
  | 0      => []
  | S len' => (a base) :: aux_segment (S base) len'
  end.

Lemma aux_segment_inc : ∀ base len, increasing (aux_segment base len).
(* the list [base; ..., base + len - 1] is increasing.
   -------------------------------------------------------------------------- *)
Proof.
  intros. revert base.
  induction len as [| len' IHlen']; intro.
  - constructor.
  - simpl. destruct len' as [| len''].
    + constructor.
    + assert (increasing (aux_segment (S base) (S len''))). {
        pose (IHlen' (S base)). assumption. }
      assert (base < S base). { constructor. }
      simpl. constructor.
      * assumption.
      * simpl in H. assumption.
Qed.

Definition segment (base len : nat) : AtomSet.
(* the function returns the name set {base; ...; base + len - 1}.
   -------------------------------------------------------------------------- *)
Proof.
  exists (aux_segment base len).
  apply aux_segment_inc.
Defined.

(* The certificate of 'segment'
     In n (segment base len) ↔ base ≤ n ∧ n < base + len
   -------------------------------------------------------------------------- *)
Lemma plus_n_1 : ∀ n : nat, n + 1 = S n.
Proof.
  induction n as [| n' IHn'].
  - trivial.
  - simpl. now rewrite IHn'.
Qed.

Lemma lt_n_plus_n_Sm : ∀ n m : nat, n < n + S m.
Proof.
  induction m as [| m' IHm'].
  - rewrite plus_n_1. constructor.
  - rewrite <- plus_n_Sm. apply Nat.lt_trans with (n + S m');
    [ assumption | constructor ].
Qed.

Lemma in_segment : ∀ base len n,
  In n (segment base len) → base ≤ (aid n) ∧ (aid n) < base + len.
Proof.
  destruct len as [| len']; intros.
  - contradiction.
  - revert base H. induction len' as [| len'' IHlen'']; intros.
    + inversion_clear H.
      * rewrite <- H0. split; try constructor. rewrite plus_n_1. constructor.
      * contradiction.
    + inversion_clear H.
      * rewrite <- H0. split; [ constructor | apply lt_n_plus_n_Sm ].
      * rewrite <- plus_n_Sm.
        pose (IH := IHlen'' (S base) H0). destruct IH. { split.
        - inversion_clear H; try do 2 constructor.
          assert (H3 : base ≤ m). { apply Nat.le_trans with (S base);
            [ do 2 constructor | assumption ]. }
          apply Nat.le_trans with m; try assumption. do 2 constructor.
        - rewrite <- plus_n_Sm. simpl in H1. now rewrite <- plus_n_Sm in H1. }
Qed.

Lemma segment_in : ∀ base len n,
  base ≤ aid n → aid n < base + len → In n (segment base len).
Proof.
  destruct len as [| len'].
  - intros. exfalso. rewrite <- plus_n_O in H0.
    pose (le_le_S_dec (aid n) base). destruct s as [H1 | H1].
    + assert (aid n < aid n). { apply Nat.le_trans with base; try assumption. }
      now apply Nat.lt_irrefl with (aid n).
    + assert (base < base). { apply Nat.le_trans with (aid n); try assumption.
      apply Nat.le_trans with (S (aid n)); [ do 2 constructor | assumption ]. }
      now apply Nat.lt_irrefl with base.
  - revert base. induction len' as [| len'' IHlen'']; intros;
    destruct (lt_eq_lt_dec (aid n) base) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    * exfalso. assert (H2 : (aid n) < (aid n)). { 
        now apply Nat.le_trans with base. }
      now apply Nat.lt_irrefl with (aid n).
    * rewrite <- Heq. left. destruct n. reflexivity.
    * exfalso. rewrite plus_n_1 in H0.
      assert (H2 : (aid n) ≤ base). { now apply le_S_n. }
      assert (H3 : base < base). { now apply Nat.le_trans with (aid n). }
      now apply Nat.lt_irrefl with base.
    * exfalso. assert (H3 : base < base). { apply Nat.le_trans with (S (aid n));
      [ now apply le_n_S | assumption ]. }
      now apply Nat.lt_irrefl with base.
    * left. destruct n. rewrite <- Heq. reflexivity.
    * right. apply IHlen''; try assumption.
      simpl. now rewrite plus_n_Sm.
Qed.
