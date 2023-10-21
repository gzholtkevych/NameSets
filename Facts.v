(* -----------------------------------------------------------------------------
   Properties, and certificates for names and finite sets of names are here.
================================================================================
   Used Libraries
============================================================================= *)
Require Import Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.
Require Import NameSets.Definitions.
Require Import NameSets.IncreasingNameLists.
(* =============================================================================

                                  Name Facts
----------------------------------------------------------------------------- *)
Lemma name_nat : ∀ n m, name_id n = name_id m ↔ n = m.
(* The set of atoms and set of natural numbers are equipower ---------------- *)
Proof.
  intros. destruct n as [idn], m as [idm]. simpl.
  split; intro.
  - now rewrite H.
  - injection H. intro. trivial.
Qed.

Definition name_eq_dec : (* The Leibnitz's equality on atoms is decidable --- *)
  ∀ n m : Name, {n = m} + {n ≠ m}.
Proof.
  intros. destruct n as [idn], m as [idm].
  destruct (Nat.eq_dec idn idm) as [H | H].
  - left. now rewrite H.
  - right. intro H'.
    assert (H'' : idn = idm). { injection H'. intro. trivial. }
    contradiction.
Defined.
(* -----------------------------------------------------------------------------

           The Operation for Injecting a Name into a Name Set
----------------------------------------------------------------------------- *)
Fixpoint aux_inject (n : Name) (lst : list Name) : list Name :=
  (* the auxiliary function for injecting a natural number 'n' into a list of
     natural numbers 'lst' before the first member of the list that is greater 
     than 'n' --------------------------------------------------------------- *)
    match lst with
    | []        => [n]
    | m :: lst' => match (lt_eq_lt_dec (name_id n) (name_id m)) with
        | inleft Hle => match Hle with
            | left _  => n :: m :: lst'
            | right _ => m :: lst'
            end
        | inright _  => m :: (aux_inject n lst')
        end
    end.

Definition inject (n : Name) (ns : NameSet) : NameSet.
(* the function injects a name 'n' into a finite set of names 'ns' ---------- *)
Proof.
  destruct ns as (lst, H). pose (aux_inject n lst) as nlst.
  exists nlst. subst nlst.
  destruct lst as [| m lst'].
  - constructor.
  - simpl. destruct (lt_eq_lt_dec (name_id n) (name_id m)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now constructor.
    + assumption.
    + revert n m H Hgt. induction lst' as [| k lst'' IHlst''].
      * constructor; [assumption | constructor].
      * intros. {
        simpl. destruct (lt_eq_lt_dec (name_id n) (name_id k)) as [Hle | Hgt'];
        try destruct Hle as [Hlt | Heq].
        - constructor; [ assumption | constructor ]; try assumption.
          now inversion_clear H.
        - assumption.
        - inversion_clear H.
          constructor; try assumption. now apply IHlst''. }
Defined.

Lemma post_inject : ∀ n ns, In n (inject n ns).
(* a name is in a name set after injecting this name into the name set ------ *)
Proof.
  intros. revert n.
  destruct ns as (lst, H).
  induction lst as [| m lst' IHlst']; intro.
  - now left.
  - simpl.
    destruct (lt_eq_lt_dec (name_id n) (name_id m)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now left.
    + left. now apply name_nat.
    + right.
      assert (increasing lst'). { 
        inversion_clear H; [ constructor | assumption ]. }
      now apply IHlst'.
Qed.

Lemma post_inject_discr : ∀ n m ns, In m (inject n ns) → m = n ∨ In m ns.
(* if a name 'm' is in the name set obtained by injecting 'n' into a name
   set 'ns', then 'n' and 'm' are equal, or 'n' is in 'ns' ------------------ *)
Proof.
  intros until ns. revert m n.
  destruct ns as (lst, H).
  induction lst as [| k lst' IHlst']; intros * H1.
  - elim H1; intro H2; [ now left | contradiction ].
  - simpl in H1 |-*.
    assert (H2 : increasing lst'). { 
      inversion_clear H; [ constructor | assumption ]. }
    simpl in IHlst'. pose (IH := IHlst' H2).
    destruct (lt_eq_lt_dec (name_id n) (name_id k)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + elim H1; intro H3.
      * left. now symmetry.
      * destruct H3 as [HL | HR]; right; [ now left | now right ].
    + destruct (lt_eq_lt_dec (name_id k) (name_id m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq'];
      try (right; inversion_clear H1; [ now left | now right ]).
    + inversion_clear H1.
      * right. now left.
      * elim (IH m n H0); intro; [ now left | right ]; now right.
Qed.
(* -------------------------------------------------------------------------- *)

(* -----------------------------------------------------------------------------
   Constructing the atom set formed by atoms with identifiers
   base, ..., base + len
----------------------------------------------------------------------------- *)

Fixpoint aux_segment (base len : nat) {struct len} : list Name :=
  (* the function generates the list [name base; ..., name (base + len - 1)]  *)
  match len with
  | 0      => []
  | S len' => (name base) :: aux_segment (S base) len'
  end.

Fixpoint segment (base len : nat) : NameSet :=
  match len with
  | 0      => noName
  | S len' => inject (name base) (segment (S base) len')
  end.

Lemma plus_n_1 : ∀ n : nat, n + 1 = S n.
Proof.
  induction n as [| n' IHn'].
  - trivial.
  - simpl. now rewrite IHn'.
Qed.

Lemma segment_inject : (* the segment with name_ids in
  ['base'; ...; base + len - 1] can be obtained by injecting name base
  into the segment with name_ids in [base + 1; ...; base + len - 1] --------- *)
  ∀ base len, segment base (S len) = inject (name base) (segment (S base) len).
Proof.
  intros. revert base.
  destruct len as [| len']; intros; destruct base; reflexivity.
Qed.

Lemma in_segment : ∀ base len n,
  In n (segment base len) → base ≤ (aid n) ∧ (aid n) < base + len.
Proof.
  intros.
  destruct len as [| len']; intros.
  - inversion H.
  - revert base n H.
    induction len' as [| len'' IHlen'']; intros.
    + elim H; intro H1; split.
      * rewrite <- H1. constructor.
      * rewrite <- H1. rewrite plus_n_1. constructor.
      * inversion H1.
      * inversion H1.
    + split.
      * simpl in H.
        pose (post_inject_discr (a base) n).
        rewrite <- (segment_inject (S base) len'') in H.
        apply IHlen''. simpl in H.
        pose (IH := IHlen'' ).
  

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
