Require Import Utf8.
Require Import Lists.List.
Import ListNotations.


Class Label (A : Set) := {
  label_eqDec : ∀ a b : A, {a = b} + {a ≠ b};
  label_enum : {e : list A | ∀ a, In a e}
}.

Definition chain {A : Set} := list A.

Section Facts.
Variable A : Set.
Context `{label : Label A}.

  (* 'In' is a decidable predicate *)
  Definition In_dec (a : A) (c : chain) : {In a c} + {¬ In a c}.
  Proof.
    induction c as [| a' c' IHc'].
    - right. intro. contradiction.
    - elim IHc'; intro H.
      + left. now right.
      + destruct (label_eqDec a' a) as [Ea'a | NEa'a].
        * left. now left.
        * right. simpl. intro DH. elim DH; intro H1; contradiction.
  Defined.

  (* Occurrences number of 'a' in 'c' *)
  Fixpoint occn (a : A) (c : chain) : nat :=
    match c with
      []       => 0
    | a' :: c' => 
      if label_eqDec a' a then S (occn a c') else occn a c'
    end.

  (* 'a' occurs at least once into 'c' iff 'a' is a member of 'c' *)
  Lemma In_occn : ∀ a c, In a c ↔ occn a c ≠ 0.
  Proof.
    intros. split; intro; revert a H;
    induction c as [| a' c' IHc']; intros; try contradiction.
    - simpl in H |-*.
      elim H; intro H1; destruct (label_eqDec a' a) as [EH | NH];
      try discriminate; try contradiction.
      destruct (In_dec a' c') as [InH | NInH]; now apply IHc'.
    - simpl in H |-*. destruct (label_eqDec a' a) as [EH | NH].
      + now left.
      + right. now apply IHc'.
  Qed.

  (* Removing duplicated members of a chain *)
  Fixpoint nodup (c : chain) : chain :=
    match c with
      []      => []
    | a :: c' => if In_dec a c' then nodup c' else a :: (nodup c')
    end.

  (**)
  Lemma nodup_without_dup : ∀ a c, In a c → occn a (nodup c) = 1.
  Admitted.
  
  (**)
  Lemma nodup_member : ∀ a c, ¬ In a c → occn a (nodup c) = 0.
  Admitted.


End Facts.