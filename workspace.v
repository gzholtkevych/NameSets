Require Import Utf8.
Require Import Lists.List.
Import ListNotations.
Require Import Label.Definitions.


Section LabelFacts.
Variable A : Set.
Context `{label : aLabel A}.
Let chain := list A.

  (* 'In' is a decidable predicate *)
  Definition In_dec (a : A) (c : chain) : {In a c} + {¬ In a c}.
  Proof.
    induction c as [| a' c' IHc'].
    - right. intro. contradiction.
    - elim IHc'; intro H.
      + left. now right.
      + destruct (lblEq_dec a' a) as [Ea'a | NEa'a].
        * left. now left.
        * right. simpl. intro DH. elim DH; intro H1; contradiction.
  Defined.

  (* Occurrences number of 'a' in 'c' *)
  Fixpoint occn (a : A) (c : chain) : nat :=
    match c with
      []       => 0
    | a' :: c' => 
      if lblEq_dec a' a then S (occn a c') else occn a c'
    end.

  (* 'a' occurs at least once into 'c' iff 'a' is a member of 'c' *)
  Lemma In_occn : ∀ a c, In a c ↔ occn a c ≠ 0.
  Proof.
    intros. split; intro; revert a H;
    induction c as [| a' c' IHc']; intros; try contradiction;
    simpl in H |-*.
    - elim H; intro H1; destruct (lblEq_dec a' a);
      try discriminate; try contradiction.
      destruct (In_dec a' c'); now apply IHc'.
    - destruct (lblEq_dec a' a); [ now left | right; now apply IHc' ].
  Qed.
  
  (* 'a' does not occur into 'c' iff 'a' is not a member of 'c' *)
  Lemma notIn_occn : ∀ a c, ¬ In a c ↔ occn a c = 0.
  Proof.
    intros. revert a.
    induction c as [| a' c' IHc']; intro; split; intro.
    - reflexivity.
    - intro. contradiction.
    - simpl. destruct (lblEq_dec a' a) as [Ea'a | Na'a].
      + rewrite Ea'a in H. exfalso. apply H. now left.
      + destruct (In_dec a c'); apply IHc';
        [ simpl in H; elim H; now right | trivial ].
    - inversion H. destruct (lblEq_dec a' a).
      + discriminate H1.
      + apply IHc' in H1. intro H2. simpl in H2.
        elim H2; intro H3; contradiction.
  Qed.

  (* Removing duplicated members of a chain *)
  Fixpoint nodup (c : chain) : chain :=
    match c with
      []      => []
    | a :: c' => if In_dec a c' then nodup c' else a :: (nodup c')
    end.

  (**)
  Lemma nodup_without_dup : ∀ a c, In a c → occn a (nodup c) = 1.
  Proof.
    intros.
    induction c as [| a' c' IHc'].
    - contradiction.
    - simpl. destruct In_dec as [InH | InN].
      + apply IHc'. elim H; intro H1; try assumption ||
        (try now rewrite H1 in InH).
      + simpl in H |-*. destruct (lblEq_dec a' a) as [Ea'a | Na'a].
        * destruct nodup. reflexivity. elim H. intro. rewrite H0. simpl. admit.
        * apply IHc'. elim H; intro H2; [ contradiction | assumption ].
  Admitted.
  
  (**)
  Lemma nodup_member : ∀ a c, ¬ In a c → occn a (nodup c) = 0.
  Admitted.


End LabelFacts.