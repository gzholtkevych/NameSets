(* -----------------------------------------------------------------------------
   This library contains definitions, properties, and certificates for
   the naming of entities.
   We assume that there is an enumerable set of names and a computable method 
   for distinguishing two different names.
   Therefore, natural numbers are used as names in the library.
   -------------------------------------------------------------------------- *)

Require Export Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.


Module Type NAME.
  Parameter name : Set.
  Parameter id : name → nat.

  Axiom id_inj : ∀ x y : name, id x = id y → x = y.
  Axiom id_surj : ∀ n : nat, ∃ x : name, id x = n.
  Parameter eq_dec : ∀ x y : name, {x = y} + {x ≠ y}.
End NAME.

Module Names (M : NAME) <: NAME with Definition name := M.name.

  Definition name := M.name.
  Definition id := M.id.
  Definition id_inj := M.id_inj.
  Definition id_surj := M.id_surj.
  Definition eq_dec := M.eq_dec.
  

  Inductive increasing : list name → Prop :=
    | inc0 : increasing []
    | inc1 : ∀ n, increasing [n]
    | incS :
        ∀ n m lst, 
          M.id n < M.id m → increasing (m :: lst) → increasing (n :: m :: lst).

  Definition inc_dec : ∀ lst : list name, {increasing lst} + {¬ increasing lst}.
  Proof.
    intro.
    destruct lst as [| n lst'].
    - left. constructor.
    - revert n. induction lst' as [| m lst'' IHlst'']; intro.
      + left. constructor.
      + destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | HGt];
        try destruct Hle as [Hlt | Heq].
        * elim (IHlst'' m); intro H; [ left | right ];
          try now constructor.
          intro.
          assert (increasing (m :: lst'')). { now inversion_clear H0. }
          contradiction.
        * right. intro. inversion_clear H. rewrite Heq in H0.
          now apply Nat.lt_irrefl with (M.id m).
        * right. intro. inversion_clear H.
          apply Nat.lt_irrefl with (M.id n).
          now apply Nat.lt_trans with (M.id m).
  Defined.

  Definition NameSet := {lst : list name | increasing lst}.
  Coercion toList := fun ns : NameSet => proj1_sig ns.

  Definition In_dec : 
    ∀ (n : name) (ns : NameSet), {In n ns} + {¬ In n ns}.
  Proof.
    intros.
    destruct ns as [lst H]. simpl. clear H.
    induction lst as [| m lst' IHlst'].
    - right. intro. inversion_clear H.
    - destruct (M.eq_dec n m) as [Heq | Hneq];
      destruct (inc_dec lst') as [H1 | H1];
      try destruct(IHlst' H1) as [H2 | H2]; clear H1;
      try now (left; rewrite <- Heq; left).
      + destruct IHlst' as [H | H]; [ left | right ].
        * now right.
        * intro. apply H. elim H0; intro; 
          [ symmetry in H1; contradiction | assumption ].
      + destruct IHlst' as [H | H].
        * left. now right.
        * right. intro. simpl in H0. elim H0; intro;
         [ symmetry in H1; contradiction | contradiction ].
  Defined.

  Definition nothing : NameSet.
  Proof. exists []. constructor. Defined.

  Fixpoint aux_inject (n : name) (lst : list name) : list name :=
  (* the auxiliary function for injecting a name 'n' into a list of names 'lst'
     before the first member of the list that has 'id' greater than 'id n'.
   -------------------------------------------------------------------------- *)
    match lst with
    | []        => [n]
    | m :: lst' => match (lt_eq_lt_dec (M.id n) (M.id m)) with
        | inleft Hle => match Hle with
            | left _  => n :: m :: lst'
            | right _ => m :: lst'
            end
        | inright _  => m :: (aux_inject n lst')
        end
    end.

  Definition inject (n : name) (ns : NameSet) : NameSet.
  (* the function Injects a name 'n' into a finite set of names 'ns' -------- *)
  Proof.
    destruct ns as (lst, H). pose (aux_inject n lst) as nlst.
    exists nlst. subst nlst.
    destruct lst as [| m lst'].
    - constructor.
    - simpl. destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + assumption.
      + revert n m H Hgt. induction lst' as [| k lst'' IHlst''].
        * constructor; [assumption | constructor].
        * intros. {
          simpl. destruct (lt_eq_lt_dec (M.id n) (M.id k)) as [Hle | Hgt'];
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
    destruct ns as [lst H]. simpl.
    induction lst as [| m lst' IHlst']; intro.
    - now constructor.
    - simpl. destruct (lt_eq_lt_dec (M.id n) (M.id m)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + constructor. now apply M.id_inj.
      + right. apply IHlst'. inversion_clear H; [constructor | assumption].
  Qed.

  Lemma inject_discr : ∀ n m ns, In m (inject n ns) → n = m \/ In m ns.
  Proof.
    intros.
    destruct (eq_dec n m) as [Heq | HNeq].
    - now left.
    - right. revert n m HNeq H. induction inject. simpl in H.
    destruct ns as [lst H]. simpl.
    induction lst as [| k lst' IHlst']; intros; simpl in H0.
    - elim H0; intro; [now left | contradiction].
<<<<<<< HEAD
    - simpl in H0. destruct (lt_eq_lt_dec (M.id n) (M.id k)) as [Hle | HGt];
      try destruct Hle as [Hlt | Heq].
      + inversion_clear H0; [now left | now right].
      + now right.
      + inversion_clear H0.
        * right. now left.
        * simpl. right. { apply IHlst'.
          - inversion_clear H; [constructor | assumption].
          - destruct (lt_eq_lt_dec (M.id m) (M.id k)) as [Hle | Hgt];
            try destruct Hle as [Hlt | Heq].
            + exfalso. now apply Nat.lt_irrefl with (M.id k).
          + 
=======
    - destruct (lt_eq_lt_dec (M.id n) (M.id k)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq]; simpl in H0 |-*.
      + assumption.
      + now right.
      + right. apply IHlst'.
        * inversion_clear H; [constructor | assumption].
        * { elim H0; intro.
          - rewrite H1. pose (post_inject.

>>>>>>> 1ce5fa930dde8cde8f897bf8480a6a01c9c5ea4d
  Definition declare (lst : list name) : NameSet.
  Proof.
    induction lst as [| n lst' ns'].
      
    - exact nothing.
    - exact (inject n ns').
  Defined.

  Lemma post_declare : ∀ lst n, In n (declare lst) ↔ In n lst.
  Proof.
    intro.
    induction lst as [| m lst' IHlst']; intro; split; intro;
    try contradiction.
    - simpl in H |-*. destruct (eq_dec m n).
      + now left.
      + right. apply IHlst'. destruct lst' as [| k lst''].
        * simpl in H. destruct H as [H1 | H1]; contradiction.
        * apply IHlst'. { destruct (eq_dec n k) as [H1 | H1].
          - now left.
          - apply IHlst'. simpl.

End Names.


Inductive var := v : nat → var.
Module Var <: NAME with Definition name := var.
  Definition name := var.
  Definition id := fun x : name => let '(v n) := x in n.

  Lemma id_inj : ∀ x y : name, id x = id y → x = y.
  Proof. intros. destruct x as [n], y as [m]. simpl in H. now rewrite H. Qed.

  Lemma id_surj : ∀ n : nat, ∃ x : name, id x = n.
  Proof. intro. now exists (v n). Qed.

  Definition eq_dec : ∀ x y : name, {x = y} + {x ≠ y}.
  Proof.
    intros. destruct x as [n], y as [m].
    destruct (Nat.eq_dec n m) as [HEq | HNeq].
    - left. now rewrite HEq.
    - right. intro. apply HNeq. now injection H.
  Defined.
End Var.

Module varScopes := Names(Var).



Fixpoint aux_segment (base len : nat) {struct len} : list nat :=
(* the function generates the list [base; ..., base + len - 1].
   -------------------------------------------------------------------------- *)
  match len with
  | 0      => []
  | S len' => base :: aux_segment (S base) len'
  end.

Lemma aux_segment0 : ∀ n, aux_segment n 0 = [].
Proof. reflexivity. Qed.

Lemma aux_segment_inc : ∀ base len, increasing (aux_segment base len).
(* the list [base; ..., base + len - 1] is increasing.
   -------------------------------------------------------------------------- *)
Proof.
  intros. revert base.
  induction len as [| len' IHlen'].
  - constructor.
  - simpl. destruct len' as [| len''].
    + constructor.
    + intro.
      assert (increasing (aux_segment (S base) (S len''))). {
       pose (IHlen' (S base)). assumption. }
      assert (base < S base). { constructor. }
      simpl. constructor.
      * assumption.
      * simpl in H. assumption.
Qed.

Definition segment (base len : nat) : NameSet.
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
  In n (segment base len) → base ≤ n ∧ n < base + len.
Proof.
  destruct len as [| len']; intros.
  - contradiction.
  - revert base H. induction len' as [| len'' IHlen'']; intros.
    + inversion_clear H.
      * rewrite H0. split; try constructor. rewrite plus_n_1. constructor.
      * contradiction.
    + inversion_clear H.
      * rewrite H0. split; [ constructor | apply lt_n_plus_n_Sm ].
      * rewrite <- plus_n_Sm.
        pose (IH := IHlen'' (S base) H0). destruct IH. { split.
        - inversion_clear H; try do 2 constructor.
          assert (H3 : base ≤ m). { apply Nat.le_trans with (S base);
            [ do 2 constructor | assumption ]. }
          apply Nat.le_trans with m; try assumption. do 2 constructor.
        - rewrite <- plus_n_Sm. simpl in H1. now rewrite <- plus_n_Sm in H1. }
Qed.

Lemma segment_in : ∀ base len n,
  base ≤ n → n < base + len → In n (segment base len).
Proof.
  destruct len as [| len'].
  - intros. exfalso. rewrite <- plus_n_O in H0.
    pose (le_le_S_dec n base). destruct s as [H1 | H1].
    + assert (n < n). { apply Nat.le_trans with base; try assumption. }
      now apply Nat.lt_irrefl with n.
    + assert (base < base). { apply Nat.le_trans with n; try assumption.
      apply Nat.le_trans with (S n); [ do 2 constructor | assumption ]. }
      now apply Nat.lt_irrefl with base.
  - revert base. induction len' as [| len'' IHlen'']; intros;
    destruct (lt_eq_lt_dec n base) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    * exfalso. assert (H2 : n < n). { now apply Nat.le_trans with base. }
      now apply Nat.lt_irrefl with n.
    * rewrite Heq. now left.
    * exfalso. rewrite plus_n_1 in H0.
      assert (H2 : n ≤ base). { now apply le_S_n. }
      assert (H3 : base < base). { now apply Nat.le_trans with n. }
      now apply Nat.lt_irrefl with base.
    * exfalso. assert (H3 : base < base). { apply Nat.le_trans with (S n);
      [ now apply le_n_S | assumption ]. }
      now apply Nat.lt_irrefl with base.
    * left. now symmetry.
    * right. apply IHlen''; try assumption.
      simpl. now rewrite plus_n_Sm.
Qed.
