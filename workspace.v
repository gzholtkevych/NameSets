Require Import Utf8.
Require Import Lists.List.
Import ListNotations.


Class Label (A : Set) := {
  label_eqDec : ∀ a b : A, {a = b} + {a ≠ b};
  label_enum : {e : list A | ∀ a, In a e}
}.

Definition chain {A : Set} := list A.

Section Decidability.
Variable A : Set.
Context `{label : Label A}.

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

End Decidability.