Require Import Utf8.
Require Import Lists.List.


Class aLabel (A : Set) : Set
  := lblEq_dec : ∀ a b : A, {a = b} + {a ≠ b}.

Class anAlphabet (A : Set) `{aLabel A} : Set
  := alpha_enum : {e : list A | ∀ a, In a e}.
