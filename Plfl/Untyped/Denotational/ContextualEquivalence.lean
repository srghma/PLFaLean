module

-- https://plfa.github.io/ContextualEquivalence/

public import Plfl.Untyped.Denotational.Adequacy

@[expose] public section

namespace ContextualEquivalence

open Untyped Untyped.Notation
open Adequacy
open BigStep BigStep.Notation
open Compositional
open Denotational
open Soundness (soundness)

-- https://plfa.github.io/ContextualEquivalence/#contextual-equivalence
abbrev Terminates (m : Term 0) : Prop := ∃ (n : Term 1), m —↠ ƛ n

/--
Two terms are contextually equivalent
if plugging them into the same holed program always produces two programs
that either terminate or diverge together.
-/
abbrev ContextualEquiv {n : Nat} (m n' : Term n) : Prop :=
  ∀ {c : Holed n 0}, Terminates (c.plug m) = Terminates (c.plug n')

namespace Notation
  scoped infixl:25 "≃ₕ" => ContextualEquiv
end Notation

open Notation

-- https://plfa.github.io/ContextualEquivalence/#denotational-equivalence-implies-contextual-equivalence
lemma Terminates.of_eq_ℰ {n : Nat} {m n' : Term n} {c : Holed n 0} (he : ℰ m = ℰ n') :
Terminates (c.plug m) → Terminates (c.plug n')
:= by
  intro ⟨n'', rs⟩
  have h_eq : ℰ (c.plug n') = ℰ (ƛ n'') := by
    calc ℰ (c.plug n')
      _ = ℰ (c.plug m) := compositionality he |>.symm
      _ = ℰ (ƛ n'') := soundness rs
  exact adequacy h_eq

theorem ContextualEquiv.of_eq_ℰ {n : Nat} {m n' : Term n} (he : ℰ m = ℰ n') : m ≃ₕ n' := by
  intro c; simp only [eq_iff_iff]; constructor
  · exact Terminates.of_eq_ℰ he
  · exact Terminates.of_eq_ℰ he.symm
