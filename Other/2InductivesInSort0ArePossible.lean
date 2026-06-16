-- prelude

/-!
# Inductive Types and Structures in `Sort 0` (`Prop`)

This module demonstrates how inductive types and structures are defined in `Sort 0`
and explains the rules governing singleton elimination and proof irrelevance.
-/

/-!
## 1. Inductive Types in `Sort 0` (`Prop`)

In Lean, `Prop` is defined as `Sort 0`. Any inductive type can be placed in
`Sort 0`. Many of Lean's core logical primitives are defined this way.
-/

/-- The empty proposition (no constructors). Equivalent to `Empty`. -/
inductive False₂ : Prop

/-- The trivially true proposition (one constructor). Equivalent to `Unit`. -/
inductive True₂ : Prop where
  | intro : True₂

/-- Propositional disjunction (two constructors). -/
inductive Or₂ (a b : Prop) : Prop where
  | inl (h : a) : Or₂ a b
  | inr (h : b) : Or₂ a b

/-- Existential quantification (contains a witness of a type). -/
inductive Exists₂ {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists₂ p

/-- Propositional equality. -/
inductive Eq₂ {α : Sort u} (a : α) : α → Prop where
  | refl : Eq₂ a a


/-!
## 2. Structures in `Sort 0` (`Prop`)

A `structure` in Lean is syntactic sugar for an inductive type with exactly
one constructor and automatically generated field projections. Since structures
can have only one constructor, any single-constructor inductive type in `Prop`
can be written as a structure.
-/

/-- Propositional conjunction (defined as a structure). -/
structure And₂ (a b : Prop) : Prop where
  left : a
  right : b

/-- The property that all elements of a type are equal (defined as a structure). -/
structure Subsingleton₂ (α : Sort u) : Prop where
  intro :: (allEq : ∀ a b : α, Eq₂ a b)


/-!
## 3. Singleton Elimination

The idea that only `Empty`-like or `Unit`-like types "live" in `Prop` is a common
misconception. This confusion stems from **Singleton Elimination**, which is the
rule restricting when we can extract data from `Sort 0` (`Prop`) to `Sort u` (`Type`, $u \ge 1$):

1. **Zero Constructors (e.g., `False`)**: Can always be eliminated to any `Type`
   because there are no cases to construct (e.g., `False` elimination).
2. **Exactly One Constructor (e.g., `And`, `Eq`)**: Can be eliminated to a `Type`
   *only if* the constructor contains no computational/non-propositional data.
3. **Multiple Constructors (e.g., `Or`)**: Cannot be constructively eliminated to
   a `Type`. We cannot write a function `Or a b → Bool` because doing so would
   violate proof irrelevance.
-/


/-!
## 4. `PropNat` and Proof Irrelevance

We can define a type structurally identical to the natural numbers inside `Prop`:
-/

inductive PropNat : Prop where
  | zero : PropNat
  | succ : PropNat → PropNat

/-!
Because `PropNat` is in `Prop`, it is subject to **Proof Irrelevance**:
every term of `PropNat` is definitionally equal to every other term.

As a demonstration, we can prove that `zero` is equal to `succ zero` using only
`Eq.refl`. Since the two sides of the equality are definitionally equal, Lean's
typechecker accepts the reflexivity proof immediately.
-/

theorem propNat_irrelevance : Eq PropNat.zero (PropNat.succ PropNat.zero) :=
  Eq.refl PropNat.zero

theorem propNat2_irrelevance : @Eq₂ PropNat PropNat.zero (PropNat.succ PropNat.zero) :=
  @Eq₂.refl PropNat PropNat.zero

-- Helper function to translate standard equality to your custom Eq₂
theorem eq_to_eq₂ {α : Sort u} {a b : α} (h : a = b) : @Eq₂ α a b :=
  match h with
  | rfl => Eq₂.refl

-- propext axiom is Fundamentally Required
-- Because the types Eq and Eq₂ are definitionally distinct
-- Proof Irrelevance Does Not Apply to Prop itself: PropNat.zero = PropNat.succ PropNat.zero, but not Eq and Eq₂
theorem propNat2_irrelevances_are_eq : @Eq₂ _ (Eq PropNat.zero (PropNat.succ PropNat.zero)) (@Eq₂ PropNat PropNat.zero (PropNat.succ PropNat.zero)) :=
  eq_to_eq₂ (propext (Iff.intro (fun _ => propNat2_irrelevance) (fun _ => propNat_irrelevance)))
