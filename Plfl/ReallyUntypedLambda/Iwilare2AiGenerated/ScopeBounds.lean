-- Free indexes and reduction, for the scope-bounded (`Fin`-indexed) calculus.
--
-- In the exact-scope development the corresponding file had to prove that
-- reduction never *increases* the scope index.  Here that statement is
-- vacuous, because it is imposed by typing: a `Term n` reduces to a `Term n`,
-- so a closed term reduces to a closed term with nothing to prove
-- (`betastar_closed`, below, is `trivial`).
--
-- What still has content is the sharper, pointwise statement: reduction never
-- *creates* a free occurrence,
--
--     M —→ N  →  occursFree i N  →  occursFree i M
--
-- (`Beta.occursFree_mono`, `BetaStar.occursFree_mono`), which is proved here
-- from the behaviour of `occursFree` under renaming and substitution.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Basic

@[expose] public section

namespace FinScope

open Term

@[simp] theorem occursFree_var {n : Nat} (i j : Fin n) : occursFree i (v# j) ↔ j = i := Iff.rfl
@[simp] theorem occursFree_abs {n : Nat} (i : Fin n) (t : Term (n + 1)) :
    occursFree i (ƛ t) ↔ occursFree i.succ t := Iff.rfl
@[simp] theorem occursFree_app {n : Nat} (i : Fin n) (a b : Term n) :
    occursFree i (a ⬝ b) ↔ occursFree i a ∨ occursFree i b := Iff.rfl

/-- The free indexes of a renamed term are exactly the renames of the free
indexes. -/
theorem occursFree_ren {n : Nat} (t : Term n) :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (i : Fin m),
      occursFree i (ren ρ t) ↔ ∃ j, occursFree j t ∧ ρ j = i := by
  induction t with
  | var j =>
      intro m ρ i
      simp only [ren_var, occursFree_var]
      constructor
      · intro h; exact ⟨j, rfl, h⟩
      · rintro ⟨k, rfl, rfl⟩; rfl
  | abs t ih =>
      intro m ρ i
      simp only [ren_abs, occursFree_abs, ih]
      constructor
      · rintro ⟨j, hj, hij⟩
        induction j using Fin.cases with
        | zero =>
            rw [ext_zero] at hij
            exact absurd hij (Fin.succ_ne_zero i).symm
        | succ k =>
            refine ⟨k, hj, ?_⟩
            exact Fin.succ_injective _ (by simpa using hij)
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k.succ, hk, by simp⟩
  | app a b iha ihb =>
      intro m ρ i
      simp only [ren_app, occursFree_app, iha, ihb]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        exacts [⟨j, Or.inl hj, rfl⟩, ⟨j, Or.inr hj, rfl⟩]
      · rintro ⟨j, hj | hj, rfl⟩
        exacts [Or.inl ⟨j, hj, rfl⟩, Or.inr ⟨j, hj, rfl⟩]

/-- The free indexes of a substituted term come from the free indexes of the
substituted values. -/
theorem occursFree_sub {n : Nat} (t : Term n) :
    ∀ {m : Nat} (σ : Fin n → Term m) (i : Fin m),
      occursFree i (sub σ t) ↔ ∃ j, occursFree j t ∧ occursFree i (σ j) := by
  induction t with
  | var j =>
      intro m σ i
      simp only [sub_var]
      constructor
      · intro h; exact ⟨j, rfl, h⟩
      · rintro ⟨k, rfl, h⟩; exact h
  | abs t ih =>
      intro m σ i
      simp only [sub_abs, occursFree_abs, ih]
      constructor
      · rintro ⟨j, hj, hij⟩
        induction j using Fin.cases with
        | zero =>
            rw [exts_zero] at hij
            exact absurd (show (0 : Fin (m + 1)) = i.succ from hij) (Fin.succ_ne_zero i).symm
        | succ k =>
            refine ⟨k, hj, ?_⟩
            rw [exts_succ] at hij
            obtain ⟨l, hl, hli⟩ := (occursFree_ren (σ k) Fin.succ i.succ).mp hij
            have : l = i := Fin.succ_injective _ hli
            exact this ▸ hl
      · rintro ⟨k, hk, hik⟩
        refine ⟨k.succ, hk, ?_⟩
        rw [exts_succ]
        exact (occursFree_ren (σ k) Fin.succ i.succ).mpr ⟨i, hik, rfl⟩
  | app a b iha ihb =>
      intro m σ i
      simp only [sub_app, occursFree_app, iha, ihb]
      constructor
      · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
        exacts [⟨j, Or.inl hj, h⟩, ⟨j, Or.inr hj, h⟩]
      · rintro ⟨j, hj | hj, h⟩
        exacts [Or.inl ⟨j, hj, h⟩, Or.inr ⟨j, hj, h⟩]

/-- The free indexes of a beta contractum: they come either from the body,
under the binder, or from the argument. -/
theorem occursFree_betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) (i : Fin n)
    (h : occursFree i (M [ N ])) : occursFree i.succ M ∨ occursFree i N := by
  obtain ⟨j, hj, hij⟩ := (occursFree_sub M (Fin.cons N Term.var) i).mp h
  induction j using Fin.cases with
  | zero => exact Or.inr (by simpa using hij)
  | succ k =>
      rw [Fin.cons_succ] at hij
      have : k = i := hij
      exact Or.inl (this ▸ hj)

/-- **Beta reduction never creates a free occurrence.** -/
theorem Beta.occursFree_mono {n : Nat} {M N : Term n} (h : M —→ N) {i : Fin n}
    (hi : occursFree i N) : occursFree i M := by
  induction h with
  | basis M N => exact occursFree_betaSubst M N _ hi
  | abs _ ih => exact ih hi
  | appL _ ih => exact hi.imp ih _root_.id
  | appR _ ih => exact hi.imp _root_.id ih

theorem BetaStar.occursFree_mono {n : Nat} {M N : Term n} (h : M —→* N) {i : Fin n}
    (hi : occursFree i N) : occursFree i M := by
  induction h with
  | refl => exact hi
  | tail _ step ih => exact ih (step.occursFree_mono hi)

/-- Closed terms reduce to closed terms — here a triviality, since the scope is
part of the type. -/
theorem betastar_closed {M N : Term 0} (_ : M —→* N) : ∀ i : Fin 0, ¬ occursFree i N :=
  closed_of_scope_zero N

end FinScope
