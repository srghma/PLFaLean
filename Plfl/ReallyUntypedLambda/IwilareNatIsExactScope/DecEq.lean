-- Decidable equality of terms, *constructively*.
--
-- This file exists for one reason: to keep the whole development free of
-- `Classical.choice`.  Several progress/normalisation results need to decide a
-- property of a term ("is this an abstraction?", "is this an eta redex?"), and
-- the classical `by_cases` tactic would pull `Classical.propDecidable` -- hence
-- the axiom of choice -- into the proof term.  All these properties are in fact
-- decidable, and the decision procedure is built here, by structural recursion.
--
-- Note that `deriving DecidableEq` does *not* work for `Term`: two terms of the
-- same scope can be built from subterms of *different* scopes (e.g. `ƛ M` with
-- `M : Term 0` and `ƛ N` with `N : Term 1` are both of scope `0`), so equality
-- has to be decided heterogeneously, comparing the term trees and reading off
-- the equality of the scopes afterwards.  That is what `Term.beq` below does.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Basic

@[expose] public section

namespace IwilareNatIsExactScope

namespace Term

/-- Heterogeneous structural equality test on term trees: the scopes are *not*
    assumed equal, they are compared implicitly through the trees. -/
def beq : {n m : Nat} → Term n → Term m → Bool
  | _, _, var i,   var j    => i == j
  | _, _, abs t,   abs t'   => beq t t'
  | _, _, app a b, app a' b' => beq a a' && beq b b'
  | _, _, _,       _        => false

@[simp] theorem beq_var_var {i j : Nat} : beq (var i) (var j) = (i == j) := rfl
@[simp] theorem beq_abs_abs {n m : Nat} (t : Term n) (t' : Term m) :
    beq (abs t) (abs t') = beq t t' := rfl
@[simp] theorem beq_app_app {n m p q : Nat} (a : Term n) (b : Term m)
    (a' : Term p) (b' : Term q) :
    beq (app a b) (app a' b') = (beq a a' && beq b b') := rfl

/-- `beq` decides equality in `Scoped`. -/
theorem beq_iff {n m : Nat} (t : Term n) (t' : Term m) :
    beq t t' = true ↔ (⟨n, t⟩ : Scoped) = ⟨m, t'⟩ := by
  induction t generalizing m with
  | var i =>
      cases t' with
      | var j =>
          simp only [beq_var_var, beq_iff_eq]
          exact ⟨fun h => by cases h; rfl, fun h => Scoped.var_eq_var.mp h⟩
      | abs t' =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.var i = Scoped.abs ⟨_, t'⟩ from h) Scoped.var_ne_abs⟩
      | app a b =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.var i = Scoped.app ⟨_, a⟩ ⟨_, b⟩ from h) Scoped.var_ne_app⟩
  | abs t ih =>
      cases t' with
      | var j =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.abs ⟨_, t⟩ = Scoped.var j from h) Scoped.abs_ne_var⟩
      | abs t' =>
          rw [beq_abs_abs, ih t']
          exact ⟨fun h => Scoped.abs_eq_abs.mpr h, fun h => Scoped.abs_eq_abs.mp h⟩
      | app a b =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.abs ⟨_, t⟩ = Scoped.app ⟨_, a⟩ ⟨_, b⟩ from h) Scoped.abs_ne_app⟩
  | app a b iha ihb =>
      cases t' with
      | var j =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.app ⟨_, a⟩ ⟨_, b⟩ = Scoped.var j from h) Scoped.app_ne_var⟩
      | abs t' =>
          exact ⟨fun h => Bool.noConfusion h,
            fun h => absurd (show Scoped.app ⟨_, a⟩ ⟨_, b⟩ = Scoped.abs ⟨_, t'⟩ from h) Scoped.app_ne_abs⟩
      | app a' b' =>
          rw [beq_app_app, Bool.and_eq_true, iha a', ihb b']
          exact ⟨fun h => Scoped.app_eq_app.mpr h, fun h => Scoped.app_eq_app.mp h⟩

end Term

/-- **Equality of terms is decidable**, without any appeal to classical logic. -/
instance : DecidableEq Scoped := fun a b =>
  decidable_of_iff (Term.beq a.2 b.2 = true) (by
    obtain ⟨n, t⟩ := a
    obtain ⟨m, t'⟩ := b
    exact Term.beq_iff t t')

namespace Scoped

/-- Being an abstraction is decidable. -/
theorem isAbs_cases (s : Scoped) : (∃ p, s = abs p) ∨ ¬ (∃ p, s = abs p) := by
  rcases Scoped.cases' s with ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inr (fun ⟨_, hp⟩ => Scoped.var_ne_abs hp)
  · exact Or.inl ⟨p, rfl⟩
  · exact Or.inr (fun ⟨_, hp⟩ => Scoped.app_ne_abs hp)

/-- Being an application is decidable. -/
theorem isApp_cases (s : Scoped) : (∃ a b, s = app a b) ∨ ¬ (∃ a b, s = app a b) := by
  rcases Scoped.cases' s with ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inr (fun ⟨_, _, hp⟩ => Scoped.var_ne_app hp)
  · exact Or.inr (fun ⟨_, _, hp⟩ => Scoped.abs_ne_app hp)
  · exact Or.inl ⟨a, b, rfl⟩

/-- Being a *shifted* term -- equivalently, not using the index `0` -- is
    decidable: the only possible witness is `sub0 (var 0) s`, and whether it is
    one can be settled by a single equality test. -/
theorem isShift_cases (s : Scoped) :
    (∃ M, s = ren Nat.succ M) ∨ ¬ (∃ M, s = ren Nat.succ M) := by
  by_cases h : s = ren Nat.succ (sub0 (var 0) s)
  · exact Or.inl ⟨_, h⟩
  · refine Or.inr (fun ⟨M, hM⟩ => h ?_)
    rw [hM, sub0_ren_succ]

end Scoped

end IwilareNatIsExactScope
