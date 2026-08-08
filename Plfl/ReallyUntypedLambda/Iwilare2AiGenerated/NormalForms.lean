-- Normal forms, uniqueness of normal forms, and consistency, for the
-- scope-bounded (`Fin`-indexed) calculus of `FinScope`.
--
-- This is the port of `IwilareNatIsExactScope/NormalForms.lean` to the new
-- representation.  Every inversion lemma that had to be proved by hand there
-- (`Beta.abs_inv'`, `Beta.app_inv'`, ...) is here just `cases` on the
-- reduction, because `Term n` is an ordinary inductive family: this is one of
-- the simplifications the `Fin`-indexed presentation buys.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Basic

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Beta conversion is a congruence -/

theorem betastar_to_betaeq {n : Nat} {a b : Term n} (h : a —→* b) : a ≡β b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem beta_to_betaeq {n : Nat} {a b : Term n} (h : a —→ b) : a ≡β b := Relation.EqvGen.rel _ _ h

theorem BetaEq.symm {n : Nat} {a b : Term n} (h : a ≡β b) : b ≡β a := Relation.EqvGen.symm _ _ h

theorem BetaEq.trans {n : Nat} {a b c : Term n} (h₁ : a ≡β b) (h₂ : b ≡β c) : a ≡β c :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem BetaEq.refl {n : Nat} (a : Term n) : a ≡β a := Relation.EqvGen.refl _

/-- Beta conversion is compatible with abstraction. -/
theorem BetaEq.abs {n : Nat} {a b : Term (n + 1)} (h : a ≡β b) : ƛ a ≡β ƛ b := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.abs hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta conversion is compatible with the function part of an application. -/
theorem BetaEq.appL {n : Nat} {a b : Term n} (L : Term n) (h : a ≡β b) : a ⬝ L ≡β b ⬝ L := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.appL hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta conversion is compatible with the argument of an application. -/
theorem BetaEq.appR {n : Nat} {a b : Term n} (L : Term n) (h : a ≡β b) : L ⬝ a ≡β L ⬝ b := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.appR hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem BetaEq.app {n : Nat} {a a' b b' : Term n} (ha : a ≡β a') (hb : b ≡β b') :
    a ⬝ b ≡β a' ⬝ b' :=
  (BetaEq.appL b ha).trans (BetaEq.appR a' hb)

/-- **Church-Rosser, in its `↔` form**: two terms are convertible exactly when
they have a common reduct. -/
theorem betaeq_iff_join {n : Nat} {a b : Term n} : a ≡β b ↔ ∃ d, a —→* d ∧ b —→* d := by
  refine ⟨betaeq_join, fun ⟨d, ha, hb⟩ => ?_⟩
  exact (betastar_to_betaeq ha).trans (betastar_to_betaeq hb).symm

/-! ## 2. Normal forms -/

/-- A term is in normal form when no beta step applies to it. -/
def Normal {n : Nat} (M : Term n) : Prop := ∀ N, ¬ M —→ N

theorem Normal.var {n : Nat} (i : Fin n) : Normal (v# i) := by
  intro N h; cases h

theorem Normal.abs {n : Nat} {M : Term (n + 1)} (h : Normal M) : Normal (ƛ M) := by
  intro N hN
  cases hN with
  | abs hp => exact h _ hp

theorem Normal.of_abs {n : Nat} {M : Term (n + 1)} (h : Normal (ƛ M)) : Normal M :=
  fun _ hN => h _ (Beta.abs hN)

@[simp] theorem normal_abs_iff {n : Nat} {M : Term (n + 1)} : Normal (ƛ M) ↔ Normal M :=
  ⟨Normal.of_abs, Normal.abs⟩

/-- An application is normal as soon as both sides are and the left side is not
an abstraction (so that the application is not itself a redex). -/
theorem Normal.app {n : Nat} {a b : Term n} (ha : Normal a) (hb : Normal b)
    (hne : ∀ p : Term (n + 1), a ≠ ƛ p) : Normal (a ⬝ b) := by
  intro N hN
  cases hN with
  | basis M N => exact hne M rfl
  | appL h => exact ha _ h
  | appR h => exact hb _ h

/-- A normal term reduces only to itself. -/
theorem Normal.betastar_eq {n : Nat} {M N : Term n} (h : Normal M) (hMN : M —→* N) : N = M := by
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of normal forms**: a term has at most one normal form. -/
theorem normal_form_unique {n : Nat} {a b c : Term n} (hb : a —→* b) (hc : a —→* c)
    (hnb : Normal b) (hnc : Normal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := beta_church_rosser hb hc
  rw [← hnb.betastar_eq hbd, ← hnc.betastar_eq hcd]

/-- Two convertible normal terms are equal. -/
theorem betaeq_normal_eq {n : Nat} {a b : Term n} (h : a ≡β b) (hna : Normal a)
    (hnb : Normal b) : a = b := by
  obtain ⟨d, ha, hb⟩ := betaeq_join h
  rw [← hna.betastar_eq ha, ← hnb.betastar_eq hb]

/-- If a term is convertible with a normal term, it *reduces* to it. -/
theorem betaeq_normal_reduces {n : Nat} {a b : Term n} (h : a ≡β b) (hnb : Normal b) :
    a —→* b := by
  obtain ⟨d, ha, hb⟩ := betaeq_join h
  rwa [hnb.betastar_eq hb] at ha

/-- Terms in beta normal form, described inductively: a variable, an
abstraction of a normal form, or an application of a normal form which is not
an abstraction (so the application is no redex) to a normal form. -/
inductive NormalForm : {n : Nat} → Term n → Prop
  | var {n : Nat} (i : Fin n) : NormalForm (v# i)
  | abs {n : Nat} {a : Term (n + 1)} : NormalForm a → NormalForm (ƛ a)
  | app {n : Nat} {a b : Term n} : NormalForm a → NormalForm b →
      (∀ p : Term (n + 1), a ≠ ƛ p) → NormalForm (a ⬝ b)

theorem NormalForm.to_normal {n : Nat} {a : Term n} (h : NormalForm a) : Normal a := by
  induction h with
  | var i => exact Normal.var i
  | abs _ ih => exact ih.abs
  | app _ _ hne iha ihb => exact iha.app ihb hne

theorem Normal.to_normalForm {n : Nat} {a : Term n} (h : Normal a) : NormalForm a := by
  induction a with
  | var i => exact NormalForm.var i
  | abs s ih => exact (ih h.of_abs).abs
  | app x y ihx ihy =>
      have hx : Normal x := fun z hz => h _ (Beta.appL hz)
      have hy : Normal y := fun z hz => h _ (Beta.appR hz)
      refine (ihx hx).app (ihy hy) ?_
      rintro p rfl
      exact h _ (Beta.basis p y)

/-- **Characterisation of the normal forms**: a term admits no beta step
exactly when it is built by the grammar of normal forms. -/
theorem normalForm_iff_normal {n : Nat} {a : Term n} : NormalForm a ↔ Normal a :=
  ⟨NormalForm.to_normal, Normal.to_normalForm⟩

/-! ## 3. Consistency: not all terms are convertible -/

/-- The Church boolean `true = ƛx. ƛy. x`. -/
def ctrue {n : Nat} : Term n := ƛ (ƛ (v# 1))

/-- The Church boolean `false = ƛx. ƛy. y`. -/
def cfalse {n : Nat} : Term n := ƛ (ƛ (v# 0))

@[simp] theorem ren_ctrue {n m : Nat} (ρ : Fin n → Fin m) : ren ρ ctrue = ctrue := by
  simp [ctrue]
@[simp] theorem sub_ctrue {n m : Nat} (σ : Fin n → Term m) : sub σ ctrue = ctrue := by
  simp [ctrue]
@[simp] theorem betaSubst_ctrue {n : Nat} (N : Term n) : (ctrue : Term (n + 1)) [ N ] = ctrue :=
  sub_ctrue _
@[simp] theorem ren_cfalse {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cfalse = cfalse := by
  simp [cfalse]
@[simp] theorem sub_cfalse {n m : Nat} (σ : Fin n → Term m) : sub σ cfalse = cfalse := by
  simp [cfalse]
@[simp] theorem betaSubst_cfalse {n : Nat} (N : Term n) : (cfalse : Term (n + 1)) [ N ] = cfalse :=
  sub_cfalse _

theorem normal_ctrue {n : Nat} : Normal (ctrue : Term n) := (Normal.var 1).abs.abs

theorem normal_cfalse {n : Nat} : Normal (cfalse : Term n) := (Normal.var 0).abs.abs

theorem ctrue_ne_cfalse {n : Nat} : (ctrue : Term n) ≠ cfalse := by
  intro h
  simp only [ctrue, cfalse, Term.abs.injEq, Term.var.injEq] at h
  rw [fin_one_eq_succ] at h
  exact absurd h (Fin.succ_ne_zero 0)

/-- **Consistency of the lambda calculus**: `true` and `false` are not
convertible, so beta conversion does not identify all terms. -/
theorem ctrue_not_betaeq_cfalse {n : Nat} : ¬ ((ctrue : Term n) ≡β cfalse) :=
  fun h => ctrue_ne_cfalse (betaeq_normal_eq h normal_ctrue normal_cfalse)

/-! ## 4. A term without a normal form: `Ω = (ƛx. x x) (ƛx. x x)` -/

/-- `ƛx. x x`. -/
def selfApp : Term 0 := ƛ (v# 0 ⬝ v# 0)

/-- `Ω = (ƛx. x x) (ƛx. x x)`. -/
def Omega : Term 0 := selfApp ⬝ selfApp

theorem normal_selfApp : Normal selfApp :=
  ((Normal.var 0).app (Normal.var 0) (fun _ h => by cases h)).abs

/-- `Ω` reduces to itself. -/
theorem Omega_step : Omega —→ Omega := Beta.basis (v# 0 ⬝ v# 0) selfApp

/-- `Ω` reduces to *nothing else*. -/
theorem Omega_step_eq {N : Term 0} (h : Omega —→ N) : N = Omega := by
  cases h with
  | basis M N => rfl
  | appL hstep => exact absurd hstep (normal_selfApp _)
  | appR hstep => exact absurd hstep (normal_selfApp _)

theorem Omega_betastar_eq {N : Term 0} (h : Omega —→* N) : N = Omega := by
  induction h with
  | refl => rfl
  | tail _ step ih => subst ih; exact Omega_step_eq step

/-- `Ω` has no normal form: it is not (even weakly) normalizing. -/
theorem Omega_has_no_normal_form : ¬ ∃ N, Omega —→* N ∧ Normal N := by
  rintro ⟨N, hN, hnorm⟩
  rw [Omega_betastar_eq hN] at hnorm
  exact hnorm _ Omega_step

end FinScope
