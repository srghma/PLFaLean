-- Normal forms, uniqueness of normal forms, and consistency of the
-- exactly-scoped lambda calculus.
--
-- A term is *normal* when no beta step applies to it (`Normal`).  From the
-- Church-Rosser theorem one gets at once that a term has at most one normal
-- form (`normal_form_unique`), that two convertible normal forms are equal
-- (`betaeq_normal_eq`) and hence that the calculus is *consistent*: not all
-- terms are convertible, for instance the two Church booleans are not
-- (`ctrue_not_betaeq_cfalse`).
--
-- Not every term has a normal form: `Omega` reduces only to itself
-- (`Omega_betastar_eq`), so it has none (`Omega_has_no_normal_form`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Standardization

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 1. Beta conversion is a congruence
-- ====================================================================

theorem betastar_to_betaeq {a b : Scoped} (h : a —→* b) : a ≡β b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem beta_to_betaeq {a b : Scoped} (h : a —→ b) : a ≡β b := Relation.EqvGen.rel _ _ h

theorem BetaEq.symm {a b : Scoped} (h : a ≡β b) : b ≡β a := Relation.EqvGen.symm _ _ h

theorem BetaEq.trans {a b c : Scoped} (h₁ : a ≡β b) (h₂ : b ≡β c) : a ≡β c :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem BetaEq.refl (a : Scoped) : a ≡β a := Relation.EqvGen.refl _

/-- Beta conversion is compatible with abstraction. -/
theorem BetaEq.abs {a b : Scoped} (h : a ≡β b) : a.abs ≡β b.abs := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.abs hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta conversion is compatible with the left argument of an application. -/
theorem BetaEq.appr {a b : Scoped} (L : Scoped) (h : a ≡β b) : a.app L ≡β b.app L := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.appr L hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta conversion is compatible with the right argument of an application. -/
theorem BetaEq.appl {a b : Scoped} (L : Scoped) (h : a ≡β b) : L.app a ≡β L.app b := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (Beta.appl L hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem BetaEq.app {a a' b b' : Scoped} (ha : a ≡β a') (hb : b ≡β b') :
    a.app b ≡β a'.app b' :=
  (BetaEq.appr b ha).trans (BetaEq.appl a' hb)

/-- **Church-Rosser, in its `↔` form**: two terms are convertible exactly when
    they have a common reduct. -/
theorem betaeq_iff_join {a b : Scoped} : a ≡β b ↔ ∃ d, a —→* d ∧ b —→* d := by
  refine ⟨betaeq_join, fun ⟨d, ha, hb⟩ => ?_⟩
  exact (betastar_to_betaeq ha).trans (betastar_to_betaeq hb).symm

-- ====================================================================
-- 2. Normal forms
-- ====================================================================

/-- A term is in normal form when no beta step applies to it. -/
def Normal (M : Scoped) : Prop := ∀ N, ¬ M —→ N

theorem Normal.var (i : Nat) : Normal (Scoped.var i) :=
  fun _ h => Beta.var_inv h rfl

theorem Normal.abs {M : Scoped} (h : Normal M) : Normal M.abs := by
  intro _ hN
  obtain ⟨p', _, hp'⟩ := Beta.abs_inv' hN
  exact h _ hp'

theorem Normal.of_abs {M : Scoped} (h : Normal M.abs) : Normal M :=
  fun _ hN => h _ (Beta.abs hN)

@[simp] theorem normal_abs_iff {M : Scoped} : Normal M.abs ↔ Normal M :=
  ⟨Normal.of_abs, Normal.abs⟩

/-- An application is normal as soon as both sides are and the left side is not
    an abstraction (so that the application is not itself a redex). -/
theorem Normal.app {a b : Scoped} (ha : Normal a) (hb : Normal b)
    (hne : ∀ p, a ≠ Scoped.abs p) : Normal (a.app b) := by
  intro N hN
  rcases Beta.app_inv' hN with ⟨a', _, h⟩ | ⟨b', _, h⟩ | ⟨p, hp, _⟩
  · exact ha _ h
  · exact hb _ h
  · exact hne p hp

/-- A normal term reduces only to itself. -/
theorem Normal.betastar_eq {M N : Scoped} (h : Normal M) (hMN : M —→* N) : N = M := by
  -- by induction on the reduction, rather than through Mathlib's
  -- `Relation.ReflTransGen.cases_head`, whose proof uses `Classical.choice`
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of normal forms**: a term has at most one normal form. -/
theorem normal_form_unique {a b c : Scoped} (hb : a —→* b) (hc : a —→* c)
    (hnb : Normal b) (hnc : Normal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := beta_church_rosser hb hc
  rw [← hnb.betastar_eq hbd, ← hnc.betastar_eq hcd]

/-- Two convertible normal terms are equal. -/
theorem betaeq_normal_eq {a b : Scoped} (h : a ≡β b) (hna : Normal a) (hnb : Normal b) :
    a = b := by
  obtain ⟨d, ha, hb⟩ := betaeq_join h
  rw [← hna.betastar_eq ha, ← hnb.betastar_eq hb]

/-- If a term is convertible with a normal term, it *reduces* to it. -/
theorem betaeq_normal_reduces {a b : Scoped} (h : a ≡β b) (hnb : Normal b) : a —→* b := by
  obtain ⟨d, ha, hb⟩ := betaeq_join h
  rwa [hnb.betastar_eq hb] at ha

/-- Terms in beta normal form, described inductively: a variable, an
    abstraction of a normal form, or an application of a normal form which is
    not an abstraction (so the application is no redex) to a normal form. -/
inductive NormalForm : Scoped → Prop
  | var (i : Nat) : NormalForm (Scoped.var i)
  | abs {a : Scoped} : NormalForm a → NormalForm a.abs
  | app {a b : Scoped} : NormalForm a → NormalForm b → (∀ p, a ≠ Scoped.abs p) →
      NormalForm (a.app b)

theorem NormalForm.to_normal {a : Scoped} (h : NormalForm a) : Normal a := by
  induction h with
  | var i => exact Normal.var i
  | abs _ ih => exact ih.abs
  | app _ _ hne iha ihb => exact iha.app ihb hne

theorem Normal.to_normalForm {a : Scoped} (h : Normal a) : NormalForm a := by
  induction a using Scoped.ind with
  | var i => exact NormalForm.var i
  | abs s ih => exact (ih h.of_abs).abs
  | app x y ihx ihy =>
      have hx : Normal x := fun z hz => h _ (Beta.appr y hz)
      have hy : Normal y := fun z hz => h _ (Beta.appl x hz)
      refine (ihx hx).app (ihy hy) ?_
      rintro p rfl
      exact h _ (Beta.basis' p y)

/-- **Characterisation of the normal forms**: a term admits no beta step
    exactly when it is built by the grammar of normal forms. -/
theorem normalForm_iff_normal {a : Scoped} : NormalForm a ↔ Normal a :=
  ⟨NormalForm.to_normal, Normal.to_normalForm⟩

-- ====================================================================
-- 3. Consistency: not all terms are convertible
-- ====================================================================

/-- The Church boolean `true = ƛx. ƛy. x`. -/
def ctrue : Scoped := Scoped.abs (Scoped.abs (Scoped.var 1))

/-- The Church boolean `false = ƛx. ƛy. y`. -/
def cfalse : Scoped := Scoped.abs (Scoped.abs (Scoped.var 0))

theorem normal_ctrue : Normal ctrue := (Normal.var 1).abs.abs

theorem normal_cfalse : Normal cfalse := (Normal.var 0).abs.abs

theorem ctrue_ne_cfalse : ctrue ≠ cfalse := by
  intro h
  simp only [ctrue, cfalse, Scoped.abs_eq_abs, Scoped.var_eq_var] at h
  exact absurd h (by decide)

/-- **Consistency of the lambda calculus**: `true` and `false` are not
    convertible, so beta conversion does not identify all terms. -/
theorem ctrue_not_betaeq_cfalse : ¬ (ctrue ≡β cfalse) :=
  fun h => ctrue_ne_cfalse (betaeq_normal_eq h normal_ctrue normal_cfalse)

-- ====================================================================
-- 4. A term without a normal form: `Ω = (ƛx. x x) (ƛx. x x)`
-- ====================================================================

/-- `ƛx. x x`. -/
def selfApp : Scoped := Scoped.abs (Scoped.app (Scoped.var 0) (Scoped.var 0))

/-- `Ω = (ƛx. x x) (ƛx. x x)`. -/
def Omega : Scoped := Scoped.app selfApp selfApp

theorem normal_selfApp : Normal selfApp :=
  ((Normal.var 0).app (Normal.var 0) (fun _ => Scoped.var_ne_abs)).abs

/-- `Ω` reduces to itself. -/
theorem Omega_step : Omega —→ Omega :=
  Beta.basis' (Scoped.app (Scoped.var 0) (Scoped.var 0)) selfApp

/-- `Ω` reduces to *nothing else*. -/
theorem Omega_step_eq {N : Scoped} (h : Omega —→ N) : N = Omega := by
  rcases Beta.app_inv' h with ⟨a', _, hstep⟩ | ⟨b', _, hstep⟩ | ⟨p, hp, hN⟩
  · exact absurd hstep (normal_selfApp _)
  · exact absurd hstep (normal_selfApp _)
  · have : p = Scoped.app (Scoped.var 0) (Scoped.var 0) :=
      (Scoped.abs_eq_abs.mp hp.symm)
    subst this
    exact hN

theorem Omega_betastar_eq {N : Scoped} (h : Omega —→* N) : N = Omega := by
  induction h with
  | refl => rfl
  | tail _ step ih => subst ih; exact Omega_step_eq step

/-- `Ω` has no normal form: it is not (even weakly) normalizing. -/
theorem Omega_has_no_normal_form : ¬ ∃ N, Omega —→* N ∧ Normal N := by
  rintro ⟨N, hN, hnorm⟩
  rw [Omega_betastar_eq hN] at hnorm
  exact hnorm _ Omega_step

end IwilareNatIsExactScope
