-- Decidability of being a normal form, and an executable normal order
-- evaluator.
--
-- `Scoped.isNormalB` decides `Normal` (`isNormalB_iff_normal`), and
-- `Scoped.lstep` computes the leftmost redex contraction, so that iterating it
-- is normal order evaluation.  The evaluator `Scoped.eval fuel` is proved
--
--   * sound      : if it answers, its answer is a normal form reached from the
--                  input (`eval_sound`), and
--   * complete   : if the input has a normal form at all, the evaluator finds
--                  it, given enough fuel (`eval_complete`).
--
-- Together: **having a normal form is semi-decidable, by normal order
-- evaluation** (`has_normal_form_iff_eval`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Leftmost
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchData

@[expose] public section

namespace IwilareNatIsExactScope

namespace Term

/-- Is the term an abstraction? -/
def isAbsB : {n : Nat} → Term n → Bool
  | _, .var _ => false
  | _, .abs _ => true
  | _, .app _ _ => false

/-- Is the term in beta normal form? -/
def isNormalB : {n : Nat} → Term n → Bool
  | _, .var _ => true
  | _, .abs t => isNormalB t
  | _, .app a b => !isAbsB a && isNormalB a && isNormalB b

/-- Contract the leftmost redex, if there is one. -/
def lstepT : {n : Nat} → Term n → Option Scoped
  | _, .var _ => none
  | _, .abs t => (lstepT t).map Scoped.abs
  | _, .app (.abs p) q => some (Scoped.sub0 ⟨_, q⟩ ⟨_, p⟩)
  | _, .app a b =>
      match lstepT a with
      | some a' => some (Scoped.app a' ⟨_, b⟩)
      | none => (lstepT b).map (Scoped.app ⟨_, a⟩)

end Term

namespace Scoped

/-- Is the term an abstraction? -/
def isAbsB (s : Scoped) : Bool := Term.isAbsB s.2

/-- Is the term in beta normal form? -/
def isNormalB (s : Scoped) : Bool := Term.isNormalB s.2

/-- Contract the leftmost redex, if there is one. -/
def lstep (s : Scoped) : Option Scoped := Term.lstepT s.2

@[simp] theorem isAbsB_var (i : Nat) : isAbsB (var i) = false := rfl
@[simp] theorem isAbsB_abs (s : Scoped) : isAbsB (abs s) = true := rfl
@[simp] theorem isAbsB_app (s t : Scoped) : isAbsB (app s t) = false := rfl

@[simp] theorem isNormalB_var (i : Nat) : isNormalB (var i) = true := rfl
@[simp] theorem isNormalB_abs (s : Scoped) : isNormalB (abs s) = isNormalB s := rfl
@[simp] theorem isNormalB_app (s t : Scoped) :
    isNormalB (app s t) = (!isAbsB s && isNormalB s && isNormalB t) := rfl

@[simp] theorem lstep_var (i : Nat) : lstep (var i) = none := rfl
@[simp] theorem lstep_abs (s : Scoped) : lstep (abs s) = (lstep s).map abs := rfl
@[simp] theorem lstep_app_abs (p q : Scoped) : lstep (app (abs p) q) = some (sub0 q p) := rfl

theorem lstep_app_of_not_isAbs {a : Scoped} (ha : isAbsB a = false) (b : Scoped) :
    lstep (app a b) =
      match lstep a with
      | some a' => some (app a' b)
      | none => (lstep b).map (app a) := by
  obtain ⟨n, t⟩ := a
  cases t with
  | var i => rfl
  | abs t => exact absurd ha (by simp [isAbsB, Term.isAbsB])
  | app x y => rfl

end Scoped

-- ====================================================================
-- 1. `isAbsB` and `isNormalB` are correct
-- ====================================================================

theorem Scoped.isAbsB_iff {s : Scoped} : s.isAbsB = true ↔ IsAbs s := by
  induction s using Scoped.ind with
  | var i =>
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro ⟨p, hp⟩
      exact absurd hp Scoped.var_ne_abs
  | abs s _ => exact ⟨fun _ => ⟨s, rfl⟩, fun _ => rfl⟩
  | app a b _ _ =>
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro ⟨p, hp⟩
      exact absurd hp Scoped.app_ne_abs

/-- **Being in normal form is decidable.** -/
theorem Scoped.isNormalB_iff_normal {s : Scoped} : s.isNormalB = true ↔ Normal s := by
  induction s using Scoped.ind with
  | var i => simpa using Normal.var i
  | abs s ih => simp [ih]
  | app a b iha ihb =>
      simp only [isNormalB_app, Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ⟨⟨hna, ha⟩, hb⟩
        exact (iha.mp ha).app (ihb.mp hb) fun p hp =>
          by simp [hp, isAbsB_abs] at hna
      · intro h
        obtain ⟨ha, hb, hna⟩ := h.app_inv
        exact ⟨⟨by
          cases hab : a.isAbsB with
          | false => rfl
          | true => exact absurd (Scoped.isAbsB_iff.mp hab) hna, iha.mpr ha⟩, ihb.mpr hb⟩

instance : DecidablePred Normal := fun s =>
  decidable_of_iff (s.isNormalB = true) Scoped.isNormalB_iff_normal

-- ====================================================================
-- 2. `lstep` computes the leftmost step
-- ====================================================================

/-- If `lstep` gives up, the term is normal. -/
theorem Scoped.lstep_none_normal {s : Scoped} (h : s.lstep = none) : Normal s := by
  induction s using Scoped.ind with
  | var i => exact Normal.var i
  | abs s ih =>
      simp only [lstep_abs, Option.map_eq_none_iff] at h
      exact (ih h).abs
  | app a b iha ihb =>
      by_cases hab : a.isAbsB = true
      · obtain ⟨p, rfl⟩ := Scoped.isAbsB_iff.mp hab
        rw [lstep_app_abs] at h
        exact absurd h (by simp)
      · rw [Bool.not_eq_true] at hab
        rw [lstep_app_of_not_isAbs hab] at h
        cases ha : a.lstep with
        | some a' => rw [ha] at h; exact absurd h (by simp)
        | none =>
            rw [ha] at h
            simp only [Option.map_eq_none_iff] at h
            refine (iha ha).app (ihb h) ?_
            intro p hp
            exact absurd (Scoped.isAbsB_iff.mpr ⟨p, hp⟩) (by simp [hab])

/-- If `lstep` answers, its answer is the leftmost reduct. -/
theorem Scoped.lstep_some {s t : Scoped} (h : s.lstep = some t) : s —→ₗ t := by
  induction s using Scoped.ind generalizing t with
  | var i => simp at h
  | abs s ih =>
      simp only [lstep_abs, Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact Leftmost.abs (ih hu)
  | app a b iha ihb =>
      by_cases hab : a.isAbsB = true
      · obtain ⟨p, rfl⟩ := Scoped.isAbsB_iff.mp hab
        rw [lstep_app_abs] at h
        cases h
        exact Leftmost.basis p b
      · rw [Bool.not_eq_true] at hab
        have hna : ¬ IsAbs a := fun hx => by simp [Scoped.isAbsB_iff.mpr hx] at hab
        rw [lstep_app_of_not_isAbs hab] at h
        cases ha : a.lstep with
        | some a' =>
            rw [ha] at h
            cases h
            exact Leftmost.appr b hna (iha ha)
        | none =>
            rw [ha] at h
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨u, hu, rfl⟩ := h
            exact Leftmost.appl (Scoped.lstep_none_normal ha) hna (ihb hu)

/-- `lstep` is total on non-normal terms. -/
theorem Scoped.lstep_isSome_of_not_normal {s : Scoped} (h : ¬ Normal s) : ∃ t, s.lstep = some t := by
  cases hs : s.lstep with
  | none => exact absurd (Scoped.lstep_none_normal hs) h
  | some t => exact ⟨t, rfl⟩

/-- `lstep` computes *the* leftmost step. -/
theorem Scoped.lstep_eq_some_iff {s t : Scoped} : s.lstep = some t ↔ s —→ₗ t := by
  refine ⟨Scoped.lstep_some, fun h => ?_⟩
  cases hs : s.lstep with
  | none => exact absurd h.to_beta (Scoped.lstep_none_normal hs _)
  | some u => rw [(Scoped.lstep_some hs).deterministic h]

-- ====================================================================
-- 3. The normal order evaluator
-- ====================================================================

/-- Normal order evaluation: contract the leftmost redex at most `fuel` times,
    and answer as soon as a normal form is reached. -/
def Scoped.eval : Nat → Scoped → Option Scoped
  | 0, _ => none
  | fuel + 1, s =>
      match s.lstep with
      | none => some s
      | some t => Scoped.eval fuel t

@[simp] theorem Scoped.eval_zero (s : Scoped) : Scoped.eval 0 s = none := rfl

theorem Scoped.eval_succ (fuel : Nat) (s : Scoped) :
    Scoped.eval (fuel + 1) s =
      match s.lstep with
      | none => some s
      | some t => Scoped.eval fuel t := rfl

/-- **Soundness of normal order evaluation**: whatever the evaluator answers is
    a normal form, reached from the input by leftmost reduction. -/
theorem eval_sound : ∀ (fuel : Nat) {s t : Scoped}, Scoped.eval fuel s = some t →
    s —→ₗ* t ∧ Normal t := by
  intro fuel
  induction fuel with
  | zero => intro s t h; simp at h
  | succ fuel ih =>
      intro s t h
      rw [Scoped.eval_succ] at h
      cases hs : s.lstep with
      | none =>
          rw [hs] at h
          cases h
          exact ⟨Relation.ReflTransGen.refl, Scoped.lstep_none_normal hs⟩
      | some u =>
          rw [hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Scoped.lstep_some hs) hred, hnorm⟩

/-- **Completeness of normal order evaluation**: if the input leftmost-reduces
    to a normal form, the evaluator finds it, given enough fuel. -/
theorem eval_complete {s t : Scoped} (h : s —→ₗ* t) (ht : Normal t) :
    ∃ fuel, Scoped.eval fuel s = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, ?_⟩
      rw [Scoped.eval_succ]
      cases hs : t.lstep with
      | none => rfl
      | some u => exact absurd (Scoped.lstep_some hs).to_beta (ht u)
  | head hstep _ ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [Scoped.eval_succ, Scoped.lstep_eq_some_iff.mpr hstep]
      exact hfuel

/-- **Having a normal form is semi-decidable**: a term has a normal form
    exactly when normal order evaluation of it terminates. -/
theorem has_normal_form_iff_eval {s : Scoped} :
    (∃ t, s —→* t ∧ Normal t) ↔ ∃ fuel t, Scoped.eval fuel s = some t := by
  constructor
  · rintro ⟨t, hred, ht⟩
    obtain ⟨fuel, hfuel⟩ := eval_complete (leftmost_normalization hred ht) ht
    exact ⟨fuel, t, hfuel⟩
  · rintro ⟨fuel, t, h⟩
    obtain ⟨hred, ht⟩ := eval_sound fuel h
    exact ⟨t, hred.to_betastar, ht⟩

-- ====================================================================
-- 4. The evaluator at work
-- ====================================================================

section Examples

/-- Kleene's predecessor, computed. -/
example : Scoped.eval 200 (Scoped.app Scoped.cpred (Scoped.church 3))
    = some (Scoped.church 2) := rfl

/-- Multiplication, computed. -/
example : Scoped.eval 200 (Scoped.app (Scoped.app Scoped.cmul (Scoped.church 3))
    (Scoped.church 4)) = some (Scoped.church 12) := rfl

/-- The test for zero, computed. -/
example : Scoped.eval 200 (Scoped.app Scoped.ciszero (Scoped.church 5)) = some cfalse := rfl

/-- The first projection of a pair, computed. -/
example : Scoped.eval 200 (Scoped.app Scoped.cfst
    (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 1)) (Scoped.church 7)))
    = some (Scoped.church 1) := rfl

set_option maxRecDepth 10000 in
/-- `Ω` never terminates, whatever the fuel. -/
example : Scoped.eval 200 Omega = none := rfl

end Examples

end IwilareNatIsExactScope
