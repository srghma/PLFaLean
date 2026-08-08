-- Decidability of being a normal form, and an executable normal order
-- evaluator, for the scope-bounded (`Fin`-indexed) calculus.
--
-- `isNormalB` decides `Normal` (`isNormalB_iff_normal`), and `lstep` computes
-- the leftmost redex contraction, so that iterating it is normal order
-- evaluation.  The evaluator `eval fuel` is proved
--
--   * sound      : if it answers, its answer is a normal form reached from the
--                  input (`eval_sound`), and
--   * complete   : if the input has a normal form at all, the evaluator finds
--                  it, given enough fuel (`eval_complete`).
--
-- Together: **having a normal form is semi-decidable, by normal order
-- evaluation** (`has_normal_form_iff_eval`).
--
-- As for `evalCBN`, the evaluator has type `Nat → Term n → Option (Term n)`:
-- evaluation never changes the scope.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Leftmost
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchData

@[expose] public section

namespace FinScope

open Term

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
def lstep : {n : Nat} → Term n → Option (Term n)
  | _, .var _ => none
  | _, .abs t => (lstep t).map Term.abs
  | _, .app (.abs p) q => some (p [ q ])
  | _, .app a b =>
      match lstep a with
      | some a' => some (a' ⬝ b)
      | none => (lstep b).map (a ⬝ ·)

@[simp] theorem isAbsB_var {n : Nat} (i : Fin n) : isAbsB (v# i) = false := rfl
@[simp] theorem isAbsB_abs {n : Nat} (s : Term (n + 1)) : isAbsB (ƛ s) = true := rfl
@[simp] theorem isAbsB_app {n : Nat} (s t : Term n) : isAbsB (s ⬝ t) = false := rfl

@[simp] theorem isNormalB_var {n : Nat} (i : Fin n) : isNormalB (v# i) = true := rfl
@[simp] theorem isNormalB_abs {n : Nat} (s : Term (n + 1)) : isNormalB (ƛ s) = isNormalB s := rfl
@[simp] theorem isNormalB_app {n : Nat} (s t : Term n) :
    isNormalB (s ⬝ t) = (!isAbsB s && isNormalB s && isNormalB t) := rfl

@[simp] theorem lstep_var {n : Nat} (i : Fin n) : lstep (v# i) = none := by simp [lstep]
@[simp] theorem lstep_abs {n : Nat} (s : Term (n + 1)) :
    lstep (ƛ s) = (lstep s).map Term.abs := by simp [lstep]
@[simp] theorem lstep_app_abs {n : Nat} (p : Term (n + 1)) (q : Term n) :
    lstep ((ƛ p) ⬝ q) = some (p [ q ]) := by simp [lstep]

theorem lstep_app_of_not_isAbs {n : Nat} {a : Term n} (ha : isAbsB a = false) (b : Term n) :
    lstep (a ⬝ b) =
      match lstep a with
      | some a' => some (a' ⬝ b)
      | none => (lstep b).map (a ⬝ ·) := by
  cases a with
  | var i => simp [lstep]
  | abs t => exact absurd ha (by simp)
  | app x y => simp [lstep]

end Term

/-! ## 1. `isAbsB` and `isNormalB` are correct -/

theorem Term.isAbsB_iff {n : Nat} {s : Term n} : isAbsB s = true ↔ IsAbs s := by
  cases s with
  | var i =>
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro ⟨p, hp⟩
      exact absurd hp (by simp)
  | abs s => exact ⟨fun _ => ⟨s, rfl⟩, fun _ => rfl⟩
  | app a b =>
      refine ⟨fun h => absurd h (by simp), ?_⟩
      rintro ⟨p, hp⟩
      exact absurd hp (by simp)

/-- **Being in normal form is decidable.** -/
theorem Term.isNormalB_iff_normal {n : Nat} {s : Term n} : isNormalB s = true ↔ Normal s := by
  induction s with
  | var i => simpa using Normal.var i
  | abs s ih => simp [ih]
  | app a b iha ihb =>
      simp only [isNormalB_app, Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ⟨⟨hna, ha⟩, hb⟩
        exact (iha.mp ha).app (ihb.mp hb) fun p hp => by simp [hp] at hna
      · intro h
        obtain ⟨ha, hb, hna⟩ := h.app_inv
        refine ⟨⟨?_, iha.mpr ha⟩, ihb.mpr hb⟩
        cases hab : isAbsB a with
        | false => rfl
        | true => exact absurd (Term.isAbsB_iff.mp hab) hna

instance {n : Nat} : DecidablePred (@Normal n) := fun s =>
  decidable_of_iff (Term.isNormalB s = true) Term.isNormalB_iff_normal

/-! ## 2. `lstep` computes the leftmost step -/

/-- If `lstep` gives up, the term is normal. -/
theorem Term.lstep_none_normal {n : Nat} {s : Term n} (h : lstep s = none) : Normal s := by
  induction s with
  | var i => exact Normal.var i
  | abs s ih =>
      simp only [lstep_abs, Option.map_eq_none_iff] at h
      exact (ih h).abs
  | app a b iha ihb =>
      cases hab : isAbsB a with
      | true =>
          obtain ⟨p, rfl⟩ := Term.isAbsB_iff.mp hab
          rw [lstep_app_abs] at h
          exact absurd h (by simp)
      | false =>
          rw [lstep_app_of_not_isAbs hab] at h
          cases ha : lstep a with
          | some a' => rw [ha] at h; exact absurd h (by simp)
          | none =>
              rw [ha] at h
              simp only [Option.map_eq_none_iff] at h
              refine (iha ha).app (ihb h) ?_
              intro p hp
              exact absurd (Term.isAbsB_iff.mpr ⟨p, hp⟩) (by simp [hab])

/-- If `lstep` answers, its answer is the leftmost reduct. -/
theorem Term.lstep_some {n : Nat} {s t : Term n} (h : lstep s = some t) : s —→ₗ t := by
  induction s with
  | var i => simp at h
  | abs s ih =>
      simp only [lstep_abs, Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact Leftmost.abs (ih hu)
  | app a b iha ihb =>
      cases hab : isAbsB a with
      | true =>
          obtain ⟨p, rfl⟩ := Term.isAbsB_iff.mp hab
          rw [lstep_app_abs] at h
          cases h
          exact Leftmost.basis p b
      | false =>
          have hna : ¬ IsAbs a := fun hx => by simp [Term.isAbsB_iff.mpr hx] at hab
          rw [lstep_app_of_not_isAbs hab] at h
          cases ha : lstep a with
          | some a' =>
              rw [ha] at h
              cases h
              exact Leftmost.appL b hna (iha ha)
          | none =>
              rw [ha] at h
              simp only [Option.map_eq_some_iff] at h
              obtain ⟨u, hu, rfl⟩ := h
              exact Leftmost.appR (Term.lstep_none_normal ha) hna (ihb hu)

/-- `lstep` is total on non-normal terms. -/
theorem Term.lstep_isSome_of_not_normal {n : Nat} {s : Term n} (h : ¬ Normal s) :
    ∃ t, lstep s = some t := by
  cases hs : lstep s with
  | none => exact absurd (Term.lstep_none_normal hs) h
  | some t => exact ⟨t, rfl⟩

/-- `lstep` computes *the* leftmost step. -/
theorem Term.lstep_eq_some_iff {n : Nat} {s t : Term n} : lstep s = some t ↔ s —→ₗ t := by
  refine ⟨Term.lstep_some, fun h => ?_⟩
  cases hs : lstep s with
  | none => exact absurd h.to_beta (Term.lstep_none_normal hs _)
  | some u => rw [(Term.lstep_some hs).deterministic h]

/-! ## 3. The normal order evaluator -/

/-- Normal order evaluation: contract the leftmost redex at most `fuel` times,
    and answer as soon as a normal form is reached. -/
def Term.eval {n : Nat} : Nat → Term n → Option (Term n)
  | 0, _ => none
  | fuel + 1, s =>
      match lstep s with
      | none => some s
      | some t => eval fuel t

@[simp] theorem Term.eval_zero {n : Nat} (s : Term n) : eval 0 s = none := rfl

theorem Term.eval_succ {n : Nat} (fuel : Nat) (s : Term n) :
    eval (fuel + 1) s =
      match lstep s with
      | none => some s
      | some t => eval fuel t := rfl

/-- **Soundness of normal order evaluation**: whatever the evaluator answers is
    a normal form, reached from the input by leftmost reduction. -/
theorem eval_sound {n : Nat} : ∀ (fuel : Nat) {s t : Term n}, Term.eval fuel s = some t →
    s —→ₗ* t ∧ Normal t := by
  intro fuel
  induction fuel with
  | zero => intro s t h; simp at h
  | succ fuel ih =>
      intro s t h
      rw [Term.eval_succ] at h
      cases hs : Term.lstep s with
      | none =>
          rw [hs] at h
          cases h
          exact ⟨.refl, Term.lstep_none_normal hs⟩
      | some u =>
          rw [hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Term.lstep_some hs) hred, hnorm⟩

/-- **Completeness of normal order evaluation**: if the input leftmost-reduces
    to a normal form, the evaluator finds it, given enough fuel. -/
theorem eval_complete {n : Nat} {s t : Term n} (h : s —→ₗ* t) (ht : Normal t) :
    ∃ fuel, Term.eval fuel s = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, ?_⟩
      rw [Term.eval_succ]
      cases hs : Term.lstep t with
      | none => rfl
      | some u => exact absurd (Term.lstep_some hs).to_beta (ht u)
  | head hstep _ ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [Term.eval_succ, Term.lstep_eq_some_iff.mpr hstep]
      exact hfuel

/-- **Having a normal form is semi-decidable**: a term has a normal form
    exactly when normal order evaluation of it terminates. -/
theorem has_normal_form_iff_eval {n : Nat} {s : Term n} :
    (∃ t, s —→* t ∧ Normal t) ↔ ∃ fuel t, Term.eval fuel s = some t := by
  constructor
  · rintro ⟨t, hred, ht⟩
    obtain ⟨fuel, hfuel⟩ := eval_complete (leftmost_normalization hred ht) ht
    exact ⟨fuel, t, hfuel⟩
  · rintro ⟨fuel, t, h⟩
    obtain ⟨hred, ht⟩ := eval_sound fuel h
    exact ⟨t, hred.to_betaStar, ht⟩

/-! ## 4. The evaluator at work -/

section Examples

/-- Kleene's predecessor, computed. -/
example : Term.eval 200 (cpred ⬝ church 3 : Term 0) = some (church 2) := by decide

/-- Multiplication, computed. -/
example : Term.eval 200 (cmul ⬝ church 3 ⬝ church 4 : Term 0) = some (church 12) := by decide

/-- The test for zero, computed. -/
example : Term.eval 200 (ciszero ⬝ church 5 : Term 0) = some cfalse := by decide

/-- The first projection of a pair, computed. -/
example : Term.eval 200 (cfst ⬝ (cpair ⬝ church 1 ⬝ church 7) : Term 0)
    = some (church 1) := by decide

set_option maxRecDepth 10000 in
/-- `Ω` never terminates, whatever the fuel. -/
example : Term.eval 200 Omega = none := by decide

end Examples

end FinScope
