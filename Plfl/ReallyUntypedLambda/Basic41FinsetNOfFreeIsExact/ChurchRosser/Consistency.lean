module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Basic

@[expose] public section

/-!
# Normal forms, the β-quotient, and consistency

Consequences of confluence, obtained by reusing Mathlib's relational API:

* `Basic41Finset.NormalS` — being a normal form, i.e. admitting no β-step;
  `Relation.reflTransGen_iff_eq` immediately gives that a normal form reduces
  only to itself;
* `Basic41Finset.unique_normal_form` — normal forms are unique (from
  `beta_confluence_S`);
* `Basic41Finset.betaEqS_eq_of_normal` — β-convertible normal forms are equal;
* `Basic41Finset.betaSetoid` / `Basic41Finset.BetaQuot` — the setoid
  `Relation.EqvGen.setoid` of β-conversion and the quotient of terms by it, with
  `abs` and `app` descending to the quotient via `Quotient.map`/`Quotient.map₂`;
* `Basic41Finset.consistency` — the β-theory is consistent: `#0` and `λ.#0` are
  not β-convertible, so the quotient has at least two elements.
-/

namespace Basic41FinsetNOfFreeIsExact

/-! ### Congruence rules for β-conversion -/

theorem betaEqS_abs {t u : SigmaTerm} (h : t ≡βs u) : t.abs ≡βs u.abs := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (StepS.abs h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem betaEqS_app_left {t t' : SigmaTerm} (h : t ≡βs t') (u : SigmaTerm) :
    t.app u ≡βs t'.app u := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (StepS.app_left h u)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem betaEqS_app_right (t : SigmaTerm) {u u' : SigmaTerm} (h : u ≡βs u') :
    t.app u ≡βs t.app u' := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (StepS.app_right t h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem betaEqS_app {t t' u u' : SigmaTerm} (h1 : t ≡βs t') (h2 : u ≡βs u') :
    t.app u ≡βs t'.app u' :=
  Relation.EqvGen.trans _ _ _ (betaEqS_app_left h1 u) (betaEqS_app_right t' h2)

/-! ### Normal forms -/

/-- A term is in normal form when no β-step applies to it. -/
def NormalS (t : SigmaTerm) : Prop := ∀ u, ¬ (t →βs u)

/-- A normal form reduces only to itself (Mathlib's
`Relation.reflTransGen_iff_eq`). -/
theorem NormalS.eq_of_betaStarS {t u : SigmaTerm} (h : NormalS t) (hs : t ⇒βs* u) : u = t :=
  (Relation.reflTransGen_iff_eq h).mp hs

theorem normalS_var (i : Nat) : NormalS (SigmaTerm.var i) := by
  intro u h
  refine StepS.induction (motive := fun a _ => ∀ j : Nat, a ≠ SigmaTerm.var j)
    ?_ ?_ ?_ ?_ h i rfl
  · intro t u j; simp
  · intro t t' u _ _ j; simp
  · intro t u u' _ _ j; simp
  · intro t u _ _ j; simp

/-- Inversion: a β-step out of an abstraction happens in its body. -/
theorem stepS_abs_inv {t w : SigmaTerm} (h : t.abs →βs w) :
    ∃ u, w = SigmaTerm.abs u ∧ t →βs u := by
  refine StepS.induction
    (motive := fun a b => ∀ t, a = SigmaTerm.abs t → ∃ u, b = SigmaTerm.abs u ∧ t →βs u)
    ?_ ?_ ?_ ?_ h t rfl
  · intro a b t ht; exact absurd ht (by simp)
  · intro a a' b _ _ t ht; exact absurd ht (by simp)
  · intro a b b' _ _ t ht; exact absurd ht (by simp)
  · intro a b hab _ t ht
    exact ⟨b, rfl, by rwa [SigmaTerm.abs_inj.mp ht] at hab⟩

theorem NormalS.abs {t : SigmaTerm} (h : NormalS t) : NormalS t.abs := by
  intro w hw
  obtain ⟨u, _, hu⟩ := stepS_abs_inv hw
  exact h u hu

/-- **Uniqueness of normal forms**, a consequence of confluence. -/
theorem unique_normal_form {t u1 u2 : SigmaTerm} (h1 : t ⇒βs* u1) (h2 : t ⇒βs* u2)
    (n1 : NormalS u1) (n2 : NormalS u2) : u1 = u2 := by
  obtain ⟨d, hd1, hd2⟩ := beta_confluence_S h1 h2
  rw [← n1.eq_of_betaStarS hd1, ← n2.eq_of_betaStarS hd2]

/-- **Church-Rosser for normal forms**: β-convertible normal forms are equal. -/
theorem betaEqS_eq_of_normal {t u : SigmaTerm} (h : t ≡βs u) (n1 : NormalS t) (n2 : NormalS u) :
    t = u := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser_S h
  rw [← n1.eq_of_betaStarS hd1, ← n2.eq_of_betaStarS hd2]

/-! ### The quotient of terms by β-conversion -/

/-- The setoid of β-conversion: Mathlib's `Relation.EqvGen.setoid` of `StepS`. -/
def betaSetoid : Setoid SigmaTerm := Relation.EqvGen.setoid StepS

theorem betaSetoid_iff {t u : SigmaTerm} : betaSetoid.r t u ↔ t ≡βs u := Iff.rfl

/-- λ-terms modulo β-conversion. -/
def BetaQuot : Type := Quotient betaSetoid

/-- The β-equivalence class of a term. -/
def BetaQuot.mk (t : SigmaTerm) : BetaQuot := Quotient.mk betaSetoid t

theorem BetaQuot.mk_eq_mk {t u : SigmaTerm} : BetaQuot.mk t = BetaQuot.mk u ↔ t ≡βs u :=
  Quotient.eq (r := betaSetoid)

/-- Two terms have the same β-equivalence class exactly when they are joinable:
this is the Church-Rosser theorem. -/
theorem BetaQuot.mk_eq_mk_iff_join {t u : SigmaTerm} :
    BetaQuot.mk t = BetaQuot.mk u ↔ BetaJoinS t u :=
  BetaQuot.mk_eq_mk.trans ⟨church_rosser_S, fun ⟨_, h1, h2⟩ =>
    Relation.EqvGen.trans _ _ _ (eqvGen_of_reflTransGen h1)
      (Relation.EqvGen.symm _ _ (eqvGen_of_reflTransGen h2))⟩

/-- Abstraction descends to the quotient. -/
def BetaQuot.abs : BetaQuot → BetaQuot :=
  Quotient.map SigmaTerm.abs (fun _ _ h => betaEqS_abs h)

/-- Application descends to the quotient. -/
def BetaQuot.app : BetaQuot → BetaQuot → BetaQuot :=
  Quotient.map₂ SigmaTerm.app (fun _ _ h1 _ _ h2 => betaEqS_app h1 h2)

@[simp] theorem BetaQuot.abs_mk (t : SigmaTerm) :
    BetaQuot.abs (BetaQuot.mk t) = BetaQuot.mk t.abs := rfl

@[simp] theorem BetaQuot.app_mk (t u : SigmaTerm) :
    BetaQuot.app (BetaQuot.mk t) (BetaQuot.mk u) = BetaQuot.mk (t.app u) := rfl

/-! ### Consistency -/

/-- **Consistency of the β-theory**: not all terms are β-convertible.  Here `#0`
and `λ.#0` are two distinct normal forms, hence not convertible. -/
theorem consistency : ¬ (SigmaTerm.var 0 ≡βs SigmaTerm.abs (SigmaTerm.var 0)) := by
  intro h
  have := betaEqS_eq_of_normal h (normalS_var 0) (normalS_var 0).abs
  exact (SigmaTerm.var_ne_abs 0 (SigmaTerm.var 0)) this

/-- The quotient by β-conversion has at least two elements. -/
theorem betaQuot_nontrivial :
    BetaQuot.mk (SigmaTerm.var 0) ≠ BetaQuot.mk (SigmaTerm.abs (SigmaTerm.var 0)) :=
  fun h => consistency (BetaQuot.mk_eq_mk.mp h)

end Basic41FinsetNOfFreeIsExact
