module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Consistency

@[expose] public section

/-!
# Normal forms: inversion, closure properties, and non-convertibility

This file develops the basic theory of β-normal forms on packaged terms
(`SigmaTerm`), on top of the confluence results of `ChurchRosser.Basic` and the
first consequences collected in `ChurchRosser.Consistency`:

* `Basic41Finset.stepS_app_inv` — inversion of a β-step out of an application;
* `Basic41Finset.NormalS.app`, `Basic41Finset.NormalS.abs_iff` — how normality
  interacts with the constructors;
* `Basic41Finset.HasNormalFormS` — having a normal form, and its invariance
  along reduction (`Basic41Finset.HasNormalFormS.of_betaStarS`);
* `Basic41Finset.ne_of_not_betaEqS`, `Basic41Finset.not_betaEqS_of_ne_normal` —
  **two distinct normal forms are never β-convertible**;
* `Basic41Finset.normalForm_unique` — the normal form of a term, when it exists,
  is unique.
-/

namespace Basic41FinsetNOfFreeIsExact

/-! ### Inversion of β-steps -/

/-- Inversion: a β-step out of an application either contracts the head redex,
or happens in the function part, or happens in the argument part. -/
theorem stepS_app_inv {t u w : SigmaTerm} (h : t.app u →βs w) :
    (∃ t0, t = t0.abs ∧ w = SigmaTerm.subst 0 u t0) ∨
    (∃ t', w = t'.app u ∧ t →βs t') ∨
    (∃ u', w = t.app u' ∧ u →βs u') := by
  refine StepS.induction
    (motive := fun a b => ∀ t u, a = SigmaTerm.app t u →
      (∃ t0, t = t0.abs ∧ b = SigmaTerm.subst 0 u t0) ∨
      (∃ t', b = t'.app u ∧ t →βs t') ∨
      (∃ u', b = t.app u' ∧ u →βs u'))
    ?_ ?_ ?_ ?_ h t u rfl
  · intro a b t u he
    obtain ⟨h1, h2⟩ := SigmaTerm.app_inj.mp he.symm
    exact Or.inl ⟨a, h1, by rw [h2]⟩
  · intro a a' b hstep _ t u he
    obtain ⟨h1, h2⟩ := SigmaTerm.app_inj.mp he.symm
    exact Or.inr (Or.inl ⟨a', by rw [h2], by rw [h1]; exact hstep⟩)
  · intro a b b' hstep _ t u he
    obtain ⟨h1, h2⟩ := SigmaTerm.app_inj.mp he.symm
    exact Or.inr (Or.inr ⟨b', by rw [h1], by rw [h2]; exact hstep⟩)
  · intro a b _ _ t u he
    exact absurd he (by simp)

/-! ### Normality and the constructors -/

/-- An application whose parts are normal and whose function part is not an
abstraction is normal. -/
theorem NormalS.app {t u : SigmaTerm} (ht : NormalS t) (hu : NormalS u)
    (hna : ∀ t0 : SigmaTerm, t ≠ t0.abs) : NormalS (t.app u) := by
  intro w hw
  rcases stepS_app_inv hw with ⟨t0, h1, _⟩ | ⟨t', _, h2⟩ | ⟨u', _, h2⟩
  · exact hna t0 h1
  · exact ht t' h2
  · exact hu u' h2

/-- An abstraction is normal exactly when its body is. -/
theorem NormalS.abs_iff {t : SigmaTerm} : NormalS t.abs ↔ NormalS t := by
  refine ⟨fun h u hu => h u.abs (StepS.abs hu), NormalS.abs⟩

/-! ### Having a normal form -/

/-- A term *has a normal form* when it reduces to a term admitting no β-step. -/
def HasNormalFormS (t : SigmaTerm) : Prop := ∃ u, t ⇒βs* u ∧ NormalS u

/-- Every reduct of a term reaches the same normal form: this is confluence. -/
theorem betaStarS_normal_of_betaStarS {t t' u : SigmaTerm} (hred : t ⇒βs* t')
    (hnf : t ⇒βs* u) (hu : NormalS u) : t' ⇒βs* u := by
  obtain ⟨d, hd1, hd2⟩ := beta_confluence_S hred hnf
  rw [← hu.eq_of_betaStarS hd2]
  exact hd1

/-- Having a normal form is invariant along reduction. -/
theorem HasNormalFormS.of_betaStarS {t t' : SigmaTerm} (h : t ⇒βs* t')
    (hn : HasNormalFormS t) : HasNormalFormS t' := by
  obtain ⟨u, hu1, hu2⟩ := hn
  exact ⟨u, betaStarS_normal_of_betaStarS h hu1 hu2, hu2⟩

theorem HasNormalFormS.betaStarS {t t' : SigmaTerm} (h : t ⇒βs* t')
    (hn : HasNormalFormS t') : HasNormalFormS t := by
  obtain ⟨u, hu1, hu2⟩ := hn
  exact ⟨u, h.trans hu1, hu2⟩

/-- Having a normal form is invariant under β-conversion. -/
theorem HasNormalFormS.of_betaEqS {t u : SigmaTerm} (h : t ≡βs u)
    (hn : HasNormalFormS t) : HasNormalFormS u := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser_S h
  exact (hn.of_betaStarS hd1).betaStarS hd2

/-- **Uniqueness of the normal form of a term.** -/
theorem normalForm_unique {t u1 u2 : SigmaTerm} (h1 : t ⇒βs* u1) (h2 : t ⇒βs* u2)
    (n1 : NormalS u1) (n2 : NormalS u2) : u1 = u2 :=
  unique_normal_form h1 h2 n1 n2

/-! ### Distinct normal forms are not β-convertible -/

/-- **Two distinct normal forms are never β-convertible.** -/
theorem not_betaEqS_of_ne_normal {t u : SigmaTerm} (n1 : NormalS t) (n2 : NormalS u)
    (hne : t ≠ u) : ¬ (t ≡βs u) :=
  fun h => hne (betaEqS_eq_of_normal h n1 n2)

/-- β-convertible normal forms are equal (restatement of
`betaEqS_eq_of_normal`), so β-conversion of normal forms is just equality. -/
theorem betaEqS_iff_eq_of_normal {t u : SigmaTerm} (n1 : NormalS t) (n2 : NormalS u) :
    t ≡βs u ↔ t = u :=
  ⟨fun h => betaEqS_eq_of_normal h n1 n2, fun h => h ▸ Relation.EqvGen.refl _⟩

/-- If a term with a normal form is convertible to a normal form, the latter is
*the* normal form. -/
theorem eq_normalForm_of_betaEqS {t u v : SigmaTerm} (h : t ≡βs u) (hv : t ⇒βs* v)
    (nv : NormalS v) (nu : NormalS u) : v = u :=
  betaEqS_eq_of_normal
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eqvGen_of_reflTransGen hv)) h) nv nu

end Basic41FinsetNOfFreeIsExact
