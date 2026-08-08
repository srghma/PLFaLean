module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Basic

@[expose] public section

/-!
# The standardization theorem

A β-reduction sequence is *standard* when redexes are contracted from the
outside in and from left to right: no redex is ever contracted to the left of
(or outside) a redex that has already been contracted.  Following Takahashi,
the existence of a standard reduction sequence from `t` to `u` is captured by
the inductively defined relation `Standard`:

* `Standard.head`  : a head redex may be contracted first, and the reduction then
  continues in a standard way;
* `Standard.var`   : a variable standardly reduces to itself;
* `Standard.abs`   : standard reduction under a `λ`;
* `Standard.app`   : standard reduction in the two components of an application,
  once no head redex is contracted any more.

The **standardization theorem** `standardization` states

```
t ⇒βs* u ↔ Standard t u
```

that is: whenever `t` β-reduces to `u`, it does so by a standard reduction
sequence.  `standardization_H` is the same statement on indexed terms.

The proof is Takahashi's: `Standard` absorbs a parallel reduction step on the right
(`Standard.parS`), and many-step β-reduction is many-step parallel reduction
(`parStarS_iff_betaStarS`), so `Standard` contains `⇒βs*`; the converse is a direct
induction.

As an application we derive the head-reduction corollary
`head_reduction_of_betaStarS_abs`: if a term β-reduces to an abstraction, then
*head* reduction alone already takes it to an abstraction.
-/

namespace Basic41FinsetNOfFreeIsExact

/-! ### Head reduction -/

/-- Head reduction: contract the redex in head position. -/
inductive HeadS : SigmaTerm → SigmaTerm → Prop
  | beta (t u : SigmaTerm) : HeadS (t.abs.app u) (SigmaTerm.subst 0 u t)
  | app_left {t t' : SigmaTerm} (h : HeadS t t') (u : SigmaTerm) : HeadS (t.app u) (t'.app u)

/-- A head step is a β-step. -/
theorem HeadS.toStepS {t u : SigmaTerm} (h : HeadS t u) : t →βs u := by
  induction h with
  | beta t u => exact StepS.head t u
  | app_left _ u ih => exact StepS.app_left ih u

/-- Head reduction is preserved by shifting. -/
theorem HeadS.shift {t u : SigmaTerm} (h : HeadS t u) (c : Nat) :
    HeadS (SigmaTerm.shift c t) (SigmaTerm.shift c u) := by
  induction h generalizing c with
  | beta t u =>
    rw [SigmaTerm.shift_app, SigmaTerm.shift_abs,
      SigmaTerm.shift_subst_ge t c 0 u (Nat.zero_le c)]
    exact HeadS.beta _ _
  | app_left _ u ih =>
    rw [SigmaTerm.shift_app, SigmaTerm.shift_app]
    exact HeadS.app_left (ih c) _

/-- Head reduction is preserved by substitution. -/
theorem HeadS.subst {t u : SigmaTerm} (h : HeadS t u) (j : Nat) (v : SigmaTerm) :
    HeadS (SigmaTerm.subst j v t) (SigmaTerm.subst j v u) := by
  induction h generalizing j with
  | beta t u =>
    rw [SigmaTerm.subst_app, SigmaTerm.subst_abs, SigmaTerm.subst_subst_zero]
    exact HeadS.beta _ _
  | app_left _ u ih =>
    rw [SigmaTerm.subst_app, SigmaTerm.subst_app]
    exact HeadS.app_left (ih j) _

/-! ### Standard reduction -/

/-- Standard reduction: the head redexes are contracted first (rule `head`),
after which the reduction proceeds structurally (rules `var`, `abs`, `app`).

`Standard t u` says exactly that there is a standard β-reduction sequence from `t`
to `u`. -/
inductive Standard : SigmaTerm → SigmaTerm → Prop
  | head {t t' u : SigmaTerm} : HeadS t t' → Standard t' u → Standard t u
  | var (i : Nat) : Standard (SigmaTerm.var i) (SigmaTerm.var i)
  | abs {t u : SigmaTerm} : Standard t u → Standard t.abs u.abs
  | app {t t' u u' : SigmaTerm} : Standard t t' → Standard u u' → Standard (t.app u) (t'.app u')

theorem Standard.refl (t : SigmaTerm) : Standard t t := by
  induction t using SigmaTerm.induction with
  | hvar i => exact Standard.var i
  | habs t ih => exact Standard.abs ih
  | happ t u iht ihu => exact Standard.app iht ihu

/-- A standard reduction is a β-reduction. -/
theorem Standard.toBetaStarS {t u : SigmaTerm} (h : Standard t u) : t ⇒βs* u := by
  induction h with
  | head hh _ ih => exact Relation.ReflTransGen.head hh.toStepS ih
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact betaStarS_abs ih
  | app _ _ ih1 ih2 => exact betaStarS_app ih1 ih2

/-- Standard reduction is preserved by shifting. -/
theorem Standard.shift {t u : SigmaTerm} (h : Standard t u) (c : Nat) :
    Standard (SigmaTerm.shift c t) (SigmaTerm.shift c u) := by
  induction h generalizing c with
  | head hh _ ih => exact Standard.head (hh.shift c) (ih c)
  | var i => exact Standard.refl _
  | abs _ ih =>
    rw [SigmaTerm.shift_abs, SigmaTerm.shift_abs]
    exact Standard.abs (ih (c + 1))
  | app _ _ ih1 ih2 =>
    rw [SigmaTerm.shift_app, SigmaTerm.shift_app]
    exact Standard.app (ih1 c) (ih2 c)

/-- Standard reduction is preserved by substitution. -/
theorem Standard.subst {t t' : SigmaTerm} (h : Standard t t') :
    ∀ (j : Nat) {u u' : SigmaTerm}, Standard u u' →
      Standard (SigmaTerm.subst j u t) (SigmaTerm.subst j u' t') := by
  induction h with
  | head hh _ ih =>
    intro j u u' hu
    exact Standard.head (hh.subst j u) (ih j hu)
  | var i =>
    intro j u u' hu
    rw [SigmaTerm.subst_var, SigmaTerm.subst_var]
    split
    · exact hu
    · split <;> exact Standard.refl _
  | abs _ ih =>
    intro j u u' hu
    rw [SigmaTerm.subst_abs, SigmaTerm.subst_abs]
    exact Standard.abs (ih (j + 1) (hu.shift 0))
  | app _ _ ih1 ih2 =>
    intro j u u' hu
    rw [SigmaTerm.subst_app, SigmaTerm.subst_app]
    exact Standard.app (ih1 j hu) (ih2 j hu)

/-- Key closure property: if `t` standardly reduces to an abstraction `λp` and
`u` standardly reduces to `q`, then `t u` standardly reduces to `p[q]`. -/
theorem Standard.app_abs_aux {t w : SigmaTerm} (h : Standard t w) :
    ∀ p : SigmaTerm, w = SigmaTerm.abs p → ∀ u q : SigmaTerm, Standard u q →
      Standard (t.app u) (SigmaTerm.subst 0 q p) := by
  induction h with
  | head hh _ ih =>
    intro p hp u q hq
    exact Standard.head (hh.app_left u) (ih p hp u q hq)
  | var i => intro p hp; exact absurd hp (by simp)
  | @abs t0 u0 h0 _ =>
    intro p hp u q hq
    have hu0 : u0 = p := SigmaTerm.abs_inj.mp hp
    subst hu0
    exact Standard.head (HeadS.beta t0 u) (h0.subst 0 hq)
  | app _ _ _ _ => intro p hp; exact absurd hp (by simp)

theorem Standard.app_abs {t u p q : SigmaTerm} (h1 : Standard t (SigmaTerm.abs p)) (h2 : Standard u q) :
    Standard (t.app u) (SigmaTerm.subst 0 q p) :=
  Standard.app_abs_aux h1 p rfl u q h2

/-! ### Inversion lemmas for parallel reduction -/

theorem ParS.var_inv_aux {a b : SigmaTerm} (h : ParS a b) :
    ∀ i : Nat, a = SigmaTerm.var i → b = SigmaTerm.var i := by
  refine ParS.cases'
    (motive := fun a b => ∀ i : Nat, a = SigmaTerm.var i → b = SigmaTerm.var i) ?_ ?_ ?_ ?_ h
  · intro i j hj; exact hj
  · intro t u _ i hi; exact absurd hi (by simp)
  · intro t t' u u' _ _ i hi; exact absurd hi (by simp)
  · intro t t' u u' _ _ i hi; exact absurd hi (by simp)

theorem ParS.var_inv {i : Nat} {v : SigmaTerm} (h : ParS (SigmaTerm.var i) v) :
    v = SigmaTerm.var i := ParS.var_inv_aux h i rfl

theorem ParS.app_inv_aux {a b : SigmaTerm} (h : ParS a b) :
    ∀ t u : SigmaTerm, a = t.app u →
      (∃ t' u', b = SigmaTerm.app t' u' ∧ ParS t t' ∧ ParS u u') ∨
      (∃ p p' u', t = SigmaTerm.abs p ∧ b = SigmaTerm.subst 0 u' p' ∧
        ParS p p' ∧ ParS u u') := by
  refine ParS.cases'
    (motive := fun a b => ∀ t u : SigmaTerm, a = t.app u →
      (∃ t' u', b = SigmaTerm.app t' u' ∧ ParS t t' ∧ ParS u u') ∨
      (∃ p p' u', t = SigmaTerm.abs p ∧ b = SigmaTerm.subst 0 u' p' ∧
        ParS p p' ∧ ParS u u')) ?_ ?_ ?_ ?_ h
  · intro i t u ht; exact absurd ht (by simp)
  · intro a a' _ t u ht; exact absurd ht (by simp)
  · intro a a' b b' h1 h2 t u ht
    obtain ⟨rfl, rfl⟩ := SigmaTerm.app_inj.mp ht
    exact Or.inl ⟨a', b', rfl, h1, h2⟩
  · intro a a' b b' h1 h2 t u ht
    obtain ⟨rfl, rfl⟩ := SigmaTerm.app_inj.mp ht
    exact Or.inr ⟨a, a', b', rfl, rfl, h1, h2⟩

/-! ### Standard reduction absorbs parallel reduction -/

/-- **The main lemma**: a standard reduction followed by a parallel reduction is
again a standard reduction. -/
theorem Standard.parS {t u : SigmaTerm} (h : Standard t u) :
    ∀ {v : SigmaTerm}, ParS u v → Standard t v := by
  induction h with
  | head hh _ ih => intro v hv; exact Standard.head hh (ih hv)
  | var i =>
    intro v hv
    rw [ParS.var_inv hv]
    exact Standard.var i
  | @abs t0 u0 _ ih =>
    intro v hv
    obtain ⟨v0, rfl, hpar⟩ := ParS.abs_inv_aux hv u0 rfl
    exact Standard.abs (ih hpar)
  | @app t1 u1 t2 u2 _ _ ih1 ih2 =>
    intro v hv
    rcases ParS.app_inv_aux hv u1 u2 rfl with ⟨v1, v2, rfl, p1, p2⟩ |
      ⟨p, p', u2', hu1, rfl, hp, hu2⟩
    · exact Standard.app (ih1 p1) (ih2 p2)
    · exact Standard.app_abs (ih1 (hu1 ▸ ParS.abs hp)) (ih2 hu2)

/-! ### The standardization theorem -/

/-- Many-step parallel reduction implies standard reduction. -/
theorem standard_of_parStarS {t u : SigmaTerm} (h : t ⇉βs* u) : Standard t u := by
  induction h with
  | refl => exact Standard.refl _
  | tail _ st ih => exact ih.parS st

/-- **The standardization theorem**: every β-reduction can be performed by a
standard reduction sequence, and conversely. -/
theorem standardization {t u : SigmaTerm} : t ⇒βs* u ↔ Standard t u :=
  ⟨fun h => standard_of_parStarS (parStarS_of_betaStarS h), Standard.toBetaStarS⟩

/-- Standard reduction between indexed terms (whose free-variable index sets may
differ), read through `pack`. -/
def StandardH {s1 s2 : Finset Nat} (M : Term s1) (N : Term s2) : Prop := Standard (pack M) (pack N)

/-- **The standardization theorem** on indexed terms. -/
theorem standardization_H {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} :
    M ⇒β* N ↔ StandardH M N := standardization

/-- Standardization for the homogeneous closure `⇒β` of the source file. -/
theorem standardization_of_reflTransGen {s : Finset Nat} {M N : Term s}
    (h : Relation.ReflTransGen BetaStep M N) : StandardH M N :=
  standardization_H.mp (betaStarH_of_reflTransGen h)

/-! ### A corollary: head reduction finds abstractions -/

theorem standard_abs_aux {t w : SigmaTerm} (h : Standard t w) :
    ∀ p : SigmaTerm, w = SigmaTerm.abs p →
      ∃ q, Relation.ReflTransGen HeadS t (SigmaTerm.abs q) ∧ Standard q p := by
  induction h with
  | head hh _ ih =>
    intro p hp
    obtain ⟨q, hq, hqp⟩ := ih p hp
    exact ⟨q, Relation.ReflTransGen.head hh hq, hqp⟩
  | var i => intro p hp; exact absurd hp (by simp)
  | @abs t0 u0 h0 _ =>
    intro p hp
    have : u0 = p := SigmaTerm.abs_inj.mp hp
    subst this
    exact ⟨t0, Relation.ReflTransGen.refl, h0⟩
  | app _ _ _ _ => intro p hp; exact absurd hp (by simp)

/-- A corollary of standardization: if a term β-reduces to an abstraction, then
head reduction alone already takes it to an abstraction. -/
theorem head_reduction_of_betaStarS_abs {t p : SigmaTerm} (h : t ⇒βs* SigmaTerm.abs p) :
    ∃ q, Relation.ReflTransGen HeadS t (SigmaTerm.abs q) ∧ Standard q p :=
  standard_abs_aux (standardization.mp h) p rfl

end Basic41FinsetNOfFreeIsExact
