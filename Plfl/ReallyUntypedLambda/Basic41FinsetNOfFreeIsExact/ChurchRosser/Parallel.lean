module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Reduction

@[expose] public section

/-!
# Parallel β-reduction and Takahashi's complete development

Everything here happens directly on the `Finset`-indexed terms: no untyped
syntax is introduced.  Whenever an operation produces a term whose free-variable
index set is not determined by the inputs, it *returns an existential*, i.e. a
`SigmaTerm` — the new free-variable index set together with the reduced term
tree.  This is the case for Takahashi's complete development `takahashi`, and it
is the reason why the diamond property below produces a
`∃ (t : Finset Nat) (D : Term t), …`.

The development follows Takahashi's proof:

* `BetaParH` (`⇉β`) — parallel reduction, sitting between `BetaStep` and
  `BetaStarH`;
* `ParS` — the same relation, phrased on packaged terms, which is what makes
  the substitution calculus of `ChurchRosser.SigmaTerm` directly applicable;
* `takahashi` — the complete development, contracting all redexes present in a
  term at once;
* `takahashi_triangle` — every parallel reduct of `M` reduces in parallel to
  `takahashi M`, whence the diamond property `betaParH_diamond`.
-/

namespace Basic41FinsetNOfFreeIsExact

/-- Parallel β-reduction between terms whose free-variable indices may differ. -/
inductive BetaParH : ∀ {s1 s2 : Finset Nat}, Term s1 → Term s2 → Prop
  | var (i : Nat) : BetaParH (Term.var i) (Term.var i)
  | abs {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} :
      BetaParH M N → BetaParH (Term.abs M) (Term.abs N)
  | app {s1 s1' s2 s2' : Finset Nat} {M : Term s1} {M' : Term s1'}
      {N : Term s2} {N' : Term s2'} :
      BetaParH M M' → BetaParH N N' → BetaParH (Term.app M N) (Term.app M' N')
  | beta {s1 s1' s2 s2' : Finset Nat} {M : Term s1} {M' : Term s1'}
      {N : Term s2} {N' : Term s2'} :
      BetaParH M M' → BetaParH N N' → BetaParH (Term.app (Term.abs M) N) (M' [N'])

@[inherit_doc] infix:64 " ⇉β " => BetaParH

theorem betaParH_congr_right {s1 s2 s2' : Finset Nat} {M : Term s1} {N : Term s2}
    {N' : Term s2'} (h : M ⇉β N) (he : pack N = pack N') : M ⇉β N' := by
  obtain ⟨rfl, hh⟩ := pack_eq_iff.mp he
  cases hh
  exact h

theorem betaParH_congr_left {s1 s1' s2 : Finset Nat} {M : Term s1} {M' : Term s1'}
    {N : Term s2} (h : M ⇉β N) (he : pack M = pack M') : M' ⇉β N := by
  obtain ⟨rfl, hh⟩ := pack_eq_iff.mp he
  cases hh
  exact h

/-! ### Parallel reduction on packaged terms -/

/-- Parallel β-reduction, read as a relation between packaged terms. -/
def ParS (t u : SigmaTerm) : Prop :=
  BetaParH t.betaReducedTermTree u.betaReducedTermTree

theorem ParS.var (i : Nat) : ParS (SigmaTerm.var i) (SigmaTerm.var i) := BetaParH.var i

theorem ParS.abs {t u : SigmaTerm} (h : ParS t u) : ParS t.abs u.abs := BetaParH.abs h

theorem ParS.app {t t' u u' : SigmaTerm} (h1 : ParS t t') (h2 : ParS u u') :
    ParS (t.app u) (t'.app u') := BetaParH.app h1 h2

theorem ParS.beta {t t' u u' : SigmaTerm} (h1 : ParS t t') (h2 : ParS u u') :
    ParS (t.abs.app u) (SigmaTerm.subst 0 u' t') := BetaParH.beta h1 h2

/-- The induction principle for parallel reduction, phrased on packaged terms. -/
@[elab_as_elim]
theorem ParS.induction {motive : SigmaTerm → SigmaTerm → Prop}
    (var : ∀ i, motive (SigmaTerm.var i) (SigmaTerm.var i))
    (abs : ∀ t u, ParS t u → motive t u → motive t.abs u.abs)
    (app : ∀ t t' u u', ParS t t' → ParS u u' → motive t t' → motive u u' →
      motive (t.app u) (t'.app u'))
    (beta : ∀ t t' u u', ParS t t' → ParS u u' → motive t t' → motive u u' →
      motive (t.abs.app u) (SigmaTerm.subst 0 u' t'))
    {t u : SigmaTerm} (h : ParS t u) : motive t u := by
  have H : ∀ {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}, M ⇉β N →
      motive (pack M) (pack N) := by
    intro s1 s2 M N h
    induction h with
    | var i => exact var i
    | @abs _ _ M N h0 ih => exact abs (pack M) (pack N) h0 ih
    | @app _ _ _ _ M M' N N' h1 h2 ih1 ih2 =>
      exact app (pack M) (pack M') (pack N) (pack N') h1 h2 ih1 ih2
    | @beta _ _ _ _ M M' N N' h1 h2 ih1 ih2 =>
      exact beta (pack M) (pack M') (pack N) (pack N') h1 h2 ih1 ih2
  exact H h

/-- Case analysis for parallel reduction, phrased on packaged terms. -/
@[elab_as_elim]
theorem ParS.cases' {motive : SigmaTerm → SigmaTerm → Prop}
    (var : ∀ i, motive (SigmaTerm.var i) (SigmaTerm.var i))
    (abs : ∀ t u, ParS t u → motive t.abs u.abs)
    (app : ∀ t t' u u', ParS t t' → ParS u u' → motive (t.app u) (t'.app u'))
    (beta : ∀ t t' u u', ParS t t' → ParS u u' →
      motive (t.abs.app u) (SigmaTerm.subst 0 u' t'))
    {t u : SigmaTerm} (h : ParS t u) : motive t u := by
  have H : ∀ {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}, M ⇉β N →
      motive (pack M) (pack N) := by
    intro s1 s2 M N h
    cases h with
    | var i => exact var i
    | @abs _ _ M N h0 => exact abs (pack M) (pack N) h0
    | @app _ _ _ _ M M' N N' h1 h2 => exact app (pack M) (pack M') (pack N) (pack N') h1 h2
    | @beta _ _ _ _ M M' N N' h1 h2 => exact beta (pack M) (pack M') (pack N) (pack N') h1 h2
  exact H h

/-- Inversion for parallel reduction out of an abstraction. -/
theorem ParS.abs_inv_aux {a b : SigmaTerm} (h : ParS a b) :
    ∀ t : SigmaTerm, a = SigmaTerm.abs t → ∃ u : SigmaTerm, b = SigmaTerm.abs u ∧ ParS t u := by
  refine ParS.cases'
    (motive := fun a b => ∀ t : SigmaTerm, a = SigmaTerm.abs t →
      ∃ u : SigmaTerm, b = SigmaTerm.abs u ∧ ParS t u) ?_ ?_ ?_ ?_ h
  · intro i t ht; exact absurd ht (by simp)
  · intro t0 u0 h0 t ht
    exact ⟨u0, rfl, by rwa [SigmaTerm.abs_inj.mp ht] at h0⟩
  · intro a a' b b' _ _ t ht; exact absurd ht (by simp)
  · intro a a' b b' _ _ t ht; exact absurd ht (by simp)

theorem ParS.abs_inv {t u : SigmaTerm} (h : ParS t.abs u.abs) : ParS t u := by
  obtain ⟨v, hv, hpar⟩ := ParS.abs_inv_aux h t rfl
  have huv : u = v := SigmaTerm.abs_inj.mp hv
  subst huv
  exact hpar

theorem ParS.refl (t : SigmaTerm) : ParS t t := by
  induction t using SigmaTerm.induction with
  | hvar i => exact ParS.var i
  | habs t ih => exact ParS.abs ih
  | happ t u iht ihu => exact ParS.app iht ihu

theorem betaParH_refl {s : Finset Nat} (M : Term s) : M ⇉β M := ParS.refl (pack M)

/-- Parallel reduction is reflexive (as a `Std.Refl` instance, so that Mathlib's
reflexivity API applies). -/
instance : Std.Refl ParS where
  refl := ParS.refl

/-! ### Parallel reduction versus single- and many-step reduction -/

/-- A single β-step is a parallel step. -/
theorem betaStep_to_betaParH {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}
    (h : BetaStep M N) : M ⇉β N := by
  induction h with
  | head P N => exact BetaParH.beta (betaParH_refl P) (betaParH_refl N)
  | app_left Q _ ih => exact BetaParH.app ih (betaParH_refl Q)
  | app_right P _ ih => exact BetaParH.app (betaParH_refl P) ih
  | abs_body _ ih => exact BetaParH.abs ih

/-- A parallel step is a many-step β-reduction. -/
theorem betaParH_to_betaStarH {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}
    (h : M ⇉β N) : M ⇒β* N := by
  induction h with
  | var i => exact BetaStarH.refl
  | abs _ ih => exact betaStarH_abs ih
  | app _ _ ihM ihN =>
    exact BetaStarH.trans (betaStarH_app_left _ ihM) (betaStarH_app_right _ ihN)
  | @beta _ _ _ _ M M' N N' _ _ ihM ihN =>
    have h1 : Term.app (Term.abs M) N ⇒β* Term.app (Term.abs M') N' :=
      BetaStarH.trans (betaStarH_app_left _ (betaStarH_abs ihM)) (betaStarH_app_right _ ihN)
    exact BetaStarH.tail h1 (BetaStep.head M' N')

/-! ### Parallel reduction is compatible with shifting and substitution -/

/-- Parallel reduction is preserved by shifting. -/
theorem ParS.shift {t u : SigmaTerm} (h : ParS t u) :
    ∀ c : Nat, ParS (SigmaTerm.shift c t) (SigmaTerm.shift c u) := by
  refine ParS.induction
    (motive := fun t u => ∀ c : Nat, ParS (SigmaTerm.shift c t) (SigmaTerm.shift c u))
    ?_ ?_ ?_ ?_ h
  · intro i c; exact ParS.refl _
  · intro t u _ ih c
    rw [SigmaTerm.shift_abs, SigmaTerm.shift_abs]
    exact ParS.abs (ih (c + 1))
  · intro t t' u u' _ _ ih1 ih2 c
    rw [SigmaTerm.shift_app, SigmaTerm.shift_app]
    exact ParS.app (ih1 c) (ih2 c)
  · intro t t' u u' _ _ ih1 ih2 c
    rw [SigmaTerm.shift_app, SigmaTerm.shift_abs,
      SigmaTerm.shift_subst_ge t' c 0 u' (Nat.zero_le c)]
    exact ParS.beta (ih1 (c + 1)) (ih2 c)

/-- Parallel reduction is preserved by substitution. -/
theorem ParS.subst {t t' : SigmaTerm} (h : ParS t t') :
    ∀ (j : Nat) {u u' : SigmaTerm}, ParS u u' →
      ParS (SigmaTerm.subst j u t) (SigmaTerm.subst j u' t') := by
  refine ParS.induction
    (motive := fun t t' => ∀ (j : Nat) {u u' : SigmaTerm}, ParS u u' →
      ParS (SigmaTerm.subst j u t) (SigmaTerm.subst j u' t')) ?_ ?_ ?_ ?_ h
  · intro i j u u' hu
    rw [SigmaTerm.subst_var, SigmaTerm.subst_var]
    split
    · exact hu
    · split <;> exact ParS.refl _
  · intro t t' _ ih j u u' hu
    rw [SigmaTerm.subst_abs, SigmaTerm.subst_abs]
    exact ParS.abs (ih (j + 1) (hu.shift 0))
  · intro t t' v v' _ _ ih1 ih2 j u u' hu
    rw [SigmaTerm.subst_app, SigmaTerm.subst_app]
    exact ParS.app (ih1 j hu) (ih2 j hu)
  · intro t t' v v' _ _ ih1 ih2 j u u' hu
    rw [SigmaTerm.subst_app, SigmaTerm.subst_abs, SigmaTerm.subst_subst_zero]
    exact ParS.beta (ih1 (j + 1) (hu.shift 0)) (ih2 j hu)

/-- Parallel reduction is preserved by the β-substitution `M [N]`. -/
theorem betaParH_subst {s1 s1' s2 s2' : Finset Nat} {M : Term s1} {M' : Term s1'}
    {N : Term s2} {N' : Term s2'} (hM : M ⇉β M') (hN : N ⇉β N') : (M [N]) ⇉β (M' [N']) :=
  ParS.subst (t := pack M) (t' := pack M') hM 0 (u := pack N) (u' := pack N') hN

/-! ### Takahashi's complete development -/

/-- Takahashi's complete development: contract all redexes present in the term.

The result is *returned as an existential*: the new free-variable index set
together with the fully developed term tree. -/
def takahashi : ∀ {s : Finset Nat}, Term s → SigmaTerm
  | _, Term.var i => SigmaTerm.var i
  | _, Term.abs M => SigmaTerm.abs (takahashi M)
  | _, Term.app (Term.var i) N => SigmaTerm.app (SigmaTerm.var i) (takahashi N)
  | _, Term.app (Term.abs M) N => SigmaTerm.subst 0 (takahashi N) (takahashi M)
  | _, Term.app (Term.app P Q) N => SigmaTerm.app (takahashi (Term.app P Q)) (takahashi N)

/-- Takahashi's complete development on packaged terms. -/
def takahashiS (t : SigmaTerm) : SigmaTerm := takahashi t.betaReducedTermTree

@[simp] theorem takahashiS_var (i : Nat) : takahashiS (SigmaTerm.var i) = SigmaTerm.var i := by
  show takahashi (Term.var i) = SigmaTerm.var i
  rw [takahashi]

@[simp] theorem takahashiS_abs (t : SigmaTerm) :
    takahashiS t.abs = SigmaTerm.abs (takahashiS t) := by
  show takahashi (Term.abs t.betaReducedTermTree) = _
  rw [takahashi]; rfl

theorem takahashiS_app_var (i : Nat) (u : SigmaTerm) :
    takahashiS ((SigmaTerm.var i).app u)
      = SigmaTerm.app (takahashiS (SigmaTerm.var i)) (takahashiS u) := by
  show takahashi (Term.app (Term.var i) u.betaReducedTermTree) = _
  rw [takahashi, takahashiS_var]; rfl

theorem takahashiS_app_app (t v u : SigmaTerm) :
    takahashiS ((t.app v).app u)
      = SigmaTerm.app (takahashiS (t.app v)) (takahashiS u) := by
  show takahashi (Term.app (Term.app t.betaReducedTermTree v.betaReducedTermTree)
      u.betaReducedTermTree) = _
  rw [takahashi]; rfl

theorem takahashiS_app_abs (t u : SigmaTerm) :
    takahashiS (t.abs.app u) = SigmaTerm.subst 0 (takahashiS u) (takahashiS t) := by
  show takahashi (Term.app (Term.abs t.betaReducedTermTree) u.betaReducedTermTree) = _
  rw [takahashi]; rfl

/-- **Takahashi's triangle property**: every parallel reduct of `t` reduces in
parallel to the complete development of `t`. -/
theorem takahashiS_triangle {t u : SigmaTerm} (h : ParS t u) : ParS u (takahashiS t) := by
  refine ParS.induction (motive := fun t u => ParS u (takahashiS t)) ?_ ?_ ?_ ?_ h
  · intro i; rw [takahashiS_var]; exact ParS.var i
  · intro t u _ ih; rw [takahashiS_abs]; exact ParS.abs ih
  · intro t t' u u' hM _ ihM ihN
    refine ParS.cases' (motive := fun t t' => ParS t' (takahashiS t) →
      ParS (t'.app u') (takahashiS (t.app u))) ?_ ?_ ?_ ?_ hM ihM
    · intro i hi
      rw [takahashiS_app_var]
      exact ParS.app hi ihN
    · intro a a' _ hi
      rw [takahashiS_app_abs]
      rw [takahashiS_abs] at hi
      exact ParS.beta (ParS.abs_inv hi) ihN
    · intro a a' b b' _ _ hi
      rw [takahashiS_app_app]
      exact ParS.app hi ihN
    · intro a a' b b' _ _ hi
      rw [takahashiS_app_app]
      exact ParS.app hi ihN
  · intro t t' u u' _ _ ihM ihN
    rw [takahashiS_app_abs]
    exact ParS.subst ihM 0 ihN

/-- Takahashi's triangle property, on indexed terms. -/
theorem takahashi_triangle {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : M ⇉β N) :
    N ⇉β (takahashi M).betaReducedTermTree :=
  takahashiS_triangle (t := pack M) (u := pack N) h

/-! ### The diamond property -/

/-- A single β-step is a parallel step (packaged form). -/
theorem ParS.of_stepS {t u : SigmaTerm} (h : t →βs u) : ParS t u := betaStep_to_betaParH h

/-- A parallel step is a many-step β-reduction (packaged form). -/
theorem ParS.toBetaStarS {t u : SigmaTerm} (h : ParS t u) : t ⇒βs* u := betaParH_to_betaStarH h

/-- **The diamond property** for parallel reduction, in exactly the shape
required by Mathlib's `Relation.church_rosser`. -/
theorem parS_diamond (a b c : SigmaTerm) (hab : ParS a b) (hac : ParS a c) :
    ∃ d, Relation.ReflGen ParS b d ∧ Relation.ReflTransGen ParS c d :=
  ⟨takahashiS a, Relation.ReflGen.single (takahashiS_triangle hab),
    Relation.ReflTransGen.single (takahashiS_triangle hac)⟩

/-- **The diamond property** for parallel reduction on indexed terms.

The common reduct is returned existentially: a new free-variable index set
together with the reduced term tree. -/
theorem betaParH_diamond {s s1 s2 : Finset Nat} {M : Term s} {N1 : Term s1} {N2 : Term s2}
    (h1 : M ⇉β N1) (h2 : M ⇉β N2) :
    ∃ (t : Finset Nat) (D : Term t), N1 ⇉β D ∧ N2 ⇉β D :=
  ⟨(takahashi M).newFreeIndexes, (takahashi M).betaReducedTermTree,
    takahashi_triangle h1, takahashi_triangle h2⟩

end Basic41FinsetNOfFreeIsExact
