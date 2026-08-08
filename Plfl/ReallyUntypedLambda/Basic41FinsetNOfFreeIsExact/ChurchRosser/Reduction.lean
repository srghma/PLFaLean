module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.SigmaTerm

@[expose] public section

/-!
# β-reduction on packaged terms, via Mathlib's `Relation` closures

`Basic41Finset.Term s` is indexed by the *exact* set `s` of free variables of the
term, so a β-step generally changes the index: `(λ.#1) #5` is indexed by
`{0, 5}` and reduces to `#0`, which is indexed by `{0}`.  Consequently the
reflexive-transitive closure of `BetaStep` has to be taken *heterogeneously*,
i.e. across different indices.

Rather than re-implementing the closures by hand, we move to the packaged terms
of `ChurchRosser.SigmaTerm` — a `SigmaTerm` is an ordinary (non-indexed) type,
namely a free-variable index set together with the term tree at that index — and
read a β-step as an ordinary relation `StepS : SigmaTerm → SigmaTerm → Prop`.
All closures are then Mathlib's:

* `Relation.ReflTransGen StepS` — many-step β-reduction `⇒β*`;
* `Relation.EqvGen StepS` — β-conversion `≡β`;
* `Relation.Join (Relation.ReflTransGen StepS)` — joinability;
* `Relation.ReflGen`, `Relation.Join` and `Relation.church_rosser` are used for
  confluence in `ChurchRosser.Basic`.

`Relation.ReflTransGen BetaStep`, as used in the source file, is the special
case in which the index happens to be constant along the whole reduction; it is
subsumed by `betaStarH_of_reflTransGen`.
-/

namespace Basic41FinsetNOfFreeIsExact

/-! ### Transporting relations along equalities of packaged terms -/

/-- A β-step is unchanged when its target is replaced by a term packaging to the
same `SigmaTerm`. -/
theorem betaStep_congr_right {s1 s2 s2' : Finset Nat} {M : Term s1} {N : Term s2}
    {N' : Term s2'} (h : BetaStep M N) (he : pack N = pack N') : BetaStep M N' := by
  obtain ⟨rfl, hh⟩ := pack_eq_iff.mp he
  cases hh
  exact h

/-- A β-step is unchanged when its source is replaced by a term packaging to the
same `SigmaTerm`. -/
theorem betaStep_congr_left {s1 s1' s2 : Finset Nat} {M : Term s1} {M' : Term s1'}
    {N : Term s2} (h : BetaStep M N) (he : pack M = pack M') : BetaStep M' N := by
  obtain ⟨rfl, hh⟩ := pack_eq_iff.mp he
  cases hh
  exact h

/-! ### Single-step β-reduction as a relation on packaged terms -/

/-- Single-step β-reduction, read as a relation between packaged terms.

Since a `SigmaTerm` bundles the free-variable index set with the term, this is an
ordinary homogeneous relation, and Mathlib's closure operations
(`Relation.ReflTransGen`, `Relation.EqvGen`, `Relation.Join`, …) apply to it
directly. -/
def StepS (t u : SigmaTerm) : Prop :=
  BetaStep t.betaReducedTermTree u.betaReducedTermTree

@[inherit_doc] infix:64 " →βs " => StepS

theorem StepS.head (t u : SigmaTerm) : (t.abs.app u) →βs SigmaTerm.subst 0 u t :=
  BetaStep.head _ _

theorem StepS.app_left {t t' : SigmaTerm} (h : t →βs t') (u : SigmaTerm) :
    (t.app u) →βs (t'.app u) := BetaStep.app_left _ h

theorem StepS.app_right (t : SigmaTerm) {u u' : SigmaTerm} (h : u →βs u') :
    (t.app u) →βs (t.app u') := BetaStep.app_right _ h

theorem StepS.abs {t u : SigmaTerm} (h : t →βs u) : t.abs →βs u.abs := BetaStep.abs_body h

/-- The induction principle for single-step β-reduction, phrased on packaged
terms. -/
@[elab_as_elim]
theorem StepS.induction {motive : SigmaTerm → SigmaTerm → Prop}
    (head : ∀ t u : SigmaTerm, motive (t.abs.app u) (SigmaTerm.subst 0 u t))
    (app_left : ∀ t t' u : SigmaTerm, t →βs t' → motive t t' → motive (t.app u) (t'.app u))
    (app_right : ∀ t u u' : SigmaTerm, u →βs u' → motive u u' → motive (t.app u) (t.app u'))
    (abs : ∀ t u : SigmaTerm, t →βs u → motive t u → motive t.abs u.abs)
    {t u : SigmaTerm} (h : t →βs u) : motive t u := by
  have H : ∀ {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}, BetaStep M N →
      motive (pack M) (pack N) := by
    intro s1 s2 M N h
    induction h with
    | head P Q => exact head (pack P) (pack Q)
    | @app_left _ _ _ P P' Q h0 ih => exact app_left (pack P) (pack P') (pack Q) h0 ih
    | @app_right _ _ _ P Q Q' h0 ih => exact app_right (pack P) (pack Q) (pack Q') h0 ih
    | @abs_body _ _ P P' h0 ih => exact abs (pack P) (pack P') h0 ih
  exact H h

/-! ### The closures, taken from Mathlib -/

/-- Many-step β-reduction on packaged terms: the reflexive-transitive closure
`Relation.ReflTransGen` of `StepS`. -/
abbrev BetaStarS : SigmaTerm → SigmaTerm → Prop := Relation.ReflTransGen StepS

@[inherit_doc] infix:64 " ⇒βs* " => BetaStarS

/-- β-conversion on packaged terms: the equivalence closure `Relation.EqvGen` of
`StepS`. -/
abbrev BetaEqS : SigmaTerm → SigmaTerm → Prop := Relation.EqvGen StepS

@[inherit_doc] infix:64 " ≡βs " => BetaEqS

/-- Joinability of packaged terms: `Relation.Join` of many-step β-reduction. -/
abbrev BetaJoinS : SigmaTerm → SigmaTerm → Prop := Relation.Join BetaStarS

/-! ### Congruence rules for many-step reduction

Each of these is an instance of Mathlib's `Relation.ReflTransGen.lift`. -/

theorem betaStarS_abs {t u : SigmaTerm} (h : t ⇒βs* u) : t.abs ⇒βs* u.abs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (StepS.abs step)

theorem betaStarS_app_left {t t' : SigmaTerm} (u : SigmaTerm) (h : t ⇒βs* t') :
    t.app u ⇒βs* t'.app u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (StepS.app_left step u)

theorem betaStarS_app_right (t : SigmaTerm) {u u' : SigmaTerm} (h : u ⇒βs* u') :
    t.app u ⇒βs* t.app u' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (StepS.app_right t step)

theorem betaStarS_app {t t' u u' : SigmaTerm} (h1 : t ⇒βs* t') (h2 : u ⇒βs* u') :
    t.app u ⇒βs* t'.app u' :=
  (betaStarS_app_left u h1).trans (betaStarS_app_right t' h2)

/-! ### Heterogeneous many-step reduction on indexed terms

These are the same relations, read on indexed terms through `pack`. -/

/-- Many-step β-reduction between terms whose free-variable indices may differ:
`Relation.ReflTransGen` of `StepS`, read through `pack`. -/
def BetaStarH {s1 s2 : Finset Nat} (M : Term s1) (N : Term s2) : Prop :=
  pack M ⇒βs* pack N

@[inherit_doc] infix:64 " ⇒β* " => BetaStarH

/-- β-conversion between terms whose free-variable indices may differ:
`Relation.EqvGen` of `StepS`, read through `pack`. -/
def BetaEqH {s1 s2 : Finset Nat} (M : Term s1) (N : Term s2) : Prop :=
  pack M ≡βs pack N

@[inherit_doc] infix:64 " ≡β " => BetaEqH

theorem BetaStarH.refl {s : Finset Nat} {M : Term s} : M ⇒β* M :=
  Relation.ReflTransGen.refl

theorem BetaStarH.tail {s1 s2 s3 : Finset Nat} {M : Term s1} {N : Term s2} {K : Term s3}
    (h : M ⇒β* N) (st : BetaStep N K) : M ⇒β* K :=
  Relation.ReflTransGen.tail h st

theorem BetaStarH.single {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2}
    (h : BetaStep M N) : M ⇒β* N :=
  Relation.ReflTransGen.single h

theorem BetaStarH.trans {s1 s2 s3 : Finset Nat} {M : Term s1} {N : Term s2} {K : Term s3}
    (h1 : M ⇒β* N) (h2 : N ⇒β* K) : M ⇒β* K :=
  Relation.ReflTransGen.trans h1 h2

/-- Many-step reduction of indexed terms is exactly many-step reduction of the
packaged terms. -/
theorem betaStarH_iff_betaStarS {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} :
    M ⇒β* N ↔ pack M ⇒βs* pack N := Iff.rfl

/-- The homogeneous closure used in the source file is a special case. -/
theorem betaStarH_of_reflTransGen {s : Finset Nat} {M N : Term s}
    (h : Relation.ReflTransGen BetaStep M N) : M ⇒β* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih step

theorem betaStarH_congr_right {s1 s2 s2' : Finset Nat} {M : Term s1} {N : Term s2}
    {N' : Term s2'} (h : M ⇒β* N) (he : pack N = pack N') : M ⇒β* N' := by
  show pack M ⇒βs* pack N'
  rw [← he]; exact h

theorem betaStarH_congr_left {s1 s1' s2 : Finset Nat} {M : Term s1} {M' : Term s1'}
    {N : Term s2} (h : M ⇒β* N) (he : pack M = pack M') : M' ⇒β* N := by
  show pack M' ⇒βs* pack N
  rw [← he]; exact h

/-! ### Congruence rules for many-step reduction on indexed terms -/

theorem betaStarH_abs {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : M ⇒β* N) :
    Term.abs M ⇒β* Term.abs N := betaStarS_abs h

theorem betaStarH_app_left {s1 s1' s2 : Finset Nat} {M : Term s1} {M' : Term s1'}
    (N : Term s2) (h : M ⇒β* M') : Term.app M N ⇒β* Term.app M' N :=
  betaStarS_app_left (pack N) h

theorem betaStarH_app_right {s1 s2 s2' : Finset Nat} (M : Term s1) {N : Term s2} {N' : Term s2'}
    (h : N ⇒β* N') : Term.app M N ⇒β* Term.app M N' :=
  betaStarS_app_right (pack M) h

/-! ### β-conversion -/

theorem BetaEqH.step {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : BetaStep M N) :
    M ≡β N := Relation.EqvGen.rel _ _ h

theorem BetaEqH.refl {s : Finset Nat} {M : Term s} : M ≡β M := Relation.EqvGen.refl _

theorem BetaEqH.symm {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : M ≡β N) : N ≡β M :=
  Relation.EqvGen.symm _ _ h

theorem BetaEqH.trans {s1 s2 s3 : Finset Nat} {M : Term s1} {N : Term s2} {K : Term s3}
    (h1 : M ≡β N) (h2 : N ≡β K) : M ≡β K := Relation.EqvGen.trans _ _ _ h1 h2

/-- The reflexive-transitive closure of a relation is contained in the
equivalence closure. -/
theorem eqvGen_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ st ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ st)

/-- Reduction implies conversion. -/
theorem BetaEqH.of_betaStarH {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : M ⇒β* N) :
    M ≡β N := eqvGen_of_reflTransGen h

end Basic41FinsetNOfFreeIsExact
