module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Parallel

@[expose] public section

/-!
# Church-Rosser for the `Finset`-indexed λ-terms

This is Takahashi's proof carried out *directly* on `Basic41Finset.Term`, with
no auxiliary untyped syntax: every operation that changes the free-variable
index set returns an existential (a `SigmaTerm`, i.e. the new free-variable
index set together with the reduced term tree).

All the relational infrastructure is Mathlib's: reduction is
`Relation.ReflTransGen StepS`, conversion is `Relation.EqvGen StepS`,
joinability is `Relation.Join`, and confluence is obtained by feeding the
diamond property of parallel reduction to `Relation.church_rosser`.

Because `Term s` is indexed by the *exact* set of free variables of the term, a
β-step generally changes the index, so the many-step reduction `⇒β*` and the
conversion `≡β` on indexed terms are heterogeneous (see
`ChurchRosser.Reduction`), and joinability is expressed existentially:

* `Basic41Finset.beta_confluence_S` : confluence of `⇒βs*` on packaged terms,
  stated with `Relation.Join`;
* `Basic41Finset.beta_confluence` : from `M ⇒β* N₁` and `M ⇒β* N₂` there are an
  index `t` and a term `D : Term t` with `N₁ ⇒β* D` and `N₂ ⇒β* D`;
* `Basic41Finset.beta_confluence_of_reflTransGen` : the same, starting from the
  homogeneous closure `⇒β` of the source file;
* `Basic41Finset.church_rosser` : β-convertible terms have a common reduct.
-/

namespace Basic41FinsetNOfFreeIsExact

/-! ### Many-step parallel reduction -/

/-- Many-step parallel reduction on packaged terms: `Relation.ReflTransGen` of
`ParS`. -/
abbrev ParStarS : SigmaTerm → SigmaTerm → Prop := Relation.ReflTransGen ParS

@[inherit_doc] infix:64 " ⇉βs* " => ParStarS

/-- Many-step β-reduction implies many-step parallel reduction: `StepS ⊆ ParS`,
lifted to the closures by `Relation.ReflTransGen.mono`. -/
theorem parStarS_of_betaStarS {t u : SigmaTerm} (h : t ⇒βs* u) : t ⇉βs* u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ParS.of_stepS step)

/-- Many-step parallel reduction implies many-step β-reduction: `ParS ⊆ ⇒βs*`,
and `⇒βs*` is reflexive and transitive. -/
theorem betaStarS_of_parStarS {t u : SigmaTerm} (h : t ⇉βs* u) : t ⇒βs* u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.trans ih (ParS.toBetaStarS step)

/-- Many-step β-reduction and many-step parallel reduction coincide. -/
theorem parStarS_iff_betaStarS {t u : SigmaTerm} : t ⇉βs* u ↔ t ⇒βs* u :=
  ⟨betaStarS_of_parStarS, parStarS_of_betaStarS⟩

/-! ### Confluence, from Mathlib's `Relation.church_rosser` -/

/-- Confluence of many-step parallel reduction: this is Mathlib's
`Relation.church_rosser` applied to the diamond property `parS_diamond`. -/
theorem parStarS_church_rosser {t u1 u2 : SigmaTerm} (h1 : t ⇉βs* u1) (h2 : t ⇉βs* u2) :
    Relation.Join ParStarS u1 u2 :=
  Relation.church_rosser parS_diamond h1 h2

/-- **Confluence** of β-reduction on packaged terms, stated with
`Relation.Join`. -/
theorem beta_confluence_S {t u1 u2 : SigmaTerm} (h1 : t ⇒βs* u1) (h2 : t ⇒βs* u2) :
    BetaJoinS u1 u2 := by
  obtain ⟨d, hd1, hd2⟩ :=
    parStarS_church_rosser (parStarS_of_betaStarS h1) (parStarS_of_betaStarS h2)
  exact ⟨d, betaStarS_of_parStarS hd1, betaStarS_of_parStarS hd2⟩

/-- **Confluence** (the Church-Rosser property) for β-reduction on `Term`:
two reduction sequences out of the same term can always be joined.

The common reduct is returned existentially: a new free-variable index set
together with the β-reduced term tree at that index. -/
theorem beta_confluence {s s1 s2 : Finset Nat} {M : Term s} {N1 : Term s1} {N2 : Term s2}
    (h1 : M ⇒β* N1) (h2 : M ⇒β* N2) :
    ∃ (t : Finset Nat) (D : Term t), N1 ⇒β* D ∧ N2 ⇒β* D := by
  obtain ⟨d, hd1, hd2⟩ := beta_confluence_S h1 h2
  exact ⟨d.newFreeIndexes, d.betaReducedTermTree, hd1, hd2⟩

/-- Confluence stated for the homogeneous closure `⇒β` of the source file. -/
theorem beta_confluence_of_reflTransGen {s : Finset Nat} {M N1 N2 : Term s}
    (h1 : Relation.ReflTransGen BetaStep M N1) (h2 : Relation.ReflTransGen BetaStep M N2) :
    ∃ (t : Finset Nat) (D : Term t), N1 ⇒β* D ∧ N2 ⇒β* D :=
  beta_confluence (betaStarH_of_reflTransGen h1) (betaStarH_of_reflTransGen h2)

/-! ### The Church-Rosser theorem -/

/-- Joinability of β-reduction is an equivalence relation: this is Mathlib's
`Relation.equivalence_join`, fed with confluence. -/
theorem equivalence_betaJoinS : Equivalence BetaJoinS :=
  Relation.equivalence_join (fun _ _ _ h1 h2 => beta_confluence_S h1 h2)

/-- **The Church-Rosser theorem** on packaged terms: β-convertible terms are
joinable. -/
theorem church_rosser_S {t u : SigmaTerm} (h : t ≡βs u) : BetaJoinS t u := by
  induction h with
  | rel _ _ step => exact ⟨_, Relation.ReflTransGen.single step, Relation.ReflTransGen.refl⟩
  | refl => exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih => exact equivalence_betaJoinS.symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact equivalence_betaJoinS.trans ih1 ih2

/-- **The Church-Rosser theorem**: β-convertible terms have a common reduct. -/
theorem church_rosser {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} (h : M ≡β N) :
    ∃ (t : Finset Nat) (D : Term t), M ⇒β* D ∧ N ⇒β* D := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser_S h
  exact ⟨d.newFreeIndexes, d.betaReducedTermTree, hd1, hd2⟩

/-- β-conversion is exactly joinability. -/
theorem betaEqH_iff_join {s1 s2 : Finset Nat} {M : Term s1} {N : Term s2} :
    M ≡β N ↔ BetaJoinS (pack M) (pack N) :=
  ⟨church_rosser_S, fun ⟨_, h1, h2⟩ =>
    BetaEqH.trans (BetaEqH.of_betaStarH h1) (BetaEqH.symm (BetaEqH.of_betaStarH h2))⟩

end Basic41FinsetNOfFreeIsExact
