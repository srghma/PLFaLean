# Summary of changes for run 17118e40-add3-46c9-b0c9-5d2fb42aebd7
## Answers to your two questions

**1. "Can it be done without `Classical.choice`?"**

Not for the `Finset`-indexed term type of the earlier development: `Finset.erase`, `Finset.image` and `Finset.union` (used in that type's own constructors) are defined in Mathlib by lifting list operations through `Multiset`, and their well-definedness proofs are classical. So `Classical.choice` already appears in the axioms of the *type*, before any theorem is stated — no proof can avoid it.

It **can** be done for a `Finset`-free presentation of the same calculus, and that is what the project now contains: the intrinsically scoped terms `Term : Nat → Type` from your original prompt (variables in `Fin n`). Every result there depends only on `propext` and `Quot.sound`. This is recorded in machine-checked form in `ChoiceFree/Axioms.lean` (`#guard_msgs` around `#print axioms`), which is compiled as part of the build.

**2. "What other fundamental theorems can be proved?"** — the choice-free library `ChoiceFree/` (root file `ChoiceFree.lean`, with a module docstring listing everything) now proves, all `sorry`-free:

* Church-Rosser for β (Takahashi's complete developments), uniqueness of normal forms, consistency of the β-theory, `Ω` has no normal form, and the fixed-point theorem `∃ X, X —→ F ⬝ X`.
* General rewriting theory: strong commutation implies commutation of the closures, and the **Hindley-Rosen lemma** (stated for arbitrary relations, proved with *no* axioms at all).
* **η-reduction**: stability under renaming/substitution, inversion of steps out of renamed terms, subcommutativity and hence confluence, termination of η, and commutation of β with η.
* **Church-Rosser for βη**, plus uniqueness of βη-normal forms and consistency of the βη-theory.
* **η-postponement** (new, `ChoiceFree/Postponement.lean`): via a parallel η-reduction relation, every βη-sequence is β-steps followed by η-steps; equivalently `—→βη*` is exactly `—→β*` then `—→η*`.
* **Simple types** (`ChoiceFree/SimpleTypes.lean`): typing judgement, renaming and substitution lemmas, and **subject reduction** for β, η and βη. (Types are *not* unique in this Curry-style system — `ƛ #0 : A ⇒ A` for every `A` — so that claim was dropped, with a comment in the file.)
* **Strong normalisation of the simply typed λ-calculus** (new, `ChoiceFree/StrongNormalization.lean`) by Tait's reducibility method: CR1–CR3, reducible inhabitants at every type and scope, the fundamental theorem of logical relations, and `Typed.strongly_normalizing`. A boolean redex test then gives, constructively, that every typed term *has* a β-normal form; `Ω` is therefore not typable. Also **canonical forms**: every closed β-normal term is an abstraction, so every closed typed term β-reduces to an abstraction.
* **Church numerals** (new, `ChoiceFree/Church.lean`): they are β-normal, the map `k ↦ church k` is injective, hence **distinct Church numerals are not β-convertible**; they are simply typable at `(A ⇒ A) ⇒ A ⇒ A` and so strongly normalising.

The whole project builds cleanly with no `sorry` and no added axioms; all work is committed and pushed. The Properties table lists the new results alongside the earlier ones.


# Summary of changes for run 4c3649fb-84ee-4891-a746-f1dfeb3ae810
All three requested topics are now formalized and proved on top of the existing Church-Rosser development, with no `sorry` anywhere; the whole project builds, and the main results depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Everything is stated on the packaged terms (`SigmaTerm` = free-variable index + term tree), which is how reduction has to be phrased here, since `Term s` records the *exact* set of free variables and a β-step generally changes it.

**1. Uniqueness of normal forms and consistency** (`ChurchRosser/NormalForm.lean`)
- Inversion of β-steps out of an application, and normality of the constructors (`NormalS.app`, `NormalS.abs_iff`).
- `normalForm_unique`: a term reduces to at most one normal form.
- `not_betaEqS_of_ne_normal` / `betaEqS_iff_eq_of_normal`: **two distinct normal forms are never β-convertible** — the strong form of consistency (the earlier concrete `consistency` for `#0` vs `λ.#0` is now an instance).
- `HasNormalFormS` (having a normal form) together with its invariance along reduction and under β-conversion.

**2. Fixed points and Ω** (`ChurchRosser/Combinators.lean`)
- `stepS_omega_iff` / `betaStarS_omega_iff`: Ω = (λx.xx)(λx.xx) reduces to nothing but itself, hence `omega_hasNoNormalForm`: **Ω has no normal form**, and `omega_not_betaEqS_normal`: Ω is not convertible to any normal form.
- `Y_fixed_point`: Curry's `Y` satisfies `Y F ≡β F (Y F)`; `theta_fixed_point`: Turing's `Θ` satisfies the equation as a *reduction*, `Θ F ⇒β* F (Θ F)`.
- `fixed_point_theorem`: every term `F` has a fixed point `X` with `X ⇒β* F X` (hence `X ≡β F X`).

**3. Church-numeral arithmetic** (`ChurchRosser/Church.lean`, `ChurchRosser/Encodings.lean`)
- `church n` and `church_app`: the defining property `⌜n⌝ F X ⇒β* Fⁿ X`.
- `succ_church`: `succ ⌜n⌝ ⇒β* ⌜n+1⌝`; `plus_church`: `plus ⌜m⌝ ⌜n⌝ ⇒β* ⌜m+n⌝`; `mult_church`: `mult ⌜m⌝ ⌜n⌝ ⇒β* ⌜m·n⌝`; `pred_church`: Kleene's predecessor, `pred ⌜n⌝ ⇒β* ⌜n∸1⌝`.
- `normalS_church`, `church_inj`, `church_betaEqS_iff`: numerals are normal forms and `⌜m⌝ ≡β ⌜n⌝ ↔ m = n`, so the arithmetic above really computes.
- The numerals and successor of the source file are shown to be these very terms (`pack_Term_zero/one/two/succ`), with `succ ⌜0⌝ ⇒β* ⌜1⌝` and `succ ⌜1⌝ ⇒β* ⌜2⌝` stated directly for `Term.zero`, `Term.one`, `Term.two`, `Term.succ`.

**Further fundamental theorems I added** (answering "what else can be proved?")
- `ChurchRosser/Encodings.lean`: Church booleans and conditional (`ifte_tru`, `ifte_fls`), pairing and projections (`fst_pair`, `snd_pair`), the zero test (`iszero_church_zero/succ`), and `Ω` not being convertible to any numeral or boolean.
- `ChurchRosser/TermModel.lean`: the combinators `K` and `S` with their equations, which descend to the quotient of terms by β-conversion: the term model is a combinatory algebra (`BetaQuot.k_eq`, `BetaQuot.s_eq`), nontrivial and infinite (`BetaQuot.church_injective`).
- `ChurchRosser/FreeVars.lean`: β-reduction never creates free variables — the exact free-variable index can only shrink — so closed terms reduce to closed terms; in particular the numerals are closed.
- `ChurchRosser/Examples.lean` gains worked examples (2+3=5, 2·3=6, pred 3 = 2, Ω, fixed points).

Other natural next steps, listed in the module documentation of `ChurchRosser.lean` but not carried out: normalization of the leftmost-outermost strategy (a corollary of the standardization theorem already proved here, but it requires formalizing the strategy itself), η-reduction and Church-Rosser for βη, Böhm's separation theorem, and undecidability of β-conversion.

`ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 7bbcf238-3f31-479f-b7d8-22184150cfd4
The Church-Rosser development is now built on Mathlib's relational API, and the standardization theorem is proved. Everything compiles with no `sorry`; the main results depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Reusing Mathlib's `Relation` constructs.** Since `Term s` is indexed by the *exact* free-variable set, a β-step changes the index, so reduction cannot be an ordinary relation on `Term s`. The fix is to state it on the packaged terms `SigmaTerm` (index + term tree), which is an ordinary type: `StepS : SigmaTerm → SigmaTerm → Prop` (`ChurchRosser/Reduction.lean`). All closures are then Mathlib's, and the hand-written inductives are gone:
- `⇒βs*` = `Relation.ReflTransGen StepS`, `≡βs` = `Relation.EqvGen StepS`, joinability = `Relation.Join`;
- the heterogeneous relations on indexed terms, `BetaStarH` (`⇒β*`) and `BetaEqH` (`≡β`), are now *definitions* in terms of those closures, with all their former constructors kept as lemmas, so existing statements are unchanged;
- congruence rules are instances of `Relation.ReflTransGen.lift`; `betaStarH_of_reflTransGen` bridges the index-preserving `⇒β` of the source file.

**Church-Rosser from Mathlib.** `parS_diamond` supplies the diamond property in exactly the shape `Relation.church_rosser` expects, and confluence (`beta_confluence_S`, `beta_confluence`, `beta_confluence_of_reflTransGen`) is obtained from it, together with `Relation.ReflTransGen.mono` and `Relation.reflTransGen_of_transitive_reflexive` for passing between β- and parallel reduction. The Church-Rosser theorem for conversion (`church_rosser_S`, `church_rosser`) comes from `Relation.equivalence_join`, `Relation.EqvGen.mono`, `Relation.join_of_single` and `Equivalence.eqvGen_iff`.

**Standardization** (`ChurchRosser/Standardization.lean`). Head reduction `HeadS` and standard reduction `Standard` (Takahashi's inductive characterisation: head redexes first, then structurally under `λ` and in applications) are defined, and `standardization : t ⇒βs* u ↔ Standard t u` is proved — i.e. every β-reduction can be performed by a standard reduction sequence. `standardization_H` is the same on indexed terms and `standardization_of_reflTransGen` starts from the source file's `⇒β`. The proof is Takahashi's: `Standard` is closed under shifting and substitution, satisfies `Standard t (λp) → Standard u q → Standard (t u) p[q]`, and absorbs a parallel step on the right, so it contains many-step parallel reduction, which coincides with `⇒βs*`. Corollary `head_reduction_of_betaStarS_abs`: if a term β-reduces to an abstraction, head reduction alone already reaches an abstraction.

**Further Mathlib reuse** (`ChurchRosser/Consistency.lean`): normal forms (`NormalS`), with "a normal form reduces only to itself" from `Relation.reflTransGen_iff_eq`; uniqueness of normal forms; β-convertible normal forms are equal; the setoid `Relation.EqvGen.setoid StepS` and the quotient `BetaQuot` of terms modulo β, with `abs`/`app` descending via `Quotient.map`/`Quotient.map₂` and `⟦t⟧ = ⟦u⟧ ↔` joinable; consistency of the β-theory (`#0` and `λ.#0` are not convertible), hence `BetaQuot` has at least two elements. A `Std.Refl ParS` instance mirrors the reflexivity instance of the original file, and `ChurchRosser/Examples.lean` gains standardization and consistency examples.

# Summary of changes for run 58c87546-7d72-4508-ad01-d43b7f1646cf
The Church-Rosser development no longer uses an auxiliary untyped ("raw") syntax: everything is now proved directly on the `Finset`-indexed `Term`, and every operation whose result index is not determined by its inputs returns an existential — a sigma-style package of the new free-variable index set together with the resulting term tree.

The core of the new approach (`ChurchRosser/SigmaTerm.lean`):

```lean
structure SigmaTerm where
  newFreeIndexes : Finset Nat
  betaReducedTermTree : Term newFreeIndexes
```

with `pack`, the operations `SigmaTerm.var/abs/app/shift/subst`, their computation rules, an induction principle, injectivity/disjointness of the three shapes, and the full substitution calculus (`shift_shift`, `subst_shift`, `shift_subst_le`, `shift_subst_ge`, `subst_subst`). Packaging the index with the term makes all these lemmas ordinary homogeneous equations, so no heterogeneous-equality bookkeeping and no untyped syntax are needed.

Files:
- `ChurchRosser/SigmaTerm.lean` — the packaging and the substitution calculus (above).
- `ChurchRosser/Reduction.lean` — heterogeneous many-step β-reduction `⇒β*`, β-conversion `≡β`, their congruence rules, and `betaStarH_of_reflTransGen` bridging the index-preserving closure `⇒β` of the source file.
- `ChurchRosser/Parallel.lean` — parallel reduction `⇉β` (with its packaged form `ParS`, induction/case principles and abstraction inversion), preservation under shifting and substitution, Takahashi's complete development `takahashi : Term s → SigmaTerm`, the triangle lemma, and the diamond property `betaParH_diamond` (its common reduct is literally the pair `(takahashi M).newFreeIndexes`, `(takahashi M).betaReducedTermTree`).
- `ChurchRosser/Basic.lean` — many-step parallel reduction, the strip lemma, `beta_confluence`, `beta_confluence_of_reflTransGen` and `church_rosser`, all delivering the common reduct existentially as an index plus a term at that index.
- `ChurchRosser/Examples.lean` — sanity checks, including the substitution examples from the source file and two examples computing `takahashi`, one of which shows the free-variable index shrinking from `{0,5}` to `{0}`.

The previous `Raw`-based files (`Raw.lean`, `RawConfluence.lean`, `Erase.lean`) have been deleted, and the results that used to be transported through them are now proved directly. The whole project builds cleanly from scratch with no `sorry`; the main theorems depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`. All work is committed and pushed.

# Summary of changes for run fbdaf431-88a1-4aca-a202-eebef073798c
Church-Rosser is now proved, with no `sorry`s, for the `Finset`-indexed `Term` of `Basic41FinsetNOfFreeIsExact.lean`, following the same Takahashi-style route as the Agda development you linked (parallel reduction → complete development → diamond → confluence).

New material lives in `ChurchRosser.lean` and the `ChurchRosser/` directory (added as a library in `lakefile.toml`; the whole project builds cleanly):

- `ChurchRosser/Raw.lean` — untyped de Bruijn terms `Raw` with `shift`/`subst`, and the substitution calculus: `shift_shift`, `subst_shift`, `shift_subst_le`, `shift_subst_ge` and the substitution lemma `subst_subst`.
- `ChurchRosser/RawConfluence.lean` — one-step `Step`, parallel `Par`, Takahashi's complete development `takahashi`, the triangle lemma, the diamond property and `Raw.star_confluence`.
- `ChurchRosser/Erase.lean` — `erase : Term s → Raw` and `reify : (r : Raw) → Term (Raw.fv r)`, with `fv_erase` (the index of a term is exactly the free-variable set of its erasure), injectivity of `erase` up to `HEq`, and compatibility of `erase` with `shift` and `subst`.
- `ChurchRosser/Basic.lean` — the main results: `beta_confluence`, `beta_confluence_of_reflTransGen` and `church_rosser`.
- `ChurchRosser/Parallel.lean` — parallel reduction `⇉β` directly on indexed terms, its relation to single/multi-step reduction, and `betaParH_diamond`.
- `ChurchRosser/Examples.lean` — sanity checks, including a concrete β-reduction.

One formulation point worth flagging: since `Term s` is indexed by the *exact* free-variable set, a β-step generally changes that index (e.g. `(λ.#1) #5` indexed by `{0,5}` reduces to `#0` indexed by `{0}`). So `Relation.ReflTransGen BetaStep` (the `⇒β` of your file) only relates terms whose index never changes along the entire reduction. I therefore added the heterogeneous closure `BetaStarH` (`⇒β*`) and conversion `BetaEqH` (`≡β`), stated confluence as: from `M ⇒β* N₁` and `M ⇒β* N₂` there are `t` and `D : Term t` with `N₁ ⇒β* D` and `N₂ ⇒β* D`, and Church-Rosser as: `M ≡β N` implies `M` and `N` have a common reduct. `beta_confluence_of_reflTransGen` gives the corresponding statement starting from your `⇒β`, and `betaStarH_of_reflTransGen` bridges the two closures.

Also: three `#guard` substitution checks in `Basic41FinsetNOfFreeIsExact.lean` (cases 4–6) do not run in this environment — the interpreter reports that no native implementation of `Multiset.bind` is available — which made the file fail to build. I commented them out (with an explanatory note, nothing deleted) and proved the same three equalities propositionally in `ChurchRosser/Examples.lean`, so the checks are still verified.
