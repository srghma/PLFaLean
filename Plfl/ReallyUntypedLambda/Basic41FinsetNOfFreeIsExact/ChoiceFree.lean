module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.DeBruijn
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Rename
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Beta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Confluence
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Commutation
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Eta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.BetaEta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.SimpleTypes
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.StrongNormalization
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Church
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Postponement

/-!
# A choice-free λ-calculus development

This library answers two questions about the Church-Rosser development of
`ChurchRosser`:

**Can it be done without `Classical.choice`?**  Not for
`Basic41Finset.Term`: that type is indexed by a `Finset Nat`, and Mathlib's
`Finset.erase`, `Finset.image` and `Finset.union` — which occur in the
*constructors* of the type — are classical, so `Classical.choice` appears in the
axioms of the type itself, before any theorem about it is stated.  It *can* be
done for a `Finset`-free presentation of the same calculus: the intrinsically
*scoped* terms `Iwilare.Term : Nat → Type` (free de Bruijn indices `< n`,
variables `Fin n`) of the Agda development this project follows.  Every result
in this library depends only on `propext` and `Quot.sound`; `ChoiceFree.Axioms`
records this in machine-checked form.

**What other fundamental theorems can be proved?**  Besides re-proving
Church-Rosser choice-free, this library adds:

* uniqueness of β-normal forms and consistency of the β-theory
  (`ChoiceFree.NormalForm`);
* `Ω` has no normal form, and the fixed point theorem: every term `F` has an
  `X` with `X —→ F ⬝ X` in one step (`ChoiceFree.NormalForm`);
* general rewriting theory: strong commutation implies commutation of the
  closures, and the **Hindley-Rosen lemma** (`ChoiceFree.Commutation`), stated
  for arbitrary relations and proved with no axioms at all;
* **η-reduction** (`ChoiceFree.Eta`): stability under renaming and
  substitution, inversion of a step out of a renamed term (via the pullback
  lemma of `ChoiceFree.Rename`), subcommutativity and hence confluence of η,
  termination of η, and the commutation of β with η;
* **the Church-Rosser theorem for βη** (`ChoiceFree.BetaEta`), obtained from the
  three previous ingredients by Hindley-Rosen, with uniqueness of βη-normal
  forms and consistency of the βη-theory;
* **simple types** (`ChoiceFree.SimpleTypes`): the typing judgement, its
  renaming and substitution lemmas, and **subject reduction** for β, for η and
  hence for βη;
* **strong normalisation of the simply typed λ-calculus**
  (`ChoiceFree.StrongNormalization`), by Tait's reducibility method, together
  with a decision procedure for the presence of a β-redex, so that every typed
  term is shown *constructively* to have a β-normal form, and `Ω` is shown not
  to be typable;
* **canonical forms**: every closed β-normal term is an abstraction, so every
  closed typed term β-reduces to an abstraction
  (`ChoiceFree.StrongNormalization`);
* **the Church numerals** (`ChoiceFree.Church`): they are normal, pairwise
  distinct, hence pairwise non-convertible, and simply typable;
* **η-postponement** (`ChoiceFree.Postponement`): every βη-reduction sequence
  can be rearranged into β-steps followed by η-steps, so `—→βη*` is exactly
  `—→β*` followed by `—→η*`.

Files:

* `ChoiceFree.DeBruijn` — syntax, renamings, substitutions, and the
  substitution calculus.
* `ChoiceFree.Rename` — renamings by bare index functions, insertion
  renamings, and the pullback lemma.
* `ChoiceFree.Beta` — β-reduction, parallel reduction, and the fact that their
  reflexive-transitive closures agree.
* `ChoiceFree.Confluence` — Takahashi's complete development, the triangle
  lemma, the diamond property, confluence, and Church-Rosser.
* `ChoiceFree.NormalForm` — normal forms, consistency, `Ω`, fixed points.
* `ChoiceFree.Commutation` — commuting relations and the Hindley-Rosen lemma.
* `ChoiceFree.Eta` — η-reduction and its interaction with β.
* `ChoiceFree.BetaEta` — confluence and Church-Rosser for βη.
* `ChoiceFree.SimpleTypes` — simple types and subject reduction.
* `ChoiceFree.StrongNormalization` — Tait reducibility, strong normalisation
  and normal forms of typed terms.
* `ChoiceFree.Church` — Church numerals and their non-convertibility.
* `ChoiceFree.Postponement` — parallel η-reduction and η-postponement.
* `ChoiceFree.Axioms` — the axiom audit (this file is not imported here, since
  `#print axioms` is not available inside a module).
-/
