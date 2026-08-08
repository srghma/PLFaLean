module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.SigmaTerm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Reduction
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Parallel
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Basic
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Standardization
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Consistency
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.FreeVars
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Combinators
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Church
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Encodings
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.TermModel
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Examples

/-!
# Church-Rosser and standardization for `Basic41Finset.Term`

The proof is Takahashi's, carried out directly on the `Finset`-indexed terms:
there is no auxiliary untyped syntax.  Since `Term s` records the *exact* set of
free variables of a term, an operation such as substitution or β-reduction
generally changes that index, so results are returned *existentially*, as a
`SigmaTerm`: the new free-variable index set together with the reduced term
tree.  A `SigmaTerm` is an ordinary (non-indexed) type, so all the relational
machinery is Mathlib's:

* reduction is `Relation.ReflTransGen StepS`,
* conversion is `Relation.EqvGen StepS`,
* joinability is `Relation.Join`,
* confluence is Mathlib's `Relation.church_rosser`, applied to the diamond
  property of parallel reduction,
* the equivalence-relation and quotient structure comes from
  `Relation.equivalence_join`, `Relation.EqvGen.setoid` and `Quotient`.

Files:

* `ChurchRosser.SigmaTerm` — `SigmaTerm`, the packaging of a term with its
  free-variable index, together with `shift`, `subst` and the substitution
  calculus (`shift_shift`, `subst_shift`, `shift_subst_le`, `shift_subst_ge`,
  `subst_subst`).
* `ChurchRosser.Reduction` — `StepS`, the β-step relation on packaged terms,
  the closures `⇒βs*` (`Relation.ReflTransGen`), `≡βs` (`Relation.EqvGen`) and
  `BetaJoinS` (`Relation.Join`), their congruence rules (instances of
  `Relation.ReflTransGen.lift`), and the heterogeneous reduction `⇒β*` and
  conversion `≡β` on indexed terms.
* `ChurchRosser.Parallel` — parallel reduction `⇉β` / `ParS`, Takahashi's
  complete development `takahashi`, the triangle lemma and the diamond property
  (`parS_diamond`, `betaParH_diamond`).
* `ChurchRosser.Basic` — confluence (`beta_confluence_S`, `beta_confluence`,
  `beta_confluence_of_reflTransGen`) and the Church-Rosser theorem
  (`church_rosser_S`, `church_rosser`), all obtained from
  `Relation.church_rosser`.
* `ChurchRosser.Standardization` — head reduction `HeadS`, standard reduction
  `Standard`, and the standardization theorem `standardization` :
  `t ⇒βs* u ↔ Standard t u` (`standardization_H` on indexed terms), with the
  head-reduction corollary `head_reduction_of_betaStarS_abs`.
* `ChurchRosser.Consistency` — normal forms, uniqueness of normal forms, the
  quotient `BetaQuot` of terms by β-conversion, and consistency of the β-theory.
* `ChurchRosser.NormalForm` — inversion of β-steps, normality of the
  constructors, having a normal form and its invariance under conversion, and
  the fact that two distinct normal forms are never β-convertible.
* `ChurchRosser.FreeVars` — β-reduction does not create free variables (the
  free-variable index can only shrink), so closed terms reduce to closed terms.
* `ChurchRosser.Combinators` — `Ω` has no normal form; Curry's `Y` and Turing's
  `Θ` are fixed-point combinators; the fixed-point theorem.
* `ChurchRosser.Church` — Church numerals, and correctness of the successor,
  addition and multiplication combinators; numerals are distinct normal forms.
* `ChurchRosser.Encodings` — Church booleans, the conditional, pairs and their
  projections, the zero test, and Kleene's predecessor.
* `ChurchRosser.TermModel` — the combinators `K` and `S` and their equations in
  the term model `BetaQuot`, which is therefore a nontrivial (indeed infinite)
  combinatory algebra.
* `ChurchRosser.Examples` — small sanity checks.

Natural further developments, not carried out here: normalization of the
leftmost-outermost strategy (a corollary of standardization, but it requires
formalizing the strategy itself), η-reduction and the Church-Rosser property of
βη, the Böhm separation theorem, and undecidability of β-conversion.
-/
