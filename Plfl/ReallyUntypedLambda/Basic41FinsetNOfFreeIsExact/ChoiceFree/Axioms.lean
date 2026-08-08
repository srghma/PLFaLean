module
import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.BetaEta
import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.StrongNormalization
import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Church
import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Postponement
import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser

/-!
# Axiom audit: where `Classical.choice` comes from, and how to avoid it

This file records, in machine-checked form (`#guard_msgs` around
`#print axioms`), the answer to the question *"can this be done without
`Classical.choice`?"*.

## 1. For `Basic41Finset.Term` the answer is **no**

`Basic41Finset.Term` is indexed by the exact set of free variables, a
`Finset Nat`, and its constructors use `Basic41Finset.unbind` (built from
`Finset.erase` and `Finset.image`) and `Finset.union`.  In Mathlib those three
operations are *defined* by lifting a list operation through the quotient
`Multiset`, and the well-definedness proofs (`List.Perm.erase`,
`List.Perm.dedup`, …) are themselves proved using `Classical.choice`.  So
`Classical.choice` already occurs in the axioms of the **type** `Term` itself,
and therefore in every statement that mentions it — no proof, however
constructive, can remove it.

## 2. In a `Finset`-free formulation the answer is **yes**

Reformulating with the intrinsically *scoped* terms `Iwilare.Term : Nat → Type`
(free indices `< n`, variables `Fin n`) removes every appeal to `Finset`, and
the whole Takahashi proof of Church-Rosser goes through unchanged.  The
resulting theorems depend only on `propext` and `Quot.sound`, the two
constructively acceptable axioms of Lean's kernel; `Classical.choice` is gone.
-/

namespace ChoiceFree.Axioms

/-! ### The `Finset`-indexed development: `Classical.choice` is unavoidable -/

-- Mathlib's `Finset.erase` is already classical.
/-- info: 'Finset.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Finset.erase

/-- info: 'Finset.image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Finset.image

/-- info: 'Finset.instUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Finset.instUnion

-- Hence the free-variable operation used in the index of `Term.abs`.
/-- info: 'Basic41FinsetNOfFreeIsExact.unbind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Basic41FinsetNOfFreeIsExact.unbind

-- And hence the type `Basic41FinsetNOfFreeIsExact.Term` itself, before any theorem is stated
-- about it.
/-- info: 'Basic41FinsetNOfFreeIsExact.Term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Basic41FinsetNOfFreeIsExact.Term

/-- info:
'Basic41FinsetNOfFreeIsExact.beta_confluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Basic41FinsetNOfFreeIsExact.beta_confluence

/-! ### The intrinsically scoped development: choice-free

`Iwilare.Term` needs no axioms at all, and all the theorems about it use only
`propext` and `Quot.sound`. -/

/-- info: 'IwilareFinsetNOfFreeIsExact.Term' does not depend on any axioms -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.Term

/-- info: 'IwilareFinsetNOfFreeIsExact.takahashi_triangle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.takahashi_triangle

/-- info: 'IwilareFinsetNOfFreeIsExact.betapar_diamond' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betapar_diamond

/-- info: 'IwilareFinsetNOfFreeIsExact.beta_confluence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.beta_confluence

/-- info: 'IwilareFinsetNOfFreeIsExact.church_rosser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.church_rosser

/-- info: 'IwilareFinsetNOfFreeIsExact.normalForm_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.normalForm_unique

/-- info: 'IwilareFinsetNOfFreeIsExact.consistency' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.consistency

/-- info: 'IwilareFinsetNOfFreeIsExact.omega_hasNoNormalForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.omega_hasNoNormalForm

/-- info: 'IwilareFinsetNOfFreeIsExact.fixed_point' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.fixed_point

/-- info: 'IwilareFinsetNOfFreeIsExact.eta_confluence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.eta_confluence

/-- info: 'IwilareFinsetNOfFreeIsExact.betaStar_etaStar_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betaStar_etaStar_commute

/-- info: 'IwilareFinsetNOfFreeIsExact.betaEta_confluence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betaEta_confluence

/-- info: 'IwilareFinsetNOfFreeIsExact.betaEta_church_rosser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betaEta_church_rosser

/-- info: 'IwilareFinsetNOfFreeIsExact.betaEta_consistency' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betaEta_consistency

/-- info: 'IwilareFinsetNOfFreeIsExact.Typed.preservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.Typed.preservation

/-- info: 'IwilareFinsetNOfFreeIsExact.Typed.preservation_betaEta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.Typed.preservation_betaEta

/-- info: 'IwilareFinsetNOfFreeIsExact.Typed.strongly_normalizing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.Typed.strongly_normalizing

/-- info: 'IwilareFinsetNOfFreeIsExact.Typed.hasNormalForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.Typed.hasNormalForm

/-- info: 'IwilareFinsetNOfFreeIsExact.eta_strongly_normalizing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.eta_strongly_normalizing

/-- info: 'IwilareFinsetNOfFreeIsExact.church_not_betaEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.church_not_betaEq

/-- info: 'IwilareFinsetNOfFreeIsExact.closed_normal_is_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.closed_normal_is_abs

/-- info: 'IwilareFinsetNOfFreeIsExact.betaEtaStar_postponement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IwilareFinsetNOfFreeIsExact.betaEtaStar_postponement

-- The general rewriting lemmas need no axioms whatsoever.

/-- info: 'Relation.commute_reflTransGen' does not depend on any axioms -/
#guard_msgs in
#print axioms Relation.commute_reflTransGen

/-- info: 'Relation.reflTransGen_union_confluent' does not depend on any axioms -/
#guard_msgs in
#print axioms Relation.reflTransGen_union_confluent

end ChoiceFree.Axioms
