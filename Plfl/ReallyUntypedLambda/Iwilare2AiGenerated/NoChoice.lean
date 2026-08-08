-- A machine-checked guarantee that the whole `FinScope` development is
-- *constructive*.
--
-- This module imports every other module of the scope-bounded (`Fin`-indexed)
-- development and then walks over all of its declarations, collecting the
-- axioms each one depends on.  If any declaration used `Classical.choice`
-- (directly, or through a Mathlib lemma, or through a tactic such as
-- `by_cases` / `by_contra` / `omega` closing a goal by contradiction) the
-- command below fails and the build breaks.
--
-- So: the untyped lambda calculus developed here in its scope-bounded form --
-- substitution, beta and eta reduction, Church-Rosser, standardization, eta
-- postponement, normal forms, the evaluators, Church numerals with subtraction,
-- primitive recursion, minimisation, the fixed point combinators -- is
-- implemented and proved without the axiom of choice.  The only axioms used are
-- `propext` and `Quot.sound`.
--
-- Note that here the decision procedures the "progress" theorems need come for
-- free: `DecidableEq (Term n)` is `deriving`-generated, and being an
-- abstraction is decided by a `cases` on the term, so the hand-built
-- constructive equality test of the exactly-scoped development
-- (`IwilareNatIsExactScope/DecEq.lean`) has no counterpart in this file tree.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Basic
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ScopeBounds
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.FixedPoint
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchNumerals
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Combinators
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchData
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Eta
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.BetaEta
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.EtaNormal
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Postponement
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Standardization
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Leftmost
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.WeakHead
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Evaluator
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Minimisation
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Subtraction

@[expose] public section

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut bad : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`FinScope).isPrefixOf n && !n.isInternal then
      let s ← Lean.collectAxioms n
      if s.contains `Classical.choice then
        bad := bad.push n
  unless bad.isEmpty do
    throwError "these declarations depend on Classical.choice: {bad.toList}"
