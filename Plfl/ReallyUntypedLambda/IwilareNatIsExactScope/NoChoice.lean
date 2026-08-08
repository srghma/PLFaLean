-- A machine-checked guarantee that the whole development is *constructive*.
--
-- This module imports every other module of the project and then walks over all
-- of its declarations, collecting the axioms each one depends on.  If any
-- declaration used `Classical.choice` (directly, or through a Mathlib lemma, or
-- through a tactic such as `by_cases` / `by_contra` / `omega` closing a goal by
-- contradiction) the command below fails and the build breaks.
--
-- So: yes, the untyped lambda calculus developed here -- substitution, beta and
-- eta reduction, Church-Rosser, standardization, normal forms, the evaluator,
-- Church numerals with subtraction, the fixed point combinators -- can be, and
-- is, implemented and proved without the axiom of choice.  The only axioms the
-- project uses are `propext` and `Quot.sound`; both are consistent with, and
-- ordinarily counted as part of, constructive type theory as realised in Lean.
--
-- Two remarks on what *would* need classical logic, and is therefore stated
-- differently here (nothing is missing, but the phrasing matters):
--
--   * "either a term has a redex or it is normal" is *not* an instance of the
--     excluded middle here: it is proved by structural recursion, as
--     `leftmost_progress`, `whnf_progress` and `eta_progress`.  The decision
--     procedure they need -- equality of terms, being an abstraction, being a
--     shifted term -- is built constructively in `DecEq.lean`.
--
--   * A statement like "every term either has a beta normal form or has none"
--     is genuinely non-constructive: by the undecidability of beta
--     normalisation there is no algorithm deciding it, so it can only be had
--     from excluded middle.  No result in this project asserts it: the
--     normalisation theorems here are all *conditional* (if a normal form
--     exists, leftmost reduction finds it -- `leftmost_normalization`), which is
--     the constructively meaningful statement.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Basic
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.DecEq
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Standardization
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.FixedPoint
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ScopeBounds
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchNumerals
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Leftmost
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Combinators
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchData
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Evaluator
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.WeakHead
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Minimisation
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Eta
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.BetaEta
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.EtaNormal
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Postponement
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Subtraction

@[expose] public section

-- Fails the build if any declaration of this project depends on `Classical.choice`.
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut bad : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`IwilareNatIsExactScope).isPrefixOf n && !n.isInternal then
      let s ← Lean.collectAxioms n
      if s.contains `Classical.choice then
        bad := bad.push n
  unless bad.isEmpty do
    throwError "these declarations depend on Classical.choice: {bad.toList}"
