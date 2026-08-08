module
prelude

-- - title: "Part 2: Programming Language Foundations"
--   chapter:
--   - include: src/plfa/part2/Lambda.lagda.md
--   - include: src/plfa/part2/Properties.lagda.md
--   - include: src/plfa/part2/DeBruijn.lagda.md
--   - include: src/plfa/part2/More.lagda.md
--   - include: src/plfa/part2/Bisimulation.lagda.md
--   - include: src/plfa/part2/Inference.lagda.md
--   - include: src/plfa/part2/Untyped.lagda.md
--   - include: src/plfa/part2/Confluence.lagda.md
--   - include: src/plfa/part2/BigStep.lagda.md
-- - title: "Part 3: Denotational Semantics"
--   chapter:
--   - include: src/plfa/part3/Denotational.lagda.md
--   - include: src/plfa/part3/Compositional.lagda.md
--   - include: src/plfa/part3/Soundness.lagda.md
--   - include: src/plfa/part3/Adequacy.lagda.md
--   - include: src/plfa/part3/ContextualEquivalence.lagda.md
-- - backmatter: True
--   title: "Appendix"
--   chapter:
--   - include: src/plfa/part2/Substitution.lagda.md
--     epub-type: appendix

public import Plfl.Lambda
public import Plfl.Lambda.Properties
public import Plfl.DeBruijn
public import Plfl.More
public import Plfl.More.DoubleSubst
public import Plfl.More.Bisimulation
public import Plfl.More.Inference
public import Plfl.Untyped
public import Plfl.Untyped.Substitution
public import Plfl.Untyped.Confluence
public import Plfl.Untyped.BigStep
public import Plfl.Untyped.Denotational
public import Plfl.Untyped.Denotational.Compositional
public import Plfl.Untyped.Denotational.Soundness
public import Plfl.Untyped.Denotational.Adequacy
public import Plfl.Untyped.Denotational.ContextualEquivalence
public import Plfl.ReallyUntypedLambda.Ernius.Term
public import Plfl.ReallyUntypedLambda.DanelnovButBetaIsNotProp.Defs
public import Plfl.ReallyUntypedLambda.Iwilare
public import Plfl.ReallyUntypedLambda.Basic1
public import Plfl.ReallyUntypedLambda.Basic2ScopeAndDepth
public import Plfl.ReallyUntypedLambda.Basic3Typed
public import Plfl.ReallyUntypedLambda.Basic41Finset
public import Plfl.ReallyUntypedLambda.Basic42Bitmask
public import Plfl.ReallyUntypedLambda.Basic43BitVec

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Basic
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.BetaEta
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchData
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchNumerals
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Combinators
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.DecEq
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Eta
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.EtaNormal
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Evaluator
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.FixedPoint
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Leftmost
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Minimisation
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NoChoice
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Postponement
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ScopeBounds
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Standardization
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Subtraction
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.WeakHead

public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.Basic
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Axioms
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Beta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.BetaEta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Church
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Commutation
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Confluence
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.DeBruijn
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Eta
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Postponement
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Rename
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.SimpleTypes
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.StrongNormalization
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Basic
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Church
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Combinators
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Consistency
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Encodings
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Examples
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.FreeVars
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Parallel
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Reduction
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.SigmaTerm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Standardization
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.TermModel
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.Scratch

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Basic
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.BetaEta
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchData
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchNumerals
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Combinators
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Eta
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.EtaNormal
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Evaluator
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.FixedPoint
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Leftmost
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Minimisation
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NoChoice
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Postponement
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ScopeBounds
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Standardization
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Subtraction
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.WeakHead
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Alpha
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Multiway
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Positions
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Strategies
