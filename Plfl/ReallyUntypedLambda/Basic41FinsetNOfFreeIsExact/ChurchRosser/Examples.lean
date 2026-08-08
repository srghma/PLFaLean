module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Standardization
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Consistency
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Encodings
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.TermModel

@[expose] public section

/-!
# Examples and sanity checks

Propositional versions of the substitution checks of
`Basic41FinsetNOfFreeIsExact.lean` (which cannot be run with `#guard` in this
environment), plus a small β-reduction example.
-/

namespace Basic41FinsetNOfFreeIsExact

/-- Two terms packaging to the same `SigmaTerm` are `Term.beq`-equal. -/
theorem beq_of_pack_eq {s1 s2 : Finset Nat} (t1 : Term s1) (t2 : Term s2)
    (h : pack t1 = pack t2) : Term.beq t1 t2 = true := by
  obtain ⟨rfl, hh⟩ := pack_eq_iff.mp h
  cases hh
  exact termBEq_refl t1

-- 4. Substitution under λ-abstraction: (λ. x_1)[0 := x_42] ⟹ λ. x_43
example :
    Term.beq (subst 0 (Term.var 42 : Term {42}) (⟦ ƛ (Term.var 1) ⟧ : Term {0}))
      (⟦ ƛ (Term.var 43) ⟧ : Term {42}) = true :=
  beq_of_pack_eq _ _ (by simp)

-- 5. Shadowing inside λ: (λ. x_0)[0 := x_42] ⟹ λ. x_0
example :
    Term.beq (subst 0 (Term.var 42 : Term {42}) (⟦ ƛ (Term.var 0) ⟧ : Term ∅))
      (⟦ ƛ (Term.var 0) ⟧ : Term ∅) = true :=
  beq_of_pack_eq _ _ (by simp)

-- 6. Real β-step substitution: (x_0 x_1)[0 := x_99] ⟹ x_99 x_0
example :
    Term.beq (subst 0 (Term.var 99 : Term {99}) (⟦ Term.var 0 ⬝ Term.var 1 ⟧ : Term {0, 1}))
      (⟦ Term.var 99 ⬝ Term.var 0 ⟧ : Term {0, 99}) = true :=
  beq_of_pack_eq _ _ (by
    rw [pack_castTerm, SigmaTerm.pack_subst, pack_castTerm, SigmaTerm.pack_app, SigmaTerm.pack_var,
      SigmaTerm.pack_var, SigmaTerm.subst_app, SigmaTerm.subst_var]
    dsimp
    rw [SigmaTerm.subst_var]
    dsimp
    rfl)

/-- `(λ x. x) x₅` β-reduces to `x₅`; note that the free-variable index changes
from `unbind {0} ∪ {5}` to `{5}` along the way. -/
example : BetaStarH (Term.app (Term.abs (Term.var 0)) (Term.var 5)) (Term.var 5) :=
  betaStarH_congr_right
    (BetaStarH.single (BetaStep.head (Term.var 0) (Term.var 5)))
    (by simp)

/-- The complete development of `(λ x. x) x₅` is `x₅`, returned together with its
free-variable index. -/
example : takahashi (Term.app (Term.abs (Term.var 0)) (Term.var 5)) = SigmaTerm.var 5 := by
  rw [takahashi, takahashi, takahashi, SigmaTerm.subst_var, if_pos rfl]

/-- Developing `(λ x. x₁) x₅` yields `x₀`: the free-variable index returned by
`takahashi` is `{0}`, whereas the index of the original term is `{0, 5}`. -/
example :
    (takahashi (Term.app (Term.abs (Term.var 1)) (Term.var 5))).newFreeIndexes = {0} := by
  rw [takahashi, takahashi, takahashi, SigmaTerm.subst_var, if_neg (by decide),
    if_pos (by decide)]
  rfl

/-! ### Standardization -/

/-- The identity, as a packaged term. -/
private def I : SigmaTerm := SigmaTerm.abs (SigmaTerm.var 0)

private theorem betaStarS_I (u : SigmaTerm) : I.app u ⇒βs* u := by
  have h := StepS.head (SigmaTerm.var 0) u
  rw [SigmaTerm.subst_var, if_pos rfl] at h
  exact Relation.ReflTransGen.single h

/-- The inner-first (hence non-standard) reduction of `I (I x₅)` to `x₅` is
matched, by the standardization theorem, by a standard reduction. -/
example : Standard (I.app (I.app (SigmaTerm.var 5))) (SigmaTerm.var 5) :=
  standardization.mp
    ((betaStarS_app_right I (betaStarS_I (SigmaTerm.var 5))).trans
      (betaStarS_I (SigmaTerm.var 5)))

/-- Standard reductions really do start with the head redexes: `I (I x₅)` first
contracts its head redex. -/
example : Standard (I.app (I.app (SigmaTerm.var 5))) (SigmaTerm.var 5) := by
  refine Standard.head (HeadS.beta (SigmaTerm.var 0) (I.app (SigmaTerm.var 5))) ?_
  rw [SigmaTerm.subst_var, if_pos rfl]
  exact standardization.mp (betaStarS_I (SigmaTerm.var 5))

/-! ### Consistency -/

/-- `x₀` and the identity are not β-convertible. -/
example : ¬ (SigmaTerm.var 0 ≡βs I) := consistency

/-! ### Arithmetic, fixed points and non-termination -/

/-- `2 + 3 = 5`, computed by β-reduction of Church numerals. -/
example : SigmaTerm.app (SigmaTerm.app plusTerm (church 2)) (church 3) ⇒βs* church 5 :=
  plus_church 2 3

/-- `2 * 3 = 6`, computed by β-reduction of Church numerals. -/
example : SigmaTerm.app (SigmaTerm.app multTerm (church 2)) (church 3) ⇒βs* church 6 :=
  mult_church 2 3

/-- `pred 3 = 2`. -/
example : SigmaTerm.app predTerm (church 3) ⇒βs* church 2 := pred_church 3

/-- `⌜2⌝` and `⌜3⌝` are not β-convertible. -/
example : ¬ (church 2 ≡βs church 3) := fun h => by simpa using church_betaEqS_iff.mp h

/-- `Ω` has no normal form, and is not convertible to any numeral. -/
example : ¬ HasNormalFormS omega := omega_hasNoNormalForm

example : ¬ (omega ≡βs church 0) := omega_not_betaEqS_church 0

/-- Every term has a fixed point. -/
example (F : SigmaTerm) : ∃ X, X ≡βs SigmaTerm.app F X :=
  ⟨_, (fixed_point_theorem F).choose_spec.2⟩

end Basic41FinsetNOfFreeIsExact
