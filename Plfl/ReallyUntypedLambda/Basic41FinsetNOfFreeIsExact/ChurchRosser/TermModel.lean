module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Encodings

@[expose] public section

/-!
# The combinators `K` and `S`, and the term model

`K = λx. λy. x` and `S = λx. λy. λz. x z (y z)` satisfy their defining
equations, and these equations descend to the quotient of terms by
β-conversion.  So `BetaQuot` — the term model — is a combinatory algebra: a
nontrivial applicative structure with elements `K` and `S` satisfying
`K x y = x` and `S x y z = x z (y z)`.

* `Basic41Finset.kComb_app`, `Basic41Finset.sComb_app` — the combinator
  equations, as reductions;
* `Basic41Finset.BetaQuot.k_eq`, `Basic41Finset.BetaQuot.s_eq` — the same
  equations in the term model;
* `Basic41Finset.BetaQuot.k_ne_id` — the term model is nontrivial.
-/

namespace Basic41FinsetNOfFreeIsExact

open SigmaTerm

/-- The combinator `K = λx. λy. x` (the Church boolean `true`). -/
def kComb : SigmaTerm := tru

/-- The combinator `S = λx. λy. λz. x z (y z)`. -/
def sComb : SigmaTerm := abs (abs (abs (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

/-- `K M N` reduces to `M`. -/
theorem kComb_app (M N : SigmaTerm) : app (app kComb M) N ⇒βs* M := tru_app M N

/-- `S M N P` reduces to `M P (N P)`. -/
theorem sComb_app (M N P : SigmaTerm) :
    app (app (app sComb M) N) P ⇒βs* app (app M P) (app N P) := by
  have step1 : app sComb M →βs
      abs (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 M)) (var 0))
        (app (var 1) (var 0)))) := by
    have h := StepS.head (abs (abs (app (app (var 2) (var 0)) (app (var 1) (var 0))))) M
    simpa [sComb] using h
  have step2 : app (abs (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 M)) (var 0))
        (app (var 1) (var 0))))) N →βs
      abs (app (app (SigmaTerm.shift 0 M) (var 0)) (app (SigmaTerm.shift 0 N) (var 0))) := by
    have h := StepS.head (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 M)) (var 0))
      (app (var 1) (var 0)))) N
    simpa using h
  refine Relation.ReflTransGen.head (StepS.app_left (StepS.app_left step1 N) P)
    (Relation.ReflTransGen.head (StepS.app_left step2 P) (Relation.ReflTransGen.single ?_))
  have h := StepS.head (app (app (SigmaTerm.shift 0 M) (var 0))
    (app (SigmaTerm.shift 0 N) (var 0))) P
  simpa [SigmaTerm.subst_shift] using h

/-! ### The equations in the term model -/

/-- `K x y = x` holds in the term model. -/
theorem BetaQuot.k_eq (x y : BetaQuot) :
    BetaQuot.app (BetaQuot.app (BetaQuot.mk kComb) x) y = x := by
  induction x using Quotient.inductionOn with
  | h t =>
    induction y using Quotient.inductionOn with
    | h u =>
      exact BetaQuot.mk_eq_mk.mpr (eqvGen_of_reflTransGen (kComb_app t u))

/-- `S x y z = x z (y z)` holds in the term model. -/
theorem BetaQuot.s_eq (x y z : BetaQuot) :
    BetaQuot.app (BetaQuot.app (BetaQuot.app (BetaQuot.mk sComb) x) y) z =
      BetaQuot.app (BetaQuot.app x z) (BetaQuot.app y z) := by
  induction x using Quotient.inductionOn with
  | h t =>
    induction y using Quotient.inductionOn with
    | h u =>
      induction z using Quotient.inductionOn with
      | h v =>
        exact BetaQuot.mk_eq_mk.mpr (eqvGen_of_reflTransGen (sComb_app t u v))

/-- The term model is infinite: the Church numerals give pairwise distinct
elements. -/
theorem BetaQuot.church_injective :
    Function.Injective (fun n : Nat => BetaQuot.mk (church n)) := by
  intro m n h
  exact church_betaEqS_iff.mp (BetaQuot.mk_eq_mk.mp h)

/-- The term model is nontrivial: `K` (i.e. `true`) and `false` are different
elements. -/
theorem BetaQuot.k_ne_fls : BetaQuot.mk kComb ≠ BetaQuot.mk fls :=
  fun h => tru_not_betaEqS_fls (BetaQuot.mk_eq_mk.mp h)

end Basic41FinsetNOfFreeIsExact
