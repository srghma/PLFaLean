module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.NormalForm

@[expose] public section

/-!
# Ω and the fixed-point combinators

* `Basic41Finset.omega` — the term `Ω = (λx. x x) (λx. x x)`.  Its only β-step
  is to itself (`Basic41Finset.stepS_omega_iff`), so it has **no normal form**
  (`Basic41Finset.omega_hasNoNormalForm`) and is not convertible to any normal
  form.
* `Basic41Finset.Y` — Curry's fixed-point combinator
  `Y = λf. (λx. f (x x)) (λx. f (x x))`, with `Y F ≡βs F (Y F)`
  (`Basic41Finset.Y_fixed_point`).
* `Basic41Finset.theta` — Turing's fixed-point combinator, for which the
  fixed-point equation holds as a *reduction*: `Θ F ⇒βs* F (Θ F)`
  (`Basic41Finset.theta_fixed_point`).
* `Basic41Finset.fixed_point_theorem` — **the fixed-point theorem**: every term
  `F` has a fixed point `X` with `X ≡βs F X`; indeed one with `X ⇒βs* F X`.
-/

namespace Basic41FinsetNOfFreeIsExact

open SigmaTerm

/-! ### `Ω` has no normal form -/

/-- The self-application term `δ = λx. x x`. -/
def delta : SigmaTerm := abs (app (var 0) (var 0))

/-- `Ω = (λx. x x) (λx. x x)`, the paradigmatic term without a normal form. -/
def omega : SigmaTerm := app delta delta

theorem normalS_delta : NormalS delta :=
  NormalS.abs_iff.mpr
    (NormalS.app (normalS_var 0) (normalS_var 0) (fun t0 => by simp))

/-- `Ω` β-reduces to itself. -/
theorem stepS_omega : omega →βs omega := by
  have h := StepS.head (app (var 0) (var 0)) delta
  rwa [subst_app, subst_var, if_pos rfl] at h

/-- `Ω` reduces to nothing but itself: its unique redex reproduces `Ω`. -/
theorem stepS_omega_iff {w : SigmaTerm} : omega →βs w ↔ w = omega := by
  refine ⟨fun h => ?_, fun h => h ▸ stepS_omega⟩
  rcases stepS_app_inv h with ⟨t0, h1, h2⟩ | ⟨t', _, h2⟩ | ⟨u', _, h2⟩
  · have ht0 : t0 = app (var 0) (var 0) := by
      have : abs (app (var 0) (var 0)) = abs t0 := h1
      exact (abs_inj.mp this).symm
    subst ht0
    rw [h2, subst_app, subst_var, if_pos rfl]
    rfl
  · exact absurd h2 (normalS_delta t')
  · exact absurd h2 (normalS_delta u')

/-- Every reduct of `Ω` is `Ω`. -/
theorem betaStarS_omega_iff {w : SigmaTerm} : omega ⇒βs* w ↔ w = omega := by
  refine ⟨fun h => ?_, fun h => h ▸ Relation.ReflTransGen.refl⟩
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih] at hstep; exact stepS_omega_iff.mp hstep

/-- `Ω` is not a normal form. -/
theorem not_normalS_omega : ¬ NormalS omega := fun h => h omega stepS_omega

/-- **`Ω` has no normal form.** -/
theorem omega_hasNoNormalForm : ¬ HasNormalFormS omega := by
  rintro ⟨u, hu1, hu2⟩
  rw [betaStarS_omega_iff.mp hu1] at hu2
  exact not_normalS_omega hu2

/-- `Ω` is not β-convertible to any normal form. -/
theorem omega_not_betaEqS_normal {u : SigmaTerm} (hu : NormalS u) : ¬ (omega ≡βs u) := by
  intro h
  exact omega_hasNoNormalForm
    (HasNormalFormS.of_betaEqS (Relation.EqvGen.symm _ _ h) ⟨u, Relation.ReflTransGen.refl, hu⟩)

/-! ### Curry's fixed-point combinator `Y` -/

/-- `Y = λf. (λx. f (x x)) (λx. f (x x))`, Curry's fixed-point combinator. -/
def Y : SigmaTerm :=
  abs (app (abs (app (var 1) (app (var 0) (var 0))))
           (abs (app (var 1) (app (var 0) (var 0)))))

/-- The term `λx. F (x x)` (with `F` shifted so that it lives under the binder). -/
def Ydup (F : SigmaTerm) : SigmaTerm := abs (app (SigmaTerm.shift 0 F) (app (var 0) (var 0)))

/-- The self-application `(λx. F (x x)) (λx. F (x x))`, the fixed point produced
by `Y`. -/
def Yfix (F : SigmaTerm) : SigmaTerm := app (Ydup F) (Ydup F)

/-- `Y F` reduces in one step to the self-application `Yfix F`. -/
theorem stepS_Y_app (F : SigmaTerm) : app Y F →βs Yfix F := by
  have h := StepS.head (app (abs (app (var 1) (app (var 0) (var 0))))
      (abs (app (var 1) (app (var 0) (var 0))))) F
  simpa [Y, Yfix, Ydup] using h

/-- `Yfix F` reduces in one step to `F (Yfix F)`: it is a fixed point of `F`. -/
theorem stepS_Yfix (F : SigmaTerm) : Yfix F →βs app F (Yfix F) := by
  have h := StepS.head (app (SigmaTerm.shift 0 F) (app (var 0) (var 0))) (Ydup F)
  rw [subst_app, subst_app, subst_var, if_pos rfl, SigmaTerm.subst_shift] at h
  exact h

/-- **Curry's `Y` is a fixed-point combinator**: `Y F ≡βs F (Y F)`. -/
theorem Y_fixed_point (F : SigmaTerm) : app Y F ≡βs app F (app Y F) := by
  have h1 : app Y F ⇒βs* app F (Yfix F) :=
    (Relation.ReflTransGen.single (stepS_Y_app F)).tail (stepS_Yfix F)
  have h2 : app F (app Y F) ⇒βs* app F (Yfix F) :=
    betaStarS_app_right F (Relation.ReflTransGen.single (stepS_Y_app F))
  exact Relation.EqvGen.trans _ _ _ (eqvGen_of_reflTransGen h1)
    (Relation.EqvGen.symm _ _ (eqvGen_of_reflTransGen h2))

/-- `Yfix F` is a fixed point of `F` *up to reduction*. -/
theorem Yfix_fixed_point (F : SigmaTerm) : Yfix F ⇒βs* app F (Yfix F) :=
  Relation.ReflTransGen.single (stepS_Yfix F)

/-! ### Turing's fixed-point combinator -/

/-- `A = λx. λy. y (x x y)`; Turing's combinator is `Θ = A A`. -/
def thetaA : SigmaTerm :=
  abs (abs (app (var 0) (app (app (var 1) (var 1)) (var 0))))

/-- Turing's fixed-point combinator `Θ = A A`. -/
def theta : SigmaTerm := app thetaA thetaA

@[simp] theorem shift_thetaA (c : Nat) : SigmaTerm.shift c thetaA = thetaA := by
  simp [thetaA]

@[simp] theorem subst_thetaA (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N thetaA = thetaA := by
  simp [thetaA]

/-- `Θ` reduces to `λy. y (Θ y)`. -/
theorem stepS_theta : theta →βs abs (app (var 0) (app theta (var 0))) := by
  have h := StepS.head (abs (app (var 0) (app (app (var 1) (var 1)) (var 0)))) thetaA
  simpa [theta, thetaA] using h

/-- **Turing's combinator gives fixed points by reduction**: `Θ F ⇒βs* F (Θ F)`. -/
theorem theta_fixed_point (F : SigmaTerm) : app theta F ⇒βs* app F (app theta F) := by
  refine (betaStarS_app_left F (Relation.ReflTransGen.single stepS_theta)).tail ?_
  have h := StepS.head (app (var 0) (app theta (var 0))) F
  simpa [theta] using h

/-! ### The fixed-point theorem -/

/-- **The fixed-point theorem.** Every term `F` has a fixed point: a term `X`
with `X ≡βs F X`.  In fact `X` can be chosen so that `X` *reduces* to `F X`. -/
theorem fixed_point_theorem (F : SigmaTerm) : ∃ X, X ⇒βs* app F X ∧ X ≡βs app F X :=
  ⟨Yfix F, Yfix_fixed_point F, eqvGen_of_reflTransGen (Yfix_fixed_point F)⟩

end Basic41FinsetNOfFreeIsExact
