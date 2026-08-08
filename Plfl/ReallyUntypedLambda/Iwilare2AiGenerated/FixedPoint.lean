-- The Fixed Point Theorem, for the scope-bounded (`Fin`-indexed) calculus.
--
-- Every term `F` has a fixed point: a term `X` with `X —→ F ⬝ X`, hence
-- `X ≡β F ⬝ X` (`fixed_point`, `fixed_point_betaeq`).  The fixed point is
-- produced uniformly by Curry's combinator `Ycomb`, a *closed* term
-- (`Ycomb : Term 0`) with `Ycomb ⬝ F ≡β F ⬝ (Ycomb ⬝ F)` (`Y_fixed_point`).
--
-- Everything is stated for an arbitrary `F : Term n`: the free indexes of `F`
-- are weakened when it is placed under a binder, which is what `betaSubst_wk`
-- undoes when the redex is contracted.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms

@[expose] public section

namespace FinScope

open Term

/-- `ƛx. F (x x)`, with the free indexes of `F` weakened under the binder. -/
def selfAppOf {n : Nat} (F : Term n) : Term n := ƛ (wk F ⬝ (v# 0 ⬝ v# 0))

/-- The fixed point of `F` built from `selfAppOf F`. -/
def fix {n : Nat} (F : Term n) : Term n := selfAppOf F ⬝ selfAppOf F

/-- Curry's fixed point combinator `Y = ƛf. (ƛx. f (x x)) (ƛx. f (x x))`, a
closed term. -/
def Ycomb {n : Nat} : Term n :=
  ƛ ((ƛ (v# 1 ⬝ (v# 0 ⬝ v# 0))) ⬝ (ƛ (v# 1 ⬝ (v# 0 ⬝ v# 0))))

/-- `fix F` beta-reduces, in one step, to `F (fix F)`. -/
theorem fix_step {n : Nat} (F : Term n) : fix F —→ F ⬝ fix F := by
  have h := Beta.basis (wk F ⬝ (v# 0 ⬝ v# 0)) (selfAppOf F)
  simp_all only [betaSubst_app, betaSubst_wk, betaSubst_var_zero]
  exact h

/-- **The Fixed Point Theorem**: every term `F` has a fixed point, reached in a
single beta step. -/
theorem fixed_point {n : Nat} (F : Term n) : ∃ X, X —→ F ⬝ X :=
  ⟨fix F, fix_step F⟩

theorem fixed_point_betaeq {n : Nat} (F : Term n) : ∃ X, X ≡β F ⬝ X :=
  ⟨fix F, beta_to_betaeq (fix_step F)⟩

/-- `Y F` reduces, in one step, to the fixed point `fix F`. -/
theorem Ycomb_step {n : Nat} (F : Term n) : Ycomb ⬝ F —→ fix F := by
  have h := Beta.basis
    ((ƛ (v# 1 ⬝ (v# 0 ⬝ v# 0))) ⬝ (ƛ (v# 1 ⬝ (v# 0 ⬝ v# 0))) : Term (n + 1)) F
  simpa [Ycomb, betaSubst_abs, selfAppOf, fix] using h

/-- **Curry's `Y` is a fixed point combinator**: `Y F` is convertible with
`F (Y F)`, for every term `F`. -/
theorem Y_fixed_point {n : Nat} (F : Term n) : Ycomb ⬝ F ≡β F ⬝ (Ycomb ⬝ F) :=
  ((beta_to_betaeq (Ycomb_step F)).trans (beta_to_betaeq (fix_step F))).trans
    (beta_to_betaeq (Beta.appR (Ycomb_step F))).symm

/-- `Y` is a closed term. -/
example : Term 0 := Ycomb

end FinScope
