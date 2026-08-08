-- The Fixed Point Theorem for the exactly-scoped lambda calculus.
--
-- Every term `F` has a fixed point: a term `X` with `X —→ F ⬝ X`, hence
-- `X ≡β F ⬝ X` (`fixed_point`, `fixed_point_betaeq`).  The fixed point is
-- produced uniformly by Curry's combinator `Ycomb`, which is a *closed* term
-- and satisfies `Ycomb ⬝ F ≡β F ⬝ (Ycomb ⬝ F)` (`Y_fixed_point`).
--
-- Everything here is stated for an arbitrary `F : Scoped`, of arbitrary scope:
-- the free indexes of `F` are shifted when it is placed under a binder, which
-- is what `Scoped.sub0_ren_succ` undoes when the redex is contracted.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

/-- `ƛx. F (x x)`, with the free indexes of `F` shifted under the binder. -/
def selfAppOf (F : Scoped) : Scoped :=
  abs (app (ren Nat.succ F) (app (var 0) (var 0)))

/-- The fixed point of `F` built from `selfAppOf F`. -/
def fix (F : Scoped) : Scoped := app (selfAppOf F) (selfAppOf F)

/-- Curry's fixed point combinator `Y = ƛf. (ƛx. f (x x)) (ƛx. f (x x))`, a
    closed term. -/
def Ycomb : Scoped :=
  abs (app (abs (app (var 1) (app (var 0) (var 0))))
           (abs (app (var 1) (app (var 0) (var 0)))))

theorem Ycomb_closed : Ycomb.newFreeIndexes = 0 := rfl

end Scoped

/-- `fix F` beta-reduces, in one step, to `F (fix F)`. -/
theorem fix_step (F : Scoped) : Scoped.fix F —→ Scoped.app F (Scoped.fix F) := by
  have h := Beta.basis' (Scoped.app (Scoped.ren Nat.succ F)
      (Scoped.app (Scoped.var 0) (Scoped.var 0))) (Scoped.selfAppOf F)
  rwa [Scoped.sub0, Scoped.sub_app, ← Scoped.sub0, ← Scoped.sub0,
    Scoped.sub0_ren_succ] at h

/-- **The Fixed Point Theorem**: every term `F` has a fixed point, reached in a
    single beta step. -/
theorem fixed_point (F : Scoped) : ∃ X, X —→ Scoped.app F X :=
  ⟨Scoped.fix F, fix_step F⟩

theorem fixed_point_betaeq (F : Scoped) : ∃ X, X ≡β Scoped.app F X :=
  ⟨Scoped.fix F, beta_to_betaeq (fix_step F)⟩

/-- `Y F` reduces, in one step, to the fixed point `fix F`. -/
theorem Ycomb_step (F : Scoped) : Scoped.app Scoped.Ycomb F —→ Scoped.fix F :=
  Beta.basis' (Scoped.app (Scoped.abs (Scoped.app (Scoped.var 1)
      (Scoped.app (Scoped.var 0) (Scoped.var 0))))
      (Scoped.abs (Scoped.app (Scoped.var 1)
        (Scoped.app (Scoped.var 0) (Scoped.var 0))))) F

/-- **Curry's `Y` is a fixed point combinator**: `Y F` is convertible with
    `F (Y F)`, for every term `F`. -/
theorem Y_fixed_point (F : Scoped) :
    Scoped.app Scoped.Ycomb F ≡β Scoped.app F (Scoped.app Scoped.Ycomb F) :=
  ((beta_to_betaeq (Ycomb_step F)).trans (beta_to_betaeq (fix_step F))).trans
    (beta_to_betaeq (Beta.appl F (Ycomb_step F))).symm

end IwilareNatIsExactScope
