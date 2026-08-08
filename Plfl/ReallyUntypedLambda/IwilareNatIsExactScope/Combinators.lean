-- The combinators `S`, `K`, `I`, and **combinatory completeness**.
--
-- The two combinators
--
--   `K = ƛx ƛy. x`         `S = ƛx ƛy ƛz. x z (y z)`
--
-- suffice to express every function that can be written with a lambda: for a
-- term `M` built from `S`, `K` and variables there is another such term
-- `bracket M` -- containing *no* lambda beyond the ones inside `S` and `K` --
-- which behaves like `ƛ M`:
--
--   `bracket M ⬝ N —→* M [N]`      (`CL.bracket_spec`)
--
-- This is the classical bracket abstraction algorithm; the statement is the
-- combinatory completeness of `{S, K}`.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ScopeBounds
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

-- ====================================================================
-- 0. A few computation rules for substitutions
-- ====================================================================

end Scoped

-- ====================================================================
-- 1. The combinators and their reduction rules
-- ====================================================================

open Scoped

/-- The combinator `K = ƛx ƛy. x`. -/
def Kcomb : Scoped := abs (abs (var 1))

/-- The combinator `S = ƛx ƛy ƛz. x z (y z)`. -/
def Scomb : Scoped := abs (abs (abs (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

/-- The combinator `I = ƛx. x`. -/
def Icomb : Scoped := abs (var 0)

theorem Kcomb_closed : Kcomb.newFreeIndexes = 0 := rfl

theorem Scomb_closed : Scomb.newFreeIndexes = 0 := rfl

theorem Icomb_closed : Icomb.newFreeIndexes = 0 := rfl

/-- `I x —→ x`. -/
theorem Icomb_step (x : Scoped) : app Icomb x —→ x := by
  have h := Beta.basis' (Scoped.var 0) x
  have e : Scoped.sub0 x (Scoped.var 0) = x := rfl
  rwa [e] at h

/-- `K x y —→* x`. -/
theorem Kcomb_red (x y : Scoped) : app (app Kcomb x) y —→* x := by
  refine Relation.ReflTransGen.head (Beta.appr y (Beta.basis' _ _)) ?_
  have e : Scoped.sub0 x (Scoped.abs (Scoped.var 1)) = abs (ren Nat.succ x) := rfl
  rw [e]
  refine Relation.ReflTransGen.head (Beta.basis' _ _) ?_
  rw [Scoped.sub0_ren_succ]

/-- `S x y z —→* x z (y z)`. -/
theorem Scomb_red (x y z : Scoped) :
    app (app (app Scomb x) y) z —→* app (app x z) (app y z) := by
  refine Relation.ReflTransGen.head (Beta.appr z (Beta.appr y (Beta.basis' _ _))) ?_
  have e1 : Scoped.sub0 x (Scoped.abs (Scoped.abs
      (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
      = abs (abs (app (app (ren Nat.succ (ren Nat.succ x)) (var 0)) (app (var 1) (var 0)))) := rfl
  rw [e1]
  refine Relation.ReflTransGen.head (Beta.appr z (Beta.basis' _ _)) ?_
  have e2 : Scoped.sub0 y (Scoped.abs
      (app (app (ren Nat.succ (ren Nat.succ x)) (var 0)) (app (var 1) (var 0))))
      = abs (app (app (sub (upSub (cons y var)) (ren Nat.succ (ren Nat.succ x))) (var 0))
          (app (ren Nat.succ y) (var 0))) := rfl
  have e3 : sub (upSub (cons y var)) (ren Nat.succ (ren Nat.succ x)) = ren Nat.succ x := by
    rw [Scoped.sub_ren, Scoped.sub_ren]
    exact Scoped.sub_var_comp x Nat.succ
  rw [e2, e3]
  refine Relation.ReflTransGen.head (Beta.basis' _ _) ?_
  have e4 : Scoped.sub0 z (app (app (ren Nat.succ x) (var 0)) (app (ren Nat.succ y) (var 0)))
      = app (app (Scoped.sub0 z (ren Nat.succ x)) z) (app (Scoped.sub0 z (ren Nat.succ y)) z) :=
    rfl
  rw [e4, Scoped.sub0_ren_succ, Scoped.sub0_ren_succ]

/-- `S K K` is the identity combinator: `S K K x —→* x`. -/
theorem SKK_red (x : Scoped) : app (app (app Scomb Kcomb) Kcomb) x —→* x :=
  (Scomb_red Kcomb Kcomb x).trans (Kcomb_red x (app Kcomb x))

-- ====================================================================
-- 2. Combinatory logic terms and bracket abstraction
-- ====================================================================

/-- The terms of combinatory logic: the two constants `S` and `K`, variables
    (de Bruijn indexes) and application. -/
inductive CL : Type
  | S : CL
  | K : CL
  | var (i : Nat) : CL
  | app (a b : CL) : CL

/-- A combinatory term as a lambda term. -/
def CL.toScoped : CL → Scoped
  | .S => Scomb
  | .K => Kcomb
  | .var i => Scoped.var i
  | .app a b => Scoped.app a.toScoped b.toScoped

/-- Bracket abstraction `λ*` over the de Bruijn index `0`: a combinatory term
    with no lambda that behaves like the abstraction of its argument. -/
def CL.bracket : CL → CL
  | .S => .app .K .S
  | .K => .app .K .K
  | .var 0 => .app (.app .S .K) .K
  | .var (i + 1) => .app .K (.var i)
  | .app a b => .app (.app .S a.bracket) b.bracket

/-- **Combinatory completeness of `{S, K}`**: for every combinatory term `M`,
    the lambda-free term `bracket M` acts on any argument `N` exactly as the
    abstraction `ƛ M` would: it reduces to `M` with `N` substituted for the
    index `0`. -/
theorem CL.bracket_spec (c : CL) (N : Scoped) :
    Scoped.app c.bracket.toScoped N —→* Scoped.sub0 N c.toScoped := by
  induction c generalizing N with
  | S =>
      show Scoped.app (Scoped.app Kcomb Scomb) N —→* Scoped.sub0 N Scomb
      have e : Scoped.sub0 N Scomb = Scomb :=
        Scoped.sub_eq_self_of_closed Scomb_closed _
      rw [e]
      exact Kcomb_red Scomb N
  | K =>
      show Scoped.app (Scoped.app Kcomb Kcomb) N —→* Scoped.sub0 N Kcomb
      have e : Scoped.sub0 N Kcomb = Kcomb :=
        Scoped.sub_eq_self_of_closed Kcomb_closed _
      rw [e]
      exact Kcomb_red Kcomb N
  | var i =>
      cases i with
      | zero => exact SKK_red N
      | succ i => exact Kcomb_red (Scoped.var i) N
  | app a b iha ihb =>
      refine (Scomb_red a.bracket.toScoped b.bracket.toScoped N).trans ?_
      refine Relation.ReflTransGen.trans (beta_star_appr _ (iha N)) ?_
      exact beta_star_appl _ (ihb N)

/-- The same statement in existential form: every combinatory term is the body
    of a function that is itself expressible with `S` and `K` alone. -/
theorem combinatory_completeness (c : CL) :
    ∃ d : CL, ∀ N : Scoped, Scoped.app d.toScoped N —→* Scoped.sub0 N c.toScoped :=
  ⟨c.bracket, c.bracket_spec⟩

end IwilareNatIsExactScope
