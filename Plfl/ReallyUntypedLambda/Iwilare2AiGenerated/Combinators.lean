-- The combinators `S`, `K`, `I`, and **combinatory completeness**, for the
-- scope-bounded (`Fin`-indexed) calculus.
--
--   `K = ƛx ƛy. x`         `S = ƛx ƛy ƛz. x z (y z)`
--
-- suffice to express every function that can be written with a lambda: for a
-- combinatory term `M` there is another one, `bracket M` -- containing *no*
-- lambda beyond the ones inside `S` and `K` -- which behaves like `ƛ M`:
--
--   `bracket M ⬝ N —→* M [N]`      (`CL.bracket_spec`)
--
-- In the `Fin`-indexed presentation the combinatory terms can themselves be
-- scope-indexed, `CL n`, and bracket abstraction gets the type it should
-- have: `CL (n + 1) → CL n`.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms

@[expose] public section

namespace FinScope

open Term

/-! ## 1. The combinators and their reduction rules -/

/-- The combinator `K = ƛx ƛy. x`. -/
def Kcomb {n : Nat} : Term n := ƛ (ƛ (v# 1))

/-- The combinator `S = ƛx ƛy ƛz. x z (y z)`. -/
def Scomb {n : Nat} : Term n := ƛ (ƛ (ƛ ((v# 2 ⬝ v# 0) ⬝ (v# 1 ⬝ v# 0))))

/-- The combinator `I = ƛx. x`. -/
def Icomb {n : Nat} : Term n := ƛ (v# 0)

@[simp] theorem ren_Kcomb {n m : Nat} (ρ : Fin n → Fin m) : ren ρ Kcomb = Kcomb := by
  simp [Kcomb]

@[simp] theorem sub_Kcomb {n m : Nat} (σ : Fin n → Term m) : sub σ Kcomb = Kcomb := by
  simp [Kcomb]

@[simp] theorem ren_Scomb {n m : Nat} (ρ : Fin n → Fin m) : ren ρ Scomb = Scomb := by
  simp [Scomb]

@[simp] theorem sub_Scomb {n m : Nat} (σ : Fin n → Term m) : sub σ Scomb = Scomb := by
  simp [Scomb]

/-- `I x —→ x`. -/
theorem Icomb_step {n : Nat} (x : Term n) : Icomb ⬝ x —→ x := by
  simpa [Icomb] using Beta.basis (v# 0) x

/-- `K x y —→* x`. -/
theorem Kcomb_red {n : Nat} (x y : Term n) : Kcomb ⬝ x ⬝ y —→* x := by
  have h₁ : (Kcomb : Term n) ⬝ x —→ ƛ (wk x) := by
    simpa [Kcomb, betaSubst_abs] using Beta.basis (ƛ (v# 1)) x
  refine Relation.ReflTransGen.head (Beta.appL h₁) ?_
  simpa using Relation.ReflTransGen.single (Beta.basis (wk x) y)

/-- `S x y z —→* x z (y z)`. -/
theorem Scomb_red {n : Nat} (x y z : Term n) :
    Scomb ⬝ x ⬝ y ⬝ z —→* (x ⬝ z) ⬝ (y ⬝ z) := by
  have h₁ : (Scomb : Term n) ⬝ x —→ ƛ (ƛ ((wk (wk x) ⬝ v# 0) ⬝ (v# 1 ⬝ v# 0))) := by
    simpa [Scomb, betaSubst_abs] using Beta.basis (ƛ (ƛ ((v# 2 ⬝ v# 0) ⬝ (v# 1 ⬝ v# 0)))) x
  have h₂ : (ƛ (ƛ ((wk (wk x) ⬝ v# 0) ⬝ (v# 1 ⬝ v# 0)))) ⬝ y —→
      ƛ ((wk x ⬝ v# 0) ⬝ (wk y ⬝ v# 0)) := by
    have h := Beta.basis (ƛ ((wk (wk x) ⬝ v# 0) ⬝ (v# 1 ⬝ v# 0))) y
    simpa [betaSubst_abs, sub_ren] using h
  have h₃ : (ƛ ((wk x ⬝ v# 0) ⬝ (wk y ⬝ v# 0))) ⬝ z —→ (x ⬝ z) ⬝ (y ⬝ z) := by
    simpa using Beta.basis ((wk x ⬝ v# 0) ⬝ (wk y ⬝ v# 0)) z
  exact Relation.ReflTransGen.head (Beta.appL (Beta.appL h₁))
    (Relation.ReflTransGen.head (Beta.appL h₂) (Relation.ReflTransGen.single h₃))

/-- `S K K` is the identity combinator: `S K K x —→* x`. -/
theorem SKK_red {n : Nat} (x : Term n) : Scomb ⬝ Kcomb ⬝ Kcomb ⬝ x —→* x :=
  (Scomb_red Kcomb Kcomb x).trans (Kcomb_red x (Kcomb ⬝ x))

/-! ## 2. Combinatory logic terms and bracket abstraction -/

/-- The terms of combinatory logic, scope-indexed: the two constants `S` and
`K`, variables (de Bruijn indexes `< n`) and application. -/
inductive CL : Nat → Type
  | S {n : Nat} : CL n
  | K {n : Nat} : CL n
  | var {n : Nat} (i : Fin n) : CL n
  | app {n : Nat} (a b : CL n) : CL n

/-- A combinatory term as a lambda term. -/
def CL.toTerm : {n : Nat} → CL n → Term n
  | _, .S => Scomb
  | _, .K => Kcomb
  | _, .var i => v# i
  | _, .app a b => a.toTerm ⬝ b.toTerm

/-- Bracket abstraction of a variable. -/
def CL.bracketVar {n : Nat} (i : Fin (n + 1)) : CL n :=
  Fin.cases (.app (.app .S .K) .K) (fun j => .app .K (.var j)) i

/-- Bracket abstraction `λ*` over the de Bruijn index `0`: a combinatory term
with no lambda that behaves like the abstraction of its argument.  The scope
decreases by one, exactly as for `ƛ`. -/
def CL.bracket : {n : Nat} → CL (n + 1) → CL n
  | _, .S => .app .K .S
  | _, .K => .app .K .K
  | _, .var i => CL.bracketVar i
  | _, .app a b => .app (.app .S a.bracket) b.bracket

@[simp] theorem CL.bracket_S {n : Nat} : (CL.S : CL (n + 1)).bracket = .app .K .S := by
  simp [CL.bracket]
@[simp] theorem CL.bracket_K {n : Nat} : (CL.K : CL (n + 1)).bracket = .app .K .K := by
  simp [CL.bracket]
@[simp] theorem CL.bracket_var {n : Nat} (i : Fin (n + 1)) :
    (CL.var i).bracket = CL.bracketVar i := by simp [CL.bracket]
@[simp] theorem CL.bracket_app {n : Nat} (a b : CL (n + 1)) :
    (a.app b).bracket = .app (.app .S a.bracket) b.bracket := by simp [CL.bracket]

@[simp] theorem CL.bracketVar_zero {n : Nat} :
    (CL.bracketVar 0 : CL n) = .app (.app .S .K) .K := by
  simp [CL.bracketVar]

@[simp] theorem CL.bracketVar_succ {n : Nat} (j : Fin n) :
    CL.bracketVar j.succ = .app .K (.var j) := by
  simp [CL.bracketVar]

@[simp] theorem CL.toTerm_S {n : Nat} : (CL.S : CL n).toTerm = Scomb := by simp [CL.toTerm]
@[simp] theorem CL.toTerm_K {n : Nat} : (CL.K : CL n).toTerm = Kcomb := by simp [CL.toTerm]
@[simp] theorem CL.toTerm_var {n : Nat} (i : Fin n) : (CL.var i).toTerm = v# i := by
  simp [CL.toTerm]
@[simp] theorem CL.toTerm_app {n : Nat} (a b : CL n) :
    (a.app b).toTerm = a.toTerm ⬝ b.toTerm := by simp [CL.toTerm]

/-- **Combinatory completeness of `{S, K}`**: for every combinatory term `M`,
the lambda-free term `bracket M` acts on any argument `N` exactly as the
abstraction `ƛ M` would: it reduces to `M` with `N` substituted for the index
`0`. -/
theorem CL.bracket_spec {n : Nat} (c : CL (n + 1)) (N : Term n) :
    c.bracket.toTerm ⬝ N —→* c.toTerm [ N ] := by
  induction c with
  | S => simpa [betaSubst] using Kcomb_red (Scomb : Term n) N
  | K => simpa [betaSubst] using Kcomb_red (Kcomb : Term n) N
  | var i =>
      induction i using Fin.cases with
      | zero => simpa using SKK_red N
      | succ j => simpa using Kcomb_red (v# j) N
  | app a b iha ihb =>
      simp only [CL.bracket_app, CL.toTerm_app, CL.toTerm_S, betaSubst_app]
      refine (Scomb_red a.bracket.toTerm b.bracket.toTerm N).trans ?_
      exact Relation.ReflTransGen.trans (BetaStar.appL iha) (BetaStar.appR ihb)

/-- The same statement in existential form: every combinatory term is the body
of a function that is itself expressible with `S` and `K` alone. -/
theorem combinatory_completeness {n : Nat} (c : CL (n + 1)) :
    ∃ d : CL n, ∀ N : Term n, d.toTerm ⬝ N —→* c.toTerm [ N ] :=
  ⟨c.bracket, c.bracket_spec⟩

end FinScope
