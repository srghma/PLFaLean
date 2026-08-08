-- Predecessor and subtraction on Church numerals *without* tuples, for the
-- scope-bounded (`Fin`-indexed) calculus.
--
-- The usual predecessor (Kleene's, in `ChurchData.lean`) iterates the map
-- `⟨a, b⟩ ↦ ⟨b, b+1⟩` on a *pair* of numerals and projects out the first
-- component; subtraction is then `ƛm ƛn. n pred m` (`PrimitiveRecursion.lean`).
-- It is often said that this pairing is unavoidable -- that Church numerals
-- "support subtraction only as a tuple".  That is not so: the term
--
--     predCPS  =  ƛn. ƛf. ƛx. n (ƛg. ƛh. h (g f)) (ƛu. x) (ƛu. u)
--
-- computes the predecessor with no pair (and no other data structure) anywhere.
-- Instead of carrying a pair, it iterates on *continuations*: the `n`-fold
-- iterate of `ƛg ƛh. h (g f)` starting from `ƛu. x` is a function which, when
-- fed the identity, "runs" one iteration less than it was given, and when fed
-- `f` runs all of them.  That is exactly the invariant `cpredA_app_var` /
-- `cpredA_app_Icomb` below.
--
-- Proved here:
--
--     cpredCPS ⬝ church n              —→*  church (n - 1)
--     csubCPS  ⬝ church m ⬝ church n    —→*  church (m - n)
--
-- both by pure beta reduction, and both truncated at `0` (`church 0 - 1 = 0`),
-- which is forced: `church (-1)` does not exist, so *every* lambda-definable
-- "subtraction" on the numerals is truncated subtraction.
--
-- Here the scopes make the intended reading of the de Bruijn indexes visible in
-- the types: `cpredB` and `cpredK` live in `Term (n + 3)`, i.e. inside the three
-- binders `ƛn. ƛf. ƛx.` of `cpredCPS`.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Combinators
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Evaluator

@[expose] public section

namespace FinScope

open Term

namespace Term

/-- The step function `ƛg. ƛh. h (g f)` of the pair-free predecessor.  It is
    written in the scope of the three binders `ƛn. ƛf. ƛx.` of `cpredCPS`, so
    `f` is the index `3` from inside its own two binders. -/
def cpredB {n : Nat} : Term (n + 2) := ƛ ƛ (v# 0 ⬝ (v# 1 ⬝ v# 3))

/-- The starting continuation `ƛu. x`, in the same scope. -/
def cpredK {n : Nat} : Term (n + 2) := ƛ (v# 1)

/-- **The pair-free predecessor**
    `ƛn. ƛf. ƛx. n (ƛg. ƛh. h (g f)) (ƛu. x) (ƛu. u)`. -/
def cpredCPS {n : Nat} : Term n := ƛ ƛ ƛ (v# 2 ⬝ cpredB ⬝ cpredK ⬝ Icomb)

/-- `ƛm. ƛn. n predCPS m` : subtraction built from the pair-free predecessor. -/
def csubCPS {n : Nat} : Term n := ƛ ƛ (v# 0 ⬝ cpredCPS ⬝ v# 1)

/-- The `k`-fold iterate of the step function on the starting continuation. -/
abbrev cpredA {n : Nat} (k : Nat) : Term (n + 2) := iterApp cpredB cpredK k

@[simp] theorem ren_cpredCPS {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cpredCPS = cpredCPS := by
  simp [cpredCPS, cpredB, cpredK, Icomb, ← fin_three_eq_succ]

@[simp] theorem sub_cpredCPS {n m : Nat} (σ : Fin n → Term m) : sub σ cpredCPS = cpredCPS := by
  simp [cpredCPS, cpredB, cpredK, Icomb, ← fin_three_eq_succ]

@[simp] theorem betaSubst_cpredCPS {n : Nat} (N : Term n) :
    (cpredCPS : Term (n + 1)) [ N ] = cpredCPS := by
  simp [betaSubst]

end Term

/-- One step of the iteration: `(ƛg ƛh. h (g f)) Z —→ ƛh. h (Z f)`. -/
theorem app_cpredB {n : Nat} (Z : Term (n + 2)) :
    cpredB ⬝ Z —→ ƛ (v# 0 ⬝ (wk Z ⬝ v# 2)) := by
  have h := Beta.basis (ƛ (v# 0 ⬝ (v# 1 ⬝ v# 3)) : Term (n + 3)) Z
  simpa [cpredB, betaSubst_abs] using h

/-- Feeding the `k`-th iterate the function `f` runs all `k` iterations. -/
theorem cpredA_app_var {n : Nat} (k : Nat) :
    (cpredA k : Term (n + 2)) ⬝ v# 1 —→* iterApp (v# 1) (v# 0) k := by
  induction k with
  | zero =>
      refine Relation.ReflTransGen.single ?_
      have h := Beta.basis (v# 1 : Term (n + 3)) (v# 1 : Term (n + 2))
      simpa [cpredK] using h
  | succ k ih =>
      refine Relation.ReflTransGen.head (Beta.appL (app_cpredB (cpredA k))) ?_
      refine Relation.ReflTransGen.head (Beta.basis _ (v# 1)) ?_
      have e : ((v# 0 ⬝ (wk (cpredA k) ⬝ v# 2) : Term (n + 3))) [ (v# 1 : Term (n + 2)) ]
          = v# 1 ⬝ (cpredA k ⬝ v# 1) := by simp
      rw [e]
      exact BetaStar.appR ih

/-- Feeding the `k`-th iterate the *identity* runs one iteration less (and, for
    `k = 0`, none at all -- which is the truncation at zero). -/
theorem cpredA_app_Icomb {n : Nat} (k : Nat) :
    (cpredA k : Term (n + 2)) ⬝ Icomb —→* iterApp (v# 1) (v# 0) (k - 1) := by
  cases k with
  | zero =>
      refine Relation.ReflTransGen.single ?_
      have h := Beta.basis (v# 1 : Term (n + 3)) (Icomb : Term (n + 2))
      simpa [cpredK] using h
  | succ k =>
      refine Relation.ReflTransGen.head (Beta.appL (app_cpredB (cpredA k))) ?_
      refine Relation.ReflTransGen.head (Beta.basis _ (Icomb : Term (n + 2))) ?_
      have e : ((v# 0 ⬝ (wk (cpredA k) ⬝ v# 2) : Term (n + 3))) [ (Icomb : Term (n + 2)) ]
          = Icomb ⬝ (cpredA k ⬝ v# 1) := by simp
      rw [e]
      refine (BetaStar.appR (cpredA_app_var k)).trans ?_
      simpa using Relation.ReflTransGen.single (Icomb_step (iterApp (v# 1) (v# 0) k))

/-- **The pair-free predecessor is correct**: no tuple, no pairing combinator,
    only continuations. -/
theorem cpredCPS_church {n : Nat} (k : Nat) :
    (cpredCPS : Term n) ⬝ church k —→* church (k - 1) := by
  refine Relation.ReflTransGen.head (Beta.basis _ (church k)) ?_
  have e : (ƛ ƛ (v# 2 ⬝ cpredB ⬝ cpredK ⬝ Icomb) : Term (n + 1)) [ (church k : Term n) ]
      = ƛ ƛ (church k ⬝ cpredB ⬝ cpredK ⬝ Icomb) := by
    simp [betaSubst_abs, cpredB, cpredK, Icomb, ← fin_three_eq_succ]
  rw [e, church]
  refine BetaStar.abs (BetaStar.abs ?_)
  refine (BetaStar.appL (church_app k cpredB cpredK)).trans ?_
  exact cpredA_app_Icomb k

/-- Iterating the pair-free predecessor `k` times on `church m`. -/
theorem iterApp_cpredCPS {n : Nat} (m k : Nat) :
    iterApp (cpredCPS : Term n) (church m) k —→* church (m - k) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
      rw [iterApp_succ]
      refine (BetaStar.appR ih).trans ?_
      have h := cpredCPS_church (n := n) (m - k)
      have e : m - k - 1 = m - (k + 1) := by omega
      rwa [e] at h

/-- **Truncated subtraction, without tuples**. -/
theorem csubCPS_church {n : Nat} (m k : Nat) :
    (csubCPS : Term n) ⬝ church m ⬝ church k —→* church (m - k) := by
  refine Relation.ReflTransGen.head (Beta.appL (Beta.basis _ (church m))) ?_
  have e : (ƛ (v# 0 ⬝ cpredCPS ⬝ v# 1) : Term (n + 1)) [ (church m : Term n) ]
      = ƛ (v# 0 ⬝ cpredCPS ⬝ church m) := by simp [betaSubst_abs]
  rw [e]
  refine Relation.ReflTransGen.head (Beta.basis _ (church k)) ?_
  have e' : ((v# 0 ⬝ cpredCPS ⬝ church m : Term (n + 1))) [ (church k : Term n) ]
      = church k ⬝ cpredCPS ⬝ church m := by simp
  rw [e']
  exact (church_app k cpredCPS (church m)).trans (iterApp_cpredCPS m k)

/-! ## Sanity checks: the terms really compute (normal order evaluator) -/

set_option maxRecDepth 100000 in
/-- `pred 5 = 4`, with the pair-free predecessor, computed. -/
example : Term.eval 2000 (cpredCPS ⬝ church 5 : Term 0) = some (church 4) := by decide

set_option maxRecDepth 100000 in
/-- `pred 0 = 0`: subtraction on the numerals is necessarily truncated. -/
example : Term.eval 2000 (cpredCPS ⬝ church 0 : Term 0) = some (church 0) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `7 - 4 = 3`, without tuples, computed. -/
example : Term.eval 3000 (csubCPS ⬝ church 7 ⬝ church 4 : Term 0) = some (church 3) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `4 - 7 = 0`, without tuples, computed. -/
example : Term.eval 3000 (csubCPS ⬝ church 4 ⬝ church 7 : Term 0) = some (church 0) := by decide

end FinScope
