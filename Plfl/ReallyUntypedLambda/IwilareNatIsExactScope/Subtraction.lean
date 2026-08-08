-- Predecessor and subtraction on Church numerals *without* tuples.
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
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchNumerals
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Combinators
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Evaluator

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

/-- The step function `ƛg. ƛh. h (g f)` of the pair-free predecessor.  It is
    written in the scope of the two binders `ƛf. ƛx.` of `cpredCPS`, so `f` is
    the index `3` from inside its own two binders. -/
def cpredB : Scoped := abs (abs (app (var 0) (app (var 1) (var 3))))

/-- The starting continuation `ƛu. x`, in the same scope. -/
def cpredK : Scoped := abs (var 1)

/-- **The pair-free predecessor**
    `ƛn. ƛf. ƛx. n (ƛg. ƛh. h (g f)) (ƛu. x) (ƛu. u)`. -/
def cpredCPS : Scoped := abs (abs (abs (app (app (app (var 2) cpredB) cpredK) Icomb)))

/-- `ƛm. ƛn. n predCPS m` : subtraction built from the pair-free predecessor. -/
def csubCPS : Scoped := abs (abs (app (app (var 0) cpredCPS) (var 1)))

/-- The `k`-fold iterate of the step function on the starting continuation. -/
abbrev cpredA (k : Nat) : Scoped := iterApp cpredB cpredK k

theorem cpredCPS_closed : cpredCPS.newFreeIndexes = 0 := rfl

@[simp] theorem sub_cpredCPS (σ : Nat → Scoped) : sub σ cpredCPS = cpredCPS :=
  sub_eq_self_of_closed cpredCPS_closed σ

theorem csubCPS_closed : csubCPS.newFreeIndexes = 0 := rfl

end Scoped

/-- One step of the iteration: `(ƛg ƛh. h (g f)) Z —→ ƛh. h (Z f)`. -/
theorem app_cpredB (Z : Scoped) :
    Scoped.app Scoped.cpredB Z —→
      Scoped.abs (Scoped.app (Scoped.var 0)
        (Scoped.app (Scoped.ren Nat.succ Z) (Scoped.var 2))) := by
  have h := Beta.basis'
    (Scoped.abs (Scoped.app (Scoped.var 0) (Scoped.app (Scoped.var 1) (Scoped.var 3)))) Z
  simpa [Scoped.cpredB, Scoped.sub0] using h

/-- Feeding the `k`-th iterate the function `f` runs all `k` iterations. -/
theorem cpredA_app_var (k : Nat) :
    Scoped.app (Scoped.cpredA k) (Scoped.var 1) —→*
      Scoped.iterApp (Scoped.var 1) (Scoped.var 0) k := by
  induction k with
  | zero =>
      refine Relation.ReflTransGen.single ?_
      have h := Beta.basis' (Scoped.var 1) (Scoped.var 1)
      simpa [Scoped.cpredK, Scoped.sub0] using h
  | succ k ih =>
      refine Relation.ReflTransGen.head (Beta.appr _ (app_cpredB (Scoped.cpredA k))) ?_
      refine Relation.ReflTransGen.head (Beta.basis' _ (Scoped.var 1)) ?_
      have e : Scoped.sub0 (Scoped.var 1) (Scoped.app (Scoped.var 0)
            (Scoped.app (Scoped.ren Nat.succ (Scoped.cpredA k)) (Scoped.var 2)))
          = Scoped.app (Scoped.var 1) (Scoped.app (Scoped.cpredA k) (Scoped.var 1)) := by
        simp [Scoped.sub0, Scoped.sub0_ren_succ]
      rw [e]
      exact beta_star_appl _ ih

/-- Feeding the `n`-th iterate the *identity* runs one iteration less (and, for
    `n = 0`, none at all -- which is the truncation at zero). -/
theorem cpredA_app_Icomb (n : Nat) :
    Scoped.app (Scoped.cpredA n) Icomb —→*
      Scoped.iterApp (Scoped.var 1) (Scoped.var 0) (n - 1) := by
  cases n with
  | zero =>
      refine Relation.ReflTransGen.single ?_
      have h := Beta.basis' (Scoped.var 1) Icomb
      simpa [Scoped.cpredK, Scoped.sub0] using h
  | succ k =>
      refine Relation.ReflTransGen.head (Beta.appr _ (app_cpredB (Scoped.cpredA k))) ?_
      refine Relation.ReflTransGen.head (Beta.basis' _ Icomb) ?_
      have e : Scoped.sub0 Icomb (Scoped.app (Scoped.var 0)
              (Scoped.app (Scoped.ren Nat.succ (Scoped.cpredA k)) (Scoped.var 2)))
          = Scoped.app Icomb (Scoped.app (Scoped.cpredA k) (Scoped.var 1)) := by
        simp [Scoped.sub0, Scoped.sub0_ren_succ]
      rw [e]
      refine (beta_star_appl _ (cpredA_app_var k)).trans ?_
      simpa [Icomb] using Relation.ReflTransGen.single
        (Beta.basis' (Scoped.var 0) (Scoped.iterApp (Scoped.var 1) (Scoped.var 0) k))

/-- **The pair-free predecessor is correct**: no tuple, no pairing combinator,
    only continuations. -/
theorem cpredCPS_church (n : Nat) :
    Scoped.app Scoped.cpredCPS (Scoped.church n) —→* Scoped.church (n - 1) := by
  have h₁ : Scoped.app Scoped.cpredCPS (Scoped.church n) —→
      Scoped.abs (Scoped.abs (Scoped.app (Scoped.app (Scoped.app (Scoped.church n)
        Scoped.cpredB) Scoped.cpredK) Icomb)) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app (Scoped.app
      (Scoped.app (Scoped.var 2) Scoped.cpredB) Scoped.cpredK) Icomb)))
      (Scoped.church n)
    simpa [Scoped.cpredCPS, Scoped.sub0, Scoped.cpredB, Scoped.cpredK, Icomb] using h
  refine Relation.ReflTransGen.head h₁ ?_
  rw [Scoped.church]
  refine beta_star_abs (beta_star_abs ?_)
  refine (beta_star_appr _ (church_app n Scoped.cpredB Scoped.cpredK)).trans ?_
  exact cpredA_app_Icomb n

/-- Iterating the pair-free predecessor `n` times on `church m`. -/
theorem iterApp_cpredCPS (m n : Nat) :
    Scoped.iterApp Scoped.cpredCPS (Scoped.church m) n —→* Scoped.church (m - n) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [Scoped.iterApp_succ]
      refine (beta_star_appl _ ih).trans ?_
      have h := cpredCPS_church (m - n)
      have e : m - n - 1 = m - (n + 1) := by omega
      rwa [e] at h

/-- **Truncated subtraction, without tuples**. -/
theorem csubCPS_church (m n : Nat) :
    Scoped.app (Scoped.app Scoped.csubCPS (Scoped.church m)) (Scoped.church n) —→*
      Scoped.church (m - n) := by
  have h₁ : Scoped.app Scoped.csubCPS (Scoped.church m) —→
      Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpredCPS)
        (Scoped.church m)) := by
    have h := Beta.basis' (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0)
      Scoped.cpredCPS) (Scoped.var 1))) (Scoped.church m)
    simpa [Scoped.csubCPS, Scoped.sub0] using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₁) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpredCPS)
      (Scoped.church m))) (Scoped.church n) —→
      Scoped.app (Scoped.app (Scoped.church n) Scoped.cpredCPS) (Scoped.church m) := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpredCPS)
      (Scoped.church m)) (Scoped.church n)
    simpa [Scoped.sub0] using h
  refine Relation.ReflTransGen.head h₂ ?_
  exact (church_app n Scoped.cpredCPS (Scoped.church m)).trans (iterApp_cpredCPS m n)

-- ====================================================================
-- Sanity checks: the terms really compute (normal order evaluator)
-- ====================================================================

set_option maxRecDepth 100000 in
/-- `pred 5 = 4`, with the pair-free predecessor, computed. -/
example : Scoped.eval 2000 (Scoped.app Scoped.cpredCPS (Scoped.church 5))
    = some (Scoped.church 4) := rfl

set_option maxRecDepth 100000 in
/-- `pred 0 = 0`: subtraction on the numerals is necessarily truncated. -/
example : Scoped.eval 2000 (Scoped.app Scoped.cpredCPS (Scoped.church 0))
    = some (Scoped.church 0) := rfl

set_option maxRecDepth 100000 in
/-- `7 - 4 = 3`, without tuples, computed. -/
example : Scoped.eval 3000 (Scoped.app (Scoped.app Scoped.csubCPS (Scoped.church 7))
    (Scoped.church 4)) = some (Scoped.church 3) := rfl

set_option maxRecDepth 100000 in
/-- `4 - 7 = 0`, without tuples, computed. -/
example : Scoped.eval 3000 (Scoped.app (Scoped.app Scoped.csubCPS (Scoped.church 4))
    (Scoped.church 7)) = some (Scoped.church 0) := rfl

end IwilareNatIsExactScope
