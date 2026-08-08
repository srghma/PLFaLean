-- Church encodings of the data: booleans, the conditional, pairs, the test for
-- zero, and Kleene's predecessor.
--
-- Together with `ChurchNumerals.lean` (successor, addition, multiplication)
-- this shows that the untyped lambda calculus represents the usual data and
-- the basic arithmetic operations, predecessor included:
--
--     cif ⬝ ctrue ⬝ x ⬝ y            —→*  x
--     cfst ⬝ (cpair ⬝ x ⬝ y)         —→*  x
--     ciszero ⬝ church 0            —→*  ctrue
--     ciszero ⬝ church (n + 1)      —→*  cfalse
--     cpred ⬝ church (n + 1)        —→*  church n
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchNumerals

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

-- ====================================================================
-- 1. Booleans and the conditional
-- ====================================================================

/-- `ƛb. ƛx. ƛy. b x y`. -/
def cif : Scoped := abs (abs (abs (app (app (var 2) (var 1)) (var 0))))

theorem ctrue_closed : ctrue.newFreeIndexes = 0 := rfl
theorem cfalse_closed : cfalse.newFreeIndexes = 0 := rfl
theorem cif_closed : cif.newFreeIndexes = 0 := rfl

@[simp] theorem ren_ctrue (ρ : Nat → Nat) : ren ρ ctrue = ctrue :=
  ren_eq_self_of_closed ctrue_closed ρ
@[simp] theorem sub_ctrue (σ : Nat → Scoped) : sub σ ctrue = ctrue :=
  sub_eq_self_of_closed ctrue_closed σ
@[simp] theorem ren_cfalse (ρ : Nat → Nat) : ren ρ cfalse = cfalse :=
  ren_eq_self_of_closed cfalse_closed ρ
@[simp] theorem sub_cfalse (σ : Nat → Scoped) : sub σ cfalse = cfalse :=
  sub_eq_self_of_closed cfalse_closed σ

end Scoped

/-- `true x y —→* x`. -/
theorem ctrue_red (x y : Scoped) : Scoped.app (Scoped.app ctrue x) y —→* x := by
  have h₁ : Scoped.app ctrue x —→ Scoped.abs (Scoped.ren Nat.succ x) := by
    have h := Beta.basis' (Scoped.abs (Scoped.var 1)) x
    simpa [ctrue] using h
  refine Relation.ReflTransGen.head (Beta.appr y h₁) ?_
  have h₂ := Beta.basis' (Scoped.ren Nat.succ x) y
  rw [Scoped.sub0_ren_succ] at h₂
  exact Relation.ReflTransGen.single h₂

/-- `false x y —→* y`. -/
theorem cfalse_red (x y : Scoped) : Scoped.app (Scoped.app cfalse x) y —→* y := by
  have h₁ : Scoped.app cfalse x —→ Scoped.abs (Scoped.var 0) := by
    have h := Beta.basis' (Scoped.abs (Scoped.var 0)) x
    simpa [cfalse] using h
  refine Relation.ReflTransGen.head (Beta.appr y h₁) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.var 0)) y —→ y := by
    have h := Beta.basis' (Scoped.var 0) y
    simpa using h
  exact Relation.ReflTransGen.single h₂

/-- The conditional applies its first argument to the other two. -/
theorem cif_red (b x y : Scoped) :
    Scoped.app (Scoped.app (Scoped.app Scoped.cif b) x) y —→* Scoped.app (Scoped.app b x) y := by
  have h₁ : Scoped.app Scoped.cif b —→
      Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.ren Nat.succ (Scoped.ren Nat.succ b)) (Scoped.var 1))
        (Scoped.var 0))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0)))) b
    simpa [Scoped.cif] using h
  refine Relation.ReflTransGen.head (Beta.appr y (Beta.appr x h₁)) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.ren Nat.succ (Scoped.ren Nat.succ b)) (Scoped.var 1))
        (Scoped.var 0)))) x —→
      Scoped.abs (Scoped.app (Scoped.app (Scoped.ren Nat.succ b) (Scoped.ren Nat.succ x))
        (Scoped.var 0)) := by
    have h := Beta.basis' (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.ren Nat.succ (Scoped.ren Nat.succ b)) (Scoped.var 1))
      (Scoped.var 0))) x
    simpa [Scoped.sub_upSub_ren_succ, Scoped.sub0_ren_succ] using h
  refine Relation.ReflTransGen.head (Beta.appr y h₂) ?_
  have h₃ := Beta.basis' (Scoped.app (Scoped.app (Scoped.ren Nat.succ b)
    (Scoped.ren Nat.succ x)) (Scoped.var 0)) y
  simp only [Scoped.sub0, Scoped.sub_app] at h₃
  rw [show Scoped.sub (Scoped.cons y Scoped.var) (Scoped.ren Nat.succ b) = b from
      Scoped.sub0_ren_succ y b,
    show Scoped.sub (Scoped.cons y Scoped.var) (Scoped.ren Nat.succ x) = x from
      Scoped.sub0_ren_succ y x,
    show Scoped.sub (Scoped.cons y Scoped.var) (Scoped.var 0) = y from rfl] at h₃
  exact Relation.ReflTransGen.single h₃

/-- The conditional selects its second argument on `true`. -/
theorem cif_ctrue (x y : Scoped) :
    Scoped.app (Scoped.app (Scoped.app Scoped.cif ctrue) x) y —→* x :=
  (cif_red ctrue x y).trans (ctrue_red x y)

/-- The conditional selects its third argument on `false`. -/
theorem cif_cfalse (x y : Scoped) :
    Scoped.app (Scoped.app (Scoped.app Scoped.cif cfalse) x) y —→* y :=
  (cif_red cfalse x y).trans (cfalse_red x y)

namespace Scoped

-- ====================================================================
-- 2. Pairs
-- ====================================================================

/-- `ƛx. ƛy. ƛf. f x y`. -/
def cpair : Scoped := abs (abs (abs (app (app (var 0) (var 2)) (var 1))))

/-- `ƛp. p true`. -/
def cfst : Scoped := abs (app (var 0) ctrue)

/-- `ƛp. p false`. -/
def csnd : Scoped := abs (app (var 0) cfalse)

/-- The value `⟨x, y⟩ = ƛf. f x y` that `cpair x y` reduces to. -/
def pairVal (x y : Scoped) : Scoped :=
  abs (app (app (var 0) (ren Nat.succ x)) (ren Nat.succ y))

theorem cpair_closed : cpair.newFreeIndexes = 0 := rfl
theorem cfst_closed : cfst.newFreeIndexes = 0 := rfl
theorem csnd_closed : csnd.newFreeIndexes = 0 := rfl

@[simp] theorem sub_cpair (σ : Nat → Scoped) : sub σ cpair = cpair :=
  sub_eq_self_of_closed cpair_closed σ
@[simp] theorem sub_cfst (σ : Nat → Scoped) : sub σ cfst = cfst :=
  sub_eq_self_of_closed cfst_closed σ
@[simp] theorem sub_csnd (σ : Nat → Scoped) : sub σ csnd = csnd :=
  sub_eq_self_of_closed csnd_closed σ

end Scoped

/-- Pairing: `cpair x y` reduces to the pair value `⟨x, y⟩`. -/
theorem cpair_red (x y : Scoped) :
    Scoped.app (Scoped.app Scoped.cpair x) y —→* Scoped.pairVal x y := by
  have h₁ : Scoped.app Scoped.cpair x —→
      Scoped.abs (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0)
        (Scoped.ren Nat.succ (Scoped.ren Nat.succ x))) (Scoped.var 1))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.var 0) (Scoped.var 2)) (Scoped.var 1)))) x
    simpa [Scoped.cpair] using h
  refine Relation.ReflTransGen.head (Beta.appr y h₁) ?_
  have h₂ := Beta.basis' (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0)
      (Scoped.ren Nat.succ (Scoped.ren Nat.succ x))) (Scoped.var 1))) y
  refine Relation.ReflTransGen.single ?_
  simpa [Scoped.pairVal, Scoped.sub_upSub_ren_succ, Scoped.sub0_ren_succ] using h₂

/-- First projection. -/
theorem cfst_pairVal (x y : Scoped) :
    Scoped.app Scoped.cfst (Scoped.pairVal x y) —→* x := by
  have h₁ : Scoped.app Scoped.cfst (Scoped.pairVal x y) —→
      Scoped.app (Scoped.pairVal x y) ctrue := by
    have h := Beta.basis' (Scoped.app (Scoped.var 0) ctrue) (Scoped.pairVal x y)
    simpa [Scoped.cfst] using h
  refine Relation.ReflTransGen.head h₁ ?_
  have h₂ : Scoped.app (Scoped.pairVal x y) ctrue —→ Scoped.app (Scoped.app ctrue x) y := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.ren Nat.succ x))
      (Scoped.ren Nat.succ y)) ctrue
    simpa [Scoped.pairVal, Scoped.sub0_ren_succ] using h
  exact Relation.ReflTransGen.head h₂ (ctrue_red x y)

/-- Second projection. -/
theorem csnd_pairVal (x y : Scoped) :
    Scoped.app Scoped.csnd (Scoped.pairVal x y) —→* y := by
  have h₁ : Scoped.app Scoped.csnd (Scoped.pairVal x y) —→
      Scoped.app (Scoped.pairVal x y) cfalse := by
    have h := Beta.basis' (Scoped.app (Scoped.var 0) cfalse) (Scoped.pairVal x y)
    simpa [Scoped.csnd] using h
  refine Relation.ReflTransGen.head h₁ ?_
  have h₂ : Scoped.app (Scoped.pairVal x y) cfalse —→ Scoped.app (Scoped.app cfalse x) y := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.ren Nat.succ x))
      (Scoped.ren Nat.succ y)) cfalse
    simpa [Scoped.pairVal, Scoped.sub0_ren_succ] using h
  exact Relation.ReflTransGen.head h₂ (cfalse_red x y)

/-- **Pairs are correct**: the first projection of a pair is its first
    component. -/
theorem cfst_cpair (x y : Scoped) :
    Scoped.app Scoped.cfst (Scoped.app (Scoped.app Scoped.cpair x) y) —→* x :=
  (beta_star_appl _ (cpair_red x y)).trans (cfst_pairVal x y)

/-- **Pairs are correct**: the second projection of a pair is its second
    component. -/
theorem csnd_cpair (x y : Scoped) :
    Scoped.app Scoped.csnd (Scoped.app (Scoped.app Scoped.cpair x) y) —→* y :=
  (beta_star_appl _ (cpair_red x y)).trans (csnd_pairVal x y)

namespace Scoped

-- ====================================================================
-- 3. The test for zero
-- ====================================================================

/-- `ƛn. n (ƛx. false) true`. -/
def ciszero : Scoped := abs (app (app (var 0) (abs cfalse)) ctrue)

theorem ciszero_closed : ciszero.newFreeIndexes = 0 := rfl

theorem csucc_closed : csucc.newFreeIndexes = 0 := rfl

@[simp] theorem sub_csucc (σ : Nat → Scoped) : sub σ csucc = csucc :=
  sub_eq_self_of_closed csucc_closed σ

end Scoped

/-- Zero is zero. -/
theorem ciszero_zero :
    Scoped.app Scoped.ciszero (Scoped.church 0) —→* ctrue := by
  have h₁ : Scoped.app Scoped.ciszero (Scoped.church 0) —→
      Scoped.app (Scoped.app (Scoped.church 0) (Scoped.abs cfalse)) ctrue := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.abs cfalse)) ctrue)
      (Scoped.church 0)
    simpa [Scoped.ciszero] using h
  refine Relation.ReflTransGen.head h₁ ?_
  simpa using church_app 0 (Scoped.abs cfalse) ctrue

/-- A successor is not zero. -/
theorem ciszero_succ (n : Nat) :
    Scoped.app Scoped.ciszero (Scoped.church (n + 1)) —→* cfalse := by
  have h₁ : Scoped.app Scoped.ciszero (Scoped.church (n + 1)) —→
      Scoped.app (Scoped.app (Scoped.church (n + 1)) (Scoped.abs cfalse)) ctrue := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.abs cfalse)) ctrue)
      (Scoped.church (n + 1))
    simpa [Scoped.ciszero] using h
  refine Relation.ReflTransGen.head h₁ ?_
  refine (church_app (n + 1) (Scoped.abs cfalse) ctrue).trans ?_
  rw [Scoped.iterApp_succ]
  have h₂ := Beta.basis' cfalse (Scoped.iterApp (Scoped.abs cfalse) ctrue n)
  simpa using Relation.ReflTransGen.single h₂

namespace Scoped

-- ====================================================================
-- 4. Kleene's predecessor
-- ====================================================================

/-- `ƛp. ⟨snd p, succ (snd p)⟩`: the step function of the predecessor. -/
def cpredStep : Scoped :=
  abs (app (app cpair (app csnd (var 0))) (app csucc (app csnd (var 0))))

/-- `ƛn. fst (n step ⟨0, 0⟩)`. -/
def cpred : Scoped :=
  abs (app cfst (app (app (var 0) cpredStep) (app (app cpair (church 0)) (church 0))))

theorem cpredStep_closed : cpredStep.newFreeIndexes = 0 := rfl

@[simp] theorem sub_cpredStep (σ : Nat → Scoped) : sub σ cpredStep = cpredStep :=
  sub_eq_self_of_closed cpredStep_closed σ

theorem pairVal_closed {x y : Scoped} (hx : x.newFreeIndexes = 0)
    (hy : y.newFreeIndexes = 0) : (pairVal x y).newFreeIndexes = 0 := by
  rw [pairVal, ren_eq_self_of_closed hx, ren_eq_self_of_closed hy]
  simp only [newFreeIndexes_abs, newFreeIndexes_app, newFreeIndexes_var, hx, hy]
  omega

end Scoped

/-- The pair of Church numerals `⟨n - 1, n⟩` the iteration builds up. -/
def predPair (n : Nat) : Scoped := Scoped.pairVal (Scoped.church (n - 1)) (Scoped.church n)

/-- The iteration of the predecessor step function builds `⟨n - 1, n⟩`. -/
theorem cpredStep_iter (n : Nat) :
    Scoped.iterApp Scoped.cpredStep
      (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.church 0)) n
      —→* predPair n := by
  induction n with
  | zero =>
      simpa [predPair] using cpair_red (Scoped.church 0) (Scoped.church 0)
  | succ n ih =>
      rw [Scoped.iterApp_succ]
      refine (beta_star_appl _ ih).trans ?_
      have h₁ : Scoped.app Scoped.cpredStep (predPair n) —→
          Scoped.app (Scoped.app Scoped.cpair (Scoped.app Scoped.csnd (predPair n)))
            (Scoped.app Scoped.csucc (Scoped.app Scoped.csnd (predPair n))) := by
        have h := Beta.basis' (Scoped.app (Scoped.app Scoped.cpair
          (Scoped.app Scoped.csnd (Scoped.var 0)))
          (Scoped.app Scoped.csucc (Scoped.app Scoped.csnd (Scoped.var 0)))) (predPair n)
        simpa [Scoped.cpredStep] using h
      refine Relation.ReflTransGen.head h₁ ?_
      have hsnd : Scoped.app Scoped.csnd (predPair n) —→* Scoped.church n :=
        csnd_pairVal _ _
      refine (beta_star_appr _ (beta_star_appl _ hsnd)).trans ?_
      refine (beta_star_appl _ (beta_star_appl _ hsnd)).trans ?_
      refine (beta_star_appl _ (csucc_church n)).trans ?_
      simpa [predPair] using cpair_red (Scoped.church n) (Scoped.church (n + 1))

/-- **Kleene's predecessor is correct**. -/
theorem cpred_church (n : Nat) :
    Scoped.app Scoped.cpred (Scoped.church n) —→* Scoped.church (n - 1) := by
  have h₁ : Scoped.app Scoped.cpred (Scoped.church n) —→
      Scoped.app Scoped.cfst (Scoped.app (Scoped.app (Scoped.church n) Scoped.cpredStep)
        (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.church 0))) := by
    have h := Beta.basis' (Scoped.app Scoped.cfst
      (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpredStep)
        (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.church 0))))
      (Scoped.church n)
    simpa [Scoped.cpred] using h
  refine Relation.ReflTransGen.head h₁ ?_
  refine (beta_star_appl _ (church_app n Scoped.cpredStep _)).trans ?_
  refine (beta_star_appl _ (cpredStep_iter n)).trans ?_
  exact cfst_pairVal _ _

end IwilareNatIsExactScope
