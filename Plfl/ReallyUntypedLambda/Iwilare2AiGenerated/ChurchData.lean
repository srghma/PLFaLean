-- Church encodings of the data: booleans, the conditional, pairs, the test for
-- zero, and Kleene's predecessor, for the scope-bounded (`Fin`-indexed)
-- calculus.
--
--     cif ⬝ ctrue ⬝ x ⬝ y            —→*  x
--     cfst ⬝ (cpair ⬝ x ⬝ y)         —→*  x
--     ciszero ⬝ church 0            —→*  ctrue
--     ciszero ⬝ church (k + 1)      —→*  cfalse
--     cpred ⬝ church k              —→*  church (k - 1)
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.ChurchNumerals

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Booleans and the conditional -/

/-- `ƛb. ƛx. ƛy. b x y`. -/
def cif {n : Nat} : Term n := ƛ (ƛ (ƛ ((v# 2 ⬝ v# 1) ⬝ v# 0)))

/-- `true x y —→* x`. -/
theorem ctrue_red {n : Nat} (x y : Term n) : ctrue ⬝ x ⬝ y —→* x := by
  have h₁ : (ctrue : Term n) ⬝ x —→ ƛ (wk x) := by
    simpa [ctrue, betaSubst_abs] using Beta.basis (ƛ (v# 1)) x
  refine Relation.ReflTransGen.head (Beta.appL h₁) ?_
  simpa using Relation.ReflTransGen.single (Beta.basis (wk x) y)

/-- `false x y —→* y`. -/
theorem cfalse_red {n : Nat} (x y : Term n) : cfalse ⬝ x ⬝ y —→* y := by
  have h₁ : (cfalse : Term n) ⬝ x —→ ƛ (v# 0) := by
    simpa [cfalse, betaSubst_abs] using Beta.basis (ƛ (v# 0)) x
  refine Relation.ReflTransGen.head (Beta.appL h₁) ?_
  simpa using Relation.ReflTransGen.single (Beta.basis (v# 0) y)

/-- The conditional applies its first argument to the other two. -/
theorem cif_red {n : Nat} (b x y : Term n) : cif ⬝ b ⬝ x ⬝ y —→* b ⬝ x ⬝ y := by
  have h₁ : (cif : Term n) ⬝ b —→ ƛ (ƛ ((wk (wk b) ⬝ v# 1) ⬝ v# 0)) := by
    simpa [cif, betaSubst_abs] using Beta.basis (ƛ (ƛ ((v# 2 ⬝ v# 1) ⬝ v# 0))) b
  have h₂ : (ƛ (ƛ ((wk (wk b) ⬝ v# 1) ⬝ v# 0))) ⬝ x —→ ƛ ((wk b ⬝ wk x) ⬝ v# 0) := by
    have h := Beta.basis (ƛ ((wk (wk b) ⬝ v# 1) ⬝ v# 0)) x
    simpa [betaSubst_abs, sub_ren] using h
  have h₃ : (ƛ ((wk b ⬝ wk x) ⬝ v# 0)) ⬝ y —→ b ⬝ x ⬝ y := by
    simpa using Beta.basis ((wk b ⬝ wk x) ⬝ v# 0) y
  exact Relation.ReflTransGen.head (Beta.appL (Beta.appL h₁))
    (Relation.ReflTransGen.head (Beta.appL h₂) (Relation.ReflTransGen.single h₃))

/-- The conditional selects its second argument on `true`. -/
theorem cif_ctrue {n : Nat} (x y : Term n) : cif ⬝ ctrue ⬝ x ⬝ y —→* x :=
  (cif_red ctrue x y).trans (ctrue_red x y)

/-- The conditional selects its third argument on `false`. -/
theorem cif_cfalse {n : Nat} (x y : Term n) : cif ⬝ cfalse ⬝ x ⬝ y —→* y :=
  (cif_red cfalse x y).trans (cfalse_red x y)

/-! ## 2. Pairs -/

/-- `ƛx. ƛy. ƛf. f x y`. -/
def cpair {n : Nat} : Term n := ƛ (ƛ (ƛ ((v# 0 ⬝ v# 2) ⬝ v# 1)))

/-- `ƛp. p true`. -/
def cfst {n : Nat} : Term n := ƛ (v# 0 ⬝ ctrue)

/-- `ƛp. p false`. -/
def csnd {n : Nat} : Term n := ƛ (v# 0 ⬝ cfalse)

/-- The value `⟨x, y⟩ = ƛf. f x y` that `cpair x y` reduces to. -/
def pairVal {n : Nat} (x y : Term n) : Term n := ƛ ((v# 0 ⬝ wk x) ⬝ wk y)

@[simp] theorem sub_cpair {n m : Nat} (σ : Fin n → Term m) : sub σ cpair = cpair := by
  simp [cpair]
@[simp] theorem betaSubst_cpair {n : Nat} (N : Term n) : (cpair : Term (n + 1)) [ N ] = cpair := sub_cpair _
@[simp] theorem sub_cfst {n m : Nat} (σ : Fin n → Term m) : sub σ cfst = cfst := by
  simp [cfst]
@[simp] theorem betaSubst_cfst {n : Nat} (N : Term n) : (cfst : Term (n + 1)) [ N ] = cfst := sub_cfst _
@[simp] theorem sub_csnd {n m : Nat} (σ : Fin n → Term m) : sub σ csnd = csnd := by
  simp [csnd]
@[simp] theorem betaSubst_csnd {n : Nat} (N : Term n) : (csnd : Term (n + 1)) [ N ] = csnd := sub_csnd _
@[simp] theorem sub_cif {n m : Nat} (σ : Fin n → Term m) : sub σ cif = cif := by
  simp [cif]
@[simp] theorem betaSubst_cif {n : Nat} (N : Term n) : (cif : Term (n + 1)) [ N ] = cif := sub_cif _
@[simp] theorem sub_csucc {n m : Nat} (σ : Fin n → Term m) : sub σ csucc = csucc := by
  simp [csucc]
@[simp] theorem betaSubst_csucc {n : Nat} (N : Term n) : (csucc : Term (n + 1)) [ N ] = csucc := sub_csucc _

/-- Pairing: `cpair x y` reduces to the pair value `⟨x, y⟩`. -/
theorem cpair_red {n : Nat} (x y : Term n) : cpair ⬝ x ⬝ y —→* pairVal x y := by
  have h₁ : (cpair : Term n) ⬝ x —→ ƛ (ƛ ((v# 0 ⬝ wk (wk x)) ⬝ v# 1)) := by
    simpa [cpair, betaSubst_abs] using Beta.basis (ƛ (ƛ ((v# 0 ⬝ v# 2) ⬝ v# 1))) x
  refine Relation.ReflTransGen.head (Beta.appL h₁) ?_
  refine Relation.ReflTransGen.single ?_
  have h₂ := Beta.basis (ƛ ((v# 0 ⬝ wk (wk x)) ⬝ v# 1)) y
  simpa [pairVal, betaSubst_abs, sub_ren] using h₂

/-- First projection. -/
theorem cfst_pairVal {n : Nat} (x y : Term n) : cfst ⬝ pairVal x y —→* x := by
  have h₁ : (cfst : Term n) ⬝ pairVal x y —→ pairVal x y ⬝ ctrue := by
    simpa [cfst] using Beta.basis (v# 0 ⬝ ctrue) (pairVal x y)
  refine Relation.ReflTransGen.head h₁ ?_
  have h₂ : pairVal x y ⬝ (ctrue : Term n) —→ ctrue ⬝ x ⬝ y := by
    simpa [pairVal] using Beta.basis ((v# 0 ⬝ wk x) ⬝ wk y) (ctrue : Term n)
  exact Relation.ReflTransGen.head h₂ (ctrue_red x y)

/-- Second projection. -/
theorem csnd_pairVal {n : Nat} (x y : Term n) : csnd ⬝ pairVal x y —→* y := by
  have h₁ : (csnd : Term n) ⬝ pairVal x y —→ pairVal x y ⬝ cfalse := by
    simpa [csnd] using Beta.basis (v# 0 ⬝ cfalse) (pairVal x y)
  refine Relation.ReflTransGen.head h₁ ?_
  have h₂ : pairVal x y ⬝ (cfalse : Term n) —→ cfalse ⬝ x ⬝ y := by
    simpa [pairVal] using Beta.basis ((v# 0 ⬝ wk x) ⬝ wk y) (cfalse : Term n)
  exact Relation.ReflTransGen.head h₂ (cfalse_red x y)

/-- **Pairs are correct**: the first projection of a pair is its first
component. -/
theorem cfst_cpair {n : Nat} (x y : Term n) : cfst ⬝ (cpair ⬝ x ⬝ y) —→* x :=
  (BetaStar.appR (cpair_red x y)).trans (cfst_pairVal x y)

/-- **Pairs are correct**: the second projection of a pair is its second
component. -/
theorem csnd_cpair {n : Nat} (x y : Term n) : csnd ⬝ (cpair ⬝ x ⬝ y) —→* y :=
  (BetaStar.appR (cpair_red x y)).trans (csnd_pairVal x y)

/-! ## 3. The test for zero -/

def ciszero {n : Nat} : Term n := ƛ ((v# 0 ⬝ (ƛ cfalse)) ⬝ ctrue)

@[simp] theorem sub_ciszero {n m : Nat} (σ : Fin n → Term m) : sub σ ciszero = ciszero := by
  simp [ciszero]
@[simp] theorem betaSubst_ciszero {n : Nat} (N : Term n) : (ciszero : Term (n + 1)) [ N ] = ciszero := sub_ciszero _

/-- Zero is zero. -/
theorem ciszero_zero {n : Nat} : (ciszero : Term n) ⬝ church 0 —→* ctrue := by
  have h₁ : (ciszero : Term n) ⬝ church 0 —→ (church 0 ⬝ (ƛ cfalse)) ⬝ ctrue := by
    simpa [ciszero, betaSubst_abs] using Beta.basis ((v# 0 ⬝ (ƛ cfalse)) ⬝ ctrue) (church 0 : Term n)
  refine Relation.ReflTransGen.head h₁ ?_
  simpa using church_app 0 (ƛ cfalse : Term n) ctrue

/-- A successor is not zero. -/
theorem ciszero_succ {n : Nat} (k : Nat) : (ciszero : Term n) ⬝ church (k + 1) —→* cfalse := by
  have h₁ : (ciszero : Term n) ⬝ church (k + 1) —→ (church (k + 1) ⬝ (ƛ cfalse)) ⬝ ctrue := by
    simpa [ciszero, betaSubst_abs] using Beta.basis ((v# 0 ⬝ (ƛ cfalse)) ⬝ ctrue) (church (k + 1) : Term n)
  refine Relation.ReflTransGen.head h₁ ?_
  refine (church_app (k + 1) (ƛ cfalse : Term n) ctrue).trans ?_
  rw [iterApp_succ]
  simpa using Relation.ReflTransGen.single
    (Beta.basis (cfalse : Term (n + 1)) (iterApp (ƛ cfalse : Term n) ctrue k))

/-! ## 4. Kleene's predecessor -/

/-- `ƛp. ⟨snd p, succ (snd p)⟩`: the step function of the predecessor. -/
def cpredStep {n : Nat} : Term n :=
  ƛ ((cpair ⬝ (csnd ⬝ v# 0)) ⬝ (csucc ⬝ (csnd ⬝ v# 0)))

/-- `ƛn. fst (n step ⟨0, 0⟩)`. -/
def cpred {n : Nat} : Term n :=
  ƛ (cfst ⬝ ((v# 0 ⬝ cpredStep) ⬝ ((cpair ⬝ church 0) ⬝ church 0)))

@[simp] theorem sub_cpredStep {n m : Nat} (σ : Fin n → Term m) :
    sub σ cpredStep = cpredStep := by
  simp [cpredStep]
@[simp] theorem betaSubst_cpredStep {n : Nat} (N : Term n) : (cpredStep : Term (n + 1)) [ N ] = cpredStep := sub_cpredStep _

@[simp] theorem sub_cpred {n m : Nat} (σ : Fin n → Term m) :
    sub σ cpred = cpred := by
  simp [cpred]
@[simp] theorem betaSubst_cpred {n : Nat} (N : Term n) : (cpred : Term (n + 1)) [ N ] = cpred := sub_cpred _

/-- The pair of Church numerals `⟨k - 1, k⟩` the iteration builds up. -/
def predPair {n : Nat} (k : Nat) : Term n := pairVal (church (k - 1)) (church k)

/-- The iteration of the predecessor step function builds `⟨k - 1, k⟩`. -/
theorem cpredStep_iter {n : Nat} (k : Nat) :
    iterApp (cpredStep : Term n) ((cpair ⬝ church 0) ⬝ church 0) k —→* predPair k := by
  induction k with
  | zero => simpa [predPair] using cpair_red (church 0 : Term n) (church 0)
  | succ k ih =>
      rw [iterApp_succ]
      refine (BetaStar.appR ih).trans ?_
      have h₁ : (cpredStep : Term n) ⬝ predPair k —→
          (cpair ⬝ (csnd ⬝ predPair k)) ⬝ (csucc ⬝ (csnd ⬝ predPair k)) := by
        simpa [cpredStep] using
          Beta.basis ((cpair ⬝ (csnd ⬝ v# 0)) ⬝ (csucc ⬝ (csnd ⬝ v# 0))) (predPair k : Term n)
      refine Relation.ReflTransGen.head h₁ ?_
      have hsnd : (csnd : Term n) ⬝ predPair k —→* church k := csnd_pairVal _ _
      refine (BetaStar.appL (BetaStar.appR hsnd)).trans ?_
      refine (BetaStar.appR (BetaStar.appR hsnd)).trans ?_
      refine (BetaStar.appR (csucc_church k)).trans ?_
      simpa [predPair] using cpair_red (church k : Term n) (church (k + 1))

/-- **Kleene's predecessor is correct**. -/
theorem cpred_church {n : Nat} (k : Nat) :
    (cpred : Term n) ⬝ church k —→* church (k - 1) := by
  have h₁ : (cpred : Term n) ⬝ church k —→
      cfst ⬝ ((church k ⬝ cpredStep) ⬝ ((cpair ⬝ church 0) ⬝ church 0)) := by
    simpa [cpred] using Beta.basis
      (cfst ⬝ ((v# 0 ⬝ cpredStep) ⬝ ((cpair ⬝ church 0) ⬝ church 0))) (church k : Term n)
  refine Relation.ReflTransGen.head h₁ ?_
  refine (BetaStar.appR (church_app k (cpredStep : Term n) _)).trans ?_
  refine (BetaStar.appR (cpredStep_iter k)).trans ?_
  exact cfst_pairVal _ _

end FinScope
