-- Subtraction, and the definability of primitive recursion, for the
-- scope-bounded (`Fin`-indexed) calculus.
--
-- Iterating the predecessor gives truncated subtraction (`csub_church`), and
-- the combinator
--
--     crec = ƛf ƛz ƛn. snd (n (ƛp. ⟨succ (fst p), f (fst p) (snd p)⟩) ⟨0, z⟩)
--
-- performs primitive recursion:
--
--     crec ⬝ F ⬝ Z ⬝ church n  —→*  F ⬝ church (n-1) ⬝ (… (F ⬝ church 0 ⬝ Z) …)
--
-- (`crec_church`).  Consequently **every function defined by primitive
-- recursion from lambda-definable data is lambda-definable**
-- (`crec_represents`).
--
-- Note that, unlike in the exactly-scoped development, `F` and `Z` need not be
-- closed: renaming and substitution are scope-directed here, so the weakenings
-- introduced by the binders of `crec` cancel automatically.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Evaluator

@[expose] public section

namespace FinScope

open Term

namespace Term

/-! ## 0. Renaming invariance of the combinators -/

@[simp] theorem ren_cpair {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cpair = cpair := by simp [cpair]
@[simp] theorem ren_cfst {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cfst = cfst := by simp [cfst]
@[simp] theorem ren_csnd {n m : Nat} (ρ : Fin n → Fin m) : ren ρ csnd = csnd := by simp [csnd]
@[simp] theorem ren_csucc {n m : Nat} (ρ : Fin n → Fin m) : ren ρ csucc = csucc := by simp [csucc]
@[simp] theorem ren_cif {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cif = cif := by simp [cif]
@[simp] theorem ren_cpredStep {n m : Nat} (ρ : Fin n → Fin m) :
    ren ρ cpredStep = cpredStep := by simp [cpredStep]
@[simp] theorem ren_cpred {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cpred = cpred := by
  simp [cpred]
@[simp] theorem sub_cpred {n m : Nat} (σ : Fin n → Term m) : sub σ cpred = cpred := by
  simp [cpred]

/-! ## 1. Truncated subtraction -/

/-- `ƛm. ƛn. n pred m`. -/
def csub {n : Nat} : Term n := ƛ ƛ (v# 0 ⬝ cpred ⬝ v# 1)

end Term

/-- Iterating the predecessor `k` times on `church m` gives `church (m - k)`. -/
theorem iterApp_cpred {n : Nat} (m k : Nat) :
    iterApp (cpred : Term n) (church m) k —→* church (m - k) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
      rw [iterApp_succ]
      refine (BetaStar.appR ih).trans ?_
      have h := cpred_church (n := n) (m - k)
      have e : m - k - 1 = m - (k + 1) := by omega
      rwa [e] at h

/-- **Truncated subtraction is representable**. -/
theorem csub_church {n : Nat} (m k : Nat) :
    (csub : Term n) ⬝ church m ⬝ church k —→* church (m - k) := by
  refine Relation.ReflTransGen.head (Beta.appL (Beta.basis _ (church m))) ?_
  simp [betaSubst_abs]
  refine Relation.ReflTransGen.head (Beta.basis _ (church k)) ?_
  simp [betaSubst]
  exact (church_app k cpred (church m)).trans (iterApp_cpred m k)

/-! ## 2. Primitive recursion -/

namespace Term

/-- The step function of `crec`, for a given `F`: `ƛp. ⟨succ (fst p), F (fst p) (snd p)⟩`. -/
def crecStep {n : Nat} (F : Term n) : Term n :=
  ƛ (cpair ⬝ (csucc ⬝ (cfst ⬝ v# 0)) ⬝ (wk F ⬝ (cfst ⬝ v# 0) ⬝ (csnd ⬝ v# 0)))

/-- `ƛf. ƛz. ƛn. snd (n (ƛp. ⟨succ (fst p), f (fst p) (snd p)⟩) ⟨0, z⟩)`. -/
def crec {n : Nat} : Term n :=
  ƛ ƛ ƛ (csnd ⬝ (v# 0 ⬝ crecStep (v# 2) ⬝ (cpair ⬝ church 0 ⬝ v# 1)))

@[simp] theorem ren_crecStep {n m : Nat} (ρ : Fin n → Fin m) (F : Term n) :
    ren ρ (crecStep F) = crecStep (ren ρ F) := by
  simp [crecStep, wk, ren_ren]

@[simp] theorem sub_crecStep {n m : Nat} (σ : Fin n → Term m) (F : Term n) :
    sub σ (crecStep F) = crecStep (sub σ F) := by
  simp [crecStep, sub_exts_wk]

end Term

/-- The value computed by primitive recursion: `recVal F Z 0 = Z` and
    `recVal F Z (k+1) = F (church k) (recVal F Z k)`. -/
def recVal {n : Nat} (F Z : Term n) : Nat → Term n
  | 0 => Z
  | k + 1 => F ⬝ church k ⬝ recVal F Z k

/-- The three head reductions of `crec`. -/
theorem crec_app {n : Nat} (F Z : Term n) (k : Nat) :
    crec ⬝ F ⬝ Z ⬝ church k —→* csnd ⬝ (church k ⬝ crecStep F ⬝ (cpair ⬝ church 0 ⬝ Z)) := by
  refine Relation.ReflTransGen.head (Beta.appL (Beta.appL (Beta.basis _ F))) ?_
  simp [betaSubst_abs]
  refine Relation.ReflTransGen.head (Beta.appL (Beta.basis _ Z)) ?_
  simp [betaSubst_abs, sub_exts_wk]
  refine Relation.ReflTransGen.head (Beta.basis _ (church k)) ?_
  simp [betaSubst, sub_ren]
  exact .refl

/-- The iteration of the step function builds the pair `⟨k, recVal F Z k⟩`. -/
theorem crecStep_iter {n : Nat} (F Z : Term n) (k : Nat) :
    iterApp (crecStep F) (cpair ⬝ church 0 ⬝ Z) k —→* pairVal (church k) (recVal F Z k) := by
  induction k with
  | zero => exact cpair_red (church 0) Z
  | succ k ih =>
      rw [iterApp_succ]
      refine (BetaStar.appR ih).trans ?_
      have h₁ : crecStep F ⬝ pairVal (church k) (recVal F Z k) —→
          cpair ⬝ (csucc ⬝ (cfst ⬝ pairVal (church k) (recVal F Z k)))
            ⬝ (F ⬝ (cfst ⬝ pairVal (church k) (recVal F Z k))
                 ⬝ (csnd ⬝ pairVal (church k) (recVal F Z k))) := by
        have h := Beta.basis
          (cpair ⬝ (csucc ⬝ (cfst ⬝ v# 0)) ⬝ (wk F ⬝ (cfst ⬝ v# 0) ⬝ (csnd ⬝ v# 0)))
          (pairVal (church k) (recVal F Z k))
        simpa [crecStep] using h
      refine Relation.ReflTransGen.head h₁ ?_
      have hfst : cfst ⬝ pairVal (church k) (recVal F Z k) —→* church k := cfst_pairVal _ _
      have hsnd : csnd ⬝ pairVal (church k) (recVal F Z k) —→* recVal F Z k := csnd_pairVal _ _
      refine (BetaStar.appL (BetaStar.appR (BetaStar.appR hfst))).trans ?_
      refine (BetaStar.appL (BetaStar.appR (csucc_church k))).trans ?_
      refine (BetaStar.appR (BetaStar.appL (BetaStar.appR hfst))).trans ?_
      refine (BetaStar.appR (BetaStar.appR hsnd)).trans ?_
      exact cpair_red (church (k + 1)) (F ⬝ church k ⬝ recVal F Z k)

/-- **Primitive recursion is representable**: the combinator `crec` computes the
    value of the primitive recursion with step `F` and base `Z`. -/
theorem crec_church {n : Nat} (F Z : Term n) (k : Nat) :
    crec ⬝ F ⬝ Z ⬝ church k —→* recVal F Z k := by
  refine (crec_app F Z k).trans ?_
  refine (BetaStar.appR (church_app k (crecStep F) _)).trans ?_
  refine (BetaStar.appR (crecStep_iter F Z k)).trans ?_
  exact csnd_pairVal _ _

/-- **Primitive recursion preserves lambda-definability**: if the term `F`
    represents the binary function `h` on numerals and `Z` is the numeral `z`,
    then `crec F Z` represents the function defined from them by primitive
    recursion. -/
theorem crec_represents {n : Nat} {F : Term n} {h : Nat → Nat → Nat}
    (hrep : ∀ a b, F ⬝ church a ⬝ church b —→* church (h a b))
    (z : Nat) {g : Nat → Nat} (hg0 : g 0 = z) (hgs : ∀ k, g (k + 1) = h k (g k)) (k : Nat) :
    crec ⬝ F ⬝ church z ⬝ church k —→* church (g k) := by
  refine (crec_church F (church z) k).trans ?_
  induction k with
  | zero => rw [hg0]; exact .refl
  | succ k ih =>
      show F ⬝ church k ⬝ recVal F (church z) k —→* _
      refine (BetaStar.appR ih).trans ?_
      rw [hgs k]
      exact hrep k (g k)

/-! ## 3. Two computations -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `g 0 = 5`, `g (k+1) = k + g k`, so `g 3 = 5 + 0 + 1 + 2 = 8`, computed by
    the normal order evaluator. -/
example : Term.eval 2000 (crec ⬝ cadd ⬝ church 5 ⬝ church 3 : Term 0)
    = some (church 8) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `7 - 4 = 3`, computed. -/
example : Term.eval 2000 (csub ⬝ church 7 ⬝ church 4 : Term 0)
    = some (church 3) := by decide

end FinScope
