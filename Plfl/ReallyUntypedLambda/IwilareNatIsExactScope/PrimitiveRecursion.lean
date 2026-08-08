-- Subtraction, and the definability of primitive recursion.
--
-- Iterating the predecessor gives truncated subtraction (`csub_church`), and
-- the combinator
--
--     crec = ƛf ƛz ƛn. snd (n (ƛp. ⟨succ (fst p), f (fst p) (snd p)⟩) ⟨0, z⟩)
--
-- performs primitive recursion: for closed `F` and `Z`,
--
--     crec ⬝ F ⬝ Z ⬝ church n  —→*  F ⬝ church (n-1) ⬝ (… (F ⬝ church 0 ⬝ Z) …)
--
-- (`crec_church`).  Consequently **every function defined by primitive
-- recursion from lambda-definable data is lambda-definable**
-- (`crec_represents`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ChurchData
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Evaluator

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

-- ====================================================================
-- 1. Truncated subtraction
-- ====================================================================

/-- `ƛm. ƛn. n pred m`. -/
def csub : Scoped := abs (abs (app (app (var 0) cpred) (var 1)))

theorem cpred_closed : cpred.newFreeIndexes = 0 := rfl

@[simp] theorem sub_cpred (σ : Nat → Scoped) : sub σ cpred = cpred :=
  sub_eq_self_of_closed cpred_closed σ

theorem csub_closed : csub.newFreeIndexes = 0 := rfl

end Scoped

/-- Iterating the predecessor `n` times on `church m` gives `church (m - n)`. -/
theorem iterApp_cpred (m n : Nat) :
    Scoped.iterApp Scoped.cpred (Scoped.church m) n —→* Scoped.church (m - n) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [Scoped.iterApp_succ]
      refine (beta_star_appl _ ih).trans ?_
      have h := cpred_church (m - n)
      have e : m - n - 1 = m - (n + 1) := by omega
      rwa [e] at h

/-- **Truncated subtraction is representable**. -/
theorem csub_church (m n : Nat) :
    Scoped.app (Scoped.app Scoped.csub (Scoped.church m)) (Scoped.church n) —→*
      Scoped.church (m - n) := by
  have h₁ : Scoped.app Scoped.csub (Scoped.church m) —→
      Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpred) (Scoped.church m)) := by
    have h := Beta.basis' (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpred)
      (Scoped.var 1))) (Scoped.church m)
    simpa [Scoped.csub] using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₁) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpred)
      (Scoped.church m))) (Scoped.church n) —→
      Scoped.app (Scoped.app (Scoped.church n) Scoped.cpred) (Scoped.church m) := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.var 0) Scoped.cpred)
      (Scoped.church m)) (Scoped.church n)
    simpa using h
  refine Relation.ReflTransGen.head h₂ ?_
  exact (church_app n Scoped.cpred (Scoped.church m)).trans (iterApp_cpred m n)

-- ====================================================================
-- 2. Primitive recursion
-- ====================================================================

namespace Scoped

/-- The step function of `crec`, for a given `F`: `ƛp. ⟨succ (fst p), F (fst p) (snd p)⟩`. -/
def crecStep (F : Scoped) : Scoped :=
  abs (app (app cpair (app csucc (app cfst (var 0))))
        (app (app F (app cfst (var 0))) (app csnd (var 0))))

@[simp] theorem sub_crecStep (σ : Nat → Scoped) (F : Scoped) :
    sub σ (crecStep F) = crecStep (sub (upSub σ) F) := rfl

/-- `ƛf. ƛz. ƛn. snd (n (ƛp. ⟨succ (fst p), f (fst p) (snd p)⟩) ⟨0, z⟩)`. -/
def crec : Scoped :=
  abs (abs (abs (app csnd
    (app (app (var 0) (crecStep (var 3))) (app (app cpair (church 0)) (var 1))))))

end Scoped

/-- The value computed by primitive recursion: `recVal F Z 0 = Z` and
    `recVal F Z (n+1) = F (church n) (recVal F Z n)`. -/
def recVal (F Z : Scoped) : Nat → Scoped
  | 0 => Z
  | n + 1 => Scoped.app (Scoped.app F (Scoped.church n)) (recVal F Z n)

/-- The iteration of the step function builds the pair `⟨n, recVal F Z n⟩`. -/
theorem crecStep_iter {F Z : Scoped} (hF : F.newFreeIndexes = 0) (n : Nat) :
    Scoped.iterApp (Scoped.crecStep F)
      (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) Z) n
      —→* Scoped.pairVal (Scoped.church n) (recVal F Z n) := by
  induction n with
  | zero => exact cpair_red (Scoped.church 0) Z
  | succ n ih =>
      rw [Scoped.iterApp_succ]
      refine (beta_star_appl _ ih).trans ?_
      have h₁ : Scoped.app (Scoped.crecStep F) (Scoped.pairVal (Scoped.church n) (recVal F Z n)) —→
          Scoped.app (Scoped.app Scoped.cpair
              (Scoped.app Scoped.csucc (Scoped.app Scoped.cfst
                (Scoped.pairVal (Scoped.church n) (recVal F Z n)))))
            (Scoped.app (Scoped.app F (Scoped.app Scoped.cfst
                (Scoped.pairVal (Scoped.church n) (recVal F Z n))))
              (Scoped.app Scoped.csnd
                (Scoped.pairVal (Scoped.church n) (recVal F Z n)))) := by
        have h := Beta.basis' (Scoped.app (Scoped.app Scoped.cpair
          (Scoped.app Scoped.csucc (Scoped.app Scoped.cfst (Scoped.var 0))))
          (Scoped.app (Scoped.app F (Scoped.app Scoped.cfst (Scoped.var 0)))
            (Scoped.app Scoped.csnd (Scoped.var 0))))
          (Scoped.pairVal (Scoped.church n) (recVal F Z n))
        simpa [Scoped.crecStep, Scoped.sub_eq_self_of_closed hF] using h
      refine Relation.ReflTransGen.head h₁ ?_
      have hfst : Scoped.app Scoped.cfst (Scoped.pairVal (Scoped.church n) (recVal F Z n))
          —→* Scoped.church n := cfst_pairVal _ _
      have hsnd : Scoped.app Scoped.csnd (Scoped.pairVal (Scoped.church n) (recVal F Z n))
          —→* recVal F Z n := csnd_pairVal _ _
      refine (beta_star_appr _ (beta_star_appl _ (beta_star_appl _ hfst))).trans ?_
      refine (beta_star_appr _ (beta_star_appl _ (csucc_church n))).trans ?_
      refine (beta_star_appl _ (beta_star_appr _ (beta_star_appl _ hfst))).trans ?_
      refine (beta_star_appl _ (beta_star_appl _ hsnd)).trans ?_
      exact cpair_red (Scoped.church (n + 1))
        (Scoped.app (Scoped.app F (Scoped.church n)) (recVal F Z n))

/-- **Primitive recursion is representable**: for closed `F` and `Z`, the
    combinator `crec` computes the value of the primitive recursion with step
    `F` and base `Z`. -/
theorem crec_church {F Z : Scoped} (hF : F.newFreeIndexes = 0) (hZ : Z.newFreeIndexes = 0)
    (n : Nat) :
    Scoped.app (Scoped.app (Scoped.app Scoped.crec F) Z) (Scoped.church n) —→*
      recVal F Z n := by
  have h₁ : Scoped.app Scoped.crec F —→
      Scoped.abs (Scoped.abs (Scoped.app Scoped.csnd
        (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
          (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.var 1))))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app Scoped.csnd
      (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep (Scoped.var 3)))
        (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.var 1)))))) F
    simpa [Scoped.crec, Scoped.sub_crecStep, Scoped.ren_eq_self_of_closed hF,
      Scoped.sub_eq_self_of_closed hF] using h
  refine Relation.ReflTransGen.head (Beta.appr _ (Beta.appr _ h₁)) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.abs (Scoped.app Scoped.csnd
        (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
          (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.var 1)))))) Z —→
      Scoped.abs (Scoped.app Scoped.csnd
        (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
          (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) Z))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.app Scoped.csnd
      (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
        (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) (Scoped.var 1))))) Z
    simpa [Scoped.crecStep, Scoped.ren_eq_self_of_closed hF, Scoped.ren_eq_self_of_closed hZ,
      Scoped.sub_eq_self_of_closed hF, Scoped.sub_eq_self_of_closed hZ] using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₂) ?_
  have h₃ : Scoped.app (Scoped.abs (Scoped.app Scoped.csnd
        (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
          (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) Z)))) (Scoped.church n) —→
      Scoped.app Scoped.csnd
        (Scoped.app (Scoped.app (Scoped.church n) (Scoped.crecStep F))
          (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) Z)) := by
    have h := Beta.basis' (Scoped.app Scoped.csnd
      (Scoped.app (Scoped.app (Scoped.var 0) (Scoped.crecStep F))
        (Scoped.app (Scoped.app Scoped.cpair (Scoped.church 0)) Z))) (Scoped.church n)
    simpa [Scoped.crecStep, Scoped.sub_eq_self_of_closed hF,
      Scoped.sub_eq_self_of_closed hZ] using h
  refine Relation.ReflTransGen.head h₃ ?_
  refine (beta_star_appl _ (church_app n (Scoped.crecStep F) _)).trans ?_
  refine (beta_star_appl _ (crecStep_iter hF n)).trans ?_
  exact csnd_pairVal _ _

/-- **Primitive recursion preserves lambda-definability**: if the closed term
    `F` represents the binary function `h` on numerals and `Z` is the numeral
    `z`, then `crec F Z` represents the function defined from them by primitive
    recursion. -/
theorem crec_represents {F : Scoped} (hF : F.newFreeIndexes = 0) {h : Nat → Nat → Nat}
    (hrep : ∀ a b, Scoped.app (Scoped.app F (Scoped.church a)) (Scoped.church b) —→*
      Scoped.church (h a b))
    (z : Nat) {g : Nat → Nat} (hg0 : g 0 = z) (hgs : ∀ n, g (n + 1) = h n (g n)) (n : Nat) :
    Scoped.app (Scoped.app (Scoped.app Scoped.crec F) (Scoped.church z)) (Scoped.church n) —→*
      Scoped.church (g n) := by
  refine (crec_church hF (Scoped.church_closed z) n).trans ?_
  induction n with
  | zero => rw [hg0]; exact Relation.ReflTransGen.refl
  | succ n ih =>
      show Scoped.app (Scoped.app F (Scoped.church n)) (recVal F (Scoped.church z) n) —→* _
      refine (beta_star_appl _ ih).trans ?_
      rw [hgs n]
      exact hrep n (g n)

-- ====================================================================
-- 3. Two computations
-- ====================================================================

set_option maxRecDepth 100000 in
/-- `g 0 = 5`, `g (n+1) = n + g n`, so `g 3 = 5 + 0 + 1 + 2 = 8`, computed by
    the normal order evaluator. -/
example : Scoped.eval 2000 (Scoped.app (Scoped.app (Scoped.app Scoped.crec Scoped.cadd)
    (Scoped.church 5)) (Scoped.church 3)) = some (Scoped.church 8) := rfl

set_option maxRecDepth 100000 in
/-- `7 - 4 = 3`, computed. -/
example : Scoped.eval 2000 (Scoped.app (Scoped.app Scoped.csub (Scoped.church 7))
    (Scoped.church 4)) = some (Scoped.church 3) := rfl

end IwilareNatIsExactScope
