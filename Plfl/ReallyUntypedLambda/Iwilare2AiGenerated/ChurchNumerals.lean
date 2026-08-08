-- Church numerals and the arithmetic combinators, for the scope-bounded
-- (`Fin`-indexed) calculus.
--
-- The natural number `k` is represented by the term
--
--     church k  =  ƛf. ƛx. f (f (... (f x)))       -- `k` applications
--
-- and the fundamental fact is that applying it to `F` and `E` iterates `F`
-- exactly `k` times on `E` (`church_app`).  From that, the standard
-- combinators for successor, addition and multiplication are proved correct:
--
--     csucc ⬝ church k            —→*  church (k + 1)
--     cadd  ⬝ church m ⬝ church n  —→*  church (m + n)
--     cmul  ⬝ church m ⬝ church n  —→*  church (m * n)
--
-- The representation is faithful: numerals are normal forms and distinct
-- numerals are not convertible (`church_betaeq_iff`).
--
-- Since the scope index is now only a bound, every combinator can be defined
-- *scope-polymorphically* (`church k : Term n` for every `n`, in particular
-- `Term 0`), and all the statements below hold at an arbitrary scope.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms

@[expose] public section

namespace FinScope

open Term

/-! ## The numerals -/

/-- `iterApp F E k = F (F (... (F E)))`, with `k` occurrences of `F`. -/
def iterApp {n : Nat} (F E : Term n) : Nat → Term n
  | 0 => E
  | k + 1 => F ⬝ iterApp F E k

@[simp] theorem iterApp_zero {n : Nat} (F E : Term n) : iterApp F E 0 = E := rfl
@[simp] theorem iterApp_succ {n : Nat} (F E : Term n) (k : Nat) :
    iterApp F E (k + 1) = F ⬝ iterApp F E k := rfl

theorem iterApp_add {n : Nat} (F E : Term n) (p q : Nat) :
    iterApp F (iterApp F E q) p = iterApp F E (p + q) := by
  induction p with
  | zero => simp
  | succ k ih =>
      have e : k + 1 + q = (k + q) + 1 := by omega
      rw [e, iterApp_succ, iterApp_succ, ih]

@[simp] theorem ren_iterApp {n m : Nat} (ρ : Fin n → Fin m) (F E : Term n) (k : Nat) :
    ren ρ (iterApp F E k) = iterApp (ren ρ F) (ren ρ E) k := by
  induction k with
  | zero => rfl
  | succ j ih => simp only [iterApp_succ, ren_app, ih]

@[simp] theorem sub_iterApp {n m : Nat} (σ : Fin n → Term m) (F E : Term n) (k : Nat) :
    sub σ (iterApp F E k) = iterApp (sub σ F) (sub σ E) k := by
  induction k with
  | zero => rfl
  | succ j ih => simp only [iterApp_succ, sub_app, ih]

@[simp] theorem betaSubst_iterApp {n : Nat} (F E : Term (n + 1)) (N : Term n) (k : Nat) :
    (iterApp F E k) [ N ] = iterApp (F [ N ]) (E [ N ]) k :=
  sub_iterApp _ F E k

/-- The Church numeral `k = ƛf. ƛx. fᵏ x`. -/
def church {n : Nat} (k : Nat) : Term n := ƛ (ƛ (iterApp (v# 1) (v# 0) k))

/-- `ƛn. ƛf. ƛx. f (n f x)`. -/
def csucc {n : Nat} : Term n := ƛ (ƛ (ƛ (v# 1 ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0))))

/-- `ƛm. ƛn. ƛf. ƛx. m f (n f x)`. -/
def cadd {n : Nat} : Term n := ƛ (ƛ (ƛ (ƛ ((v# 3 ⬝ v# 1) ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0)))))

/-- `ƛm. ƛn. ƛf. ƛx. m (n f) x`. -/
def cmul {n : Nat} : Term n := ƛ (ƛ (ƛ (ƛ ((v# 3 ⬝ (v# 2 ⬝ v# 1)) ⬝ v# 0))))

/-- Church numerals are closed: renaming does not change them (in particular
`church k : Term 0` is the closed numeral). -/
@[simp] theorem ren_church {n m : Nat} (ρ : Fin n → Fin m) (k : Nat) :
    ren ρ (church k) = church k := by
  simp [church]

@[simp] theorem sub_church {n m : Nat} (σ : Fin n → Term m) (k : Nat) :
    sub σ (church k) = church k := by
  simp [church]

@[simp] theorem betaSubst_church {n : Nat} (N : Term n) (k : Nat) :
    (church k : Term (n + 1)) [ N ] = church k :=
  sub_church _ k

/-! ## The fundamental property: a numeral iterates its first argument -/

/-- **A Church numeral iterates**: `k F E` reduces to `F` applied `k` times to
`E`, for arbitrary terms `F` and `E`. -/
theorem church_app {n : Nat} (k : Nat) (F E : Term n) :
    church k ⬝ F ⬝ E —→* iterApp F E k := by
  have h₁ : church k ⬝ F —→ ƛ (iterApp (wk F) (v# 0) k) := by
    have h := Beta.basis (ƛ (iterApp (v# 1) (v# 0) k)) F
    simpa [church, betaSubst_abs] using h
  have h₂ : (ƛ (iterApp (wk F) (v# 0) k)) ⬝ E —→ iterApp F E k := by
    have h := Beta.basis (iterApp (wk F) (v# 0) k) E
    simpa using h
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Beta.appL h₁)) h₂

/-! ## Correctness of the arithmetic combinators -/

/-- **The successor combinator is correct.** -/
theorem csucc_church {n : Nat} (k : Nat) :
    (csucc : Term n) ⬝ church k —→* church (k + 1) := by
  have h₁ : (csucc : Term n) ⬝ church k —→
      ƛ (ƛ (v# 1 ⬝ ((church k ⬝ v# 1) ⬝ v# 0))) := by
    have h := Beta.basis (ƛ (ƛ (v# 1 ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0)))) (church k : Term n)
    simpa [csucc, betaSubst_abs] using h
  refine Relation.ReflTransGen.head h₁ ?_
  exact BetaStar.abs (BetaStar.abs (BetaStar.appR (church_app k _ _)))

/-- **The addition combinator is correct.** -/
theorem cadd_church {n : Nat} (p q : Nat) :
    (cadd : Term n) ⬝ church p ⬝ church q —→* church (p + q) := by
  have h₁ : (cadd : Term n) ⬝ church p —→
      ƛ (ƛ (ƛ ((church p ⬝ v# 1) ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0)))) := by
    have h := Beta.basis (ƛ (ƛ (ƛ ((v# 3 ⬝ v# 1) ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0)))))
      (church p : Term n)
    simpa [cadd, betaSubst_abs] using h
  have h₂ : (ƛ (ƛ (ƛ ((church p ⬝ v# 1) ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0))))) ⬝ (church q : Term n) —→
      ƛ (ƛ ((church p ⬝ v# 1) ⬝ ((church q ⬝ v# 1) ⬝ v# 0))) := by
    have h := Beta.basis (ƛ (ƛ ((church p ⬝ v# 1) ⬝ ((v# 2 ⬝ v# 1) ⬝ v# 0))))
      (church q : Term n)
    simpa [betaSubst_abs] using h
  refine Relation.ReflTransGen.head (Beta.appL h₁) (Relation.ReflTransGen.head h₂ ?_)
  refine BetaStar.abs (BetaStar.abs ?_)
  refine Relation.ReflTransGen.trans (BetaStar.appR (church_app q (v# 1) (v# 0))) ?_
  refine Relation.ReflTransGen.trans (church_app p (v# 1) (iterApp (v# 1) (v# 0) q)) ?_
  rw [iterApp_add]

/-- Iterating `q F` `p` times is iterating `F` `q * p` times. -/
theorem iterApp_church_app {n : Nat} (q p : Nat) (F E : Term n) :
    iterApp (church q ⬝ F) E p —→* iterApp F E (q * p) := by
  induction p with
  | zero => rw [Nat.mul_zero]; exact Relation.ReflTransGen.refl
  | succ k ih =>
      refine Relation.ReflTransGen.trans (BetaStar.appR ih) ?_
      refine Relation.ReflTransGen.trans (church_app q F (iterApp F E (q * k))) ?_
      rw [iterApp_add, Nat.mul_succ, Nat.add_comm (q * k) q]

/-- **The multiplication combinator is correct.** -/
theorem cmul_church {n : Nat} (p q : Nat) :
    (cmul : Term n) ⬝ church p ⬝ church q —→* church (p * q) := by
  have h₁ : (cmul : Term n) ⬝ church p —→
      ƛ (ƛ (ƛ ((church p ⬝ (v# 2 ⬝ v# 1)) ⬝ v# 0))) := by
    have h := Beta.basis (ƛ (ƛ (ƛ ((v# 3 ⬝ (v# 2 ⬝ v# 1)) ⬝ v# 0)))) (church p : Term n)
    simpa [cmul, betaSubst_abs] using h
  have h₂ : (ƛ (ƛ (ƛ ((church p ⬝ (v# 2 ⬝ v# 1)) ⬝ v# 0)))) ⬝ (church q : Term n) —→
      ƛ (ƛ ((church p ⬝ (church q ⬝ v# 1)) ⬝ v# 0)) := by
    have h := Beta.basis (ƛ (ƛ ((church p ⬝ (v# 2 ⬝ v# 1)) ⬝ v# 0))) (church q : Term n)
    simpa [betaSubst_abs] using h
  refine Relation.ReflTransGen.head (Beta.appL h₁) (Relation.ReflTransGen.head h₂ ?_)
  refine BetaStar.abs (BetaStar.abs ?_)
  refine Relation.ReflTransGen.trans (church_app p (church q ⬝ v# 1) (v# 0)) ?_
  refine Relation.ReflTransGen.trans (iterApp_church_app q p (v# 1) (v# 0)) ?_
  rw [Nat.mul_comm]

/-! ## The numerals are pairwise distinct normal forms -/

theorem normal_iterApp {n : Nat} (k : Nat) :
    Normal (iterApp (v# 1 : Term (n + 2)) (v# 0) k) := by
  induction k with
  | zero => exact Normal.var 0
  | succ j ih => exact (Normal.var 1).app ih (fun _ h => by cases h)

theorem normal_church {n : Nat} (k : Nat) : Normal (church k : Term n) :=
  (normal_iterApp k).abs.abs

theorem iterApp_injective {n : Nat} {p q : Nat}
    (h : iterApp (v# 1 : Term (n + 2)) (v# 0) p = iterApp (v# 1) (v# 0) q) : p = q := by
  induction p generalizing q with
  | zero =>
      cases q with
      | zero => rfl
      | succ k => exact absurd h (by simp)
  | succ j ih =>
      cases q with
      | zero => exact absurd h (by simp)
      | succ k =>
          simp only [iterApp_succ, Term.app.injEq, true_and] at h
          rw [ih h]

theorem church_injective {n : Nat} {p q : Nat}
    (h : (church p : Term n) = church q) : p = q := by
  simp only [church, Term.abs.injEq] at h
  exact iterApp_injective h

/-- **Distinct numerals are not convertible**: the representation of the
natural numbers by Church numerals is faithful. -/
theorem church_betaeq_iff {n : Nat} {p q : Nat} :
    (church p : Term n) ≡β church q ↔ p = q := by
  refine ⟨fun h => church_injective (n := n) ?_, fun h => h ▸ BetaEq.refl _⟩
  exact betaeq_normal_eq h (normal_church p) (normal_church q)

end FinScope
