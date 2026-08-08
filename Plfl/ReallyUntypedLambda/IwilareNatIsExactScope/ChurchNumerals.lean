-- Church numerals, and the correctness of the arithmetic combinators.
--
-- The natural number `n` is represented by the closed term
--
--     church n  =  ƛf. ƛx. f (f (... (f x)))       -- `n` applications
--
-- and the fundamental fact about it is that applying it to `F` and `E` iterates
-- `F` exactly `n` times on `E` (`church_app`).  From that, the standard
-- combinators for successor, addition and multiplication are proved correct:
--
--     csucc ⬝ church n            —→*  church (n + 1)
--     cadd  ⬝ church m ⬝ church n  —→*  church (m + n)
--     cmul  ⬝ church m ⬝ church n  —→*  church (m * n)
--
-- so addition and multiplication are *representable* in the pure untyped
-- lambda calculus.  The representation is faithful: numerals are normal forms
-- and distinct numerals are not convertible (`church_betaeq_iff`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.ScopeBounds

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

-- Computation rules for the substitutions crossing a binder, so that `simp`
-- can evaluate the substitutions produced by contracting a redex.
@[simp] theorem cons_zero (N : Scoped) (σ : Nat → Scoped) : cons N σ 0 = N := rfl
@[simp] theorem cons_succ (N : Scoped) (σ : Nat → Scoped) (i : Nat) :
    cons N σ (i + 1) = σ i := rfl
@[simp] theorem upSub_zero (σ : Nat → Scoped) : upSub σ 0 = var 0 := rfl
@[simp] theorem upSub_succ (σ : Nat → Scoped) (i : Nat) :
    upSub σ (i + 1) = ren Nat.succ (σ i) := rfl

/-- `iterApp F E n = F (F (... (F E)))`, with `n` occurrences of `F`. -/
def iterApp (F E : Scoped) : Nat → Scoped
  | 0 => E
  | k + 1 => app F (iterApp F E k)

@[simp] theorem iterApp_zero (F E : Scoped) : iterApp F E 0 = E := rfl
@[simp] theorem iterApp_succ (F E : Scoped) (k : Nat) :
    iterApp F E (k + 1) = app F (iterApp F E k) := rfl

theorem iterApp_add (F E : Scoped) (m n : Nat) :
    iterApp F (iterApp F E n) m = iterApp F E (m + n) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have e : k + 1 + n = (k + n) + 1 := by omega
      rw [e, iterApp_succ, iterApp_succ, ih]

@[simp] theorem sub_iterApp (σ : Nat → Scoped) (F E : Scoped) (n : Nat) :
    sub σ (iterApp F E n) = iterApp (sub σ F) (sub σ E) n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [iterApp_succ, sub_app, ih]

/-- The Church numeral `n = ƛf. ƛx. fⁿ x`. -/
def church (n : Nat) : Scoped := abs (abs (iterApp (var 1) (var 0) n))

/-- `ƛn. ƛf. ƛx. f (n f x)`. -/
def csucc : Scoped :=
  abs (abs (abs (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- `ƛm. ƛn. ƛf. ƛx. m f (n f x)`. -/
def cadd : Scoped :=
  abs (abs (abs (abs (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))

/-- `ƛm. ƛn. ƛf. ƛx. m (n f) x`. -/
def cmul : Scoped :=
  abs (abs (abs (abs (app (app (var 3) (app (var 2) (var 1))) (var 0)))))

theorem newFreeIndexes_iterApp_le (n : Nat) :
    (iterApp (var 1) (var 0) n).newFreeIndexes ≤ 2 := by
  induction n with
  | zero => simp
  | succ k ih => simp only [iterApp_succ, newFreeIndexes_app, newFreeIndexes_var]; omega

/-- Church numerals are closed terms. -/
theorem church_closed (n : Nat) : (church n).newFreeIndexes = 0 := by
  have := newFreeIndexes_iterApp_le n
  simp only [church, newFreeIndexes_abs]
  omega

@[simp] theorem ren_church (n : Nat) (ρ : Nat → Nat) : ren ρ (church n) = church n :=
  ren_eq_self_of_closed (church_closed n) ρ

@[simp] theorem sub_church (n : Nat) (σ : Nat → Scoped) : sub σ (church n) = church n :=
  sub_eq_self_of_closed (church_closed n) σ

end Scoped

-- ====================================================================
-- The fundamental property: a numeral iterates its first argument
-- ====================================================================

/-- **A Church numeral iterates**: `n F E` reduces to `F` applied `n` times to
    `E`, for arbitrary terms `F` and `E`. -/
theorem church_app (n : Nat) (F E : Scoped) :
    Scoped.app (Scoped.app (Scoped.church n) F) E —→* Scoped.iterApp F E n := by
  have h₁ : Scoped.app (Scoped.church n) F —→
      Scoped.abs (Scoped.iterApp (Scoped.ren Nat.succ F) (Scoped.var 0) n) := by
    have h := Beta.basis' (Scoped.abs (Scoped.iterApp (Scoped.var 1) (Scoped.var 0) n)) F
    simp_all only [Scoped.sub_abs, Scoped.sub_iterApp, Scoped.sub_var', Scoped.upSub_succ, Scoped.cons_zero,
      Scoped.upSub_zero]
    obtain ⟨fst, snd⟩ := F
    obtain ⟨fst_1, snd_1⟩ := E
    exact h
  have h₂ : Scoped.app
      (Scoped.abs (Scoped.iterApp (Scoped.ren Nat.succ F) (Scoped.var 0) n)) E —→
      Scoped.iterApp F E n := by
    have h := Beta.basis' (Scoped.iterApp (Scoped.ren Nat.succ F) (Scoped.var 0) n) E
    simpa [Scoped.sub0_ren_succ] using h
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (Beta.appr E h₁)) h₂

-- ====================================================================
-- Correctness of the arithmetic combinators
-- ====================================================================

/-- **The successor combinator is correct.** -/
theorem csucc_church (n : Nat) :
    Scoped.app Scoped.csucc (Scoped.church n) —→* Scoped.church (n + 1) := by
  have h₁ : Scoped.app Scoped.csucc (Scoped.church n) —→
      Scoped.abs (Scoped.abs (Scoped.app (Scoped.var 1)
        (Scoped.app (Scoped.app (Scoped.church n) (Scoped.var 1)) (Scoped.var 0)))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app (Scoped.var 1)
      (Scoped.app (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0)))))
      (Scoped.church n)
    simp_all only [Scoped.sub_abs, Scoped.sub_app, Scoped.sub_var', Scoped.upSub_succ, Scoped.upSub_zero,
      Scoped.ren_var, Nat.succ_eq_add_one, Nat.zero_add, Scoped.cons_zero, Scoped.ren_church]
    exact h
  refine Relation.ReflTransGen.head h₁ ?_
  exact beta_star_abs (beta_star_abs (beta_star_appl _ (church_app n _ _)))

/-- **The addition combinator is correct.** -/
theorem cadd_church (m n : Nat) :
    Scoped.app (Scoped.app Scoped.cadd (Scoped.church m)) (Scoped.church n) —→*
      Scoped.church (m + n) := by
  have h₁ : Scoped.app Scoped.cadd (Scoped.church m) —→
      Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.var 1))
        (Scoped.app (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0))))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.var 3) (Scoped.var 1))
      (Scoped.app (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0))))))
      (Scoped.church m)
    simp_all only [Scoped.sub_abs, Scoped.sub_app, Scoped.sub_var', Scoped.upSub_succ, Scoped.cons_zero,
      Scoped.ren_church, Scoped.upSub_zero, Scoped.ren_var, Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceAdd]
    exact h
  have h₂ : Scoped.app
      (Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.var 1))
        (Scoped.app (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0))))))
      (Scoped.church n) —→
      Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.var 1))
        (Scoped.app (Scoped.app (Scoped.church n) (Scoped.var 1)) (Scoped.var 0)))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.church m) (Scoped.var 1))
      (Scoped.app (Scoped.app (Scoped.var 2) (Scoped.var 1)) (Scoped.var 0)))))
      (Scoped.church n)
    simpa using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₁) (Relation.ReflTransGen.head h₂ ?_)
  refine beta_star_abs (beta_star_abs ?_)
  refine Relation.ReflTransGen.trans
    (beta_star_appl _ (church_app n (Scoped.var 1) (Scoped.var 0))) ?_
  refine Relation.ReflTransGen.trans
    (church_app m (Scoped.var 1) (Scoped.iterApp (Scoped.var 1) (Scoped.var 0) n)) ?_
  rw [Scoped.iterApp_add]

/-- Iterating `n F` `m` times is iterating `F` `n * m` times. -/
theorem iterApp_church_app (n m : Nat) (F E : Scoped) :
    Scoped.iterApp (Scoped.app (Scoped.church n) F) E m —→* Scoped.iterApp F E (n * m) := by
  induction m with
  | zero => rw [Nat.mul_zero]; exact Relation.ReflTransGen.refl
  | succ k ih =>
      refine Relation.ReflTransGen.trans (beta_star_appl _ ih) ?_
      refine Relation.ReflTransGen.trans (church_app n F (Scoped.iterApp F E (n * k))) ?_
      rw [Scoped.iterApp_add, Nat.mul_succ, Nat.add_comm (n * k) n]

/-- **The multiplication combinator is correct.** -/
theorem cmul_church (m n : Nat) :
    Scoped.app (Scoped.app Scoped.cmul (Scoped.church m)) (Scoped.church n) —→*
      Scoped.church (m * n) := by
  have h₁ : Scoped.app Scoped.cmul (Scoped.church m) —→
      Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.app (Scoped.var 2) (Scoped.var 1)))
        (Scoped.var 0)))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.var 3) (Scoped.app (Scoped.var 2) (Scoped.var 1)))
      (Scoped.var 0))))) (Scoped.church m)
    simp_all only [Scoped.sub_abs, Scoped.sub_app, Scoped.sub_var', Scoped.upSub_succ, Scoped.cons_zero,
      Scoped.ren_church, Scoped.upSub_zero, Scoped.ren_var, Nat.succ_eq_add_one, Nat.zero_add, Nat.reduceAdd]
    exact h
  have h₂ : Scoped.app
      (Scoped.abs (Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.app (Scoped.var 2) (Scoped.var 1)))
        (Scoped.var 0)))))
      (Scoped.church n) —→
      Scoped.abs (Scoped.abs (Scoped.app
        (Scoped.app (Scoped.church m) (Scoped.app (Scoped.church n) (Scoped.var 1)))
        (Scoped.var 0))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.abs (Scoped.app
      (Scoped.app (Scoped.church m) (Scoped.app (Scoped.var 2) (Scoped.var 1)))
      (Scoped.var 0)))) (Scoped.church n)
    simpa using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₁) (Relation.ReflTransGen.head h₂ ?_)
  refine beta_star_abs (beta_star_abs ?_)
  refine Relation.ReflTransGen.trans
    (church_app m (Scoped.app (Scoped.church n) (Scoped.var 1)) (Scoped.var 0)) ?_
  refine Relation.ReflTransGen.trans
    (iterApp_church_app n m (Scoped.var 1) (Scoped.var 0)) ?_
  rw [Nat.mul_comm]

-- ====================================================================
-- The numerals are pairwise distinct normal forms
-- ====================================================================

theorem normal_iterApp (n : Nat) :
    Normal (Scoped.iterApp (Scoped.var 1) (Scoped.var 0) n) := by
  induction n with
  | zero => exact Normal.var 0
  | succ k ih =>
      exact (Normal.var 1).app ih (fun _ => Scoped.var_ne_abs)

theorem normal_church (n : Nat) : Normal (Scoped.church n) :=
  (normal_iterApp n).abs.abs

theorem iterApp_injective {m n : Nat}
    (h : Scoped.iterApp (Scoped.var 1) (Scoped.var 0) m
        = Scoped.iterApp (Scoped.var 1) (Scoped.var 0) n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ k => exact absurd h Scoped.var_ne_app
  | succ j ih =>
      cases n with
      | zero => exact absurd h Scoped.app_ne_var
      | succ k =>
          simp only [Scoped.iterApp_succ, Scoped.app_eq_app] at h
          rw [ih h.2]

theorem church_injective {m n : Nat} (h : Scoped.church m = Scoped.church n) : m = n := by
  simp only [Scoped.church, Scoped.abs_eq_abs] at h
  exact iterApp_injective h

/-- **Distinct numerals are not convertible**: the representation of the
    natural numbers by Church numerals is faithful. -/
theorem church_betaeq_iff {m n : Nat} : Scoped.church m ≡β Scoped.church n ↔ m = n := by
  refine ⟨fun h => church_injective ?_, fun h => h ▸ BetaEq.refl _⟩
  exact betaeq_normal_eq h (normal_church m) (normal_church n)

end IwilareNatIsExactScope
