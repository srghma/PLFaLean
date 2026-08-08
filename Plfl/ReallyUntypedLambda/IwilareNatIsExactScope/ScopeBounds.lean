-- Reduction never creates free indexes.
--
-- The index `n` of a `Term n` is the exact number of free indexes of the term,
-- so the scope of a `Scoped` is a genuine measure of how open it is.  This file
-- shows that beta reduction can only make a term *more* closed:
--
--     M —→ N   →   N.newFreeIndexes ≤ M.newFreeIndexes
--
-- (`Beta.newFreeIndexes_le`, `BetaStar.newFreeIndexes_le`), the point being the
-- bound `newFreeIndexes_sub0_le` on the scope of a substitution.  In
-- particular, closed terms reduce to closed terms (`betastar_closed`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Basic

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

@[simp] theorem newFreeIndexes_var (i : Nat) : (var i).newFreeIndexes = i + 1 := rfl
@[simp] theorem newFreeIndexes_abs (s : Scoped) :
    (abs s).newFreeIndexes = s.newFreeIndexes - 1 := rfl
@[simp] theorem newFreeIndexes_app (s t : Scoped) :
    (app s t).newFreeIndexes = max s.newFreeIndexes t.newFreeIndexes := rfl

/-- A renaming that maps every free index of `s` below `k` produces a term of
    scope at most `k`. -/
theorem newFreeIndexes_ren_le (s : Scoped) : ∀ (ρ : Nat → Nat) (k : Nat),
    (∀ i < s.newFreeIndexes, ρ i < k) → (ren ρ s).newFreeIndexes ≤ k := by
  induction s using Scoped.ind with
  | var i =>
    intro ρ k h;
    simp_all only [newFreeIndexes_var, ren_var]
    apply h
    simp_all only [Nat.lt_add_one]
  | abs s ih =>
      intro ρ k h
      have := ih (upRen ρ) (k + 1) (by
        intro i hi
        cases i with
        | zero => simp [upRen]
        | succ j =>
            have : ρ j < k := h j (by simp only [newFreeIndexes_abs]; omega)
            simpa [upRen] using this)
      simp only [ren_abs, newFreeIndexes_abs]
      omega
  | app a b iha ihb =>
      intro ρ k h
      have ha := iha ρ k (fun i hi => h i (by simp; omega))
      have hb := ihb ρ k (fun i hi => h i (by simp; omega))
      simp only [ren_app, newFreeIndexes_app]
      omega

/-- A substitution whose values on the free indexes of `s` have scope at most
    `k` produces a term of scope at most `k`. -/
theorem newFreeIndexes_sub_le (s : Scoped) : ∀ (σ : Nat → Scoped) (k : Nat),
    (∀ i < s.newFreeIndexes, (σ i).newFreeIndexes ≤ k) → (sub σ s).newFreeIndexes ≤ k := by
  induction s using Scoped.ind with
  | var i => intro σ k h; simpa using h i (by simp)
  | abs s ih =>
      intro σ k h
      have := ih (upSub σ) (k + 1) (by
        intro i hi
        cases i with
        | zero => simp [upSub]
        | succ j =>
            have hj : (σ j).newFreeIndexes ≤ k :=
              h j (by simp only [newFreeIndexes_abs]; omega)
            refine newFreeIndexes_ren_le (σ j) Nat.succ (k + 1) ?_
            intro l hl
            omega)
      simp only [sub_abs, newFreeIndexes_abs]
      omega
  | app a b iha ihb =>
      intro σ k h
      have ha := iha σ k (fun i hi => h i (by simp; omega))
      have hb := ihb σ k (fun i hi => h i (by simp; omega))
      simp only [sub_app, newFreeIndexes_app]
      omega

/-- Renamings that agree on the free indexes of `s` act the same on `s`. -/
theorem ren_congr (s : Scoped) : ∀ (ρ ρ' : Nat → Nat),
    (∀ i < s.newFreeIndexes, ρ i = ρ' i) → ren ρ s = ren ρ' s := by
  induction s using Scoped.ind with
  | var i => intro ρ ρ' h; simp [h i (by simp)]
  | abs s ih =>
      intro ρ ρ' h
      refine congrArg abs (ih (upRen ρ) (upRen ρ') ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [upRen, h j (by simp only [newFreeIndexes_abs]; omega)]
  | app a b iha ihb =>
      intro ρ ρ' h
      simp only [ren_app]
      rw [iha ρ ρ' (fun i hi => h i (by simp; omega)),
        ihb ρ ρ' (fun i hi => h i (by simp; omega))]

/-- A closed term is invariant under renaming. -/
theorem ren_eq_self_of_closed {s : Scoped} (h : s.newFreeIndexes = 0) (ρ : Nat → Nat) :
    ren ρ s = s := by
  -- (the hypothesis is vacuous: `h` says there is no free index at all;
  --  eliminated by `Nat.not_lt_zero` rather than by `omega`, which would
  --  discharge the contradiction through `Classical.byContradiction`)
  rw [ren_congr s ρ (fun i => i) (fun i hi => absurd (h ▸ hi) (Nat.not_lt_zero i)), ren_id]

/-- Substitutions that agree on the free indexes of `s` act the same on `s`. -/
theorem sub_congr (s : Scoped) : ∀ (σ σ' : Nat → Scoped),
    (∀ i < s.newFreeIndexes, σ i = σ' i) → sub σ s = sub σ' s := by
  induction s using Scoped.ind with
  | var i => intro σ σ' h; simpa using h i (by simp)
  | abs s ih =>
      intro σ σ' h
      refine congrArg abs (ih (upSub σ) (upSub σ') ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [upSub, h j (by simp only [newFreeIndexes_abs]; omega)]
  | app a b iha ihb =>
      intro σ σ' h
      simp only [sub_app]
      rw [iha σ σ' (fun i hi => h i (by simp; omega)),
        ihb σ σ' (fun i hi => h i (by simp; omega))]

/-- A closed term is invariant under substitution. -/
theorem sub_eq_self_of_closed {s : Scoped} (h : s.newFreeIndexes = 0) (σ : Nat → Scoped) :
    sub σ s = s := by
  rw [sub_congr s σ var (fun i hi => absurd (h ▸ hi) (Nat.not_lt_zero i)), sub_var]

/-- **The scope of a beta contractum**: substituting `N` for the index `0` of
    `M` yields a term with at most `max (M.newFreeIndexes - 1) N.newFreeIndexes`
    free indexes. -/
theorem newFreeIndexes_sub0_le (N M : Scoped) :
    (sub0 N M).newFreeIndexes ≤ max (M.newFreeIndexes - 1) N.newFreeIndexes := by
  refine newFreeIndexes_sub_le M _ _ ?_
  intro i hi
  cases i with
  | zero => exact Nat.le_max_right _ _
  | succ j => simp only [cons, newFreeIndexes_var]; omega

end Scoped

/-- The same bound for the structurally defined beta substitution. -/
theorem Term.newFreeIndexes_betaSubstSigma_le {m n : Nat} (M : Term m) (N : Term n) :
    (M ⟦N⟧).newFreeIndexes ≤ max (m - 1) n := by
  rw [Term.betaSubstSigma_eq_sub0]
  exact Scoped.newFreeIndexes_sub0_le ⟨n, N⟩ ⟨m, M⟩

/-- **Beta reduction never creates free indexes.** -/
theorem Beta.newFreeIndexes_le {M N : Scoped} (h : M —→ N) :
    N.newFreeIndexes ≤ M.newFreeIndexes := by
  induction h with
  | appl L _ ih => simp only [Scoped.newFreeIndexes_app]; omega
  | appr L _ ih => simp only [Scoped.newFreeIndexes_app]; omega
  | abs _ ih => simp only [Scoped.newFreeIndexes_abs]; omega
  | @basis m n M N =>
      have := Term.newFreeIndexes_betaSubstSigma_le M N
      simpa using this

theorem BetaStar.newFreeIndexes_le {M N : Scoped} (h : M —→* N) :
    N.newFreeIndexes ≤ M.newFreeIndexes := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans step.newFreeIndexes_le ih

/-- Closed terms reduce to closed terms. -/
theorem betastar_closed {M N : Scoped} (hM : M.newFreeIndexes = 0) (h : M —→* N) :
    N.newFreeIndexes = 0 :=
  Nat.le_zero.mp (hM ▸ h.newFreeIndexes_le)

end IwilareNatIsExactScope
