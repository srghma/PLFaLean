module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.NormalForm

@[expose] public section

/-!
# β-reduction does not create free variables

Since `Term s` is indexed by the *exact* set of free variables of the term, this
is the statement that the index can only shrink along a β-step:

* `Basic41Finset.StepS.newFreeIndexes_subset` — one step;
* `Basic41Finset.BetaStarS.newFreeIndexes_subset` — many steps;
* `Basic41Finset.closed_of_betaStarS` — **closed terms reduce to closed terms**.
-/

namespace Basic41FinsetNOfFreeIsExact

@[simp] theorem newFreeIndexes_var (i : Nat) : (SigmaTerm.var i).newFreeIndexes = {i} := rfl

@[simp] theorem newFreeIndexes_abs (t : SigmaTerm) :
    (SigmaTerm.abs t).newFreeIndexes = unbind t.newFreeIndexes := rfl

@[simp] theorem newFreeIndexes_app (t u : SigmaTerm) :
    (SigmaTerm.app t u).newFreeIndexes = t.newFreeIndexes ∪ u.newFreeIndexes := rfl

@[simp] theorem newFreeIndexes_subst (j : Nat) (N t : SigmaTerm) :
    (SigmaTerm.subst j N t).newFreeIndexes = substSet j N.newFreeIndexes t.newFreeIndexes := rfl

theorem unbind_subset {s s' : Finset Nat} (h : s ⊆ s') : unbind s ⊆ unbind s' := by
  intro x hx
  rw [mem_unbind] at hx ⊢
  exact h hx

/-- Substituting the top variable can only produce free variables that were
already free in the abstraction or in the argument. -/
theorem substSet_zero_subset (sN sP : Finset Nat) :
    substSet 0 sN sP ⊆ unbind sP ∪ sN := by
  intro x hx
  rw [mem_substSet] at hx
  obtain ⟨i, hi, hx⟩ := hx
  by_cases h0 : i = 0
  · subst h0
    exact Finset.mem_union_right _ hx
  · rw [if_neg h0, if_pos (by omega)] at hx
    refine Finset.mem_union_left _ ?_
    rw [mem_unbind, hx]
    have : i - 1 + 1 = i := by omega
    rwa [this]

/-- A β-step does not create free variables. -/
theorem StepS.newFreeIndexes_subset {t u : SigmaTerm} (h : t →βs u) :
    u.newFreeIndexes ⊆ t.newFreeIndexes := by
  refine StepS.induction
    (motive := fun a b => b.newFreeIndexes ⊆ a.newFreeIndexes) ?_ ?_ ?_ ?_ h
  · intro t u
    simpa using substSet_zero_subset u.newFreeIndexes t.newFreeIndexes
  · intro t t' u _ ih
    simpa using Finset.union_subset_union_left ih
  · intro t u u' _ ih
    simpa using Finset.union_subset_union_right ih
  · intro t u _ ih
    simpa using unbind_subset ih

/-- Many-step β-reduction does not create free variables. -/
theorem BetaStarS.newFreeIndexes_subset {t u : SigmaTerm} (h : t ⇒βs* u) :
    u.newFreeIndexes ⊆ t.newFreeIndexes := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ hstep ih => exact hstep.newFreeIndexes_subset.trans ih

/-- **Closed terms reduce to closed terms.** -/
theorem closed_of_betaStarS {t u : SigmaTerm} (h : t ⇒βs* u) (ht : t.newFreeIndexes = ∅) :
    u.newFreeIndexes = ∅ :=
  Finset.subset_empty.mp (ht ▸ h.newFreeIndexes_subset)

end Basic41FinsetNOfFreeIsExact
