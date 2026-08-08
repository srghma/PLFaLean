-- Minimisation (unbounded search) is lambda-definable, for the scope-bounded
-- (`Fin`-indexed) calculus.
--
-- With the fixed point combinator one can define, for a term `F`,
--
--     cmin F = fix (ƛg. ƛn. if (iszero (F n)) then n else g (succ n))
--
-- which searches for the least zero of `F` from a given starting point:
-- if the term `F` represents `f` and `m` is the least `k ≥ n` with `f k = 0`,
-- then `cmin F ⬝ church n —→* church m` (`cmin_represents`).
--
-- Together with `PrimitiveRecursion.lean` this gives the two schemes -- primitive
-- recursion and minimisation -- by which every partial recursive function is
-- built.
--
-- As in `PrimitiveRecursion.lean`, no closedness hypothesis on `F` is needed:
-- the weakenings that the binders of `searchGen` introduce are undone by the
-- substitutions that contract the redexes.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.FixedPoint

@[expose] public section

namespace FinScope

open Term

namespace Term

@[simp] theorem ren_ctrue {n m : Nat} (ρ : Fin n → Fin m) : ren ρ ctrue = ctrue := by simp [ctrue]
@[simp] theorem ren_cfalse {n m : Nat} (ρ : Fin n → Fin m) : ren ρ cfalse = cfalse := by
  simp [cfalse]
@[simp] theorem sub_ctrue {n m : Nat} (σ : Fin n → Term m) : sub σ ctrue = ctrue := by simp [ctrue]
@[simp] theorem sub_cfalse {n m : Nat} (σ : Fin n → Term m) : sub σ cfalse = cfalse := by
  simp [cfalse]
@[simp] theorem ren_ciszero {n m : Nat} (ρ : Fin n → Fin m) : ren ρ ciszero = ciszero := by
  simp [ciszero]
@[simp] theorem sub_ciszero {n m : Nat} (σ : Fin n → Term m) : sub σ ciszero = ciszero := by
  simp [ciszero]

/-- `ƛg. ƛn. if (iszero (F n)) then n else g (succ n)`. -/
def searchGen {n : Nat} (F : Term n) : Term n :=
  ƛ ƛ (cif ⬝ (ciszero ⬝ (wk (wk F) ⬝ v# 0)) ⬝ v# 0 ⬝ (v# 1 ⬝ (csucc ⬝ v# 0)))

/-- The search combinator: the fixed point of `searchGen F`. -/
def cmin {n : Nat} (F : Term n) : Term n := fix (searchGen F)

end Term

/-- One unfolding of the search combinator. -/
theorem searchGen_red {n : Nat} (F X : Term n) (k : Nat) :
    searchGen F ⬝ X ⬝ church k —→*
      cif ⬝ (ciszero ⬝ (F ⬝ church k)) ⬝ church k ⬝ (X ⬝ church (k + 1)) := by
  refine Relation.ReflTransGen.head (Beta.appL (Beta.basis _ X)) ?_
  have e : (ƛ (cif ⬝ (ciszero ⬝ (wk (wk F) ⬝ v# 0)) ⬝ v# 0 ⬝ (v# 1 ⬝ (csucc ⬝ v# 0)))
        : Term (n + 1)) [ X ]
      = ƛ (cif ⬝ (ciszero ⬝ (wk F ⬝ v# 0)) ⬝ v# 0 ⬝ (wk X ⬝ (csucc ⬝ v# 0))) := by
    simp [betaSubst_abs, wk, sub_ren]
  rw [e]
  refine Relation.ReflTransGen.head (Beta.basis _ (church k)) ?_
  have e' : (cif ⬝ (ciszero ⬝ (wk F ⬝ v# 0)) ⬝ v# 0 ⬝ (wk X ⬝ (csucc ⬝ v# 0))
        : Term (n + 1)) [ church k ]
      = cif ⬝ (ciszero ⬝ (F ⬝ church k)) ⬝ church k ⬝ (X ⬝ (csucc ⬝ church k)) := by
    simp [betaSubst, sub_ren]
  rw [e']
  exact BetaStar.appR (BetaStar.appR (csucc_church k))

/-- One unfolding of `cmin F`. -/
theorem cmin_unfold {n : Nat} (F : Term n) (k : Nat) :
    cmin F ⬝ church k —→*
      cif ⬝ (ciszero ⬝ (F ⬝ church k)) ⬝ church k ⬝ (cmin F ⬝ church (k + 1)) := by
  refine Relation.ReflTransGen.head (Beta.appL (fix_step (searchGen F))) ?_
  exact searchGen_red F (cmin F) k

/-- If `f k = 0` the search stops at `k`. -/
theorem cmin_found {n : Nat} {F : Term n} {f : Nat → Nat}
    (hrep : ∀ a, F ⬝ church a —→* church (f a)) {k : Nat} (h : f k = 0) :
    cmin F ⬝ church k —→* church k := by
  refine (cmin_unfold F k).trans ?_
  have hcond : ciszero ⬝ (F ⬝ church k) —→* ctrue := by
    refine (BetaStar.appR (hrep k)).trans ?_
    rw [h]
    exact ciszero_zero
  refine (BetaStar.appL (BetaStar.appL (BetaStar.appR hcond))).trans ?_
  exact cif_ctrue _ _

/-- If `f k ≠ 0` the search moves on to `k + 1`. -/
theorem cmin_next {n : Nat} {F : Term n} {f : Nat → Nat}
    (hrep : ∀ a, F ⬝ church a —→* church (f a)) {k : Nat} (h : f k ≠ 0) :
    cmin F ⬝ church k —→* cmin F ⬝ church (k + 1) := by
  refine (cmin_unfold F k).trans ?_
  obtain ⟨j, hj⟩ : ∃ j, f k = j + 1 := by
    cases hfk : f k with
    | zero => exact absurd hfk h
    | succ j => exact ⟨j, rfl⟩
  have hcond : ciszero ⬝ (F ⬝ church k) —→* cfalse := by
    refine (BetaStar.appR (hrep k)).trans ?_
    rw [hj]
    exact ciszero_succ j
  refine (BetaStar.appL (BetaStar.appL (BetaStar.appR hcond))).trans ?_
  exact cif_cfalse _ _

/-- **Minimisation is lambda-definable**: if the term `F` represents `f` and `m`
    is the least zero of `f` above `k`, then `cmin F` maps the numeral `k` to the
    numeral `m`. -/
theorem cmin_represents {n : Nat} {F : Term n} {f : Nat → Nat}
    (hrep : ∀ a, F ⬝ church a —→* church (f a)) {k m : Nat}
    (hkm : k ≤ m) (hm : f m = 0) (hlt : ∀ j, k ≤ j → j < m → f j ≠ 0) :
    cmin F ⬝ church k —→* church m := by
  induction hd : m - k generalizing k with
  | zero =>
      have : k = m := by omega
      subst this
      exact cmin_found hrep hm
  | succ d ih =>
      have hlt' : k < m := by omega
      refine (cmin_next hrep (hlt k (Nat.le_refl k) hlt')).trans ?_
      exact ih (by omega) (fun j hj hjm => hlt j (by omega) hjm) (by omega)

/-- The least zero of `f`, found from `0`. -/
theorem cmin_least_zero {n : Nat} {F : Term n} {f : Nat → Nat}
    (hrep : ∀ a, F ⬝ church a —→* church (f a)) {m : Nat}
    (hm : f m = 0) (hlt : ∀ j, j < m → f j ≠ 0) :
    cmin F ⬝ church 0 —→* church m :=
  cmin_represents hrep (Nat.zero_le m) hm (fun j _ hjm => hlt j hjm)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The least `k` with `3 - k = 0` is `3`, found by the search combinator and
    computed by the normal order evaluator. -/
example : Term.eval 3000 (cmin (csub ⬝ church 3) ⬝ church 0 : Term 0)
    = some (church 3) := by decide

end FinScope
