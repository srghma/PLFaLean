-- Minimisation (unbounded search) is lambda-definable.
--
-- With the fixed point combinator one can define, for a term `F`,
--
--     cmin F = fix (ƛg. ƛn. if (iszero (F n)) then n else g (succ n))
--
-- which searches for the least zero of `F` from a given starting point:
-- if the closed term `F` represents `f` and `m` is the least `k ≥ n` with
-- `f k = 0`, then `cmin F ⬝ church n —→* church m` (`cmin_represents`).
--
-- Together with `PrimitiveRecursion.lean` this gives the two schemes -- primitive
-- recursion and minimisation -- by which every partial recursive function is
-- built.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.PrimitiveRecursion
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.FixedPoint

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

/-- `ƛg. ƛn. if (iszero (F n)) then n else g (succ n)`. -/
def searchGen (F : Scoped) : Scoped :=
  abs (abs (app (app (app cif
      (app ciszero (app (ren Nat.succ (ren Nat.succ F)) (var 0)))) (var 0))
    (app (var 1) (app csucc (var 0)))))

/-- The search combinator: the fixed point of `searchGen F`. -/
def cmin (F : Scoped) : Scoped := fix (searchGen F)

theorem cif_closed' : cif.newFreeIndexes = 0 := rfl

theorem selfAppOf_closed {F : Scoped} (hF : F.newFreeIndexes = 0) :
    (selfAppOf F).newFreeIndexes = 0 := by
  rw [selfAppOf, ren_eq_self_of_closed hF]
  simp only [newFreeIndexes_abs, newFreeIndexes_app, newFreeIndexes_var, hF]
  omega

theorem fix_closed {F : Scoped} (hF : F.newFreeIndexes = 0) :
    (fix F).newFreeIndexes = 0 := by
  simp only [fix, newFreeIndexes_app, selfAppOf_closed hF]
  rfl

theorem searchGen_closed {F : Scoped} (hF : F.newFreeIndexes = 0) :
    (searchGen F).newFreeIndexes = 0 := by
  rw [searchGen, ren_eq_self_of_closed hF, ren_eq_self_of_closed hF]
  simp only [newFreeIndexes_abs, newFreeIndexes_app, newFreeIndexes_var, hF,
    ciszero_closed, cif_closed', csucc_closed]
  omega

theorem cmin_closed {F : Scoped} (hF : F.newFreeIndexes = 0) :
    (cmin F).newFreeIndexes = 0 := fix_closed (searchGen_closed hF)

end Scoped

/-- One unfolding of the search combinator. -/
theorem searchGen_red {F X : Scoped} (hF : F.newFreeIndexes = 0) (hX : X.newFreeIndexes = 0)
    (n : Nat) :
    Scoped.app (Scoped.app (Scoped.searchGen F) X) (Scoped.church n) —→*
      Scoped.app (Scoped.app (Scoped.app Scoped.cif
          (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.church n)))) (Scoped.church n))
        (Scoped.app X (Scoped.church (n + 1))) := by
  have h₁ : Scoped.app (Scoped.searchGen F) X —→
      Scoped.abs (Scoped.app (Scoped.app (Scoped.app Scoped.cif
          (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.var 0)))) (Scoped.var 0))
        (Scoped.app X (Scoped.app Scoped.csucc (Scoped.var 0)))) := by
    have h := Beta.basis' (Scoped.abs (Scoped.app (Scoped.app (Scoped.app Scoped.cif
        (Scoped.app Scoped.ciszero
          (Scoped.app (Scoped.ren Nat.succ (Scoped.ren Nat.succ F)) (Scoped.var 0))))
        (Scoped.var 0))
      (Scoped.app (Scoped.var 1) (Scoped.app Scoped.csucc (Scoped.var 0))))) X
    simpa [Scoped.searchGen, Scoped.ren_eq_self_of_closed hF, Scoped.ren_eq_self_of_closed hX,
      Scoped.sub_eq_self_of_closed hF, Scoped.sub_eq_self_of_closed hX,
      Scoped.sub_eq_self_of_closed Scoped.cif_closed',
      Scoped.sub_eq_self_of_closed Scoped.ciszero_closed,
      Scoped.sub_eq_self_of_closed Scoped.csucc_closed] using h
  refine Relation.ReflTransGen.head (Beta.appr _ h₁) ?_
  have h₂ : Scoped.app (Scoped.abs (Scoped.app (Scoped.app (Scoped.app Scoped.cif
          (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.var 0)))) (Scoped.var 0))
        (Scoped.app X (Scoped.app Scoped.csucc (Scoped.var 0))))) (Scoped.church n) —→
      Scoped.app (Scoped.app (Scoped.app Scoped.cif
          (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.church n)))) (Scoped.church n))
        (Scoped.app X (Scoped.app Scoped.csucc (Scoped.church n))) := by
    have h := Beta.basis' (Scoped.app (Scoped.app (Scoped.app Scoped.cif
        (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.var 0)))) (Scoped.var 0))
      (Scoped.app X (Scoped.app Scoped.csucc (Scoped.var 0)))) (Scoped.church n)
    simpa [Scoped.sub_eq_self_of_closed hF, Scoped.sub_eq_self_of_closed hX,
      Scoped.sub_eq_self_of_closed Scoped.cif_closed',
      Scoped.sub_eq_self_of_closed Scoped.ciszero_closed,
      Scoped.sub_eq_self_of_closed Scoped.csucc_closed] using h
  refine Relation.ReflTransGen.head h₂ ?_
  exact beta_star_appl _ (beta_star_appl _ (csucc_church n))

/-- One unfolding of `cmin F`. -/
theorem cmin_unfold {F : Scoped} (hF : F.newFreeIndexes = 0) (n : Nat) :
    Scoped.app (Scoped.cmin F) (Scoped.church n) —→*
      Scoped.app (Scoped.app (Scoped.app Scoped.cif
          (Scoped.app Scoped.ciszero (Scoped.app F (Scoped.church n)))) (Scoped.church n))
        (Scoped.app (Scoped.cmin F) (Scoped.church (n + 1))) := by
  refine Relation.ReflTransGen.head
    (Beta.appr (Scoped.church n) (fix_step (Scoped.searchGen F))) ?_
  exact searchGen_red hF (Scoped.cmin_closed hF) n

/-- If `f n = 0` the search stops at `n`. -/
theorem cmin_found {F : Scoped} (hF : F.newFreeIndexes = 0) {f : Nat → Nat}
    (hrep : ∀ a, Scoped.app F (Scoped.church a) —→* Scoped.church (f a)) {n : Nat}
    (h : f n = 0) :
    Scoped.app (Scoped.cmin F) (Scoped.church n) —→* Scoped.church n := by
  refine (cmin_unfold hF n).trans ?_
  have hcond : Scoped.app Scoped.ciszero (Scoped.app F (Scoped.church n)) —→* ctrue := by
    refine (beta_star_appl _ (hrep n)).trans ?_
    rw [h]
    exact ciszero_zero
  refine (beta_star_appr _ (beta_star_appr _ (beta_star_appl _ hcond))).trans ?_
  exact cif_ctrue _ _

/-- If `f n ≠ 0` the search moves on to `n + 1`. -/
theorem cmin_next {F : Scoped} (hF : F.newFreeIndexes = 0) {f : Nat → Nat}
    (hrep : ∀ a, Scoped.app F (Scoped.church a) —→* Scoped.church (f a)) {n : Nat}
    (h : f n ≠ 0) :
    Scoped.app (Scoped.cmin F) (Scoped.church n) —→*
      Scoped.app (Scoped.cmin F) (Scoped.church (n + 1)) := by
  refine (cmin_unfold hF n).trans ?_
  obtain ⟨k, hk⟩ : ∃ k, f n = k + 1 := by
    cases hfn : f n with
    | zero => exact absurd hfn h
    | succ k => exact ⟨k, rfl⟩
  have hcond : Scoped.app Scoped.ciszero (Scoped.app F (Scoped.church n)) —→* cfalse := by
    refine (beta_star_appl _ (hrep n)).trans ?_
    rw [hk]
    exact ciszero_succ k
  refine (beta_star_appr _ (beta_star_appr _ (beta_star_appl _ hcond))).trans ?_
  exact cif_cfalse _ _

/-- **Minimisation is lambda-definable**: if the closed term `F` represents `f`
    and `m` is the least zero of `f` above `n`, then `cmin F` maps the numeral
    `n` to the numeral `m`. -/
theorem cmin_represents {F : Scoped} (hF : F.newFreeIndexes = 0) {f : Nat → Nat}
    (hrep : ∀ a, Scoped.app F (Scoped.church a) —→* Scoped.church (f a)) {n m : Nat}
    (hnm : n ≤ m) (hm : f m = 0) (hlt : ∀ k, n ≤ k → k < m → f k ≠ 0) :
    Scoped.app (Scoped.cmin F) (Scoped.church n) —→* Scoped.church m := by
  induction hd : m - n generalizing n with
  | zero =>
      have : n = m := by omega
      subst this
      exact cmin_found hF hrep hm
  | succ d ih =>
      have hlt' : n < m := by omega
      refine (cmin_next hF hrep (hlt n (Nat.le_refl n) hlt')).trans ?_
      refine ih (by omega) (fun k hk hkm => hlt k (by omega) hkm) (by omega)

/-- The least zero of `f`, found from `0`. -/
theorem cmin_least_zero {F : Scoped} (hF : F.newFreeIndexes = 0) {f : Nat → Nat}
    (hrep : ∀ a, Scoped.app F (Scoped.church a) —→* Scoped.church (f a)) {m : Nat}
    (hm : f m = 0) (hlt : ∀ k, k < m → f k ≠ 0) :
    Scoped.app (Scoped.cmin F) (Scoped.church 0) —→* Scoped.church m :=
  cmin_represents hF hrep (Nat.zero_le m) hm (fun k _ hkm => hlt k hkm)

set_option maxRecDepth 1000000 in
/-- The least `n` with `3 - n = 0` is `3`, found by the search combinator and
    computed by the normal order evaluator. -/
example : Scoped.eval 3000 (Scoped.app (Scoped.cmin (Scoped.app Scoped.csub (Scoped.church 3)))
    (Scoped.church 0)) = some (Scoped.church 3) := rfl

end IwilareNatIsExactScope
