module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.DeBruijn
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-!
# Renamings by plain index functions

The `RenameWeaken` structure of `ChoiceFree.DeBruijn` carries a proof `n < m`,
which is inconvenient when one wants to compare *two* renamings.  This file
introduces the same operation for a bare index function, `ren f`, identifies it
with `renameWeaken`, and specialises it to the insertion renamings
`renAt i = ren i.succAbove` (insert a fresh variable at position `i`), of which
`shift = renAt 0` is the basic case.

The main result is the **pullback lemma** `ren_pullback`: if two renamed terms
are equal, and the two index functions have a pullback, then the terms come
from a common term.  Its consequence `renAt_exchange` is what makes the
inversion lemmas for η-reduction work.
-/

namespace IwilareFinsetNOfFreeIsExact

/-- Extend an index function under a binder. -/
def extF {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

@[simp] theorem extF_zero {n m : Nat} (f : Fin n → Fin m) : extF f 0 = 0 := rfl

@[simp] theorem extF_succ {n m : Nat} (f : Fin n → Fin m) (i : Fin n) :
    extF f i.succ = (f i).succ := rfl

/-- Apply a renaming given by a bare index function. -/
def ren {n m : Nat} (f : Fin n → Fin m) : Term n → Term m
  | v#i   => v#(f i)
  | ƛ M   => ƛ (ren (extF f) M)
  | M ⬝ N => (ren f M) ⬝ (ren f N)

@[simp] theorem ren_var {n m : Nat} (f : Fin n → Fin m) (i : Fin n) : ren f (v#i) = v#(f i) := rfl

@[simp] theorem ren_abs {n m : Nat} (f : Fin n → Fin m) (M : Term (n + 1)) :
    ren f (ƛ M) = ƛ (ren (extF f) M) := rfl

@[simp] theorem ren_app {n m : Nat} (f : Fin n → Fin m) (M N : Term n) :
    ren f (M ⬝ N) = (ren f M) ⬝ (ren f N) := rfl

theorem extF_congr {n m : Nat} {f g : Fin n → Fin m} (h : ∀ i, f i = g i) (i : Fin (n + 1)) :
    extF f i = extF g i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; simp [h j]

theorem ren_congr {n m : Nat} {f g : Fin n → Fin m} (h : ∀ i, f i = g i) (M : Term n) :
    ren f M = ren g M := by
  induction M generalizing m with
  | var i => simp [h i]
  | abs M ih => simp [ih (extF_congr h)]
  | app M N ihM ihN => simp [ihM h, ihN h]

@[simp] theorem renameWeaken_var {n m : Nat} (w : RenameWeaken n m) (i : Fin n) :
    renameWeaken w (v#i) = v#(w.map i) := rfl

@[simp] theorem renameWeaken_abs {n m : Nat} (w : RenameWeaken n m) (M : Term (n + 1)) :
    renameWeaken w (ƛ M) = ƛ (renameWeaken w.ext M) := rfl

@[simp] theorem renameWeaken_app {n m : Nat} (w : RenameWeaken n m) (M N : Term n) :
    renameWeaken w (M ⬝ N) = (renameWeaken w M) ⬝ (renameWeaken w N) := rfl

/-- `renameWeaken` is `ren` on the underlying index function. -/
theorem renameWeaken_eq_ren {n m : Nat} (w : RenameWeaken n m) (M : Term n) :
    renameWeaken w M = ren w.map M := by
  induction M generalizing m with
  | var i => rfl
  | abs M ih =>
    simp only [renameWeaken_abs, ren_abs]
    exact congrArg Term.abs (ih w.ext)
  | app M N ihM ihN => simp [renameWeaken, ihM w, ihN w]

/-- Package an index function `Fin n → Fin (n+1)` as a `RenameWeaken`. -/
def rwOf {n : Nat} (f : Fin n → Fin (n + 1)) : RenameWeaken n (n + 1) where
  lt := Nat.lt_succ_self n
  map := f

@[simp] theorem renameWeaken_rwOf {n : Nat} (f : Fin n → Fin (n + 1)) (M : Term n) :
    renameWeaken (rwOf f) M = ren f M := renameWeaken_eq_ren (rwOf f) M

/-- Insertion of a fresh variable at position `i`. -/
abbrev renAt {n : Nat} (i : Fin (n + 1)) : Term n → Term (n + 1) := ren i.succAbove

theorem shift_eq_renAt_zero {n : Nat} (M : Term n) : shift M = renAt 0 M := by
  rw [shift, renameWeaken_eq_ren]
  exact ren_congr (fun i => (Fin.zero_succAbove i).symm) M

theorem shift_eq_ren_succ {n : Nat} (M : Term n) : shift M = ren Fin.succ M := by
  rw [shift, renameWeaken_eq_ren]; rfl

theorem extF_succAbove {n : Nat} (i : Fin (n + 1)) (j : Fin (n + 1)) :
    extF i.succAbove j = i.succ.succAbove j := by
  refine Fin.cases ?_ ?_ j
  · simp
  · intro j'; simp [Fin.succ_succAbove_succ]

theorem renAt_abs {n : Nat} (i : Fin (n + 1)) (M : Term (n + 1)) :
    renAt i (ƛ M) = ƛ (renAt i.succ M) := by
  simp only [ren_abs]
  exact congrArg Term.abs (ren_congr (extF_succAbove i) M)

/-- Renaming commutes with single substitution. -/
theorem ren_betaSubst {n : Nat} (f : Fin n → Fin (n + 1)) (M : Term (n + 1)) (N : Term n) :
    ren f (M[N]) = (ren (extF f) M)[ren f N] := by
  have h := rename_betaSubst (rwOf f) M N
  rw [renameWeaken_eq_ren, renameWeaken_eq_ren, renameWeaken_eq_ren] at h
  exact h

theorem renAt_betaSubst {n : Nat} (i : Fin (n + 1)) (M : Term (n + 1)) (N : Term n) :
    renAt i (M[N]) = (renAt i.succ M)[renAt i N] := by
  have h := ren_betaSubst i.succAbove M N
  rw [ren_congr (extF_succAbove i) M] at h
  exact h

/-! ### The pullback lemma -/

/-- If two renamed terms agree and the index functions have a pullback, then the
two terms come from a common term. -/
theorem ren_pullback {n m p q : Nat} {f : Fin n → Fin p} {g : Fin m → Fin p}
    {u : Fin q → Fin n} {v : Fin q → Fin m}
    (hpb : ∀ x y, f x = g y → ∃ z, x = u z ∧ y = v z)
    {A : Term n} {B : Term m} (h : ren f A = ren g B) :
    ∃ C : Term q, A = ren u C ∧ B = ren v C := by
  induction A generalizing m p q B with
  | var x =>
    cases B with
    | var y =>
      obtain ⟨z, hx, hy⟩ := hpb x y (by injection h)
      exact ⟨v#z, by simp [hx], by simp [hy]⟩
    | abs B => simp at h
    | app B1 B2 => simp at h
  | abs A ih =>
    cases B with
    | var y => simp at h
    | abs B =>
      have h' : ren (extF f) A = ren (extF g) B := by
        simpa using h
      have hpb' : ∀ x y, extF f x = extF g y → ∃ z, x = extF u z ∧ y = extF v z := by
        intro x y
        refine Fin.cases ?_ ?_ x
        · refine Fin.cases ?_ ?_ y
          · intro _; exact ⟨0, rfl, rfl⟩
          · intro y' hxy
            simp only [extF_zero, extF_succ] at hxy
            exact absurd hxy.symm (Fin.succ_ne_zero _)
        · intro x'
          refine Fin.cases ?_ ?_ y
          · intro hxy
            simp only [extF_zero, extF_succ] at hxy
            exact absurd hxy (Fin.succ_ne_zero _)
          · intro y' hxy
            simp only [extF_succ] at hxy
            obtain ⟨z, hx, hy⟩ := hpb x' y' (Fin.succ_inj.mp hxy)
            exact ⟨z.succ, by simp [hx], by simp [hy]⟩
      obtain ⟨C, hA, hB⟩ := ih hpb' h'
      exact ⟨ƛ C, by simp [hA], by simp [hB]⟩
    | app B1 B2 => simp at h
  | app A1 A2 ih1 ih2 =>
    cases B with
    | var y => simp at h
    | abs B => simp at h
    | app B1 B2 =>
      simp only [ren_app, Term.app.injEq] at h
      obtain ⟨C1, hA1, hB1⟩ := ih1 hpb h.1
      obtain ⟨C2, hA2, hB2⟩ := ih2 hpb h.2
      exact ⟨C1 ⬝ C2, by rw [hA1, hA2, ren_app], by rw [hB1, hB2, ren_app]⟩

/-- **Exchange**: a term that is both an insertion at `i.succ` and a shift comes
from a single term, inserted the other way round. -/
theorem renAt_exchange {n : Nat} (i : Fin (n + 1)) {A R : Term (n + 1)}
    (h : renAt i.succ A = shift R) :
    ∃ A' : Term n, A = shift A' ∧ R = renAt i A' := by
  have hpb : ∀ (x y : Fin (n + 1)), i.succ.succAbove x = Fin.succ y →
      ∃ z : Fin n, x = Fin.succ z ∧ y = i.succAbove z := by
    intro x y
    refine Fin.cases ?_ ?_ x
    · intro hxy
      rw [Fin.succ_succAbove_zero] at hxy
      exact absurd hxy.symm (Fin.succ_ne_zero _)
    · intro x' hxy
      rw [Fin.succ_succAbove_succ] at hxy
      exact ⟨x', rfl, (Fin.succ_inj.mp hxy).symm⟩
  rw [shift_eq_ren_succ] at h
  obtain ⟨C, hA, hR⟩ := ren_pullback hpb h
  exact ⟨C, by rw [hA, shift_eq_ren_succ], hR⟩

/-- **Exchange**, for a `RenameWeaken`: a term whose extension is a shift is
itself a shift. -/
theorem renameWeaken_ext_exchange {n m : Nat} (w : RenameWeaken n m) {A : Term (n + 1)}
    {R : Term m} (h : renameWeaken w.ext A = shift R) :
    ∃ A' : Term n, A = shift A' ∧ R = renameWeaken w A' := by
  have hpb : ∀ (x : Fin (n + 1)) (y : Fin m), w.ext.map x = Fin.succ y →
      ∃ z : Fin n, x = Fin.succ z ∧ y = w.map z := by
    intro x y
    refine Fin.cases ?_ ?_ x
    · intro hxy
      exact absurd (show (0 : Fin (m + 1)) = Fin.succ y from hxy).symm (Fin.succ_ne_zero _)
    · intro x' hxy
      exact ⟨x', rfl, (Fin.succ_inj.mp (show (w.map x').succ = Fin.succ y from hxy)).symm⟩
  rw [renameWeaken_eq_ren, shift_eq_ren_succ] at h
  obtain ⟨C, hA, hR⟩ := ren_pullback hpb h
  exact ⟨C, by rw [hA, shift_eq_ren_succ], by rw [hR, renameWeaken_eq_ren]⟩

/-- Only variable `0` is sent to `0` by an extended renaming. -/
theorem RenameWeaken.ext_map_eq_zero {n m : Nat} (w : RenameWeaken n m) {i : Fin (n + 1)}
    (h : w.ext.map i = 0) : i = 0 := by
  revert h
  refine Fin.cases ?_ ?_ i
  · intro _; rfl
  · intro j hj
    exact absurd (show (w.map j).succ = 0 from hj) (Fin.succ_ne_zero _)

end IwilareFinsetNOfFreeIsExact
