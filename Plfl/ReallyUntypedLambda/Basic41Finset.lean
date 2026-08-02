module
import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

-- import Mathlib.Data.Finset.Lattice  -- for biUnion, if you need it elsewhere

attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

-- Helper function: Removes bound variable 0 and shifts remaining free variable indices down by 1.
-- `unbind` transforms the set of free variables $s \subseteq \{0, 1, \dots, n\}$ into $s' \subseteq \{0, 1, \dots, n-1\}$:
-- def unbind {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
--   -- image is like map but for any map, but Finset.map is only for injective funcs
--   Finset.map
--     (fun (⟨v, hi⟩ : ↥(s.erase ⟨0, Nat.succ_pos n⟩)) =>
--     -- SAME AS
--     -- (fun (⟨v, hi⟩ : { x : Fin (n + 1) // x ∈ s.erase ⟨0, Nat.succ_pos n⟩ }) =>
--     -- but will use
--     -- #synth CoeSort (Finset Nat) (Type _)
--     -- #print Finset.instSetLike
--       have hne : v ≠ ⟨0, Nat.succ_pos n⟩ := (Finset.mem_erase.mp hi).1
--       ⟨v.val - 1, by omega⟩)
--     (s.erase ⟨0, Nat.succ_pos n⟩).attach

-- set_option pp.all true in #print unbind

/-- Map a non-zero element of `Fin (n + 1)` to `Fin n` by subtracting 1. -/
def predEmbedding (n : Nat) : {x : Fin (n + 1) // x ≠ 0} ↪ Fin n where
  toFun := fun ⟨fin, notZero⟩ => ⟨fin - 1, by omega⟩
  inj' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    ext
    have hx0 : x.val ≠ 0 := fun h0 => hx (Fin.ext h0)
    have hy0 : y.val ≠ 0 := fun h0 => hy (Fin.ext h0)
    have hxlt := x.isLt
    have hylt := y.isLt
    simp only [Fin.mk.injEq] at h
    grind

/-- `unbind s` shifts all non-zero elements of `s` down by 1. -/
def unbind {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  (s.subtype (· ≠ 0)).map (predEmbedding n)

-- `Term n s d`:
--   n : Scope size
--   s : Finset (Fin n) — EXACT set of free variables used in this term
--   d : Abstraction depth
inductive Term : (n : Nat) → Finset (Fin n) → Nat → Type
  | var : ∀ {n : Nat} (i : Fin n), Term n {i} 0
  | abs : ∀ {n : Nat} {s : Finset (Fin (n + 1))} {d : Nat},
      Term (n + 1) s d → Term n (unbind s) (d + 1)
  | app : ∀ {n : Nat} {s1 s2 : Finset (Fin n)} {d1 d2 : Nat},
      Term n s1 d1 → Term n s2 d2 → Term n (s1 ∪ s2) (max d1 d2)

deriving instance Repr for Term
-- deriving instance Hashable for Term

/-- Structural equality for terms across any scope, set, and depth. -/
def Term.beq : ∀ {n1 : Nat} {s1 : Finset (Fin n1)} {d1 : Nat}
                {n2 : Nat} {s2 : Finset (Fin n2)} {d2 : Nat},
    Term n1 s1 d1 → Term n2 s2 d2 → Bool
  | _, _, _, _, _, _, Term.var i, t2 =>
      match t2 with
      | Term.var j => i.val == j.val
      | _ => false
  | _, _, _, _, _, _, Term.abs P, t2 =>
      match t2 with
      | Term.abs Q => Term.beq P Q
      | _ => false
  | _, _, _, _, _, _, Term.app P1 P2, t2 =>
      match t2 with
      | Term.app Q1 Q2 => Term.beq P1 Q1 && Term.beq P2 Q2
      | _ => false

instance {n : Nat} {s : Finset (Fin n)} {d : Nat} : BEq (Term n s d) where
  beq := Term.beq

/-- `Term.beq` is reflexive for any term `t`. -/
theorem termBEq_refl {n : Nat} {s : Finset (Fin n)} {d : Nat} (t : Term n s d) :
    Term.beq t t = true := by
  induction t with
  | var i =>
    change (i.val == i.val) = true
    simp_all only [BEq.rfl]
  | abs P ih =>
    change Term.beq P P = true
    exact ih
  | app P Q ihP ihQ =>
    change (Term.beq P P && Term.beq Q Q) = true
    rw [ihP, ihQ]
    rfl

/-- `Term n s d` satisfies `ReflBEq`. -/
instance {n : Nat} {s : Finset (Fin n)} {d : Nat} : ReflBEq (Term n s d) where
  rfl {t} := termBEq_refl t

/-- `Term.beq` implies heterogeneous equality for terms in the same scope size `n`. -/
theorem termBEq_heq : ∀ {n : Nat} {s1 : Finset (Fin n)} {d1 : Nat} (t1 : Term n s1 d1)
    {s2 : Finset (Fin n)} {d2 : Nat} (t2 : Term n s2 d2),
    Term.beq t1 t2 = true → s1 = s2 ∧ d1 = d2 ∧ HEq t1 t2 := by
  intro n s1 d1 t1
  induction t1 with
  | var i =>
    intro s2 d2 t2 h
    cases t2 with
    | var j =>
      change (i.val == j.val) = true at h
      have hij : i = j := Fin.ext (eq_of_beq h)
      subst hij
      exact ⟨rfl, rfl, HEq.rfl⟩
    | abs Q => simp [Term.beq] at h
    | app Q1 Q2 => simp [Term.beq] at h
  | abs P ih =>
    intro s2 d2 t2 h
    cases t2 with
    | var j => simp [Term.beq] at h
    | abs Q =>
      change Term.beq P Q = true at h
      obtain ⟨hs, hd, hheq⟩ := ih Q h
      subst hs; subst hd
      have hPQ : P = Q := eq_of_heq hheq
      subst hPQ
      exact ⟨rfl, rfl, HEq.rfl⟩
    | app Q1 Q2 => simp [Term.beq] at h
  | app P1 P2 ih1 ih2 =>
    intro s2 d2 t2 h
    cases t2 with
    | var j => simp [Term.beq] at h
    | abs Q => simp [Term.beq] at h
    | app Q1 Q2 =>
      change (Term.beq P1 Q1 && Term.beq P2 Q2) = true at h
      have h1 := Bool.and_elim_left h
      have h2 := Bool.and_elim_right h
      obtain ⟨hs1, hd1, hheq1⟩ := ih1 Q1 h1
      obtain ⟨hs2, hd2, hheq2⟩ := ih2 Q2 h2
      subst hs1; subst hd1
      subst hs2; subst hd2
      have e1 : P1 = Q1 := eq_of_heq hheq1
      have e2 : P2 = Q2 := eq_of_heq hheq2
      subst e1; subst e2
      exact ⟨rfl, rfl, HEq.rfl⟩

/-- `Term n s d` satisfies `LawfulBEq`. -/
instance {n : Nat} {s : Finset (Fin n)} {d : Nat} : LawfulBEq (Term n s d) where
  eq_of_beq {t1 t2} h := eq_of_heq (termBEq_heq t1 t2 h).2.2

instance {n : Nat} {s : Finset (Fin n)} {d : Nat} : DecidableEq (Term n s d) :=
  fun t1 t2 =>
    match h : Term.beq t1 t2 with
    | true  => isTrue (eq_of_heq (termBEq_heq t1 t2 h).2.2)
    | false => isFalse (by
        intro heq
        subst heq
        rw [termBEq_refl t1] at h
        exact absurd h (by decide))

abbrev computeAndNormalizeUnbindAndUnion (t : Term n s d) (hs : s = s' := by decide) (hd : d = d' := by decide) : Term n s' d' :=
  match hs, hd with | rfl, rfl => t
  -- hs ▸ hd ▸ t -- will use Eq.rec
  -- by subst hs; subst hd; exact t -- will use Eq.ndrec

-- set_option pp.all true in #print computeAndNormalizeUnbindAndUnion

macro:max "⟦" t:term "⟧" : term => `(computeAndNormalizeUnbindAndUnion $t)

-- inductive Term : (n : Nat) → Finset (Fin n) → Nat → Type
--   | var : ∀ {n : Nat} (i : Fin n), Term n {i} 0
--   | abs : ∀ {n : Nat} {s : Finset (Fin (n + 1))} {d : Nat}
--       (_t : Term (n + 1) s d)
--       {s' : Finset (Fin n)} (_h : s' = unbind s := by decide),
--       Term n s' (d + 1)
--   | app : ∀ {n : Nat} {s1 s2 : Finset (Fin n)} {d1 d2 : Nat}
--       (_t1 : Term n s1 d1) (_t2 : Term n s2 d2)
--       {s' : Finset (Fin n)} (_h : s' = s1 ∪ s2 := by decide),
--       Term n s' (max d1 d2)

theorem max_var_bound {n : Nat} {s : Finset (Fin n)} {d : Nat} (_ : Term n s d) : n ≤ n + d := by
  exact Nat.le_add_right n d

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term => `(Term.var (n := $n) (Fin.mk $i (by decide)))

macro:max "𝔽[" n:term "]{" xs:term,* "}" : term => do
  let elems ← xs.getElems.mapM (fun x => `((⟨$x, by decide⟩ : Fin $n)))
  `(([$[$elems],*] : List (Fin $n)).toFinset)

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0 ∅ 1 (0 free variables remaining)
def id : Term 0 ∅ 1 := ƛ (# 0)

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0 ∅ 2
def const : Term 0 ∅ 2 := ⟦ƛ (ƛ (##[2] 1))⟧

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 ∅ 2 := ƛ (ƛ (# 0))
def one  : Term 0 ∅ 2 := ⟦ƛ (ƛ (##[2] 1 ⬝ # 0))⟧
def two  : Term 0 ∅ 2 := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0)))⟧

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0 ∅ 3
def succ : Term 0 ∅ 3 :=
  ⟦ƛ (ƛ (ƛ (
    ##[3] 1 ⬝ ((##[3] 2 ⬝ ##[3] 1) ⬝ # 0)
  )))⟧

-- A term with 2 free variables, depth 0:
-- Set of free variables is {0, 1}
def freeTerm : Term 2 (𝔽[2]{0, 1}) 0 := ⟦##[2] 0 ⬝ ##[2] 1⟧

-- A term with 1 free variable, depth 1 (λy. y ⬝ x0):
-- Inside ƛ, free vars are {0, 1}. After ƛ, var 0 is bound, leaving {0} as free variable.
def boundAndFree : Term 1 {0} 1 := ⟦ƛ (# 0 ⬝ ##[2] 1)⟧

end Term

-------------------------------------------------------------------------------
-- 1. Free Variable Transformations for Shift & Substitution
-------------------------------------------------------------------------------

/-- Calculates shifted free variable set when scope increases by 1 at cutoff `c`. -/
def shiftSet {n : Nat} (c : Nat) (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  Finset.image (fun i => if i.val ≥ c then ⟨i.val + 1, by omega⟩ else ⟨i.val, by omega⟩) s

/-- Calculates new free variable set after substituting variable `j` with `sN`. -/
def substSet {n : Nat} (j : Nat) (sN : Finset (Fin n)) (sP : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.biUnion sP (fun i =>
    if h1 : i.val = j then
      sN
    else if h2 : i.val > j then
      {⟨i.val - 1, by have hlt := i.isLt; omega⟩}
    else if h3 : i.val < n then
      {⟨i.val, h3⟩}
    else
      ∅)

-------------------------------------------------------------------------------
-- 2. Term Shifting (Weakening) & Substitution
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Helper Theorems for `shiftSet`
-------------------------------------------------------------------------------

theorem shiftSet_singleton_ge {n : Nat} (c : Nat) (i : Fin n) (h : i.val ≥ c) :
    shiftSet c {i} = {⟨i.val + 1, by omega⟩} := by
  ext ⟨x, hx⟩
  simp [shiftSet]
  simp_all only [ge_iff_le, ↓reduceIte, Fin.mk.injEq]

theorem shiftSet_singleton_lt {n : Nat} (c : Nat) (i : Fin n) (h : ¬ i.val ≥ c) :
    shiftSet c {i} = {⟨i.val, by omega⟩} := by
  ext ⟨x, hx⟩
  simp [shiftSet]
  constructor
  simp only [↓reduceIte, Fin.mk.injEq, imp_self, h]
  simp only [↓reduceIte, Fin.mk.injEq, imp_self, h]

theorem shiftSet_union {n : Nat} (c : Nat) (s1 s2 : Finset (Fin n)) :
    shiftSet c (s1 ∪ s2) = shiftSet c s1 ∪ shiftSet c s2 := by
  simp [shiftSet, Finset.image_union]

theorem mem_unbind {n : Nat} {s : Finset (Fin (n + 1))} {x : Fin n} :
    x ∈ unbind s ↔ (⟨x.val + 1, by omega⟩ : Fin (n + 1)) ∈ s := by
  simp only [unbind, Finset.mem_map, Finset.mem_subtype]
  constructor
  · rintro ⟨⟨a, ha⟩, ha_s, h_eq⟩
    have ha_val : a.val ≠ 0 := fun h0 => ha (Fin.ext h0)
    have hval := congr_arg Fin.val h_eq
    change a.val - 1 = x.val at hval
    have ha_eq : a = ⟨x.val + 1, by omega⟩ := Fin.ext (by grind only [!Function.Embedding.injective])
    rw [← ha_eq]
    exact ha_s
  · intro h
    refine ⟨⟨⟨x.val + 1, by omega⟩, fun h0 => by have := congr_arg Fin.val h0; simp_all only [Fin.mk_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false]⟩, h, ?_⟩
    ext
    simp [predEmbedding]
    rfl

theorem mem_shiftSet {n : Nat} {c : Nat} {s : Finset (Fin n)} {y : Fin (n + 1)} :
    y ∈ shiftSet c s ↔ ∃ i ∈ s, (if i.val ≥ c then i.val + 1 else i.val) = y.val := by
  simp only [shiftSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by split <;> rfl⟩
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    by_cases h : i.val ≥ c <;> simp only [h, if_true, if_false] at heq ⊢ <;> exact Fin.ext heq

theorem unbind_shiftSet {n : Nat} (c : Nat) (s : Finset (Fin (n + 1))) :
    unbind (shiftSet (c + 1) s) = shiftSet c (unbind s) := by
  ext x
  rw [mem_unbind, mem_shiftSet, mem_shiftSet]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hy1 : y.val ≥ 1 := by by_contra h; push Not at h; grind only
    refine ⟨⟨y.val - 1, by omega⟩, ?_, ?_⟩
    · rw [mem_unbind]
      have heq' : (⟨(⟨y.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ : Fin (n + 1)) = y := by
        ext; simp; omega
      rwa [heq']
    · split <;> grind only [= Lean.Grind.toInt_fin]
  · rintro ⟨z, hz, heq⟩
    rw [mem_unbind] at hz
    exact ⟨⟨z.val + 1, by omega⟩, hz, by split at heq <;> split <;> grind only⟩

-------------------------------------------------------------------------------
-- Fully Proved `shift` Implementation (No Sorries)
-------------------------------------------------------------------------------

/-- Shifts free variables $\ge c$ by +1 when going under binders. -/
def shift (c : Nat) : ∀ {n : Nat} {s : Finset (Fin n)} {d : Nat},
    Term n s d → Term (n + 1) (shiftSet c s) d
  | _, _, _, Term.var i =>
    have h_lt := i.isLt
    if h : i.val ≥ c then
      have h_eq := shiftSet_singleton_ge c i h
      h_eq ▸ Term.var ⟨i.val + 1, by omega⟩
    else
      have h_eq := shiftSet_singleton_lt c i h
      h_eq ▸ Term.var ⟨i.val, by omega⟩
  | _, _, _, Term.app P Q =>
    have h_eq := shiftSet_union c _ _
    h_eq ▸ Term.app (shift c P) (shift c Q)
  | _, _, _, Term.abs P =>
    have h_eq := unbind_shiftSet c _
    h_eq ▸ Term.abs (shift (c + 1) P)

theorem substSet_singleton_eq {n : Nat} (j : Nat) (sN : Finset (Fin n)) (i : Fin (n + 1))
    (h : i.val = j) : substSet j sN {i} = sN := by
  ext x; simp [substSet, h]

theorem substSet_singleton_gt {n : Nat} (j : Nat) (sN : Finset (Fin n)) (i : Fin (n + 1))
    (h : i.val > j) : substSet j sN {i} = {⟨i.val - 1, by omega⟩} := by
  ext x; simp [substSet]; grind

theorem substSet_singleton_lt {n : Nat} (j : Nat) (sN : Finset (Fin n)) (i : Fin (n + 1))
    (h : i.val < j) (hlt : i.val < n) : substSet j sN {i} = {⟨i.val, hlt⟩} := by
  ext x; simp [substSet]; grind

theorem substSet_union {n : Nat} (j : Nat) (sN : Finset (Fin n)) (s1 s2 : Finset (Fin (n+1))) :
    substSet j sN (s1 ∪ s2) = substSet j sN s1 ∪ substSet j sN s2 := by
  simp [substSet]
  grind only [= Finset.mem_biUnion, = Finset.mem_union]

theorem mem_substSet {n : Nat} {j : Nat} {sN : Finset (Fin n)} {sP : Finset (Fin (n + 1))} {x : Fin n} :
    x ∈ substSet j sN sP ↔
      ∃ i ∈ sP,
        if i.val = j then x ∈ sN
        else if i.val > j then x.val = i.val - 1
        else x.val = i.val := by
  simp only [substSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    split at hx
    · rename_i h
      subst h
      simp_all only [↓reduceIte]
    · split at hx
      · simp only [Finset.mem_singleton, Fin.ext_iff] at hx
        simp_all only [gt_iff_lt, ↓reduceIte]
      · split at hx
        · simp only [Finset.mem_singleton, Fin.ext_iff] at hx
          simp_all only [gt_iff_lt, not_lt, ↓reduceIte, if_true_right, isEmpty_Prop, IsEmpty.forall_iff]
        · contradiction
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    split
    · rename_i h
      subst h
      simp_all only [↓reduceIte]
    · split
      · simp only [Finset.mem_singleton, Fin.ext_iff]
        simp_all only [↓reduceIte, gt_iff_lt]
      · split
        · simp only [Finset.mem_singleton, Fin.ext_iff]
          simp_all only [↓reduceIte, gt_iff_lt, not_lt]
        · have hlt := i.isLt
          have : i.val < n := by grind only
          contradiction

theorem unbind_substSet {n : Nat} (j : Nat) (sN : Finset (Fin n)) (s' : Finset (Fin (n + 2))) :
    unbind (substSet (j + 1) (shiftSet 0 sN) s') = substSet j sN (unbind s') := by
  ext x
  rw [mem_unbind, mem_substSet, mem_substSet]
  constructor
  · rintro ⟨i, hi, heq⟩
    have hi0 : i.val ≠ 0 := by
      split at heq
      · omega
      · split at heq
        · omega
        · simp_all only [gt_iff_lt, not_lt, ne_eq, Fin.val_eq_zero_iff]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [Fin.val_zero, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
            Nat.le_add_left]
    refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, ?_, ?_⟩
    · rw [mem_unbind]
      have : (⟨(⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (n + 1)).val + 1, by omega⟩ : Fin (n + 2)) = i := Fin.ext (by grind only)
      rwa [this]
    · split at heq <;> split
      · rw [mem_shiftSet] at heq
        rcases heq with ⟨k, hk, hkeq⟩
        dsimp at hkeq
        have : k.val = x.val := by omega
        have : k = x := Fin.ext this
        rwa [← this]
      · simp_all only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, Nat.add_one_sub_one, not_true_eq_false]
      · grind only [= Lean.Grind.toInt_fin]
      · grind only [= Lean.Grind.toInt_fin]
  · rintro ⟨i', hi', heq⟩
    rw [mem_unbind] at hi'
    refine ⟨⟨i'.val + 1, by have := i'.isLt; omega⟩, hi', ?_⟩
    split at heq <;> split
    · rw [mem_shiftSet]
      refine ⟨x, heq, ?_⟩
      dsimp
    · rename_i h h_1
      subst h
      simp_all only [not_true_eq_false]
    · simp_all only [gt_iff_lt, Nat.add_right_cancel_iff]
    · grind only


def subst : ∀ {n : Nat} (j : Nat) {sN : Finset (Fin n)} {dN : Nat} (_N : Term n sN dN) (_hj : j ≤ n)
    {sP : Finset (Fin (n + 1))} {dP : Nat}, Term (n + 1) sP dP →
    Σ' d : Nat, Term n (substSet j sN sP) d
  | n, j, sN, dN, N, hj, _, _, Term.var i =>
    have hlt := i.isLt
    if h1 : i.val = j then
      ⟨dN, by rw [substSet_singleton_eq j sN i h1]; exact N⟩
    else if h2 : i.val > j then
      ⟨0, by rw [substSet_singleton_gt j sN i h2]; exact Term.var ⟨i.val - 1, by omega⟩⟩
    else
      have h3 : i.val < n := by omega
      ⟨0, by rw [substSet_singleton_lt j sN i (by omega) h3]; exact Term.var ⟨i.val, h3⟩⟩
  | n, j, sN, dN, N, hj, _, _, Term.app P Q =>
    let ⟨dP', P'⟩ := subst j N hj P
    let ⟨dQ', Q'⟩ := subst j N hj Q
    ⟨max dP' dQ', by rw [substSet_union j sN _ _]; exact Term.app P' Q'⟩
  | n, j, sN, dN, N, hj, _, _, Term.abs P =>
    let ⟨d', P'⟩ := subst (j + 1) (shift 0 N) (by omega) P
    ⟨d' + 1, by rw [← unbind_substSet j sN _]; exact Term.abs P'⟩
termination_by n j sN dN _N _hj sP dP p => sizeOf p
decreasing_by all_goals simp_wf; omega

-- 1. Simple substitution: x_0[0 := N] ⟹ N
#guard
  let N : Term 100 {⟨42, by decide⟩} 0 := ##[100] 42
  let P : Term 101 {⟨0, by decide⟩} 0 := ##[101] 0
  Term.beq (subst 0 N (by omega) P).2 N

-- 2. Inner variable remains unchanged: x_0[1 := N] ⟹ x_0
#guard
  let N : Term 100 {⟨42, by decide⟩} 0 := ##[100] 42
  let P : Term 101 {⟨0, by decide⟩} 0 := ##[101] 0
  Term.beq (subst 1 N (by omega) P).2 (##[100] 0)

-- 3. Free variable decrement: x_2[0 := N] ⟹ x_1
#guard
  let N : Term 100 {⟨42, by decide⟩} 0 := ##[100] 42
  let P : Term 101 {⟨2, by decide⟩} 0 := ##[101] 2
  Term.beq (subst 0 N (by omega) P).2 (##[100] 1)

-- 4. Substitution under λ-abstraction: (λ. x_1)[0 := N] ⟹ λ. N_shifted
#guard
  let N : Term 100 {⟨42, by decide⟩} 0 := ##[100] 42
  let P : Term 101 {⟨0, by decide⟩} 1 := ⟦ ƛ (##[102] 1) ⟧
  let expected : Term 100 {⟨42, by decide⟩} 1 := ⟦ ƛ (##[101] 43) ⟧
  Term.beq (subst 0 N (by omega) P).2 expected

-- 5. Shadowing inside λ: (λ. x_0)[0 := N] ⟹ λ. x_0
#guard
  let N : Term 100 {⟨42, by decide⟩} 0 := ##[100] 42
  let P : Term 101 ∅ 1 := ⟦ ƛ (##[102] 0) ⟧
  let expected : Term 100 ∅ 1 := ⟦ ƛ (##[101] 0) ⟧
  Term.beq (subst 0 N (by omega) P).2 expected

-- 6. Real β-step substitution: (x_0 x_1)[0 := var 99] ⟹ var 99 var 0
#guard
  let N : Term 100 {⟨99, by decide⟩} 0 := ##[100] 99
  let body : Term 101 (𝔽[101]{0, 1}) 0 := ⟦ ##[101] 0 ⬝ ##[101] 1 ⟧
  let expected : Term 100 (𝔽[100]{0, 99}) 0 := ⟦ ##[100] 99 ⬝ ##[100] 0 ⟧
  Term.beq (subst 0 N (by omega) body).2 expected

-------------------------------------------------------------------------------
-- 3. Beta Reduction Step Relation
-------------------------------------------------------------------------------

namespace Term

/-- Beta substitution $M[N]$ substitutes variable $0$ in $M$ with $N$. -/
def betaSubst {n : Nat} {sP : Finset (Fin (n + 1))} {dP : Nat} (M : Term (n + 1) sP dP)
    {sN : Finset (Fin n)} {dN : Nat} (N : Term n sN dN) :
    Term n (substSet 0 sN sP) (subst 0 N (by omega) M).1 :=
  (subst 0 N (by omega) M).2

end Term

-- Notation for substitution
notation:70 M " [" N "]" => Term.betaSubst M N

set_option quotPrecheck false in
set_option hygiene false in
infixl:65 " →β " => BetaStep

/-- Single-step $\beta$-reduction relation `P ⟶β Q`. -/
inductive BetaStep : ∀ {n : Nat} {s1 d1 s2 d2}, Term n s1 d1 → Term n s2 d2 → Prop where
  | head {n : Nat} {sP : Finset (Fin (n + 1))} {dP : Nat} {sN : Finset (Fin n)} {dN : Nat}
      (P : Term (n + 1) sP dP) (N : Term n sN dN) :
      ((ƛ P) ⬝ N) →β P [N]

  | app_left {n : Nat} {s1 s1' s2 : Finset (Fin n)} {d1 d1' d2 : Nat}
      {P : Term n s1 d1} {P' : Term n s1' d1'} (Q : Term n s2 d2) :
      (P →β P') → (P ⬝ Q) →β (P' ⬝ Q)

  | app_right {n : Nat} {s1 s2 s2' : Finset (Fin n)} {d1 d2 d2' : Nat}
      (P : Term n s1 d1) {Q : Term n s2 d2} {Q' : Term n s2' d2'} :
      Q →β Q' → (P ⬝ Q) →β (P ⬝ Q')

  | abs_body {n : Nat} {s s' : Finset (Fin (n + 1))} {d d' : Nat}
      {P : Term (n + 1) s d} {P' : Term (n + 1) s' d'} :
      P →β P' → (ƛ P) →β (ƛ P')

-- Many-step Beta reduction
notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen BetaStep N₁ N₂

syntax (name := betaStepTac) "beta_step" : tactic

macro_rules
  | `(tactic| beta_step) =>
    `(tactic| first
      | exact BetaStep.head _ _
      | apply BetaStep.abs; beta_step
      | apply BetaStep.app_left; beta_step
      | apply BetaStep.app_right; beta_step)

example : Term.id ⬝ Term.zero →β (subst 0 Term.zero (by omega) (# (0 : Fin 1))).2 :=
  BetaStep.head (Term.var 0) Term.zero

-- the substitution result actually *is* `zero`, up to `Term.beq`:
example : Term.beq (subst 0 Term.zero (by omega) (Term.var (0 : Fin 1))).2 Term.zero = true := by
  delta subst
  dsimp
  have h : substSet 0 (∅ : Finset (Fin 0)) ({0} : Finset (Fin 1)) = (∅ : Finset (Fin 0)) := rfl
  cases h
  rfl

theorem subst_beq_eq {n} (j) {sN dN} (N : Term n sN dN) (hj) {sP dP} (P : Term (n+1) sP dP) {s d} (expected : Term n s d) :
    Term.beq (subst j N hj P).2 expected = true →
    HEq (subst j N hj P).2 expected := by
  intro h
  exact (termBEq_heq _ _ h).2.2

theorem my_cast_heq {n : Nat} {s s' : Finset (Fin n)} {d d' : Nat} (t : Term n s d)
    (hs : s = s') (hd : d = d') :
    HEq (computeAndNormalizeUnbindAndUnion t hs hd) t := by
  subst hs; subst hd; rfl

example : computeAndNormalizeUnbindAndUnion
    (subst 0 Term.zero (by omega) (Term.var (0 : Fin 1))).2
    (hd := by grind [= substSet, = subst])
    = Term.zero := by
  apply eq_of_heq
  refine HEq.trans (my_cast_heq _ _ _) ?_
  have h_beq : Term.beq (subst 0 Term.zero (by omega) (Term.var (0 : Fin 1))).2 Term.zero = true := by
    rw [subst]
    simp only [Fin.val_zero]
    apply termBEq_refl

  exact (termBEq_heq _ _ h_beq).2.2
