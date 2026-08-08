module
public import Aesop
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Logic.Relation
public meta import Mathlib.Data.Finset.Insert
public meta import Mathlib.Data.Finset.Empty
public meta import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

namespace Basic41FinsetNOfFreeIsExact

attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

/-- `unbind s` shifts all non-zero elements of `s` down by 1 and removes 0. -/
def unbind (s : Finset Nat) : Finset Nat :=
  (s.erase 0).image (fun x => x - 1)

-- `Term s`:
--   s : Finset Nat — EXACT set of free variables used in this term
inductive Term : Finset Nat → Type
  | var : (i : Nat) → Term {i}
  | abs : {s : Finset Nat} → Term s → Term (unbind s)
  | app : {s1 s2 : Finset Nat} → Term s1 → Term s2 → Term (s1 ∪ s2)

deriving instance Repr for Term

/-- Structural equality for terms indexed by `Finset Nat`. -/
def Term.beq : ∀ {s1 s2 : Finset Nat}, Term s1 → Term s2 → Bool
  | _, _, Term.var i, t2 =>
      match t2 with
      | Term.var j => i == j
      | _ => false
  | _, _, Term.abs P, t2 =>
      match t2 with
      | Term.abs Q => Term.beq P Q
      | _ => false
  | _, _, Term.app P1 P2, t2 =>
      match t2 with
      | Term.app Q1 Q2 => Term.beq P1 Q1 && Term.beq P2 Q2
      | _ => false

instance {s : Finset Nat} : BEq (Term s) where
  beq := Term.beq

/-- `Term.beq` is reflexive for any term `t`. -/
theorem termBEq_refl {s : Finset Nat} (t : Term s) :
    Term.beq t t = true := by
  induction t with
  | var i =>
    simp [Term.beq]
  | abs P ih =>
    simp [Term.beq, ih]
  | app P Q ihP ihQ =>
    simp [Term.beq, ihP, ihQ]

/-- `Term s` satisfies `ReflBEq`. -/
instance {s : Finset Nat} : ReflBEq (Term s) where
  rfl {t} := termBEq_refl t

/-- `Term.beq` implies heterogeneous equality for terms. -/
theorem termBEq_heq : ∀ {s1 : Finset Nat} (t1 : Term s1)
    {s2 : Finset Nat} (t2 : Term s2),
    Term.beq t1 t2 = true → s1 = s2 ∧ HEq t1 t2 := by
  intro s1 t1
  induction t1 with
  | var i =>
    intro s2 t2 h
    cases t2 with
    | var j =>
      simp [Term.beq] at h
      have hij : i = j := by omega
      subst hij
      exact ⟨rfl, HEq.rfl⟩
    | abs Q => simp [Term.beq] at h
    | app Q1 Q2 => simp [Term.beq] at h
  | abs P ih =>
    intro s2 t2 h
    cases t2 with
    | var j => simp [Term.beq] at h
    | abs Q =>
      simp [Term.beq] at h
      obtain ⟨hs, hheq⟩ := ih Q h
      subst hs
      have hPQ : P = Q := eq_of_heq hheq
      subst hPQ
      exact ⟨rfl, HEq.rfl⟩
    | app Q1 Q2 => simp [Term.beq] at h
  | app P1 P2 ih1 ih2 =>
    intro s2 t2 h
    cases t2 with
    | var j => simp [Term.beq] at h
    | abs Q => simp [Term.beq] at h
    | app Q1 Q2 =>
      simp [Term.beq] at h
      obtain ⟨hs1, hheq1⟩ := ih1 Q1 h.1
      obtain ⟨hs2, hheq2⟩ := ih2 Q2 h.2
      subst hs1; subst hs2
      have e1 : P1 = Q1 := eq_of_heq hheq1
      have e2 : P2 = Q2 := eq_of_heq hheq2
      subst e1; subst e2
      exact ⟨rfl, HEq.rfl⟩

/-- `Term s` satisfies `LawfulBEq`. -/
instance {s : Finset Nat} : LawfulBEq (Term s) where
  eq_of_beq {t1 t2} h := eq_of_heq (termBEq_heq t1 t2 h).2

instance {s : Finset Nat} : DecidableEq (Term s) :=
  fun t1 t2 =>
    match h : Term.beq t1 t2 with
    | true  => isTrue (eq_of_heq (termBEq_heq t1 t2 h).2)
    | false => isFalse (by
        intro heq
        subst heq
        rw [termBEq_refl t1] at h
        exact absurd h (by decide))

def castTerm {s : Finset Nat} (t : Term s) {s' : Finset Nat} (hs : s = s') : Term s' :=
  hs ▸ t

macro "⟦" t:term "⟧" : term => `(castTerm $t (by decide))

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var

namespace Term

-- 1. Identity Function: ƛx. x
def id : Term ∅ := ⟦ƛ (# 0)⟧

-- 2. Constant Function: ƛx. ƛy. x
def const : Term ∅ := ⟦ƛ (ƛ (# 1))⟧

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term ∅ := ⟦ƛ (ƛ (# 0))⟧
def one  : Term ∅ := ⟦ƛ (ƛ (# 1 ⬝ # 0))⟧
def two  : Term ∅ := ⟦ƛ (ƛ (# 1 ⬝ (# 1 ⬝ # 0)))⟧

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
def succ : Term ∅ :=
  ⟦ƛ (ƛ (ƛ (
    # 1 ⬝ ((# 2 ⬝ # 1) ⬝ # 0)
  )))⟧

-- A term with 2 free variables:
-- Set of free variables is {0, 1}
def freeTerm : Term {0, 1} := ⟦# 0 ⬝ # 1⟧

-- A term with 1 free variable (λy. y ⬝ x0):
-- Inside ƛ, free vars are {0, 1}. After ƛ, var 0 is bound, leaving {0} as free variable.
def boundAndFree : Term {0} := ⟦ƛ (# 0 ⬝ # 1)⟧

end Term

-------------------------------------------------------------------------------
-- 1. Free Variable Transformations for Shift & Substitution
-------------------------------------------------------------------------------

/-- Calculates shifted free variable set when scope increases by 1 at cutoff `c`. -/
def shiftSet (c : Nat) (s : Finset Nat) : Finset Nat :=
  s.image (fun i => if i ≥ c then i + 1 else i)

/-- Calculates new free variable set after substituting variable `j` with `sN`. -/
def substSet (j : Nat) (sN : Finset Nat) (sP : Finset Nat) : Finset Nat :=
  sP.biUnion (fun i =>
    if i = j then
      sN
    else if i > j then
      {i - 1}
    else
      {i})

-------------------------------------------------------------------------------
-- 2. Term Shifting (Weakening) & Substitution
-------------------------------------------------------------------------------

theorem shiftSet_singleton_ge (c : Nat) (i : Nat) (h : i ≥ c) :
    shiftSet c {i} = {i + 1} := by
  ext x
  simp [shiftSet, h]

theorem shiftSet_singleton_lt (c : Nat) (i : Nat) (h : ¬ i ≥ c) :
    shiftSet c {i} = {i} := by
  ext x
  simp [shiftSet, h]

theorem shiftSet_union (c : Nat) (s1 s2 : Finset Nat) :
    shiftSet c (s1 ∪ s2) = shiftSet c s1 ∪ shiftSet c s2 := by
  simp [shiftSet, Finset.image_union]

theorem mem_unbind {s : Finset Nat} {x : Nat} :
    x ∈ unbind s ↔ x + 1 ∈ s := by
  simp only [unbind, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ⟨ha0, ha_s⟩, rfl⟩
    have : a = a - 1 + 1 := by omega
    rwa [← this]
  · intro h
    refine ⟨x + 1, ⟨by omega, h⟩, by omega⟩

theorem mem_shiftSet {c : Nat} {s : Finset Nat} {y : Nat} :
    y ∈ shiftSet c s ↔ ∃ i ∈ s, (if i ≥ c then i + 1 else i) = y := by
  simp [shiftSet]

theorem unbind_shiftSet (c : Nat) (s : Finset Nat) :
    unbind (shiftSet (c + 1) s) = shiftSet c (unbind s) := by
  ext x
  rw [mem_unbind, mem_shiftSet, mem_shiftSet]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hy1 : y ≥ 1 := by
      by_contra h0
      have : y = 0 := by omega
      subst this
      split at heq <;> omega
    refine ⟨y - 1, ?_, ?_⟩
    · rw [mem_unbind]
      have : y - 1 + 1 = y := by omega
      rwa [this]
    · split at heq <;> split <;> omega
  · rintro ⟨z, hz, heq⟩
    rw [mem_unbind] at hz
    refine ⟨z + 1, hz, ?_⟩
    split at heq <;> split <;> omega

/-- Shifts free variables $\ge c$ by +1 when going under binders. -/
def shift (c : Nat) : ∀ {s : Finset Nat},
    Term s → Term (shiftSet c s)
  | _, Term.var i =>
    if h : i ≥ c then
      castTerm (Term.var (i + 1)) (shiftSet_singleton_ge c i h).symm
    else
      castTerm (Term.var i) (shiftSet_singleton_lt c i h).symm
  | _, Term.app P Q =>
    castTerm (Term.app (shift c P) (shift c Q)) (shiftSet_union c _ _).symm
  | _, Term.abs P =>
    castTerm (Term.abs (shift (c + 1) P)) (unbind_shiftSet c _)

theorem substSet_singleton_eq (j : Nat) (sN : Finset Nat) (i : Nat)
    (h : i = j) : substSet j sN {i} = sN := by
  ext x
  subst h
  simp [substSet]

theorem substSet_singleton_gt (j : Nat) (sN : Finset Nat) (i : Nat)
    (h : i > j) : substSet j sN {i} = {i - 1} := by
  ext x
  have h1 : ¬ i = j := by omega
  have h2 : i > j := h
  simp [substSet, h1, h2]

theorem substSet_singleton_lt (j : Nat) (sN : Finset Nat) (i : Nat)
    (h : i < j) : substSet j sN {i} = {i} := by
  ext x
  have h1 : ¬ i = j := by omega
  have h2 : ¬ i > j := by omega
  simp [substSet, h1, h2]

theorem substSet_union (j : Nat) (sN : Finset Nat) (s1 s2 : Finset Nat) :
    substSet j sN (s1 ∪ s2) = substSet j sN s1 ∪ substSet j sN s2 := by
  ext x
  simp [substSet]
  constructor
  · rintro ⟨i, (hi1 | hi2), hx⟩
    · left; exact ⟨i, hi1, hx⟩
    · right; exact ⟨i, hi2, hx⟩
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
    · exact ⟨i, Or.inl hi, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

theorem mem_substSet {j : Nat} {sN : Finset Nat} {sP : Finset Nat} {x : Nat} :
    x ∈ substSet j sN sP ↔
      ∃ i ∈ sP,
        if i = j then x ∈ sN
        else if i > j then x = i - 1
        else x = i := by
  simp only [substSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    split at hx
    · rename_i h; subst h; simp_all
    · split at hx
      · have h_eq := Finset.mem_singleton.mp hx
        simp_all
      · have h_eq := Finset.mem_singleton.mp hx
        simp_all
  · rintro ⟨i, hi, hx⟩
    refine ⟨i, hi, ?_⟩
    by_cases h1 : i = j
    · simp [h1] at hx ⊢; exact hx
    · by_cases h2 : i > j
      · simp [h1, h2] at hx ⊢; simp [hx]
      · simp [h1, h2] at hx ⊢; simp [hx]

theorem unbind_substSet (j : Nat) (sN : Finset Nat) (s' : Finset Nat) :
    unbind (substSet (j + 1) (shiftSet 0 sN) s') = substSet j sN (unbind s') := by
  ext x
  rw [mem_unbind, mem_substSet, mem_substSet]
  constructor
  · rintro ⟨i, hi, heq⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      by_cases h2 : 0 > j + 1
      · omega
      · simp [h2] at heq
    have hi1 : i ≥ 1 := by omega
    refine ⟨i - 1, ?_, ?_⟩
    · rw [mem_unbind]
      have : i - 1 + 1 = i := by omega
      rwa [this]
    · by_cases h1 : i = j + 1
      · simp [h1] at heq ⊢
        rw [mem_shiftSet] at heq
        rcases heq with ⟨k, hk, hkeq⟩
        dsimp at hkeq
        have : k = x := by omega
        rwa [← this]
      · by_cases h2 : i > j + 1
        · have h2_sub : i - 1 > j := by omega
          have h1_sub : ¬ i - 1 = j := by omega
          simp [h1, h2, h2_sub, h1_sub] at heq ⊢
          omega
        · have h3_sub : ¬ i - 1 > j := by omega
          have h3_eq : ¬ i - 1 = j := by omega
          simp [h1, h2, h3_sub, h3_eq] at heq ⊢
          omega
  · rintro ⟨i', hi', heq⟩
    rw [mem_unbind] at hi'
    refine ⟨i' + 1, hi', ?_⟩
    by_cases h1 : i' = j
    · simp [h1] at heq ⊢
      rw [mem_shiftSet]
      refine ⟨x, heq, by simp⟩
    · by_cases h2 : i' > j
      · have hi_gt : i' + 1 > j + 1 := by omega
        simp [h1, h2, hi_gt] at heq ⊢
        omega
      · have hi_lt : ¬ i' + 1 > j + 1 := by omega
        simp [h1, h2, hi_lt] at heq ⊢
        omega

def Term.size : ∀ {s : Finset Nat}, Term s → Nat
  | _, Term.var _ => 1
  | _, Term.abs P => 1 + Term.size P
  | _, Term.app P Q => 1 + Term.size P + Term.size Q

def subst (j : Nat) {sN : Finset Nat} (N : Term sN)
    {sP : Finset Nat} (M : Term sP) : Term (substSet j sN sP) :=
  match sP, M with
  | _, Term.var i =>
    if h1 : i = j then
      castTerm N (substSet_singleton_eq j sN i h1).symm
    else if h2 : i > j then
      castTerm (Term.var (i - 1)) (substSet_singleton_gt j sN i h2).symm
    else
      have h3 : i < j := by omega
      castTerm (Term.var i) (substSet_singleton_lt j sN i h3).symm
  | _, Term.app P Q =>
    castTerm (Term.app (subst j N P) (subst j N Q)) (substSet_union j sN _ _).symm
  | _, Term.abs P =>
    castTerm (Term.abs (subst (j + 1) (shift 0 N) P)) (unbind_substSet j sN _)
termination_by M.size
decreasing_by all_goals (first | omega | (simp [Term.size]; try omega))

-- 1. Simple substitution: x_0[0 := N] ⟹ N
#guard
  let N : Term {42} := Term.var 42
  let P : Term {0} := Term.var 0
  Term.beq (subst 0 N P) N

-- 2. Inner variable remains unchanged: x_0[1 := N] ⟹ x_0
#guard
  let N : Term {42} := Term.var 42
  let P : Term {0} := Term.var 0
  Term.beq (subst 1 N P) (Term.var 0)

-- 3. Free variable decrement: x_2[0 := N] ⟹ x_1
#guard
  let N : Term {42} := Term.var 42
  let P : Term {2} := Term.var 2
  Term.beq (subst 0 N P) (Term.var 1)

-- 4. Substitution under λ-abstraction: (λ. x_1)[0 := N] ⟹ λ. N_shifted
-- (The following three `#guard` checks are commented out because they do not
-- run in this environment: `#guard` evaluates the Boolean with the interpreter,
-- which reports "Could not find native implementation of external declaration
-- 'Multiset.bind'".  This is an evaluation-time limitation, not a statement
-- that the checks are false.  Corresponding propositional versions are proved
-- in `ChurchRosser/Examples.lean`.)
/-
#guard
  let N : Term {42} := Term.var 42
  let P : Term {0} := ⟦ ƛ (Term.var 1) ⟧
  let expected : Term {42} := ⟦ ƛ (Term.var 43) ⟧
  Term.beq (subst 0 N P) expected

-- 5. Shadowing inside λ: (λ. x_0)[0 := N] ⟹ λ. x_0
#guard
  let N : Term {42} := Term.var 42
  let P : Term ∅ := ⟦ ƛ (Term.var 0) ⟧
  let expected : Term ∅ := ⟦ ƛ (Term.var 0) ⟧
  Term.beq (subst 0 N P) expected

-- 6. Real β-step substitution: (x_0 x_1)[0 := var 99] ⟹ var 99 var 0
#guard
  let N : Term {99} := Term.var 99
  let body : Term {0, 1} := ⟦ Term.var 0 ⬝ Term.var 1 ⟧
  let expected : Term {0, 99} := ⟦ Term.var 99 ⬝ Term.var 0 ⟧
  Term.beq (subst 0 N body) expected
-/

-------------------------------------------------------------------------------
-- 3. Beta Reduction Step Relation
-------------------------------------------------------------------------------

namespace Term

/-- Beta substitution $M[N]$ substitutes variable $0$ in $M$ with $N$. -/
def betaSubst {sP : Finset Nat} (M : Term sP) {sN : Finset Nat} (N : Term sN) :
    Term (substSet 0 sN sP) :=
  subst 0 N M

end Term

-- Notation for substitution
notation:70 M " [" N "]" => Term.betaSubst M N

set_option quotPrecheck false in
set_option hygiene false in
infixl:65 " →β " => BetaStep

/-- Single-step $\beta$-reduction relation `P ⟶β Q`. -/
inductive BetaStep : ∀ {s1 s2 : Finset Nat}, Term s1 → Term s2 → Prop where
  | head {sP sN : Finset Nat}
      (P : Term sP) (N : Term sN) :
      ((ƛ P) ⬝ N) →β P [N]

  | app_left {s1 s1' s2 : Finset Nat}
      {P : Term s1} {P' : Term s1'} (Q : Term s2) :
      (P →β P') → (P ⬝ Q) →β (P' ⬝ Q)

  | app_right {s1 s2 s2' : Finset Nat}
      (P : Term s1) {Q : Term s2} {Q' : Term s2'} :
      Q →β Q' → (P ⬝ Q) →β (P ⬝ Q')

  | abs_body {s s' : Finset Nat}
      {P : Term s} {P' : Term s'} :
      P →β P' → (ƛ P) →β (ƛ P')

-- Many-step Beta reduction
notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen BetaStep N₁ N₂

syntax (name := betaStepTac) "beta_step" : tactic

macro_rules
  | `(tactic| beta_step) =>
    `(tactic| first
      | exact BetaStep.head _ _
      | apply BetaStep.abs_body; beta_step
      | apply BetaStep.app_left; beta_step
      | apply BetaStep.app_right; beta_step)

example : Term.id ⬝ Term.zero →β (subst 0 Term.zero (# 0)) :=
  BetaStep.head (# 0) Term.zero

#guard Term.beq (subst 0 Term.zero (Term.var 0)) Term.zero

theorem subst_beq_eq (j : Nat) {sN} (N : Term sN) {sP} (P : Term sP) {s} (expected : Term s) :
    Term.beq (subst j N P) expected = true →
    HEq (subst j N P) expected := by
  intro h
  exact (termBEq_heq _ _ h).2

theorem my_cast_heq {s s' : Finset Nat} (t : Term s) (hs : s = s') :
    HEq (castTerm t hs) t := by
  subst hs; rfl

end Basic41FinsetNOfFreeIsExact
