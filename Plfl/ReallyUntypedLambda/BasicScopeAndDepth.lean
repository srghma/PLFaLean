import Mathlib.Data.Nat.Basic

-- we want to force user to use `##` bc default `#synth OfNat (Fin 5) 10` will use mod. Disable these two (they do the same thing)
attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

-- `Term n d`:
--   n : Scope size (the number of abstractions currently surrounding this subterm)
--   d : Abstraction depth (maximum nested λ abstractions)
--
-- Core Invariant: $\text{Scope} \le d + \text{Initial Scope}$
inductive Term : Nat → Nat → Type
  | var : ∀ {n : Nat}, Fin n → Term n 0
  | abs : ∀ {n d : Nat}, Term (n + 1) d → Term n (d + 1)
  | app : ∀ {n d1 d2 : Nat}, Term n d1 → Term n d2 → Term n (max d1 d2)

-- A theorem showing that in any `Term n d`,
-- the maximum variable index in scope is strictly bounded by `n + d`.
theorem max_var_bound {n d : Nat} (_ : Term n d) : n ≤ n + d := by exact Nat.le_add_right n d

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "## " n:term:max : term => `(Term.var (Fin.mk $n (by decide)))

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0
def id : Term 0 1 := ƛ (# 0)

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0
def const : Term 0 2 := ƛ (ƛ (## 1))

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 2 := ƛ (ƛ (# 0))

-- One: ƛf. ƛx. f x
def one : Term 0 2 := ƛ (ƛ (## 1 ⬝ # 0))

-- Two: ƛf. ƛx. f (f x)
def two : Term 0 2 := ƛ (ƛ (## 1 ⬝ (## 1 ⬝ # 0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0
def succ : Term 0 3 :=
  ƛ (             -- n is var 2
    ƛ (           -- f is var 1
      ƛ (         -- x is var 0
        ## 1 ⬝
        ((## 2 ⬝ ## 1) ⬝ # 0)
      )
    )
  )

end Term

-- 1. WEAKENING / EXPANSION (n < m)
-- Inserts new unused variables into scope.
structure Weaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Fin m

-- 2. PERMUTATION (n = m)
-- Reorders/swaps variables in scope. Must be a bijection (invertible).
structure Perm (n : Nat) where
  map       : Fin n → Fin n
  inv       : Fin n → Fin n
  left_inv  : ∀ x, inv (map x) = x
  right_inv : ∀ x, map (inv x) = x

-- 3. CONTRACTION (n > m)
-- Merges multiple variables into one.
structure Contract (n m : Nat) where
  gt  : n > m
  map : Fin n → Fin m

-- Extend Weakening under λ
def Weaken.ext {n m : Nat} (w : Weaken n m) : Weaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ w.lt
  map := Fin.cases 0 (fun i => (w.map i).succ)

-- Extend Permutation under λ
def Perm.ext {n : Nat} (p : Perm n) : Perm (n + 1) where
  map := Fin.cases 0 (fun i => (p.map i).succ)
  inv := Fin.cases 0 (fun i => (p.inv i).succ)
  left_inv := fun x => match x with
    | ⟨0, _⟩     => rfl
    | ⟨i + 1, h⟩ => by simp [p.left_inv ⟨i, Nat.lt_of_succ_lt_succ h⟩]
  right_inv := fun x => match x with
    | ⟨0, _⟩     => rfl
    | ⟨i + 1, h⟩ => by simp [p.right_inv ⟨i, Nat.lt_of_succ_lt_succ h⟩]

-- Extend Contraction under λ
def Contract.ext {n m : Nat} (c : Contract n m) : Contract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ c.gt
  map := Fin.cases 0 (fun i => (c.map i).succ)

-- Apply Weakening (n < m) — Preserves abstraction depth d
def renameWeaken {n m d : Nat} (w : Weaken n m) : Term n d → Term m d
  | Term.var i => Term.var (w.map i)
  | ƛ M        => ƛ (renameWeaken w.ext M)
  | M ⬝ N      => (renameWeaken w M) ⬝ (renameWeaken w N)

-- Apply Permutation (n = m) — Preserves abstraction depth d
def renamePerm {n d : Nat} (p : Perm n) : Term n d → Term n d
  | Term.var i => Term.var (p.map i)
  | ƛ M        => ƛ (renamePerm p.ext M)
  | M ⬝ N      => (renamePerm p M) ⬝ (renamePerm p N)

-- Apply Contraction (n > m) — Preserves abstraction depth d
def renameContract {n m d : Nat} (c : Contract n m) : Term n d → Term m d
  | Term.var i => Term.var (c.map i)
  | ƛ M        => ƛ (renameContract c.ext M)
  | M ⬝ N      => (renameContract c M) ⬝ (renameContract c N)

inductive Rename (n m : Nat) where
  | weaken   : Weaken n m → Rename n m
  | perm     : (h : n = m) → Perm n → Rename n m
  | contract : Contract n m → Rename n m

-- Master rename function that delegates to the appropriate case
def rename {n m d : Nat} (r : Rename n m) (t : Term n d) : Term m d :=
  match r with
  | .weaken w   => renameWeaken w t
  | .perm h p   => h ▸ renamePerm p t
  | .contract c => renameContract c t
