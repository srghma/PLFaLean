import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Image

-- import Mathlib.Data.Finset.Lattice  -- for biUnion, if you need it elsewhere

attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

-- Helper function: Removes bound variable 0 and shifts remaining free variable indices down by 1.
def unbind {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.image
    (fun (p : ↥(s.erase ⟨0, Nat.succ_pos n⟩)) =>
      have hi := p.2
      have hne : p.1 ≠ ⟨0, Nat.succ_pos n⟩ := (Finset.mem_erase.mp hi).1
      have hval : p.1.val ≠ 0 := fun h => hne (Fin.ext h)
      have hlt : p.1.val < n + 1 := p.1.isLt
      ⟨p.1.val - 1, by omega⟩)
    (s.erase ⟨0, Nat.succ_pos n⟩).attach

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

theorem max_var_bound {n : Nat} {s : Finset (Fin n)} {d : Nat} (_ : Term n s d) : n ≤ n + d := by
  exact Nat.le_add_right n d

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term =>
  `(Term.var (n := $n) (Fin.mk $i (of_decide_eq_true (Eq.refl true))))

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0 ∅ 1 (0 free variables remaining)
def id : Term 0 ∅ 1 := ƛ (# 0)

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0 ∅ 2
def const : Term 0 ∅ 2 := ƛ (ƛ (##[2] 1))

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 ∅ 2 := ƛ (ƛ (# 0))
def one  : Term 0 ∅ 2 := ƛ (ƛ (##[2] 1 ⬝ # 0))
def two  : Term 0 ∅ 2 := ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0 ∅ 3
def succ : Term 0 ∅ 3 :=
  ƛ (ƛ (ƛ (
    ##[3] 1 ⬝ ((##[3] 2 ⬝ ##[3] 1) ⬝ # 0)
  )))

-- A term with 2 free variables, depth 0:
-- Set of free variables is {0, 1}
def freeTerm : Term 2 {0, 1} 0 := ##[2] 0 ⬝ ##[2] 1

-- A term with 1 free variable, depth 1 (λy. y ⬝ x0):
-- Inside ƛ, free vars are {0, 1}. After ƛ, var 0 is bound, leaving {0} as free variable.
def boundAndFree : Term 1 {0} 1 := ƛ (# 0 ⬝ ##[2] 1)

end Term
