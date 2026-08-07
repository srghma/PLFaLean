module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace Basic42Bitmask

attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

-- `Term n s d`:
--   n : Scope size
--   s : Nat — bitmask of free variables (bit i set ⟺ variable i is free)
--   d : Abstraction depth
-- NOTE: lol, bc BitVec is implemented using Nat
inductive Term : (n : Nat) → Nat → Nat → Type
  | var : ∀ {n : Nat} (i : Fin n), Term n (1 <<< i.val) 0
  | abs : ∀ {n : Nat} {s : Nat} {d : Nat},
      Term (n + 1) s d → Term n (s >>> 1) (d + 1)
  | app : ∀ {n : Nat} {s1 s2 d1 d2 : Nat},
      Term n s1 d1 → Term n s2 d2 → Term n (s1 ||| s2) (max d1 d2)

theorem max_var_bound {n : Nat} {s d : Nat} (_ : Term n s d) : n ≤ n + d := by
  exact Nat.le_add_right n d

-- A theorem proving that the free-variable bitmask is ALWAYS strictly bounded by 2^n
-- theorem mask_lt_scope {n s d : Nat} (t : Term n s d) : s < (1 <<< n) := by
--   induction t with
--   | var i =>
--     have h := i.isLt
--     try? +missing
--   | abs _ ih =>
--     -- s >>> 1 < 2^n because s < 2^(n+1)
--     exact Nat.shiftRight_lt_of_lt_shiftLeft ih
--   | app _ _ ih1 ih2 =>
--     -- s1 ||| s2 < 2^n because both s1, s2 < 2^n
--     exact Nat.or_lt_shiftLeft ih1 ih2

-- Cast a Term along propositional (but not definitional) equalities of s, d.
-- Needed because Nat shift/or expressions don't auto-reduce under the unifier;
-- `decide` closes the gap via kernel computation.
def castTerm (t : Term n s d) (hs : s = s' := by decide) (hd : d = d' := by decide) :
    Term n s' d' := by subst hs; subst hd; exact t

macro:max "⟦" t:term "⟧" : term => `(castTerm $t)

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term => `(Term.var (n := $n) (Fin.mk $i (by decide)))

-- Bitmask literal builder: toBitmask {0, 1} ↦ bit 0 set, bit 1 set.
def toBitmaskList (l : List Nat) : Nat := l.foldl (fun acc i => acc ||| (1 <<< i)) 0
macro "b{" xs:term,* "}" : term => `(toBitmaskList [$xs,*])

namespace Term

-- 1. Identity Function: ƛx. x
def id : Term 0 0 1 := ƛ (# 0)

-- 2. Constant Function: ƛx. ƛy. x
def const : Term 0 0 2 := ⟦ƛ (ƛ (##[2] 1))⟧

-- 3. Church Numerals: ƛf. ƛx. f^n x
def zero : Term 0 0 2 := ƛ (ƛ (# 0))
def one  : Term 0 0 2 := ⟦ƛ (ƛ (##[2] 1 ⬝ # 0))⟧
def two  : Term 0 0 2 := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0)))⟧

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
def succ : Term 0 0 3 :=
  ⟦ƛ (ƛ (ƛ (
    ##[3] 1 ⬝ ((##[3] 2 ⬝ ##[3] 1) ⬝ # 0)
  )))⟧

-- A term with 2 free variables, depth 0.
def freeTerm : Term 2 (b{0, 1}) 0 := ⟦##[2] 0 ⬝ ##[2] 1⟧

-- A term with 1 free variable, depth 1.
def boundAndFree : Term 1 (b{0}) 1 := ⟦ƛ (# 0 ⬝ ##[2] 1)⟧

end Term

end Basic42Bitmask
