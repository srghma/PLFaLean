import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

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

-- A term with 2 free variables, depth 0:
def freeTerm : Term 2 0 := ## 0 ⬝ ## 1

-- A term with 1 free variable, depth 1 (λy. y ⬝ x0):
def boundAndFree : Term 1 1 := ƛ (# 0 ⬝ ## 1)

end Term

-- 1. WEAKENING / EXPANSION (n < m)
-- Inserts new unused variables into scope.
structure RenameWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Fin m

-- 2. PERMUTATION (n = m)
-- Reorders/swaps variables in scope. Must be a bijection (invertible).
structure RenamePerm (n : Nat) where
  map       : Fin n → Fin n
  inv       : Fin n → Fin n
  left_inv  : ∀ x, inv (map x) = x
  right_inv : ∀ x, map (inv x) = x

-- 3. CONTRACTION (n > m)
-- Merges multiple variables into one.
structure RenameContract (n m : Nat) where
  gt  : n > m
  map : Fin n → Fin m

-- Extend Weakening under λ
def RenameWeaken.ext {n m : Nat} (w : RenameWeaken n m) : RenameWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ w.lt
  map := Fin.cases 0 (fun i => (w.map i).succ)

-- Extend Permutation under λ
def RenamePerm.ext {n : Nat} (p : RenamePerm n) : RenamePerm (n + 1) where
  map := Fin.cases 0 (fun i => (p.map i).succ)
  inv := Fin.cases 0 (fun i => (p.inv i).succ)
  left_inv := fun x => match x with
    | ⟨0, _⟩     => rfl
    | ⟨i + 1, h⟩ => by simp [p.left_inv ⟨i, Nat.lt_of_succ_lt_succ h⟩]
  right_inv := fun x => match x with
    | ⟨0, _⟩     => rfl
    | ⟨i + 1, h⟩ => by simp [p.right_inv ⟨i, Nat.lt_of_succ_lt_succ h⟩]

-- Extend Contraction under λ
def RenameContract.ext {n m : Nat} (c : RenameContract n m) : RenameContract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ c.gt
  map := Fin.cases 0 (fun i => (c.map i).succ)

-- Apply Weakening (n < m) — Preserves abstraction depth d
def renameWeaken {n m d : Nat} (w : RenameWeaken n m) : Term n d → Term m d
  | Term.var i => Term.var (w.map i)
  | ƛ M        => ƛ (renameWeaken w.ext M)
  | M ⬝ N      => (renameWeaken w M) ⬝ (renameWeaken w N)

-- Apply Permutation (n = m) — Preserves abstraction depth d
def renamePerm {n d : Nat} (p : RenamePerm n) : Term n d → Term n d
  | Term.var i => Term.var (p.map i)
  | ƛ M        => ƛ (renamePerm p.ext M)
  | M ⬝ N      => (renamePerm p M) ⬝ (renamePerm p N)

-- Apply Contraction (n > m) — Preserves abstraction depth d
def renameContract {n m d : Nat} (c : RenameContract n m) : Term n d → Term m d
  | Term.var i => Term.var (c.map i)
  | ƛ M        => ƛ (renameContract c.ext M)
  | M ⬝ N      => (renameContract c M) ⬝ (renameContract c N)

-- Helper Weakening constructor for shifting variables by +1 (Fin.succ)
def RenameWeaken.succ (m : Nat) : RenameWeaken m (m + 1) where
  lt  := Nat.lt_succ_self m
  map := Fin.succ

namespace Term

-- Substitution maps (Fin n → Σ d, Term m d)
def Subst (n m : Nat) : Type := Fin n → (d : Nat) × Term m d

def exts {n m : Nat} (σ : Subst n m) : Subst (n + 1) (m + 1)
  | ⟨0, _⟩     => ⟨0, # ⟨0, Nat.succ_pos _⟩⟩
  | ⟨i + 1, h⟩ =>
      let ⟨d, t⟩ := σ ⟨i, Nat.lt_of_succ_lt_succ h⟩
      ⟨d, renameWeaken (RenameWeaken.succ m) t⟩

def subst {n m : Nat} (σ : Subst n m) : ∀ {d : Nat}, Term n d → (d' : Nat) × Term m d'
  | _, Term.var i => σ i
  | _, ƛ M        => let ⟨d', M'⟩ := subst (exts σ) M; ⟨d' + 1, ƛ M'⟩
  | _, M ⬝ N      => let ⟨dM', M'⟩ := subst σ M; let ⟨dN', N'⟩ := subst σ N; ⟨max dM' dN', M' ⬝ N'⟩

-- Substitution of top variable (Fin (n+1) → Σ d, Term n d)
def substZero {n dN : Nat} (N : Term n dN) : Subst (n + 1) n
  | ⟨0, _⟩     => ⟨dN, N⟩
  | ⟨i + 1, h⟩ => ⟨0, # ⟨i, Nat.lt_of_succ_lt_succ h⟩⟩

-- Clean single-substitution operator
def betaSubst {n dM dN : Nat} (M : Term (n + 1) dM) (N : Term n dN) : (d' : Nat) × Term n d' :=
  subst (substZero N) M

end Term

notation:70 M " [" N "]" => (Term.betaSubst M N)

-- Standard Single-Step Beta Reduction (Beta)
inductive Beta : ∀ {n d1 d2 : Nat}, Term n d1 → Term n d2 → Prop where
  | basis {n dM dN : Nat} (M : Term (n + 1) dM) (N : Term n dN) :
      Beta ((ƛ M) ⬝ N) (M[N].2)
  | appr {n d1 d2 d3 : Nat} {M : Term n d1} {N : Term n d2} (L : Term n d3) :
      Beta M N → Beta (M ⬝ L) (N ⬝ L)
  | appl {n d1 d2 d3 : Nat} {M : Term n d1} {N : Term n d2} (L : Term n d3) :
      Beta M N → Beta (L ⬝ M) (L ⬝ N)
  | abs {n d1 d2 : Nat} {M : Term (n + 1) d1} {N : Term (n + 1) d2} :
      Beta M N → Beta (ƛ M) (ƛ N)

infixl:65 " →β " => Beta

-- Many-step Beta reduction
notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen Beta N₁ N₂

-- Parallel Beta Reduction (BetaP)
inductive BetaP : ∀ {n d1 d2 : Nat}, Term n d1 → Term n d2 → Prop where
  | var {n : Nat} (i : Fin n) :
      BetaP (# i) (# i)
  | abs {n d1 d2 : Nat} {M : Term (n + 1) d1} {N : Term (n + 1) d2} :
      BetaP M N → BetaP (ƛ M) (ƛ N)
  | app {n dM dM' dN dN' : Nat} {M : Term n dM} {M' : Term n dM'} {N : Term n dN} {N' : Term n dN'} :
      BetaP M M' → BetaP N N' → BetaP (M ⬝ N) (M' ⬝ N')
  | subst {n dM dM' dN dN' : Nat} {M : Term (n + 1) dM} {M' : Term (n + 1) dM'} {N : Term n dN} {N' : Term n dN'} :
      BetaP M M' → BetaP N N' → BetaP ((ƛ M) ⬝ N) (M'[N'].2)

infixl:65 " →βp " => BetaP

-- Reflexivity of Parallel Reduction
@[refl]
theorem betap_refl {n d : Nat} (N : Term n d) : N →βp N := by
  induction N with
  | var i => exact BetaP.var i
  | abs M ih => exact BetaP.abs ih
  | app M N ihM ihN => exact BetaP.app ihM ihN
