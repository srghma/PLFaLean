import Mathlib.Logic.Relation

-- we want to force user to use `##` bc default `#synth OfNat (Fin 5) 10` will use mod. Disable these two (they do the same thing)
attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

-- 1. Intrinsically scoped Lambda terms parameterized by scope size `n : Nat`
inductive Term : Nat → Type
  | var : ∀ {n : Nat}, Fin n → Term n
  | abs : ∀ {n : Nat}, Term (n + 1) → Term n
  | app : ∀ {n : Nat}, Term n → Term n → Term n
  deriving DecidableEq

-- Override `λ` using explicit syntax with term:max
-- syntax (name := myAbs) "λ " term:max : term
-- macro_rules | `(λ $M) => `(Term.abs $M)
--
-- prefix:100 "λ " => Term.abs
--
prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "## " n:term:max : term => `(Term.var (Fin.mk $n (by decide)))

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0
def id : Term 0 := ƛ (# 0)

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0
def const : Term 0 := ƛ (ƛ (## 1))

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 := ƛ (ƛ (# 0))

-- One: ƛf. ƛx. f x
def one : Term 0 := ƛ (ƛ (## 1 ⬝ # 0))

-- Two: ƛf. ƛx. f (f x)
def two : Term 0 := ƛ (ƛ (## 1 ⬝ (## 1 ⬝ # 0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0
def succ : Term 0 :=
  ƛ (             -- n is var 2
    ƛ (           -- f is var 1
      ƛ (         -- x is var 0
        ## 1 ⬝
        ((## 2 ⬝ ## 1) ⬝ # 0)
      )
    )
  )

-- A term with 2 free variables: (x0 x1)
def freeTerm : Term 2 := ## 0 ⬝ ## 1

-- A term with 1 free variable (x0): λy. (y x0)
def boundAndFree : Term 1 := ƛ (# 0 ⬝ ## 1)

end Term

-- WEAKENING / EXPANSION (n < m)
-- Inserts new unused variables into scope.
structure RenameWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Fin m

-- Extend Weakening under λ
def RenameWeaken.ext {n m : Nat} (w : RenameWeaken n m) : RenameWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ w.lt
  map := Fin.cases 0 (fun i => (w.map i).succ)

-- Apply Weakening (n < m)
def renameWeaken {n m : Nat} (w : RenameWeaken n m) : Term n → Term m
  | Term.var i => Term.var (w.map i)
  | ƛ M        => ƛ (renameWeaken w.ext M)
  | M ⬝ N      => (renameWeaken w M) ⬝ (renameWeaken w N)

-- Helper Weakening constructor for shifting variables by +1 (Fin.succ)
def RenameWeaken.succ (m : Nat) : RenameWeaken m (m + 1) where
  lt  := Nat.lt_succ_self m
  map := Fin.succ

-- 1. WEAKENING SUBSTITUTION (n < m)
structure SubstWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Term m

-- Extend Weakening Substitution under λ
def SubstWeaken.ext {n m : Nat} (σ : SubstWeaken n m) : SubstWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ σ.lt
  map := Fin.cases (# 0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

-- Apply Weakening Substitution (n < m)
def substWeaken {n m : Nat} (σ : SubstWeaken n m) : Term n → Term m
  | # i   => σ.map i
  | ƛ M   => ƛ (substWeaken σ.ext M)
  | M ⬝ N => (substWeaken σ M) ⬝ (substWeaken σ N)

-- 2. SAME-SCOPE SUBSTITUTION (n = m)
structure SubstSame (n : Nat) where
  map : Fin n → Term n

-- Extend Same-Scope Substitution under λ
def SubstSame.ext {n : Nat} (σ : SubstSame n) : SubstSame (n + 1) where
  map := Fin.cases (# 0) (fun i => renameWeaken (RenameWeaken.succ n) (σ.map i))

-- Apply Same-Scope Substitution (n = m)
def substSame {n : Nat} (σ : SubstSame n) : Term n → Term n
  | # i   => σ.map i
  | ƛ M   => ƛ (substSame σ.ext M)
  | M ⬝ N => (substSame σ M) ⬝ (substSame σ N)

-- 3. CONTRACTING SUBSTITUTION (n > m)
structure SubstContract (n m : Nat) where
  gt  : n > m
  map : Fin n → Term m

-- Extend Contracting Substitution under λ
def SubstContract.ext {n m : Nat} (σ : SubstContract n m) : SubstContract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ σ.gt
  map := Fin.cases (# 0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

-- Apply Contracting Substitution (n > m)
def substContract {n m : Nat} (σ : SubstContract n m) : Term n → Term m
  | # i   => σ.map i
  | ƛ M   => ƛ (substContract σ.ext M)
  | M ⬝ N => (substContract σ M) ⬝ (substContract σ N)

namespace Term

-- Substitution of top variable (Fin (n+1) → Term n)
def mkSubstZero {n : Nat} (N : Term n) : SubstContract (n + 1) n where
  gt  := Nat.lt_succ_self n
  map := Fin.cases N (fun i => # i)

-- Clean single-substitution operator
def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  substContract (mkSubstZero N) M

end Term

-- Notation for substitution
notation:70 M " [" N "]" => Term.betaSubst M N

-- 2. Standard Single-Step Beta Reduction (Beta)
inductive Beta : ∀ {n : Nat}, Term n → Term n → Prop
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) :
      Beta ((ƛ M) ⬝ N) (M[N])
  | appr {n : Nat} {M N : Term n} (L : Term n) :
      Beta M N → Beta (M ⬝ L) (N ⬝ L)
  | appl {n : Nat} {M N : Term n} (L : Term n) :
      Beta M N → Beta (L ⬝ M) (L ⬝ N)
  | abs {n : Nat} {M N : Term (n + 1)} :
      Beta M N → Beta (ƛ M) (ƛ N)

infixl:65 " →β " => Beta

-- Many-step Beta reduction
notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen Beta N₁ N₂

-- 3. Parallel Beta Reduction (BetaP)
inductive BetaP : ∀ {n : Nat}, Term n → Term n → Prop
  | var {n : Nat} (i : Fin n) :
      BetaP (# i) (# i)
  | abs {n : Nat} {M N : Term (n + 1)} :
      BetaP M N → BetaP (ƛ M) (ƛ N)
  | app {n : Nat} {M M' N N' : Term n} :
      BetaP M M' → BetaP N N' → BetaP (M ⬝ N) (M' ⬝ N')
  | subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n} :
      BetaP M M' → BetaP N N' → BetaP ((ƛ M) ⬝ N) (M'[N'])

infixl:65 " →βp " => BetaP

-- 4. Reflexivity of Parallel Reduction
@[refl]
theorem betap_refl {n : Nat} (N : Term n) : N →βp N := by
  induction N with
  | var i => exact BetaP.var i
  | abs M ih => exact BetaP.abs ih
  | app M N ihM ihN => exact BetaP.app ihM ihN
