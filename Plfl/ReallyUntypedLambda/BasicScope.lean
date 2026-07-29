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

end Term

namespace Term

-- Renaming functions (index maps Fin n → Fin m)
def Rename (n m : Nat) : Type := Fin n → Fin m

def ext {n m : Nat} (ρ : Rename n m) : Rename (n + 1) (m + 1)
  | ⟨0, _⟩     => ⟨0, Nat.succ_pos _⟩
  | ⟨i + 1, h⟩ => (ρ ⟨i, Nat.lt_of_succ_lt_succ h⟩).succ

def rename {n m : Nat} (ρ : Rename n m) : Term n → Term m
  | # i     => # (ρ i)
  | ƛ M     => ƛ (rename (ext ρ) M)
  | M ⬝ N   => (rename ρ M) ⬝ (rename ρ N)

-- Substitution maps (Fin n → Term m)
def Subst (n m : Nat) : Type := Fin n → Term m

def exts {n m : Nat} (σ : Subst n m) : Subst (n + 1) (m + 1)
  | ⟨0, _⟩     => # ⟨0, Nat.succ_pos _⟩
  | ⟨i + 1, h⟩ => rename Fin.succ (σ ⟨i, Nat.lt_of_succ_lt_succ h⟩)

def subst {n m : Nat} (σ : Subst n m) : Term n → Term m
  | # i   => σ i
  | ƛ M   => ƛ (subst (exts σ) M)
  | M ⬝ N => (subst σ M) ⬝ (subst σ N)

-- Substitution of top variable (Fin (n+1) → Term n)
def substZero {n : Nat} (N : Term n) : Subst (n + 1) n
  | ⟨0, _⟩     => N
  | ⟨i + 1, h⟩ => # ⟨i, Nat.lt_of_succ_lt_succ h⟩

-- Clean single-substitution operator
def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  subst (substZero N) M

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
