-- https://github.com/iwilare/church-rosser/blob/main/DeBruijn.agda

import Aesop
import Mathlib.Logic.Relation

-- we want to force user to use `v##` bc default `v#synth OfNat (Fin 5) 10` will use mod. Disable these two (they do the same thing)
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
prefix:71 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:72 "v#" => Term.var
macro:72 "v##" n:term:max : term => `(Term.var (Fin.mk $n (by decide)))

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0
def id : Term 0 := ƛ v#0

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0
def const : Term 0 := ƛ (ƛ v##1)

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 := ƛ (ƛ (v#0))

-- One: ƛf. ƛx. f x
def one : Term 0 := ƛ (ƛ (v##1 ⬝ v#0))

-- Two: ƛf. ƛx. f (f x)
def two : Term 0 := ƛ (ƛ (v##1 ⬝ (v##1 ⬝ v#0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0
def succ : Term 0 :=
  ƛ (             -- n is var 2
    ƛ (           -- f is var 1
      ƛ (         -- x is var 0
        v##1 ⬝
        ((v##2 ⬝ v##1) ⬝ v#0)
      )
    )
  )

-- A term with 2 free variables: (x0 x1)
def freeTerm : Term 2 := v##0 ⬝ v##1

-- A term with 1 free variable (x0): λy. (y x0)
def boundAndFree : Term 1 := ƛ (v#0 ⬝ v##1)

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
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

-- Apply Weakening Substitution (n < m)
def substWeaken {n m : Nat} (σ : SubstWeaken n m) : Term n → Term m
  | v#i   => σ.map i
  | ƛ M   => ƛ (substWeaken σ.ext M)
  | M ⬝ N => (substWeaken σ M) ⬝ (substWeaken σ N)

-- 2. SAME-SCOPE SUBSTITUTION (n = m)
structure SubstSame (n : Nat) where
  map : Fin n → Term n

-- Extend Same-Scope Substitution under λ
def SubstSame.ext {n : Nat} (σ : SubstSame n) : SubstSame (n + 1) where
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ n) (σ.map i))

-- Apply Same-Scope Substitution (n = m)
def substSame {n : Nat} (σ : SubstSame n) : Term n → Term n
  | v#i   => σ.map i
  | ƛ M   => ƛ (substSame σ.ext M)
  | M ⬝ N => (substSame σ M) ⬝ (substSame σ N)

-- 3. CONTRACTING SUBSTITUTION (n > m)
structure SubstContract (n m : Nat) where
  gt  : n > m
  map : Fin n → Term m

-- Extend Contracting Substitution under λ
def SubstContract.ext {n m : Nat} (σ : SubstContract n m) : SubstContract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ σ.gt
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

-- Apply Contracting Substitution (n > m)
def substContract {n m : Nat} (σ : SubstContract n m) : Term n → Term m
  | v#i   => σ.map i
  | ƛ M   => ƛ (substContract σ.ext M)
  | M ⬝ N => (substContract σ M) ⬝ (substContract σ N)

namespace Term

-- Substitution of top variable (Fin (n+1) → Term n)
def mkSubstZero {n : Nat} (N : Term n) : SubstContract (n + 1) n where
  gt  := Nat.lt_succ_self n
  map := Fin.cases N (fun i => v#i)

-- Clean single-substitution operator
def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  substContract (mkSubstZero N) M

end Term

-- Notation for substitution
notation:70 M " [" N "]" => Term.betaSubst M N

-- https://github.com/iwilare/church-rosser/blob/main/Beta.agda

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→" => Beta -- the std → and -> have binding power 25

-- 2. Standard Single-Step Beta Reduction (Beta)
inductive Beta : ∀ {n : Nat}, Term n → Term n → Prop
  | appl {n : Nat} {M N : Term n} (L : Term n) :
      M —→ N
      --------------------
      → L ⬝ M —→ L ⬝ N
  | appr {n : Nat} {M N : Term n} (L : Term n) :
      M —→ N
      --------------------
      → M ⬝ L —→ N ⬝ L
  | abs {n : Nat} {M N : Term (n + 1)} :
      M —→ N
      --------------------
      → ƛ M —→ ƛ N
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) :
      --------------------
      ƛ M ⬝ N —→ M[N]

#print Beta.appr
#print Beta.appl
#print Beta.abs
#print Beta.basis

infixl:65 "—→-ξₗ" => Beta.appr
infixl:65 "—→-ξᵣ" => Beta.appl
prefix:65 "—→-ƛ " => Beta.abs
infixl:65 "—→-β"  => Beta.basis

theorem step_test {n : Nat} {t1 t2 : Term n} (h : t1 —→ t2) : True :=
  match h with
  | L —→-ξₗ h' => True.intro
  | L —→-ξᵣ h' => True.intro
  | —→-ƛ h'   => True.intro
  | M —→-β N  => True.intro

abbrev BetaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Beta
infix:64 " —→* " => BetaStar -- in original repo —↠

-- -- 3. Reflexivity (0-step) notation
-- notation:4 " ∎" => Relation.ReflTransGen.refl

-- -- 4. Step-prepending notation matching Agda —→⟨ h ⟩ rest
-- syntax:3 " —→⟨ " term " ⟩ " term : term
-- macro_rules
--   | `(—→⟨ $h ⟩ $rest) => `(Relation.ReflTransGen.head $h $rest)

-- 3. Parallel Beta Reduction (BetaPar)
set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "⇉" => BetaPar -- the std → and -> have binding power 25

inductive BetaPar : ∀ {n : Nat}, Term n → Term n → Prop
  | var {n : Nat} (x : Fin n)
      ---------
      : v#x ⇉ v#x
  | abs {n : Nat} {M N : Term (n + 1)}
      : M ⇉ N
      ---------
      → ƛ M ⇉ ƛ N
  | app {n : Nat} {M M' N N' : Term n}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → M ⬝ N ⇉ M' ⬝ N'
  | subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → ƛ M ⬝ N ⇉ M'[N']

infixl:65 "⇉-c" => BetaPar.var
prefix:65 "⇉-ƛ " => BetaPar.abs
infixl:65 "⇉-ξ" => BetaPar.app
infixl:65 "⇉-β"  => BetaPar.subst

-- 4. Reflexivity of Parallel Reduction
-- Typeclass instance for Reflexivity of BetaP
instance : Std.Refl (BetaPar (n := n)) where
  refl N := by
    induction N with
    | var i => exact BetaPar.var i
    | abs M ih => exact BetaPar.abs ih
    | app M N ihM ihN => exact BetaPar.app ihM ihN

abbrev BetaParStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaPar
infix:64 " ⇉* " => BetaParStar

-- 1. Single-step implies parallel reduction:
theorem beta_to_betapar {n : Nat} {M N : Term n} (h : M —→ N) : M ⇉ N := by
  induction h with
  | appl L _ ih =>
    -- L ⬝ M —→ L ⬝ N
    exact BetaPar.app (refl L) ih
  | appr L _ ih =>
    -- M ⬝ L —→ N ⬝ L
    exact BetaPar.app ih (refl L)
  | abs _ ih =>
    -- ƛ M —→ ƛ N
    exact BetaPar.abs ih
  | basis M N =>
    -- ƛ M ⬝ N —→ M[N]
    exact BetaPar.subst (refl M) (refl N)

-- ====================================================================
-- Helper Congruence Lemmas for Multi-Step Reduction (BetaStar / —→*)
-- ====================================================================

theorem beta_star_abs {n : Nat} {M N : Term (n + 1)} (h : M —→* N) : ƛ M —→* ƛ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.abs step)

theorem beta_star_appr {n : Nat} {M M' : Term n} (N : Term n) (h : M —→* M') : M ⬝ N —→* M' ⬝ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appr N step)

theorem beta_star_appl {n : Nat} {N N' : Term n} (M : Term n) (h : N —→* N') : M ⬝ N —→* M ⬝ N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appl M step)

-- ====================================================================
-- Main Equivalence Theorems
-- ====================================================================

-- 2. Parallel reduction implies multi-step reduction:
theorem betapar_to_betastar {n : Nat} {M N : Term n} (h : M ⇉ N) : M —→* N := by
  induction h with
  | var i =>
    exact Relation.ReflTransGen.refl
  | abs _ ih =>
    exact beta_star_abs ih
  | app _ _ ihM ihN =>
    exact Relation.ReflTransGen.trans (beta_star_appr _ ihM) (beta_star_appl _ ihN)
  | subst _ _ ihM ihN =>
    have h1 : (ƛ _) ⬝ _ —→* (ƛ _) ⬝ _ :=
      Relation.ReflTransGen.trans (beta_star_appr _ (beta_star_abs ihM)) (beta_star_appl _ ihN)
    exact Relation.ReflTransGen.tail h1 (Beta.basis _ _)

-- 3. Their reflexive-transitive closures are identical!
theorem betapar_star_eq_betastar {n : Nat} {M N : Term n} :
  M ⇉* N ↔ M —→* N := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.trans ih (betapar_to_betastar step)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.tail ih (beta_to_betapar step)

-- --------------------------------------------------------------------
-- 3. Beta Equivalence / Conversion (BetaEq / ≡β)
-- --------------------------------------------------------------------
abbrev BetaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen (Beta (n := n))

infix:64 " ≡β " => BetaEq

-- --------------------------------------------------------------------
-- 4. Joinability / Confluence (BetaJoin)
-- --------------------------------------------------------------------
abbrev BetaJoin {n : Nat} : Term n → Term n → Prop := Relation.Join (BetaStar (n := n))

-- Abbreviation for at-most-1-step beta reduction (ReflGen Beta)
abbrev BetaRefl {n : Nat} : Term n → Term n → Prop := Relation.ReflGen (Beta (n := n))

-- Infix notation for 0 or 1 step reduction
infix:65 " —→≤1 " => BetaRefl

-- Takahashi's Complete Development Function (M*)
-- Performs maximal parallel reduction in 1 step
def takahashi {n : Nat} : Term n → Term n
  | v#i          => v#i
  | (ƛ M) ⬝ N    => (takahashi M)[takahashi N]  -- Fire redex!
  | ƛ M          => ƛ (takahashi M)
  | M ⬝ N        => (takahashi M) ⬝ (takahashi N)

-- ====================================================================
-- Substitution Lemma for Parallel Reduction
-- ====================================================================

-- Parallel reduction is preserved under substitution
theorem betapar_subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇉ M') (hN : N ⇉ N') : M[N] ⇉ M'[N'] := by
  try? +missing

-- ====================================================================
-- Takahashi's Triangle Lemma (Main Proof)
-- ====================================================================

theorem takahashi_triangle {n : Nat} {M N : Term n} (h : M ⇉ N) : N ⇉ takahashi M := by
  induction h with
  | var i =>
    exact BetaPar.var i
  | abs _ ih =>
    exact BetaPar.abs ih
  | app hM hN ihM ihN =>
    -- Case analysis on M to check if (M ⬝ N) is a redex (ƛ M0 ⬝ N)
    match M with
    | v#i =>
      · induction M
        · aesop?
        · solve_by_elim
        · solve_by_elim
    | M1 ⬝ M2 =>
      · induction M
        · aesop?
        · solve_by_elim
        · solve_by_elim
    | ƛ M0 =>
      -- M = ƛ M0, so (M ⬝ N) is the redex (ƛ M0) ⬝ N
      -- takahashi ((ƛ M0) ⬝ N) = (takahashi M0)[takahashi N]
      · induction M
        · aesop?
        · aesop?
        · solve_by_elim
  | subst hM hN ihM ihN =>
    -- takahashi ((ƛ M) ⬝ N) = (takahashi M)[takahashi N]
    -- Goal: M'[N'] ⇉ (takahashi M)[takahashi N]
    exact betapar_subst ihM ihN

-- ====================================================================
-- Confluence Theorems
-- ====================================================================

-- Diamond Property for Parallel Reduction
theorem betapar_diamond {n : Nat} {M N1 N2 : Term n} (h1 : M ⇉ N1) (h2 : M ⇉ N2) :
    ∃ D, N1 ⇉ D ∧ N2 ⇉ D :=
  ⟨takahashi M, takahashi_triangle h1, takahashi_triangle h2⟩

-- Full Church-Rosser (Confluence) Theorem for BetaStar
theorem beta_confluence {n : Nat} {M N1 N2 : Term n}
    (h1 : M —→* N1) (h2 : M —→* N2) : BetaJoin N1 N2 := by
  have h1_par : M ⇉* N1 := betapar_star_eq_betastar.mpr h1
  have h2_par : M ⇉* N2 := betapar_star_eq_betastar.mpr h2
  have h_join : ∃ D, N1 ⇉* D ∧ N2 ⇉* D := by
    induction h1_par generalizing N2 with
    | refl =>
      exact ⟨N2, h2_par, Relation.ReflTransGen.refl⟩
    | tail h_head step ih =>
      rcases ih h2_par with ⟨D1, hN1_D1, hN2_D1⟩
      have ⟨D2, hstep_D2, hD1_D2⟩ : ∃ D2, _ ⇉ D2 ∧ D1 ⇉ D2 := by
        sorry -- Strip lemma for parallel reduction
      exact ⟨D2, Relation.ReflTransGen.tail hN1_D1 hstep_D2,
                 Relation.ReflTransGen.tail hN2_D1 hD1_D2⟩
  rcases h_join with ⟨D, hN1_D, hN2_D⟩
  exact ⟨D, betapar_star_eq_betastar.mp hN1_D, betapar_star_eq_betastar.mp hN2_D⟩

/-- The Strip Lemma for Single-Step Beta Reduction:
    If x reduces in 1 step to y and z, they can join within ≤1 step and * steps. -/
theorem beta_strip {n : Nat} (x y z : Term n) (h1 : x —→ y) (h2 : x —→ z) :
    ∃ d, (y —→≤1 d) ∧ (z —→* d) := by
  sorry

-- Church-Rosser for multi-step beta reduction on Terms
theorem beta_church_rosser {n : Nat} {a b c : Term n}
    (hab : a —→* b) (hac : a —→* c) : BetaJoin b c :=
  Relation.church_rosser beta_strip hab hac
