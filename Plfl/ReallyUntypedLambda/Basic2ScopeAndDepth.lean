module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Relation
import Aesop

@[expose] public section

namespace Basic2ScopeAndDepth

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
prefix:100 "v#" => Term.var
macro:100 "v##" n:term:max : term => `(Term.var (Fin.mk $n (by decide)))

namespace Term

-- 1. Identity Function: ƛx. x
-- Type: Term 0
def id : Term 0 1 := ƛ (v#0)

-- 2. Constant Function: ƛx. ƛy. x
-- Type: Term 0
def const : Term 0 2 := ƛ (ƛ (v## 1))

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x
def zero : Term 0 2 := ƛ (ƛ (v#0))

-- One: ƛf. ƛx. f x
def one : Term 0 2 := ƛ (ƛ (v##1 ⬝ v#0))

-- Two: ƛf. ƛx. f (f x)
def two : Term 0 2 := ƛ (ƛ (v##1 ⬝ (v##1 ⬝ v#0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
-- Type: Term 0
def succ : Term 0 3 :=
  ƛ (             -- n is var 2
    ƛ (           -- f is var 1
      ƛ (         -- x is var 0
        v## 1 ⬝
        ((v## 2 ⬝ v## 1) ⬝ v# 0)
      )
    )
  )

-- A term with 2 free variables, depth 0:
def freeTerm : Term 2 0 := v##0 ⬝ v##1

-- A term with 1 free variable, depth 1 (λy. y ⬝ x0):
def boundAndFree : Term 1 1 := ƛ (v# 0 ⬝ v## 1)

namespace BetaWay1


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

-- 1. WEAKENING SUBSTITUTION (n < m)
structure SubstWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → (d : Nat) × Term m d

def SubstWeaken.ext {n m : Nat} (σ : SubstWeaken n m) : SubstWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ σ.lt
  map := Fin.cases ⟨0, v# 0⟩ (fun i => let ⟨d, t⟩ := σ.map i; ⟨d, renameWeaken (RenameWeaken.succ m) t⟩)

def substWeaken {n m : Nat} (σ : SubstWeaken n m) : ∀ {d : Nat}, Term n d → (d' : Nat) × Term m d'
  | _, Term.var i => σ.map i
  | _, ƛ M        => let ⟨d', M'⟩ := substWeaken σ.ext M; ⟨d' + 1, ƛ M'⟩
  | _, M ⬝ N      => let ⟨dM', M'⟩ := substWeaken σ M; let ⟨dN', N'⟩ := substWeaken σ N; ⟨max dM' dN', M' ⬝ N'⟩

-- 2. SAME-SCOPE SUBSTITUTION (n = m)
structure SubstSame (n : Nat) where
  map : Fin n → (d : Nat) × Term n d

def SubstSame.ext {n : Nat} (σ : SubstSame n) : SubstSame (n + 1) where
  map := Fin.cases ⟨0, v# 0⟩ (fun i => let ⟨d, t⟩ := σ.map i; ⟨d, renameWeaken (RenameWeaken.succ n) t⟩)

def substSame {n : Nat} (σ : SubstSame n) : ∀ {d : Nat}, Term n d → (d' : Nat) × Term n d'
  | _, Term.var i => σ.map i
  | _, ƛ M        => let ⟨d', M'⟩ := substSame σ.ext M; ⟨d' + 1, ƛ M'⟩
  | _, M ⬝ N      => let ⟨dM', M'⟩ := substSame σ M; let ⟨dN', N'⟩ := substSame σ N; ⟨max dM' dN', M' ⬝ N'⟩

-- 3. CONTRACTING SUBSTITUTION (n > m)
structure SubstContract (n m : Nat) where
  gt  : n > m
  map : Fin n → (d : Nat) × Term m d

def SubstContract.ext {n m : Nat} (σ : SubstContract n m) : SubstContract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ σ.gt
  map := Fin.cases ⟨0, v# 0⟩ (fun i => let ⟨d, t⟩ := σ.map i; ⟨d, renameWeaken (RenameWeaken.succ m) t⟩)

def substContract {n m : Nat} (σ : SubstContract n m) : ∀ {d : Nat}, Term n d → (d' : Nat) × Term m d'
  | _, Term.var i =>
    σ.map i
  | _, ƛ M =>
    let ⟨d', M'⟩ := substContract σ.ext M;
    ⟨d' + 1, ƛ M'⟩
  | _, M ⬝ N =>
    let ⟨dM', M'⟩ := substContract σ M;
    let ⟨dN', N'⟩ := substContract σ N;
    ⟨max dM' dN', M' ⬝ N'⟩

-- Substitution of top variable (Fin (n+1) → Σ d, Term n d)
def mkSubstZero {n dN : Nat} (N : Term n dN) : SubstContract (n + 1) n where
  gt  := Nat.lt_succ_self n
  map := Fin.cases ⟨dN, N⟩ (fun i => ⟨0, v# i⟩)

end BetaWay1

def size : Term n d → Nat
  | Term.var _ => 1
  | ƛ P => 1 + P.size
  | P ⬝ Q => 1 + P.size + Q.size

namespace BetaWay2

----- RUNNER PATTERN
def betaSubstGo
  (targetIndex : Nat)
  {outerScope argDepth : Nat}
  (argTerm : Term outerScope argDepth)
  (h_target : targetIndex ≤ outerScope) :
  ∀ {bodyDepth : Nat},
  Term (outerScope + 1) bodyDepth →
  (resultDepth : Nat) × Term outerScope resultDepth
  | _, Term.var varIdx =>
      if h_eq : varIdx.val = targetIndex then
        ⟨argDepth, argTerm⟩
      else if h_gt : varIdx.val > targetIndex then
        ⟨0, Term.var ⟨varIdx.val - 1, by omega⟩⟩
      else
        ⟨0, Term.var ⟨varIdx.val, by omega⟩⟩
  | _, ƛ body =>
      let shiftedArg := BetaWay1.renameWeaken (BetaWay1.RenameWeaken.succ outerScope) argTerm
      let ⟨substBodyDepth, substBody⟩ := betaSubstGo (targetIndex + 1) shiftedArg (by omega) body
      ⟨substBodyDepth + 1, ƛ substBody⟩
  | _, leftBody ⬝ rightBody =>
      let ⟨leftDepth, leftSubst⟩ := betaSubstGo targetIndex argTerm h_target leftBody
      let ⟨rightDepth, rightSubst⟩ := betaSubstGo targetIndex argTerm h_target rightBody
      ⟨max leftDepth rightDepth, leftSubst ⬝ rightSubst⟩
termination_by _ bodyTerm => bodyTerm.size
decreasing_by (all_goals (simp [Term.size]; try omega))

end BetaWay2

-- Non-recursive helper for shiftGo abs case:
-- casts Term ((n+1)+i) d to Term ((n+i)+1) d (avoids ▸ in recursive body)
def shiftCast (n i d : Nat) (t : Term ((n + 1) + i) d) : Term ((n + i) + 1) d :=
  (show (n + 1) + i = (n + i) + 1 from by omega) ▸ t

namespace BetaWay3

-- shift c i: shift all free variables ≥ c upward by i positions
-- Takes n explicitly for WF recursion; returns Term (n+i) d.
def shiftGo (c i : Nat) :
    ∀ (n : Nat) {d : Nat}, Term n d → Term (n + i) d
  | n, _, Term.var v =>
    if v.val < c then Term.var ⟨v.val, by omega⟩
    else Term.var ⟨v.val + i, by omega⟩
  | n, _, ƛ M =>
    -- shiftGo (c+1) i (n+1) M : Term ((n+1)+i) d
    -- shiftCast maps that to Term ((n+i)+1) d so ƛ gives Term (n+i) (d+1)
    ƛ (shiftCast n i _ (shiftGo (c + 1) i (n + 1) M))
  | _, _, M ⬝ N =>
    shiftGo c i _ M ⬝ shiftGo c i _ N
termination_by n _ t => t.size
decreasing_by
  all_goals simp [Term.size]
  simp +arith only
  simp +arith only

def shift (c i : Nat) {n d : Nat} (t : Term n d) : Term (n + i) d :=
  shiftGo c i n t

-- Danelnov-style ↑ notation
notation:70 "↑" => shift

-- subst k e v: substitute e for variable k in v
-- Returns sigma-pair since the depth changes
def substGo {n dN : Nat} (k : Nat) (e : Term n dN) :
    ∀ {dM : Nat}, Term n dM → (d' : Nat) × Term n d'
  | _, Term.var i =>
    if i.val = k then ⟨dN, e⟩ else ⟨0, Term.var i⟩
  | _, ƛ M =>
    let ⟨d', M'⟩ := substGo (k + 1) ((↑) 0 1 e) M
    ⟨d' + 1, ƛ M'⟩
  | _, M ⬝ N =>
    let ⟨dM', M'⟩ := substGo k e M
    let ⟨dN', N'⟩ := substGo k e N
    ⟨max dM' dN', M' ⬝ N'⟩
termination_by _ t => t.size
decreasing_by
  all_goals simp [Term.size]
  simp +arith only
  simp +arith only

def subst {n dM dN : Nat} (v : Term n dM) (k : Nat) (e : Term n dN) : (d' : Nat) × Term n d' :=
  substGo k e v

notation t "[" k " := " s "]" => subst t k s

-- Non-recursive helper for unshiftGo abs case:
-- casts Term ((n+i)+1) d to Term ((n+1)+i) d (avoids ▸ in recursive body)
def unshiftCast (n i d : Nat) (M : Term ((n + i) + 1) d) : Term ((n + 1) + i) d :=
  (show (n + i) + 1 = (n + 1) + i from by omega) ▸ M

-- unshift c i: inverse of shift. Returns sigma (Term n d') from Term (n+i) d.
-- All of shift/subst/unshift follow the Danelnov pattern using existentials.
-- Takes n explicitly for WF recursion.
def unshiftGo (c i : Nat) :
    ∀ (n : Nat) {d : Nat}, Term (n + i) d → (d' : Nat) × Term n d'
  | n, _, Term.var v =>
    if h : v.val < c then
      -- Protected var: must land at same index (valid when c ≤ n)
      if h2 : v.val < n then ⟨0, Term.var ⟨v.val, h2⟩⟩
      else if h3 : 0 < n then ⟨0, Term.var ⟨0, h3⟩⟩
      -- n = 0: unreachable in well-typed beta; return dummy closed term
      else ⟨1, ƛ (Term.var ⟨0, by simp_all only [not_lt, Nat.le_zero_eq, Nat.zero_add, Nat.lt_add_one]⟩)⟩
    else
      -- Shifted var: subtract i. When 0 < n: v.val - i < n from v.val < n+i.
      if h3 : 0 < n then ⟨0, Term.var ⟨v.val - i, by have := v.isLt; omega⟩⟩
      -- n = 0: unreachable for well-typed beta; return dummy closed term
      else ⟨1, ƛ (Term.var ⟨0, by simp_all only [not_lt, Nat.le_zero_eq, Nat.zero_add, Nat.lt_add_one]⟩)⟩
  | n, _, ƛ M =>
    -- M : Term ((n+i)+1) d. unshiftCast maps to Term ((n+1)+i) d.
    -- Recursive call reduces scope from (n+1)+i to n+1.
    let ⟨d', M'⟩ := unshiftGo (c + 1) i (n + 1) (unshiftCast n i _ M)
    ⟨d' + 1, ƛ M'⟩
  | _, _, M ⬝ N =>
    let ⟨dM', M'⟩ := unshiftGo c i _ M
    let ⟨dN', N'⟩ := unshiftGo c i _ N
    ⟨max dM' dN', M' ⬝ N'⟩
termination_by n _ t => t.size
decreasing_by
  all_goals simp [Term.size]
  grind [= size, = unshiftCast]
  simp +arith only
  simp +arith only

-- unshiftPair: lift unshiftGo to sigma-pairs
-- (↓) c i : (Σ d, Term (n+i) d) → (Σ d', Term n d')
def unshiftPair (c i : Nat) {n : Nat} (p : (d' : Nat) × Term (n + i) d') : (d' : Nat) × Term n d' :=
  unshiftGo c i n p.2

-- Danelnov-style ↓ notation
notation:70 "↓" => unshiftPair

def beta {n dM dN : Nat} (M : Term (n + 1) dM) (N : Term n dN) : (d' : Nat) × Term n d' :=
  (↓) 0 1 (M[0 := (↑) 0 1 N])

end BetaWay3

-- beta reduction: (λ M) N → M[N]
-- Danelnov structure: shift N up by 1, substitute into M at var 0, unshift result by 1

-- will subst vars with 0 with target term and -1 all others
def betaSubst {n dM dN : Nat} (M : Term (n + 1) dM) (N : Term n dN) : (d' : Nat) × Term n d' :=
  -- CAN USE THIS INSTEAD
  -- substContract (BetaWay1.mkSubstZero N) M
  -- OR THIS
  -- BetaWay2.betaSubstGo 0 N (by omega) M
  -- OR THIS
  BetaWay3.beta M N

end Term

-- notation:70 M " [" N "]" => (Term.betaSubst M N).2 -- impossible
macro:70 M:term "[" N:term "]" : term => `((Term.betaSubst $M $N).2)

-- Standard Single-Step Beta Reduction (Beta)
inductive Beta : ∀ {n d1 d2 : Nat}, Term n d1 → Term n d2 → Prop where
  | basis {n dM dN : Nat} (M : Term (n + 1) dM) (N : Term n dN) :
      Beta ((ƛ M) ⬝ N) (M[N])
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
      BetaP (v# i) (v# i)
  | abs {n d1 d2 : Nat} {M : Term (n + 1) d1} {N : Term (n + 1) d2} :
      BetaP M N → BetaP (ƛ M) (ƛ N)
  | app {n dM dM' dN dN' : Nat} {M : Term n dM} {M' : Term n dM'} {N : Term n dN} {N' : Term n dN'} :
      BetaP M M' → BetaP N N' → BetaP (M ⬝ N) (M' ⬝ N')
  | subst {n dM dM' dN dN' : Nat} {M : Term (n + 1) dM} {M' : Term (n + 1) dM'} {N : Term n dN} {N' : Term n dN'} :
      BetaP M M' → BetaP N N' → BetaP ((ƛ M) ⬝ N) (M'[N'])

infixl:65 " →βp " => BetaP

-- Reflexivity of Parallel Reduction
@[refl]
theorem betap_refl {n d : Nat} (N : Term n d) : N →βp N := by
  induction N with
  | var i => exact BetaP.var i
  | abs M ih => exact BetaP.abs ih
  | app M N ihM ihN => exact BetaP.app ihM ihN

end Basic2ScopeAndDepth
