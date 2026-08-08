-- https://github.com/iwilare/church-rosser/blob/main/DeBruijn.agda
--
-- Intrinsically exact-scoped de Bruijn lambda terms, with substitution and beta
-- reduction implemented by *direct structural recursion on the terms* -- there
-- is no auxiliary raw/extrinsic syntax anywhere in this development.
--
-- The one thing the exact-scope discipline forces is that the scope of the
-- result of a substitution cannot be imposed in advance: substituting into a
-- term of scope `n` may *decrease* the number of free indexes.  So every
-- operation returns its scope existentially, as a
--
--     Sigma  newFreeIndexes  betaReducedTermTree   :   Σ n, Term n
--
-- which is the type `Scoped` below.  Beta reduction is a relation on `Scoped`,
-- and it is confluent: see `Scoped.beta_church_rosser`.  (The Standardization
-- theorem is proved in `IwilareNatIsExactScope/Standardization.lean`.)
module

public import Aesop
public import Mathlib.Logic.Relation

@[expose] public section

namespace IwilareNatIsExactScope

-- 1. Intrinsically exact-scoped Lambda terms parameterized by exact scope size `n : Nat`
--    n = 0 <==> 100% statically CLOSED term (uses 0 free variables)
--    n > 0 <==> 100% statically OPEN term (uses free variables with maximum index n - 1)
inductive Term : Nat → Type
  | var : (i : Nat) → Term (i + 1)
  | abs : ∀ {n : Nat}, Term n → Term (n - 1)
  | app : ∀ {n m : Nat}, Term n → Term m → Term (max n m)

prefix:71 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:72 "v#" => Term.var
macro:72 "v##" n:term:max : term => `(Term.var $n)

namespace Term

-- 1. Identity Function: ƛx. x
-- Statically 100% CLOSED: Term 0
def id : Term 0 := ƛ v#0

-- 2. Constant Function: ƛx. ƛy. x
-- Statically 100% CLOSED: Term 0
def const : Term 0 := ƛ (ƛ v##1)

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x (Term 0)
def zero : Term 0 := ƛ (ƛ (v#0))

-- One: ƛf. ƛx. f x (Term 0)
def one : Term 0 := ƛ (ƛ (v##1 ⬝ v#0))

-- Two: ƛf. ƛx. f (f x) (Term 0)
def two : Term 0 := ƛ (ƛ (v##1 ⬝ (v##1 ⬝ v#0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x) (Term 0)
def succ : Term 0 :=
  ƛ (
    ƛ (
      ƛ (
        v##1 ⬝
        ((v##2 ⬝ v##1) ⬝ v#0)
      )
    )
  )

-- A term with 2 free variables: (x0 x1) -> Statically OPEN (Term 2)
def freeTerm : Term 2 := v##0 ⬝ v##1

-- A term with 1 free variable (x0): λy. (y x0) -> Statically OPEN (Term 1)
def boundAndFree : Term 1 := ƛ (v#0 ⬝ v##1)

-- ====================================================================
-- The index `n` is exactly the number of free indexes, as advertised:
--   n = 0  <==>  the term is closed
--   n > 0  <==>  every free index is < n, and the index n - 1 does occur
-- ====================================================================

/-- `occurs i t` : the free de Bruijn index `i` really occurs in `t`. -/
def occurs : {n : Nat} → Nat → Term n → Prop
  | _, i, var j => j = i
  | _, i, abs t => occurs (i + 1) t
  | _, i, app a b => occurs i a ∨ occurs i b

/-- Every free index of a `Term n` is `< n`. -/
theorem free_lt_scope {n : Nat} (t : Term n) : ∀ {i : Nat}, occurs i t → i < n := by
  induction t with
  | var j =>
      intro i h
      have h' : j = i := h
      omega
  | abs t ih =>
      intro i h
      have := ih (show occurs (i + 1) t from h)
      omega
  | app a b iha ihb =>
      intro i h
      rcases (show occurs i a ∨ occurs i b from h) with h | h
      · have := iha h; omega
      · have := ihb h; omega

/-- For `n > 0` the maximal index `n - 1` really is used. -/
theorem max_free_occurs {n : Nat} (t : Term n) : 0 < n → occurs (n - 1) t := by
  induction t with
  | var j => intro _; rfl
  | @abs n t ih =>
      intro h
      show occurs (n - 1 - 1 + 1) t
      rw [show n - 1 - 1 + 1 = n - 1 from by omega]
      exact ih (by omega)
  | @app n m a b iha ihb =>
      intro h
      show occurs (max n m - 1) a ∨ occurs (max n m - 1) b
      rcases Nat.le_total n m with hnm | hnm
      · right
        rw [show max n m = m from by omega]
        exact ihb (by omega)
      · left
        rw [show max n m = n from by omega]
        exact iha (by omega)

/-- `n = 0` if and only if the term is closed. -/
theorem closed_iff_scope_zero {n : Nat} (t : Term n) :
    n = 0 ↔ ∀ i, ¬ occurs i t := by
  constructor
  · intro h i hi
    have := free_lt_scope t hi
    omega
  · intro h
    by_cases hn : n = 0
    · exact hn
    · exact (h (n - 1) (max_free_occurs t (by omega))).elim

end Term


-- ====================================================================
-- 2. Existentially scoped terms
--
-- Substitution into a `Term n` may *decrease* the number of free indexes, so
-- its scope cannot be imposed in advance: it is returned together with the
-- term, as a pair `⟨newFreeIndexes, betaReducedTermTree⟩ : Σ n, Term n`.
-- ====================================================================

/-- A lambda term whose exact number of free indexes is carried existentially. -/
abbrev Scoped : Type := Σ n : Nat, Term n

namespace Scoped

/-- The exact number of free indexes of the term (`0` iff the term is closed). -/
abbrev newFreeIndexes (s : Scoped) : Nat := s.1

/-- The term tree itself, of scope exactly `s.newFreeIndexes`. -/
abbrev betaReducedTermTree (s : Scoped) : Term s.newFreeIndexes := s.2

/-- Existential variable. -/
abbrev var (i : Nat) : Scoped := ⟨i + 1, Term.var i⟩

/-- Existential abstraction: binding a variable removes one free index. -/
abbrev abs (s : Scoped) : Scoped := ⟨s.1 - 1, Term.abs s.2⟩

/-- Existential application. -/
abbrev app (s t : Scoped) : Scoped := ⟨max s.1 t.1, Term.app s.2 t.2⟩

end Scoped

-- ====================================================================
-- `Scoped` is a term algebra: its three constructors are injective, pairwise
-- disjoint, and generate everything.  All of this comes straight from
-- injectivity of `Sigma.mk` together with the no-confusion principle of
-- `Term` -- no auxiliary one-layer view type is needed.
-- ====================================================================

namespace Scoped

@[simp] theorem var_eq_var {i j : Nat} : var i = var j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  injection h with h₁ h₂
  exact Term.noConfusion h₁ h₂ (fun h => h)

@[simp] theorem abs_eq_abs {s t : Scoped} : abs s = abs t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨n, a⟩ := s; obtain ⟨m, b⟩ := t
  injection h with h₁ h₂
  exact Term.noConfusion h₁ h₂ (fun hn ha => by cases hn; cases ha; rfl)

@[simp] theorem app_eq_app {a b c d : Scoped} : app a b = app c d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  obtain ⟨n, x⟩ := a; obtain ⟨m, y⟩ := b; obtain ⟨p, z⟩ := c; obtain ⟨q, w⟩ := d
  injection h with h₁ h₂
  exact Term.noConfusion h₁ h₂
    (fun hn hm hx hy => by cases hn; cases hm; cases hx; cases hy; exact ⟨rfl, rfl⟩)

@[simp] theorem var_ne_abs {i : Nat} {s : Scoped} : var i ≠ abs s := by
  intro h; obtain ⟨n, a⟩ := s; injection h with h₁ h₂; exact Term.noConfusion h₁ h₂

@[simp] theorem abs_ne_var {i : Nat} {s : Scoped} : abs s ≠ var i :=
  fun h => var_ne_abs h.symm

@[simp] theorem var_ne_app {i : Nat} {s t : Scoped} : var i ≠ app s t := by
  intro h; injection h with h₁ h₂; exact Term.noConfusion h₁ h₂

@[simp] theorem app_ne_var {i : Nat} {s t : Scoped} : app s t ≠ var i :=
  fun h => var_ne_app h.symm

@[simp] theorem abs_ne_app {s a b : Scoped} : abs s ≠ app a b := by
  intro h; obtain ⟨n, x⟩ := s; injection h with h₁ h₂; exact Term.noConfusion h₁ h₂

@[simp] theorem app_ne_abs {s a b : Scoped} : app a b ≠ abs s :=
  fun h => abs_ne_app h.symm

/-- Structural induction for existentially scoped terms. -/
@[elab_as_elim] theorem ind {P : Scoped → Prop}
    (var : ∀ i, P (Scoped.var i))
    (abs : ∀ s, P s → P (Scoped.abs s))
    (app : ∀ s t, P s → P t → P (Scoped.app s t)) : ∀ s, P s := by
  rintro ⟨n, t⟩
  induction t with
  | var i => exact var i
  | abs t ih => exact abs ⟨_, t⟩ ih
  | app a b iha ihb => exact app ⟨_, a⟩ ⟨_, b⟩ iha ihb

/-- Every existentially scoped term is a variable, an abstraction, or an application. -/
theorem cases' (s : Scoped) :
    (∃ i, s = var i) ∨ (∃ p, s = abs p) ∨ (∃ a b, s = app a b) := by
  induction s using Scoped.ind with
  | var i => exact Or.inl ⟨i, rfl⟩
  | abs s _ => exact Or.inr (Or.inl ⟨s, rfl⟩)
  | app a b _ _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)

end Scoped


-- ====================================================================
-- 3. The de Bruijn substitution algebra on `Scoped`
--
-- Renaming and parallel substitution, again by direct structural recursion on
-- `Term`, with the resulting scope returned existentially.
-- ====================================================================

namespace Scoped

/-- Lifting a renaming under a binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

end Scoped

namespace Term

/-- Renaming (capture-avoiding, thanks to `Scoped.upRen`). -/
def renS : {n : Nat} → (Nat → Nat) → Term n → Scoped
  | _, ρ, var i => Scoped.var (ρ i)
  | _, ρ, abs t => Scoped.abs (renS (Scoped.upRen ρ) t)
  | _, ρ, app a b => Scoped.app (renS ρ a) (renS ρ b)

end Term

namespace Scoped

/-- Renaming of an existentially scoped term. -/
def ren (ρ : Nat → Nat) (s : Scoped) : Scoped := Term.renS ρ s.2

@[simp] theorem ren_var (ρ : Nat → Nat) (i : Nat) : ren ρ (var i) = var (ρ i) := rfl
@[simp] theorem ren_abs (ρ : Nat → Nat) (s : Scoped) :
    ren ρ (abs s) = abs (ren (upRen ρ) s) := rfl
@[simp] theorem ren_app (ρ : Nat → Nat) (s t : Scoped) :
    ren ρ (app s t) = app (ren ρ s) (ren ρ t) := rfl

/-- Lifting a substitution under a binder. -/
def upSub (σ : Nat → Scoped) : Nat → Scoped
  | 0 => var 0
  | i + 1 => ren Nat.succ (σ i)

end Scoped

namespace Term

/-- Parallel (simultaneous) substitution. -/
def subS : {n : Nat} → (Nat → Scoped) → Term n → Scoped
  | _, σ, var i => σ i
  | _, σ, abs t => Scoped.abs (subS (Scoped.upSub σ) t)
  | _, σ, app a b => Scoped.app (subS σ a) (subS σ b)

end Term

namespace Scoped

/-- Parallel substitution on an existentially scoped term. -/
def sub (σ : Nat → Scoped) (s : Scoped) : Scoped := Term.subS σ s.2

@[simp] theorem sub_var' (σ : Nat → Scoped) (i : Nat) : sub σ (var i) = σ i := rfl
@[simp] theorem sub_abs (σ : Nat → Scoped) (s : Scoped) :
    sub σ (abs s) = abs (sub (upSub σ) s) := rfl
@[simp] theorem sub_app (σ : Nat → Scoped) (s t : Scoped) :
    sub σ (app s t) = app (sub σ s) (sub σ t) := rfl

/-- `cons N σ` sends `0` to `N` and `i + 1` to `σ i`. -/
def cons (N : Scoped) (σ : Nat → Scoped) : Nat → Scoped
  | 0 => N
  | i + 1 => σ i

/-- The one-variable substitution used by beta reduction. -/
abbrev sub0 (N s : Scoped) : Scoped := sub (cons N var) s

theorem upRen_comp (ρ ρ' : Nat → Nat) :
    upRen (fun i => ρ (ρ' i)) = fun i => upRen ρ (upRen ρ' i) := by
  funext i; cases i <;> rfl

theorem ren_ren (r : Scoped) : ∀ (ρ ρ' : Nat → Nat),
    ren ρ (ren ρ' r) = ren (fun i => ρ (ρ' i)) r := by
  induction r using Scoped.ind with
  | var i => intro ρ ρ'; rfl
  | abs r ih => intro ρ ρ'; simp [ih, upRen_comp]
  | app a b iha ihb => intro ρ ρ'; simp [iha, ihb]

theorem ren_id (r : Scoped) : ren (fun i => i) r = r := by
  induction r using Scoped.ind with
  | var i => rfl
  | abs r ih =>
      have h : upRen (fun i => i) = fun i => i := by funext i; cases i <;> rfl
      simp only [ren_abs, h, ih]
  | app a b iha ihb => simp [iha, ihb]

theorem upSub_ren (ρ : Nat → Nat) (σ : Nat → Scoped) :
    upSub (fun i => ren ρ (σ i)) = fun i => ren (upRen ρ) (upSub σ i) := by
  funext i
  cases i with
  | zero => rfl
  | succ j => simp [upSub, ren_ren, upRen]

theorem ren_sub (r : Scoped) : ∀ (ρ : Nat → Nat) (σ : Nat → Scoped),
    ren ρ (sub σ r) = sub (fun i => ren ρ (σ i)) r := by
  induction r using Scoped.ind with
  | var i => intro ρ σ; rfl
  | abs r ih => intro ρ σ; simp [ih, upSub_ren]
  | app a b iha ihb => intro ρ σ; simp [iha, ihb]

theorem sub_ren (r : Scoped) : ∀ (ρ : Nat → Nat) (σ : Nat → Scoped),
    sub σ (ren ρ r) = sub (fun i => σ (ρ i)) r := by
  induction r using Scoped.ind with
  | var i => intro ρ σ; rfl
  | abs r ih =>
      intro ρ σ
      have hup : (fun i => upSub σ (upRen ρ i)) = upSub (fun i => σ (ρ i)) := by
        funext i; cases i <;> rfl
      simp only [ren_abs, sub_abs, ih, hup]
  | app a b iha ihb => intro ρ σ; simp [iha, ihb]

theorem sub_sub (r : Scoped) : ∀ (σ τ : Nat → Scoped),
    sub σ (sub τ r) = sub (fun i => sub σ (τ i)) r := by
  induction r using Scoped.ind with
  | var i => intro σ τ; rfl
  | abs r ih =>
      intro σ τ
      have hup : (fun i => sub (upSub σ) (upSub τ i)) = upSub (fun i => sub σ (τ i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ j => simp [upSub, ren_sub, sub_ren]
      simp only [sub_abs, ih, hup]
  | app a b iha ihb => intro σ τ; simp [iha, ihb]

theorem sub_var (r : Scoped) : sub var r = r := by
  induction r using Scoped.ind with
  | var i => rfl
  | abs r ih =>
      have hup : upSub var = var := by funext i; cases i <;> rfl
      simp only [sub_abs, hup, ih]
  | app a b iha ihb => simp [iha, ihb]

/-- Renaming commutes with a one-variable substitution. -/
theorem ren_sub0 (ρ : Nat → Nat) (q p : Scoped) :
    ren ρ (sub0 q p) = sub0 (ren ρ q) (ren (upRen ρ) p) := by
  rw [sub0, sub0, ren_sub, sub_ren]
  congr 1
  funext i
  cases i <;> rfl

/-- Substituting for the index `0` of a shifted term does nothing: the shifted
    term has no free occurrence of `0`. -/
theorem sub0_ren_succ (N s : Scoped) : sub0 N (ren Nat.succ s) = s := by
  rw [sub0, sub_ren]
  have h : (fun i => cons N var (i + 1)) = var := by funext i; rfl
  rw [h, sub_var]

/-- Substituting under a binder into a shifted term is shifting the
    substitution. -/
theorem sub_upSub_ren_succ (σ : Nat → Scoped) (s : Scoped) :
    sub (upSub σ) (ren Nat.succ s) = ren Nat.succ (sub σ s) := by
  rw [sub_ren, ren_sub]
  rfl

theorem upSub_var_comp (ρ : Nat → Nat) :
    upSub (fun i => var (ρ i)) = fun i => var (upRen ρ i) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => rfl

/-- A substitution by variables only is a renaming. -/
theorem sub_var_comp (s : Scoped) : ∀ ρ : Nat → Nat,
    sub (fun i => var (ρ i)) s = ren ρ s := by
  induction s using Scoped.ind with
  | var i => intro ρ; rfl
  | abs s ih => intro ρ; rw [sub_abs, ren_abs, upSub_var_comp, ih]
  | app a b iha ihb => intro ρ; rw [sub_app, ren_app, iha, ihb]

/-- The substitution lemma, in the form needed for parallel reduction. -/
theorem sub_sub0 (σ : Nat → Scoped) (q p : Scoped) :
    sub σ (sub0 q p) = sub0 (sub σ q) (sub (upSub σ) p) := by
  rw [sub0, sub0, sub_sub, sub_sub]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ j => simp [cons, upSub, sub_ren, sub_var]

end Scoped

-- ====================================================================
-- 4. Shifting and beta substitution: THE implementation
--
-- `shiftAt` / `substAt` / `betaSubstSigma` are defined by direct structural
-- recursion on `Term n` and return the new number of free indexes together
-- with the resulting term tree.  They are shown below to compute exactly the
-- usual de Bruijn renaming and substitution (`substAt_eq_sub`,
-- `betaSubstSigma_eq_sub0`), which is what the metatheory then uses.
-- ====================================================================

namespace Term

/-- `shiftAt d t` increments every free index of `t` that is `≥ d`, returning the
    new scope existentially.  (Note that this is *not* a map `Term n → Term (n+1)`:
    a closed term stays closed.) -/
def shiftAt : {n : Nat} → Nat → Term n → Scoped
  | _, d, var i => if i < d then Scoped.var i else Scoped.var (i + 1)
  | _, d, abs t => Scoped.abs (shiftAt (d + 1) t)
  | _, d, app a b => Scoped.app (shiftAt d a) (shiftAt d b)

/-- Shift all free indexes of an existentially scoped term. -/
def shift (s : Scoped) : Scoped := shiftAt 0 s.2

/-- `substAt d N t` replaces the free index `d` of `t` by `N` and decrements
    every free index above `d`.  It is capture-avoiding: `N` is shifted every
    time a binder is crossed. -/
def substAt : {n : Nat} → Nat → Scoped → Term n → Scoped
  | _, d, N, var i =>
      if i < d then Scoped.var i else if i = d then N else Scoped.var (i - 1)
  | _, d, N, abs t => Scoped.abs (substAt (d + 1) (shift N) t)
  | _, d, N, app a b => Scoped.app (substAt d N a) (substAt d N b)

/-- **Beta substitution**: substitute `N` for the index `0` of `M`, returning the
    new number of free indexes together with the reduced term tree.  No
    constraint whatsoever relates the scopes of `M` and `N`. -/
def betaSubstSigma {m n : Nat} (M : Term m) (N : Term n) : Scoped :=
  substAt 0 ⟨n, N⟩ M

end Term

@[inherit_doc] notation:70 M " ⟦" N "⟧" => Term.betaSubstSigma M N
@[inherit_doc] notation:70 M " [" N "]" => Term.betaSubstSigma M N

-- A few computations (all by `rfl`).
example : (v#0 : Term 1)[Term.id] = ⟨0, Term.id⟩ := rfl
example : (v##1 : Term 2)[(v##0 : Term 1)] = ⟨1, v##0⟩ := rfl
example : ((ƛ v##2) : Term 2)[(v##0 : Term 1)] = ⟨1, ƛ v##1⟩ := rfl
example : (v##0 ⬝ v##1 : Term 2)[(v##0 : Term 1)] = ⟨1, v##0 ⬝ v##0⟩ := rfl
-- The argument may be dropped, in which case the scope *decreases*:
example : (v##1 : Term 2)[(v##3 : Term 4)] = ⟨1, v##0⟩ := rfl

namespace Scoped

/-- Shifting of an existentially scoped term. -/
def shiftAt (d : Nat) (s : Scoped) : Scoped := Term.shiftAt d s.2

/-- Substitution into an existentially scoped term. -/
def substAt (d : Nat) (N s : Scoped) : Scoped := Term.substAt d N s.2

@[simp] theorem shiftAt_var (d i : Nat) :
    shiftAt d (var i) = if i < d then var i else var (i + 1) := rfl
@[simp] theorem shiftAt_abs (d : Nat) (s : Scoped) :
    shiftAt d (abs s) = abs (shiftAt (d + 1) s) := rfl
@[simp] theorem shiftAt_app (d : Nat) (s t : Scoped) :
    shiftAt d (app s t) = app (shiftAt d s) (shiftAt d t) := rfl

@[simp] theorem substAt_var (d i : Nat) (N : Scoped) :
    substAt d N (var i) = if i < d then var i else if i = d then N else var (i - 1) := rfl
@[simp] theorem substAt_abs (d : Nat) (N s : Scoped) :
    substAt d N (abs s) = abs (substAt (d + 1) (shiftAt 0 N) s) := rfl
@[simp] theorem substAt_app (d : Nat) (N s t : Scoped) :
    substAt d N (app s t) = app (substAt d N s) (substAt d N t) := rfl

/-- The renaming performed by `shiftAt d`. -/
def rshift (d : Nat) : Nat → Nat := fun i => if i < d then i else i + 1

theorem upRen_rshift (d : Nat) : upRen (rshift d) = rshift (d + 1) := by
  funext i
  cases i with
  | zero => simp [upRen, rshift]
  | succ j => by_cases h : j < d <;> simp [upRen, rshift, h]

theorem shiftAt_eq_ren (s : Scoped) : ∀ d : Nat, shiftAt d s = ren (rshift d) s := by
  induction s using Scoped.ind with
  | var i => intro d; by_cases h : i < d <;> simp [rshift, h]
  | abs s ih => intro d; simp [ih, upRen_rshift]
  | app a b iha ihb => intro d; simp [iha, ihb]

theorem rshift_zero : rshift 0 = Nat.succ := by
  funext i; simp [rshift]

theorem shift_eq_ren (s : Scoped) : shiftAt 0 s = ren Nat.succ s := by
  rw [shiftAt_eq_ren, rshift_zero]

/-- The parallel substitution performed by `substAt d N`. -/
def sigma0 (d : Nat) (N : Scoped) : Nat → Scoped :=
  fun i => if i < d then var i else if i = d then N else var (i - 1)

theorem upSub_sigma0 (d : Nat) (N : Scoped) :
    upSub (sigma0 d N) = sigma0 (d + 1) (ren Nat.succ N) := by
  funext i
  cases i with
  | zero => simp [upSub, sigma0]
  | succ j =>
      by_cases h1 : j < d
      · simp [upSub, sigma0, h1, Nat.succ_lt_succ h1]
      · by_cases h2 : j = d
        · subst h2
          simp [upSub, sigma0]
        · have hj : 0 < j := by omega
          simp only [upSub, sigma0, if_neg h1, if_neg h2,
            if_neg (show ¬ (j + 1 < d + 1) by omega),
            if_neg (show ¬ (j + 1 = d + 1) by omega)]
          rw [ren_var]
          congr 1
          omega

theorem substAt_eq_sub (s : Scoped) : ∀ (d : Nat) (N : Scoped),
    substAt d N s = sub (sigma0 d N) s := by
  induction s using Scoped.ind with
  | var i => intro d N; simp [sigma0]
  | abs s ih => intro d N; simp [ih, shift_eq_ren, upSub_sigma0]
  | app a b iha ihb => intro d N; simp [iha, ihb]

/-- The one-variable substitution `sigma0 0 N` is exactly `cons N var`. -/
theorem sigma0_zero (N : Scoped) : sigma0 0 N = cons N var := by
  funext i
  cases i <;> simp [sigma0, cons]

end Scoped

/-- **Beta substitution is de Bruijn substitution**: the structurally defined
    `betaSubstSigma` computes the usual one-variable parallel substitution. -/
theorem Term.betaSubstSigma_eq_sub0 {m n : Nat} (M : Term m) (N : Term n) :
    M ⟦N⟧ = Scoped.sub0 ⟨n, N⟩ ⟨m, M⟩ := by
  show Scoped.substAt 0 ⟨n, N⟩ ⟨m, M⟩ = _
  rw [Scoped.substAt_eq_sub, Scoped.sigma0_zero]

-- ====================================================================
-- 5. Beta reduction
--
-- https://github.com/iwilare/church-rosser/blob/main/Beta.agda
--
-- The redex rule puts NO constraint on the scopes of the body `M` and of the
-- argument `N`: the scope of the contractum is whatever `betaSubstSigma`
-- computes it to be.  This is what makes the calculus closed under reduction,
-- and hence confluent.
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→" => Beta -- the std → and -> have binding power 25

/-- Standard single-step beta reduction. -/
inductive Beta : Scoped → Scoped → Prop
  | appl (L : Scoped) {M N : Scoped} :
      M —→ N
      --------------------
      → L.app M —→ L.app N
  | appr (L : Scoped) {M N : Scoped} :
      M —→ N
      --------------------
      → M.app L —→ N.app L
  | abs {M N : Scoped} :
      M —→ N
      --------------------
      → M.abs —→ N.abs
  | basis {m n : Nat} (M : Term m) (N : Term n) :
      --------------------
      Scoped.app (Scoped.abs ⟨m, M⟩) ⟨n, N⟩ —→ M ⟦N⟧

infixl:65 "—→-ξₗ" => Beta.appr
infixl:65 "—→-ξᵣ" => Beta.appl
prefix:65 "—→-ƛ " => Beta.abs
infixl:65 "—→-β"  => Beta.basis

theorem step_test {t1 t2 : Scoped} (h : t1 —→ t2) : True :=
  match h with
  | L —→-ξₗ h' => True.intro
  | L —→-ξᵣ h' => True.intro
  | —→-ƛ h'   => True.intro
  | M —→-β N  => True.intro

/-- The redex rule, stated with the one-variable parallel substitution. -/
theorem Beta.basis' (M N : Scoped) : Scoped.app (Scoped.abs M) N —→ Scoped.sub0 N M := by
  have h := Beta.basis M.2 N.2
  rwa [Term.betaSubstSigma_eq_sub0] at h

abbrev BetaStar : Scoped → Scoped → Prop := Relation.ReflTransGen Beta
infix:64 " —→* " => BetaStar -- in original repo —↠

-- ====================================================================
-- Congruence lemmas for multi-step reduction
-- ====================================================================

theorem beta_star_abs {M N : Scoped} (h : M —→* N) : M.abs —→* N.abs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.abs step)

theorem beta_star_appr {M M' : Scoped} (N : Scoped) (h : M —→* M') :
    M.app N —→* M'.app N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appr N step)

theorem beta_star_appl {N N' : Scoped} (M : Scoped) (h : N —→* N') :
    M.app N —→* M.app N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appl M step)

-- ====================================================================
-- 6. Parallel beta reduction
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "⇉" => BetaPar -- the std → and -> have binding power 25

/-- Parallel beta reduction: contract any set of redexes simultaneously. -/
inductive BetaPar : Scoped → Scoped → Prop
  | var (i : Nat)
      ---------
      : Scoped.var i ⇉ Scoped.var i
  | abs {M N : Scoped}
      : M ⇉ N
      ---------
      → M.abs ⇉ N.abs
  | app {M M' N N' : Scoped}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → M.app N ⇉ M'.app N'
  | subst {M M' N N' : Scoped}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → (Scoped.abs M).app N ⇉ Scoped.sub0 N' M'

infixl:65 "⇉-c" => BetaPar.var
prefix:65 "⇉-ƛ " => BetaPar.abs
infixl:65 "⇉-ξ" => BetaPar.app
infixl:65 "⇉-β"  => BetaPar.subst

abbrev BetaParStar : Scoped → Scoped → Prop := Relation.ReflTransGen BetaPar
infix:64 " ⇉* " => BetaParStar

/-- Parallel reduction is reflexive (contract nothing). -/
instance : Std.Refl BetaPar where
  refl M := by
    induction M using Scoped.ind with
    | var i => exact BetaPar.var i
    | abs M ih => exact BetaPar.abs ih
    | app M N ihM ihN => exact BetaPar.app ihM ihN

theorem BetaPar.refl (M : Scoped) : M ⇉ M := Std.Refl.refl M

/-- Parallel reduction is stable under renaming. -/
theorem BetaPar.ren_mono {r r' : Scoped} (h : r ⇉ r') : ∀ ρ : Nat → Nat,
    Scoped.ren ρ r ⇉ Scoped.ren ρ r' := by
  induction h with
  | var i => intro ρ; exact BetaPar.var _
  | abs _ ih => intro ρ; exact BetaPar.abs (ih _)
  | app _ _ iha ihb => intro ρ; exact BetaPar.app (iha _) (ihb _)
  | @subst p p' q q' _ _ ihp ihq =>
      intro ρ
      rw [Scoped.ren_app, Scoped.ren_abs, Scoped.ren_sub0]
      exact BetaPar.subst (ihp _) (ihq _)

/-- Parallel reduction is stable under parallel substitution. -/
theorem BetaPar.sub_mono {r r' : Scoped} (h : r ⇉ r') :
    ∀ {σ σ' : Nat → Scoped}, (∀ i, σ i ⇉ σ' i) → Scoped.sub σ r ⇉ Scoped.sub σ' r' := by
  induction h with
  | var i => intro σ σ' hσ; exact hσ i
  | abs _ ih =>
      intro σ σ' hσ
      refine BetaPar.abs (ih ?_)
      intro i
      cases i with
      | zero => exact BetaPar.var 0
      | succ j => exact (hσ j).ren_mono _
  | app _ _ iha ihb => intro σ σ' hσ; exact BetaPar.app (iha hσ) (ihb hσ)
  | @subst p p' q q' _ _ ihp ihq =>
      intro σ σ' hσ
      rw [Scoped.sub_app, Scoped.sub_abs, Scoped.sub_sub0]
      refine BetaPar.subst (ihp ?_) (ihq hσ)
      intro i
      cases i with
      | zero => exact BetaPar.var 0
      | succ j => exact (hσ j).ren_mono _

theorem BetaPar.sub0_mono {p p' q q' : Scoped} (hp : p ⇉ p') (hq : q ⇉ q') :
    Scoped.sub0 q p ⇉ Scoped.sub0 q' p' := by
  refine hp.sub_mono ?_
  intro i
  cases i with
  | zero => exact hq
  | succ j => exact BetaPar.var j

-- ====================================================================
-- 7. Takahashi's complete development and the triangle lemma
-- ====================================================================

namespace Term

/-- The complete development: contract every redex present in the term. -/
def cdT : {n : Nat} → Term n → Scoped
  | _, var i => Scoped.var i
  | _, abs t => Scoped.abs (cdT t)
  | _, app (abs p) q => Scoped.sub0 (cdT q) (cdT p)
  | _, app a b => Scoped.app (cdT a) (cdT b)

end Term

namespace Scoped

/-- The complete development of an existentially scoped term. -/
def cd (s : Scoped) : Scoped := Term.cdT s.2

@[simp] theorem cd_var (i : Nat) : cd (var i) = var i := rfl
@[simp] theorem cd_abs (s : Scoped) : cd (abs s) = abs (cd s) := rfl
@[simp] theorem cd_app_abs (p q : Scoped) : cd (app (abs p) q) = sub0 (cd q) (cd p) := rfl
@[simp] theorem cd_app_var (i : Nat) (q : Scoped) : cd (app (var i) q) = app (var i) (cd q) := rfl
@[simp] theorem cd_app_app (a b q : Scoped) :
    cd (app (app a b) q) = app (cd (app a b)) (cd q) := rfl

end Scoped

/-- Inversion for parallel reduction out of an abstraction. -/
theorem BetaPar.abs_inv {x s : Scoped} (h : x ⇉ s) :
    ∀ {p : Scoped}, x = Scoped.abs p → ∃ p', s = Scoped.abs p' ∧ p ⇉ p' := by
  induction h with
  | var i => intro p hp; exact absurd hp Scoped.var_ne_abs
  | @abs r r' h' _ =>
      intro p hp
      cases Scoped.abs_eq_abs.mp hp
      exact ⟨r', rfl, h'⟩
  | app _ _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | subst _ _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs

theorem BetaPar.abs_inv' {p s : Scoped} (h : Scoped.abs p ⇉ s) :
    ∃ p', s = Scoped.abs p' ∧ p ⇉ p' := h.abs_inv rfl

/-- Takahashi's triangle: every parallel reduct of `r` parallel-reduces to `cd r`. -/
theorem BetaPar.triangle {r s : Scoped} (h : r ⇉ s) : s ⇉ Scoped.cd r := by
  induction h with
  | var i => exact BetaPar.var i
  | abs _ ih => exact BetaPar.abs ih
  | @app a a' b b' ha _ iha ihb =>
      rcases Scoped.cases' a with ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨x, y, rfl⟩
      · simpa using BetaPar.app iha ihb
      · obtain ⟨p', rfl, _⟩ := ha.abs_inv'
        obtain ⟨p'', hp'', hcd⟩ := iha.abs_inv'
        rw [Scoped.cd_abs] at hp''
        cases Scoped.abs_eq_abs.mp hp''
        rw [Scoped.cd_app_abs]
        exact BetaPar.subst hcd ihb
      · simpa using BetaPar.app iha ihb
  | @subst p p' q q' _ _ ihp ihq =>
      rw [Scoped.cd_app_abs]
      exact BetaPar.sub0_mono ihp ihq

-- ====================================================================
-- 8. Beta reduction and parallel reduction have the same closure
-- ====================================================================

theorem beta_to_betapar {M N : Scoped} (h : M —→ N) : M ⇉ N := by
  induction h with
  | appl L _ ih => exact BetaPar.app (BetaPar.refl L) ih
  | appr L _ ih => exact BetaPar.app ih (BetaPar.refl L)
  | abs _ ih => exact BetaPar.abs ih
  | basis M N =>
      rw [Term.betaSubstSigma_eq_sub0]
      exact BetaPar.subst (BetaPar.refl _) (BetaPar.refl _)

theorem betapar_to_betastar {M N : Scoped} (h : M ⇉ N) : M —→* N := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact beta_star_abs ih
  | app _ _ iha ihb =>
      exact Relation.ReflTransGen.trans (beta_star_appr _ iha) (beta_star_appl _ ihb)
  | @subst p p' q q' _ _ ihp ihq =>
      have h1 : Scoped.app (Scoped.abs p) q —→* Scoped.app (Scoped.abs p') q' :=
        Relation.ReflTransGen.trans (beta_star_appr _ (beta_star_abs ihp))
          (beta_star_appl _ ihq)
      exact Relation.ReflTransGen.tail h1 (Beta.basis' p' q')

theorem betastar_to_betaparstar {M N : Scoped} (h : M —→* N) : M ⇉* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (beta_to_betapar step)

theorem betaparstar_to_betastar {M N : Scoped} (h : M ⇉* N) : M —→* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.trans ih (betapar_to_betastar step)

/-- `⇉*` and `—→*` are the same relation. -/
theorem betapar_star_eq_betastar {M N : Scoped} : M ⇉* N ↔ M —→* N :=
  ⟨betaparstar_to_betastar, betastar_to_betaparstar⟩

-- ====================================================================
-- 9. Confluence and the Church-Rosser theorem
-- ====================================================================

theorem betapar_diamond {M N1 N2 : Scoped} (h1 : M ⇉ N1) (h2 : M ⇉ N2) :
    ∃ d, N1 ⇉ d ∧ N2 ⇉ d :=
  ⟨Scoped.cd M, h1.triangle, h2.triangle⟩

/-- Confluence of parallel reduction, via Mathlib's abstract `Relation.church_rosser`. -/
theorem betapar_church_rosser {a b c : Scoped} (hab : a ⇉* b) (hac : a ⇉* c) :
    Relation.Join BetaParStar b c :=
  Relation.church_rosser
    (fun _ _ _ h1 h2 =>
      ⟨Scoped.cd _, Relation.ReflGen.single h1.triangle,
        Relation.ReflTransGen.single h2.triangle⟩)
    hab hac

/-- **The Church-Rosser theorem**: any two reducts of a term are joinable. -/
theorem beta_church_rosser {a b c : Scoped} (hab : a —→* b) (hac : a —→* c) :
    ∃ d, b —→* d ∧ c —→* d := by
  obtain ⟨d, hbd, hcd⟩ :=
    betapar_church_rosser (betastar_to_betaparstar hab) (betastar_to_betaparstar hac)
  exact ⟨d, betaparstar_to_betastar hbd, betaparstar_to_betastar hcd⟩

/-- Confluence, in the `Relation.Join` formulation. -/
theorem beta_confluence {a b c : Scoped} (hab : a —→* b) (hac : a —→* c) :
    Relation.Join BetaStar b c := by
  obtain ⟨d, hbd, hcd⟩ := beta_church_rosser hab hac
  exact ⟨d, hbd, hcd⟩

/-- Beta conversion. -/
abbrev BetaEq : Scoped → Scoped → Prop := Relation.EqvGen Beta
infix:63 " ≡β " => BetaEq

/-- Church-Rosser for beta *conversion*: convertible terms have a common reduct. -/
theorem betaeq_join {a b : Scoped} (h : a ≡β b) : ∃ d, a —→* d ∧ b —→* d := by
  induction h with
  | rel x y hxy => exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
  | refl x => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm x y _ ih => obtain ⟨d, h1, h2⟩ := ih; exact ⟨d, h2, h1⟩
  | trans x y z _ _ ih1 ih2 =>
      obtain ⟨d1, hx, hy1⟩ := ih1
      obtain ⟨d2, hy2, hz⟩ := ih2
      obtain ⟨d, hd1, hd2⟩ := beta_church_rosser hy1 hy2
      exact ⟨d, Relation.ReflTransGen.trans hx hd1, Relation.ReflTransGen.trans hz hd2⟩

-- ====================================================================
-- 10. Two sample reductions
-- ====================================================================

/-- `𝟙 = ƛ v#0`, as an existentially scoped (closed) term. -/
def sid : Scoped := ⟨0, Term.id⟩

/-- `(ƛ 𝟙) ⬝ 𝟙 —→ 𝟙`: an abstraction whose body is CLOSED is still a redex here,
    because the redex rule does not relate the scope of the body to that of the
    argument. -/
example : Scoped.app (Scoped.abs sid) sid —→ sid := Beta.basis Term.id Term.id

/-- `(λx. (λy. x) x) 𝟙`. -/
def sample : Scoped := Scoped.app (Scoped.abs ⟨1, (ƛ v##1) ⬝ v##0⟩) sid

/-- Contracting the outer redex first: `sample —→ (ƛ 𝟙) ⬝ 𝟙 —→ 𝟙`. -/
example : sample —→* sid :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (Beta.basis ((ƛ v##1) ⬝ v##0) Term.id))
    (Beta.basis Term.id Term.id)

/-- Contracting the inner redex first: `sample —→ 𝟙 ⬝ 𝟙 —→ 𝟙`. -/
example : sample —→* sid :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single
      (Beta.appr sid (Beta.abs (Beta.basis (v##1 : Term 2) (v##0 : Term 1)))))
    (Beta.basis (v#0 : Term 1) Term.id)

end IwilareNatIsExactScope
