-- Intrinsically *scope-bounded* de Bruijn lambda terms.
--
-- This is the second implementation in this project.  The first one
-- (`IwilareNatIsExactScope`) indexes a term by the *exact* number of free
-- indexes it uses, which forces substitution to return its scope
-- existentially (a `Σ n, Term n`).  Here the index is instead an *upper bound*
-- on the free indexes, variables being elements of `Fin n`:
--
--     inductive Term : Nat → Type
--       | var : ∀ {n : Nat}, Fin n → Term n
--       | abs : ∀ {n : Nat}, Term (n + 1) → Term n
--       | app : ∀ {n : Nat}, Term n → Term n → Term n
--       deriving DecidableEq
--
-- and the simplification the user predicted really happens:
--
--   * `DecidableEq` comes for free from `deriving` (in the exact-scope
--     development it had to be written by hand, because two terms of the same
--     scope can be built from subterms of *different* scopes);
--   * every operation is scope-directed: renaming is
--     `(Fin n → Fin m) → Term n → Term m` and substitution is
--     `(Fin n → Term m) → Term n → Term m`, so nothing has to be returned
--     existentially and **no Sigma type occurs anywhere** in this development;
--   * `betaSubst : Term (n+1) → Term n → Term n` is a one-liner, and beta
--     reduction is an ordinary relation on `Term n` which is confluent:
--     `beta_church_rosser` below.
--
-- The price is that the index is no longer exact: see the section
-- "How exact is the index?" at the end of the file, where the equivalence
--
--     n = 0 ⟺ closed        n > 0 ⟺ the index n - 1 occurs
--
-- of the exact-scope development is shown to hold only in the first
-- (⟸ is still fine) and to *fail* in the second: `notExact` is a term of
-- type `Term 1` with no free index at all.
module

public import Aesop
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace FinScope

/-- Scope-bounded intrinsically typed de Bruijn terms: a `Term n` uses only
free de Bruijn indexes `< n`. -/
inductive Term : Nat → Type
  | var : ∀ {n : Nat}, Fin n → Term n
  | abs : ∀ {n : Nat}, Term (n + 1) → Term n
  | app : ∀ {n : Nat}, Term n → Term n → Term n
  deriving DecidableEq

prefix:71 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:72 "v#" => Term.var

namespace Term

/-! ## Renaming -/

/-- Lift a renaming under a binder. -/
def ext {n m : Nat} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 (fun i => (ρ i).succ)

/-- Apply a renaming to a term. -/
def ren : {n m : Nat} → (Fin n → Fin m) → Term n → Term m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, ρ, .abs t => .abs (ren (ext ρ) t)
  | _, _, ρ, .app a b => .app (ren ρ a) (ren ρ b)

/-! ## Substitution -/

/-- Lift a substitution under a binder. -/
def exts {n m : Nat} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cons (.var 0) (fun i => ren Fin.succ (σ i))

/-- Apply a substitution to a term. -/
def sub : {n m : Nat} → (Fin n → Term m) → Term n → Term m
  | _, _, σ, .var i => σ i
  | _, _, σ, .abs t => .abs (sub (exts σ) t)
  | _, _, σ, .app a b => .app (sub σ a) (sub σ b)

/-- **Beta substitution**: substitute `N` for the index `0` of `M`, decreasing
the scope by one.  This is the operation that had to be returned
existentially in the exact-scope development. -/
def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  sub (Fin.cons N .var) M

@[inherit_doc] notation:max M " [ " N " ] " => Term.betaSubst M N

/-! ### Computation rules -/

@[simp] theorem ren_var {n m} (ρ : Fin n → Fin m) (i) : ren ρ (v# i) = v# (ρ i) := rfl
@[simp] theorem ren_abs {n m} (ρ : Fin n → Fin m) (t) : ren ρ (ƛ t) = ƛ (ren (ext ρ) t) := rfl
@[simp] theorem ren_app {n m} (ρ : Fin n → Fin m) (a b) :
    ren ρ (a ⬝ b) = ren ρ a ⬝ ren ρ b := rfl
@[simp] theorem sub_var {n m} (σ : Fin n → Term m) (i) : sub σ (v# i) = σ i := rfl
@[simp] theorem sub_abs {n m} (σ : Fin n → Term m) (t) : sub σ (ƛ t) = ƛ (sub (exts σ) t) := rfl
@[simp] theorem sub_app {n m} (σ : Fin n → Term m) (a b) :
    sub σ (a ⬝ b) = sub σ a ⬝ sub σ b := rfl

@[simp] theorem ext_zero {n m} (ρ : Fin n → Fin m) : ext ρ 0 = 0 := rfl
@[simp] theorem ext_succ {n m} (ρ : Fin n → Fin m) (i : Fin n) : ext ρ i.succ = (ρ i).succ := by
  simp [ext]
@[simp] theorem exts_zero {n m} (σ : Fin n → Term m) : exts σ 0 = v# 0 := rfl
@[simp] theorem exts_succ {n m} (σ : Fin n → Term m) (i : Fin n) :
    exts σ i.succ = ren Fin.succ (σ i) := by
  simp [exts]

/-! ### The substitution algebra -/

theorem ext_id {n} : ext (fun i : Fin n => i) = fun i => i := by
  funext i; induction i using Fin.cases <;> simp

@[simp] theorem ren_id {n} (t : Term n) : ren (fun i => i) t = t := by
  induction t with
  | var i => rfl
  | abs t ih => simp [ext_id, ih]
  | app a b iha ihb => simp [iha, ihb]

theorem ren_ren {n m k} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Term n) :
    ren ρ' (ren ρ t) = ren (fun i => ρ' (ρ i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | abs t ih => simp only [ren_abs, ih, Term.abs.injEq]
                congr 1; funext i; induction i using Fin.cases <;> simp
  | app a b iha ihb => simp [iha, ihb]

theorem sub_ren {n m k} (ρ : Fin n → Fin m) (σ : Fin m → Term k) (t : Term n) :
    sub σ (ren ρ t) = sub (fun i => σ (ρ i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | abs t ih => simp only [ren_abs, sub_abs, ih, Term.abs.injEq]
                congr 1; funext i; induction i using Fin.cases <;> simp
  | app a b iha ihb => simp [iha, ihb]

theorem ren_sub {n m k} (σ : Fin n → Term m) (ρ : Fin m → Fin k) (t : Term n) :
    ren ρ (sub σ t) = sub (fun i => ren ρ (σ i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | abs t ih => simp only [sub_abs, ren_abs, ih, Term.abs.injEq]
                congr 1; funext i
                induction i using Fin.cases <;> simp [ren_ren]
  | app a b iha ihb => simp [iha, ihb]

theorem sub_sub {n m k} (σ : Fin n → Term m) (τ : Fin m → Term k) (t : Term n) :
    sub τ (sub σ t) = sub (fun i => sub τ (σ i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | abs t ih => simp only [sub_abs, ih, Term.abs.injEq]
                congr 1; funext i
                induction i using Fin.cases <;> simp [ren_sub, sub_ren]
  | app a b iha ihb => simp [iha, ihb]

@[simp] theorem exts_var {n} : exts (@var n) = var := by
  funext i; induction i using Fin.cases <;> simp

@[simp] theorem sub_id {n} (t : Term n) : sub var t = t := by
  induction t with
  | var i => rfl
  | abs t ih => simp [ih]
  | app a b iha ihb => simp [iha, ihb]

theorem ren_eq_sub {n m} (ρ : Fin n → Fin m) (t : Term n) :
    ren ρ t = sub (fun i => v# (ρ i)) t := by
  induction t generalizing m with
  | var i => rfl
  | abs t ih => simp only [ren_abs, sub_abs, ih, Term.abs.injEq]
                congr 1; funext i; induction i using Fin.cases <;> simp
  | app a b iha ihb => simp [iha, ihb]

/-! ### How `betaSubst` interacts with renaming and substitution -/

theorem sub_betaSubst {n m} (σ : Fin n → Term m) (M : Term (n + 1)) (N : Term n) :
    sub σ (M [ N ]) = (sub (exts σ) M) [ sub σ N ] := by
  simp only [betaSubst, sub_sub]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp [sub_ren]

theorem ren_betaSubst {n m} (ρ : Fin n → Fin m) (M : Term (n + 1)) (N : Term n) :
    ren ρ (M [ N ]) = (ren (ext ρ) M) [ ren ρ N ] := by
  simp only [ren_eq_sub, sub_betaSubst]
  congr 2
  funext i
  induction i using Fin.cases <;> simp

/-! ### The first few numeral indices

`Fin`-numerals do not reduce definitionally to iterated `Fin.succ` (there is a
`% (n + k)` in the way), so the computation rules for the small indices that
occur in the usual combinators are recorded once and for all. -/

theorem fin_one_eq_succ {n : Nat} : (1 : Fin (n + 2)) = Fin.succ 0 := by simp

theorem fin_two_eq_succ {n : Nat} : (2 : Fin (n + 3)) = Fin.succ 1 := by
  apply Fin.ext; simp

theorem fin_three_eq_succ {n : Nat} : (3 : Fin (n + 4)) = Fin.succ 2 := by
  apply Fin.ext
  simp
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

@[simp] theorem ext_one {n m : Nat} (ρ : Fin (n + 1) → Fin m) : ext ρ 1 = (ρ 0).succ := by
  rw [fin_one_eq_succ, ext_succ]

@[simp] theorem ext_two {n m : Nat} (ρ : Fin (n + 2) → Fin m) : ext ρ 2 = (ρ 1).succ := by
  rw [fin_two_eq_succ, ext_succ]

@[simp] theorem ext_three {n m : Nat} (ρ : Fin (n + 3) → Fin m) : ext ρ 3 = (ρ 2).succ := by
  rw [fin_three_eq_succ, ext_succ]

@[simp] theorem exts_one {n m : Nat} (σ : Fin (n + 1) → Term m) :
    exts σ 1 = ren Fin.succ (σ 0) := by
  rw [fin_one_eq_succ, exts_succ]

@[simp] theorem exts_two {n m : Nat} (σ : Fin (n + 2) → Term m) :
    exts σ 2 = ren Fin.succ (σ 1) := by
  rw [fin_two_eq_succ, exts_succ]

@[simp] theorem exts_three {n m : Nat} (σ : Fin (n + 3) → Term m) :
    exts σ 3 = ren Fin.succ (σ 2) := by
  rw [fin_three_eq_succ, exts_succ]

@[simp] theorem fin_cons_one {n : Nat} {β : Fin (n + 2) → Type*} (a : β 0) (f : (i : Fin (n + 1)) → β i.succ) :
    Fin.cons a f 1 = f 0 := by
  have : (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := fin_one_eq_succ
  cases this
  rfl

@[simp] theorem fin_cons_two {n : Nat} {β : Fin (n + 3) → Type*} (a : β 0) (f : (i : Fin (n + 2)) → β i.succ) :
    Fin.cons a f 2 = f 1 := by
  have : (2 : Fin (n + 3)) = (1 : Fin (n + 2)).succ := fin_two_eq_succ
  cases this
  rfl

@[simp] theorem fin_cons_three {n : Nat} {β : Fin (n + 4) → Type*} (a : β 0) (f : (i : Fin (n + 3)) → β i.succ) :
    Fin.cons a f 3 = f 2 := by
  have : (3 : Fin (n + 4)) = (2 : Fin (n + 3)).succ := fin_three_eq_succ
  cases this
  rfl

@[simp] theorem betaSubst_app {n : Nat} (a b : Term (n + 1)) (N : Term n) :
    (a ⬝ b) [ N ] = a [ N ] ⬝ b [ N ] := rfl

@[simp] theorem betaSubst_var_zero {n : Nat} (N : Term n) : (v# 0 : Term (n + 1)) [ N ] = N := rfl

@[simp] theorem betaSubst_var_succ {n : Nat} (N : Term n) (i : Fin n) :
    (v# i.succ : Term (n + 1)) [ N ] = v# i := by
  simp [betaSubst]

theorem betaSubst_abs {n : Nat} (t : Term (n + 2)) (N : Term n) :
    (ƛ t) [ N ] = ƛ (sub (exts (Fin.cons N var)) t) := rfl

@[simp] theorem betaSubst_var_one {n : Nat} (N : Term (n + 1)) :
    (v# 1 : Term (n + 2)) [ N ] = v# 0 := by
  rw [fin_one_eq_succ, betaSubst_var_succ]

@[simp] theorem betaSubst_var_two {n : Nat} (N : Term (n + 2)) :
    (v# 2 : Term (n + 3)) [ N ] = v# 1 := by
  rw [fin_two_eq_succ, betaSubst_var_succ]

@[simp] theorem betaSubst_var_three {n : Nat} (N : Term (n + 3)) :
    (v# 3 : Term (n + 4)) [ N ] = v# 2 := by
  rw [fin_three_eq_succ, betaSubst_var_succ]

/-- A closed term is unaffected by the (unique) renaming into its own scope. -/
@[simp] theorem ren_elim0_self (t : Term 0) : ren Fin.elim0 t = t := by
  have h : (Fin.elim0 : Fin 0 → Fin 0) = fun i => i := funext (fun i => i.elim0)
  rw [h, ren_id]

/-- A substitution by variables only is a renaming. -/
@[simp] theorem sub_var_eq_ren {n m : Nat} (ρ : Fin n → Fin m) (t : Term n) :
    sub (fun i => v# (ρ i)) t = ren ρ t := (ren_eq_sub ρ t).symm

/-- **Weakening**, which the exact-scope discipline could not provide: a
`Term n` is a `Term (n+1)` that does not use the index `0`. -/
abbrev wk {n : Nat} (t : Term n) : Term (n + 1) := ren Fin.succ t

/-- Substituting for the index `0` of a weakened term does nothing. -/
@[simp] theorem betaSubst_wk {n : Nat} (M N : Term n) : (wk M) [ N ] = M := by
  simp [betaSubst, sub_ren]

end Term

open Term

/-! ## Beta reduction -/

/-- One step of beta reduction. -/
inductive Beta : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) : Beta ((ƛ M) ⬝ N) (M [ N ])
  | abs {n : Nat} {M M' : Term (n + 1)} : Beta M M' → Beta (ƛ M) (ƛ M')
  | appL {n : Nat} {a a' b : Term n} : Beta a a' → Beta (a ⬝ b) (a' ⬝ b)
  | appR {n : Nat} {a b b' : Term n} : Beta b b' → Beta (a ⬝ b) (a ⬝ b')

@[inherit_doc] infix:60 " —→ " => Beta

/-- Many steps of beta reduction. -/
abbrev BetaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Beta

@[inherit_doc] infix:60 " —→* " => BetaStar

/-- Beta conversion. -/
abbrev BetaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen Beta

@[inherit_doc] infix:60 " ≡β " => BetaEq

/-! ### Inversion for `—→` -/

theorem Beta.var_inv {n : Nat} {i : Fin n} {s : Term n} (h : v# i —→ s) : False := by
  cases h

theorem Beta.abs_inv {n : Nat} {p : Term (n + 1)} {s : Term n} (h : ƛ p —→ s) :
    ∃ p', s = ƛ p' ∧ p —→ p' := by
  cases h with
  | abs h' => exact ⟨_, rfl, h'⟩

theorem Beta.app_inv {n : Nat} {a b s : Term n} (h : a ⬝ b —→ s) :
    (∃ P : Term (n + 1), a = ƛ P ∧ s = P [ b ])
      ∨ (∃ a', s = a' ⬝ b ∧ a —→ a') ∨ (∃ b', s = a ⬝ b' ∧ b —→ b') := by
  cases h with
  | @basis _ P Q => exact Or.inl ⟨P, rfl, rfl⟩
  | appL h' => exact Or.inr (Or.inl ⟨_, rfl, h'⟩)
  | appR h' => exact Or.inr (Or.inr ⟨_, rfl, h'⟩)

/-! ### Congruence rules for `—→*` -/

theorem BetaStar.abs {n : Nat} {M M' : Term (n + 1)} (h : M —→* M') : ƛ M —→* ƛ M' := by
  induction h with
  | refl => exact .refl
  | tail _ hb ih => exact ih.tail (Beta.abs hb)

theorem BetaStar.appL {n : Nat} {a a' b : Term n} (h : a —→* a') : a ⬝ b —→* a' ⬝ b := by
  induction h with
  | refl => exact .refl
  | tail _ hb ih => exact ih.tail (Beta.appL hb)

theorem BetaStar.appR {n : Nat} {a b b' : Term n} (h : b —→* b') : a ⬝ b —→* a ⬝ b' := by
  induction h with
  | refl => exact .refl
  | tail _ hb ih => exact ih.tail (Beta.appR hb)

theorem BetaStar.app {n : Nat} {a a' b b' : Term n} (ha : a —→* a') (hb : b —→* b') :
    a ⬝ b —→* a' ⬝ b' :=
  (BetaStar.appL ha).trans (BetaStar.appR hb)

/-! ## Parallel reduction and the Church-Rosser theorem -/

/-- Tait / Martin-Löf parallel reduction. -/
inductive BetaPar : {n : Nat} → Term n → Term n → Prop
  | var {n : Nat} (i : Fin n) : BetaPar (v# i) (v# i)
  | abs {n : Nat} {M M' : Term (n + 1)} : BetaPar M M' → BetaPar (ƛ M) (ƛ M')
  | app {n : Nat} {a a' b b' : Term n} :
      BetaPar a a' → BetaPar b b' → BetaPar (a ⬝ b) (a' ⬝ b')
  | beta {n : Nat} {M M' : Term (n + 1)} {N N' : Term n} :
      BetaPar M M' → BetaPar N N' → BetaPar ((ƛ M) ⬝ N) (M' [ N' ])

@[inherit_doc] infix:60 " ⇉ " => BetaPar

abbrev BetaParStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaPar

@[inherit_doc] infix:60 " ⇉* " => BetaParStar

@[refl] theorem BetaPar.refl {n : Nat} (M : Term n) : M ⇉ M := by
  induction M with
  | var i => exact .var i
  | abs t ih => exact .abs ih
  | app a b iha ihb => exact .app iha ihb

instance {n : Nat} : Std.Refl (@BetaPar n) := ⟨BetaPar.refl⟩

/-- Parallel reduction is stable under renaming. -/
theorem BetaPar.ren {n : Nat} {M M' : Term n} (h : M ⇉ M') :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ M ⇉ ren ρ M' := by
  induction h with
  | var i => intro m ρ; exact .var _
  | abs _ ih => intro m ρ; exact .abs (ih _)
  | app _ _ iha ihb => intro m ρ; exact .app (iha _) (ihb _)
  | beta _ _ ihM ihN =>
      intro m ρ
      simpa [ren_betaSubst] using BetaPar.beta (ihM (ext ρ)) (ihN ρ)

/-- Pointwise parallel reduction of substitutions. -/
def ParSub {n m : Nat} (σ τ : Fin n → Term m) : Prop := ∀ i, σ i ⇉ τ i

theorem ParSub.exts {n m : Nat} {σ τ : Fin n → Term m} (h : ParSub σ τ) :
    ParSub (exts σ) (exts τ) := by
  intro i
  induction i using Fin.cases with
  | zero => simpa using BetaPar.var 0
  | succ i => simpa using (h i).ren Fin.succ

/-- Parallel reduction is stable under parallel substitution. -/
theorem BetaPar.sub {n : Nat} {M M' : Term n} (h : M ⇉ M') :
    ∀ {m : Nat} {σ τ : Fin n → Term m}, ParSub σ τ → sub σ M ⇉ sub τ M' := by
  induction h with
  | var i => intro m σ τ hst; exact hst i
  | abs _ ih => intro m σ τ hst; exact .abs (ih hst.exts)
  | app _ _ iha ihb => intro m σ τ hst; exact .app (iha hst) (ihb hst)
  | beta _ _ ihM ihN =>
      intro m σ τ hst
      simpa [sub_betaSubst] using BetaPar.beta (ihM hst.exts) (ihN hst)

theorem BetaPar.betaSubst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇉ M') (hN : N ⇉ N') : M [ N ] ⇉ M' [ N' ] := by
  refine hM.sub (τ := Fin.cons N' Term.var) ?_
  intro i
  induction i using Fin.cases with
  | zero => simpa using hN
  | succ i => simpa using BetaPar.var i

/-- The **complete development** of a term: contract, simultaneously, all the
redexes present in it. -/
def cd : {n : Nat} → Term n → Term n
  | _, .var i => .var i
  | _, .abs t => .abs (cd t)
  | _, .app (.abs M) N => (cd M) [ cd N ]
  | _, .app (.var i) b => .app (.var i) (cd b)
  | _, .app (.app a b) c => .app (cd (.app a b)) (cd c)

@[simp] theorem cd_var {n : Nat} (i : Fin n) : cd (v# i) = v# i := rfl
@[simp] theorem cd_abs {n : Nat} (t : Term (n + 1)) : cd (ƛ t) = ƛ (cd t) := rfl
@[simp] theorem cd_app_abs {n : Nat} (M : Term (n + 1)) (N : Term n) :
    cd ((ƛ M) ⬝ N) = (cd M) [ cd N ] := rfl
@[simp] theorem cd_app_var {n : Nat} (i : Fin n) (b : Term n) :
    cd ((v# i) ⬝ b) = (v# i) ⬝ cd b := rfl
@[simp] theorem cd_app_app {n : Nat} (a b c : Term n) :
    cd ((a ⬝ b) ⬝ c) = cd (a ⬝ b) ⬝ cd c := rfl

/-- Takahashi's triangle property: every parallel reduct of `M` parallel
reduces to the complete development of `M`. -/
theorem BetaPar.triangle {n : Nat} {M N : Term n} (h : M ⇉ N) : N ⇉ cd M := by
  induction h with
  | var i => exact .var i
  | abs _ ih => simpa using BetaPar.abs ih
  | @app n a a' b b' ha _ iha ihb =>
      cases a with
      | var i =>
          cases ha
          simpa using BetaPar.app (BetaPar.var i) ihb
      | abs M =>
          cases ha with
          | abs hM =>
              rename_i M'
              simp only [cd_app_abs]
              have : (ƛ M') ⇉ ƛ (cd M) := iha
              cases this with
              | abs h' => exact BetaPar.beta h' ihb
      | app c d =>
          simpa using BetaPar.app iha ihb
  | beta _ _ ihM ihN =>
      simpa using BetaPar.betaSubst ihM ihN

theorem BetaPar.diamond {n : Nat} {a b c : Term n} (hb : a ⇉ b) (hc : a ⇉ c) :
    ∃ d, b ⇉ d ∧ c ⇉ d :=
  ⟨cd a, hb.triangle, hc.triangle⟩

/-! ### `⇉` sits between `—→` and `—→*` -/

theorem BetaPar.of_beta {n : Nat} {a b : Term n} (h : a —→ b) : a ⇉ b := by
  induction h with
  | basis M N => exact BetaPar.beta (BetaPar.refl M) (BetaPar.refl N)
  | abs _ ih => exact .abs ih
  | appL _ ih => exact .app ih (BetaPar.refl _)
  | appR _ ih => exact .app (BetaPar.refl _) ih

theorem BetaPar.toBetaStar {n : Nat} {a b : Term n} (h : a ⇉ b) : a —→* b := by
  induction h with
  | var i => exact .refl
  | abs _ ih => exact ih.abs
  | app _ _ iha ihb => exact BetaStar.app iha ihb
  | @beta n M M' N N' _ _ ihM ihN =>
      exact (BetaStar.app (BetaStar.abs ihM) ihN).tail (Beta.basis M' N')

theorem betaparstar_iff_betastar {n : Nat} {a b : Term n} : a ⇉* b ↔ a —→* b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hb ih => exact ih.trans hb.toBetaStar
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hb ih => exact ih.tail (BetaPar.of_beta hb)

/-- **The Church-Rosser theorem** for beta reduction. -/
theorem beta_church_rosser {n : Nat} {a b c : Term n} (hb : a —→* b) (hc : a —→* c) :
    ∃ d, b —→* d ∧ c —→* d := by
  have hb' : a ⇉* b := betaparstar_iff_betastar.mpr hb
  have hc' : a ⇉* c := betaparstar_iff_betastar.mpr hc
  obtain ⟨d, hd1, hd2⟩ :=
    Relation.church_rosser (fun _ _ _ h1 h2 => by
      obtain ⟨d, h1', h2'⟩ := BetaPar.diamond h1 h2
      exact ⟨d, Relation.ReflGen.single h1', Relation.ReflTransGen.single h2'⟩) hb' hc'
  exact ⟨d, betaparstar_iff_betastar.mp hd1, betaparstar_iff_betastar.mp hd2⟩

/-- Confluence, in `Relation.Join` form. -/
theorem beta_confluence {n : Nat} {a b c : Term n} (hb : a —→* b) (hc : a —→* c) :
    Relation.Join BetaStar b c := beta_church_rosser hb hc

/-- Beta convertible terms are joinable. -/
theorem betaeq_join {n : Nat} {a b : Term n} (h : a ≡β b) : ∃ d, a —→* d ∧ b —→* d := by
  induction h with
  | rel a b hab => exact ⟨b, Relation.ReflTransGen.single hab, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih => obtain ⟨d, h1, h2⟩ := ih; exact ⟨d, h2, h1⟩
  | trans a b c _ _ ih1 ih2 =>
      obtain ⟨d, h1, h2⟩ := ih1
      obtain ⟨e, h3, h4⟩ := ih2
      obtain ⟨f, h5, h6⟩ := beta_church_rosser h2 h3
      exact ⟨f, h1.trans h5, h4.trans h6⟩

/-! ## How exact is the index? -/

/-- `occursFree i t` : the free de Bruijn index `i` really occurs in `t`. -/
def occursFree : {n : Nat} → Fin n → Term n → Prop
  | _, i, .var j => j = i
  | _, i, .abs t => occursFree i.succ t
  | _, i, .app a b => occursFree i a ∨ occursFree i b

/-- A `Term 0` is closed, in the strong sense that there is no index to occur:
`Fin 0` is empty. -/
theorem closed_of_scope_zero (t : Term 0) : ∀ i : Fin 0, ¬ occursFree i t :=
  fun i => absurd i.isLt (by omega)

/-- With `Fin`-indexed variables the scope is only an upper bound, not the
exact number of free indexes: this term of type `Term 1` uses no free index. -/
def notExact : Term 1 := ƛ (v# 0)

theorem notExact_no_free_index : ¬ occursFree (0 : Fin 1) notExact := by
  intro h
  exact absurd (show (0 : Fin 2) = (0 : Fin 1).succ from h) (by decide)


/-! ## Two sample reductions -/

/-- The identity `𝟙 = ƛ v#0`, a closed term: no Sigma type is needed to say
that it is closed, its scope is simply `0`. -/
def sid : Term 0 := ƛ v# 0

/-- `(ƛ 𝟙) ⬝ 𝟙 —→ 𝟙`. -/
example : (ƛ (wk sid)) ⬝ sid —→ sid := by
  simpa using Beta.basis (wk sid) sid

/-- `(λx. (λy. x) x) 𝟙`. -/
def sample : Term 0 := (ƛ ((ƛ v# 1) ⬝ v# 0)) ⬝ sid

/-- Contracting the outer redex first: `sample —→ (ƛ 𝟙) ⬝ 𝟙 —→ 𝟙`. -/
example : sample —→* sid := by
  refine Relation.ReflTransGen.head (Beta.basis ((ƛ v# 1) ⬝ v# 0) sid) ?_
  refine Relation.ReflTransGen.single ?_
  simp_all only [Nat.reduceAdd, Fin.isValue, betaSubst_app, betaSubst_var_zero]
  solve_by_elim

/-- Contracting the inner redex first: `sample —→ 𝟙 ⬝ 𝟙 —→ 𝟙`. -/
example : sample —→* sid := by
  refine Relation.ReflTransGen.head
    (Beta.appL (Beta.abs (Beta.basis (v# 1 : Term 2) (v# 0 : Term 1)))) ?_
  refine Relation.ReflTransGen.single ?_
  simpa [sid] using Beta.basis (v# 0 : Term 1) sid


end FinScope
