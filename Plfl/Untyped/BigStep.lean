module

-- https://plfa.github.io/BigStep/

public import Plfl.Untyped
public import Plfl.Untyped.Substitution
import Mathlib.Logic.Lemmas

@[expose] public section

namespace BigStep

open Untyped Notation
open Substitution (Subst ids sub_ids)

-- https://plfa.github.io/BigStep/#environments
/--
A closure in call-by-name is a term paired with its environment.
-/
inductive Clos : Type where
| clos : ∀ {n : Nat}, (m : Term n) → (γ : Fin n → Clos) → Clos

/--
An environment in call-by-name is a mapping from variables to closures.
-/
abbrev ClosEnv (n : Nat) := Fin n → Clos

def ClosEnv.empty : ClosEnv 0 := nofun

instance ClosEnv.instEmptyCollection : EmptyCollection (ClosEnv 0) where
  emptyCollection := empty

def ClosEnv.tail (γ : ClosEnv n) (c : Clos) : ClosEnv (n + 1) :=
  Fin.cases c γ

namespace Notation
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚' " => ClosEnv.tail
end Notation

open Notation

/--
Big-step evaluation relation (`γ ⊢ m ⇓ c`).

Read `Eval γ m c` or `γ ⊢ m ⇓ c` as:
"Under local environment `γ`, evaluating term `m` produces final result closure `c`."
-/
inductive Eval : ClosEnv n → Term n → Clos → Prop where

/--
RULE 1: Evaluating a Variable (`‵ i`)

How to evaluate a variable (like looking up variable `x`):
1. Look up index `i` in current environment `γ`. This gives back a saved computation
   (a closure: term `m` + its saved environment `δ`).
2. Evaluate that saved term `m` inside its own environment `δ` to get final result `v`.
-/
| var
    (lookup : γ i = .clos m δ := by rfl)  -- Step 1: Look up variable `i` in environment `γ`
    (eval   : Eval δ m v)                 -- Step 2: Evaluate the retrieved term `m` in environment `δ`
    : Eval γ (‵ i) v

/--
RULE 2: Evaluating a Function Definition (`ƛ m`, i.e., `λx. m`)

Functions do NOT run immediately when defined!
To evaluate a lambda function:
- Package the function code `ƛ m` together with the current environment `γ`
  into a "closure" `(.clos (ƛ m) γ)` and return it immediately as a value.
-/
| lam
    : Eval γ (ƛ m) (.clos (ƛ m) γ)

/--
RULE 3: Evaluating Function Application (`l ⬝ m`, i.e., calling function `l` with argument `m`)

To run a function call `l ⬝ m`:
1. Evaluate the left term `l` in environment `γ`. It must return a function closure
   `(.clos (ƛ n) δ)` (which contains function body `n` and captured environment `δ`).
2. Because this is Call-By-Name, DO NOT evaluate argument `m` yet!
   Instead, package argument `m` and environment `γ` into a delayed closure `(.clos m γ)`.
3. Push this delayed argument closure onto the function's captured environment `δ`
   (`δ ‚' .clos m γ`).
4. Evaluate the function body `n` in this extended environment to get final result `v`.
-/
| ap
    (eval_fun  : Eval γ l (.clos (ƛ n) δ))   -- Step 1: Evaluate `l` to get function code `ƛ n` & captured env `δ`
    (eval_body : Eval (δ ‚' .clos m γ) n v)   -- Step 2-4: Run function body `n` with delayed argument `.clos m γ`
    : Eval γ (l ⬝ m) v

namespace Notation
  -- Human-friendly notation: `γ ⊢ m ⇓ c` means "In environment `γ`, term `m` evaluates to closure `c`"
  scoped notation:40 γ " ⊢ " m " ⇓ " c:51 => Eval γ m c
end Notation

-- /-- Call-By-Value Big-Step Evaluation (`γ ⊢ m ⇓_cbv v`) -/
-- inductive EvalCBV : EnvCBV n → Term n → ValCBV → Prop where
-- | var : EvalCBV γ (‵ i) (γ i)  -- Variables store already-evaluated values!
-- | lam : EvalCBV γ (ƛ m) (.clos m γ)
-- | ap  : EvalCBV γ l (.clos n δ) →
--         EvalCBV γ m v_arg →            -- Step 1: Force argument `m` to evaluate to `v_arg`
--         EvalCBV (δ ‚'' v_arg) n v →     -- Step 2: Run body `n` with evaluated argument `v_arg`
--         EvalCBV γ (l ⬝ m) v

-- scoped notation:40 γ " ⊢ " m " ⇓_cbv " v:51 => EvalCBV γ m v

open Notation

-- https://plfa.github.io/BigStep/#exercise-big-step-eg-practice
example
: γ ⊢ (ƛ ƛ #1) $ (ƛ #0 ⬝ #0) $ (ƛ #0 ⬝ #0)
-- (λ x y => x) Ω ⇓ (λ y => Ω)
⇓ .clos (ƛ #1) (γ ‚' .clos ((ƛ #0 ⬝ #0) $ (ƛ #0 ⬝ #0)) γ)
:= .ap .lam .lam

-- https://plfa.github.io/BigStep/#the-big-step-semantics-is-deterministic
theorem Eval.determ (e : γ ⊢ m ⇓ v) (e' : γ ⊢ m ⇓ v') : v = v' := by
  induction e generalizing v' with cases e'
  | lam => rfl
  | var h _ ih =>
    rename_i h' e'
    cases h.symm.trans h'
    exact ih e'
  | ap _ _ ih ih₁ =>
    rename_i e' e₁'
    cases ih e'
    exact ih₁ e₁'

-- https://plfa.github.io/BigStep/#big-step-evaluation-implies-beta-reduction-to-a-lambda
noncomputable def Clos.Equiv : Clos → Term 0 → Prop
| .clos (n := n) m γ, t =>
  ∃ (σ : Subst n 0), (∀ i, Clos.Equiv (γ i) (σ i)) ∧ (t = ⟪σ⟫ m)

abbrev ClosEnv.Equiv (γ : ClosEnv n) (σ : Subst n 0) : Prop :=
  ∀ i, Clos.Equiv (γ i) (σ i)

namespace Notation
  scoped infix:20 " ~~ " => Clos.Equiv
  scoped infix:20 " ~~ₑ " => ClosEnv.Equiv
end Notation

open Notation

section
  open Untyped.Subst
  open Substitution

  @[simp] lemma ClosEnv.empty_equiv_ids : ClosEnv.empty ~~ₑ ids := nofun

  abbrev ext_subst (σ : Subst n m) (t : Term m) : Subst (n + 1) m := (·⟦t⟧) ∘ exts σ

  lemma subst₁σ_exts {σ : Subst n m} {t : Term m} {i : Fin n}
  : (ext_subst σ t) (Fin.succ i) = σ i
  := by
    change ⟪subst₁σ t⟫ (rename Fin.succ (σ i)) = σ i
    rw [rename_subst]
    have h : subst₁σ t ∘ Fin.succ = ids := by funext y; rfl
    rw [h, sub_ids]

  theorem ClosEnv.ext {γ : ClosEnv n} {σ : Subst n 0} {t : Term 0}
  (ee : γ ~~ₑ σ) (e : v ~~ t) : (γ ‚' v ~~ₑ ext_subst σ t)
  := by intro i; cases i using Fin.cases with
  | zero => exact e
  | succ i => simp only [subst₁σ_exts]; exact ee i

  theorem Eval.clos_env_equiv {γ : ClosEnv n} {σ : Subst n 0} {m : Term n}
  (ev : γ ⊢ m ⇓ v) (ee : γ ~~ₑ σ)
  : ∃ (t : Term 0), (⟪σ⟫ m —↠ t) ∧ (v ~~ t)
  := open Untyped.Reduce in by induction ev with
  | lam => rename_i n; exists ⟪σ⟫ (ƛ n), by rfl, σ, ee
  | var h _ev ih =>
    rename_i i; have := ee i; rw [h] at this; have ⟨τ, eeτ, hτ⟩ := this
    have ⟨t, rn, en⟩ := ih eeτ; rw [←hτ] at rn; exists t, rn
  | ap _ev _ev' ih ih' =>
    have ⟨t, rn, τ, eeτ, hτ⟩ := ih ee; subst hτ
    have ⟨t', rn', en'⟩ := ih' <| ClosEnv.ext eeτ ⟨σ, ee, rfl⟩
    refine ⟨t', ?_, en'⟩; simp only [sub_ap]; rename_i n _ m _
    apply (ap_congr₁ rn).trans; unfold ext_subst at rn'
    calc ⟪τ⟫ (ƛ n) ⬝ ⟪σ⟫ m
      _ = (ƛ (⟪exts τ⟫ n)) ⬝ ⟪σ⟫ m := rfl
      _ —→ ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts τ⟫ n) := lamβ
      _ = ⟪⟪subst₁σ (⟪σ⟫ m)⟫ ∘ exts τ⟫ n := Substitution.sub_sub
      _ —↠ t' := rn'

  /--
  If call-by-name can produce a value,
  then the program can be reduced to a λ-abstraction via β-rules.
  -/
  theorem Eval.reduce_of_cbn {m : Term 0} {δ : ClosEnv n} {n' : Term (n + 1)}
  (ev : ClosEnv.empty ⊢ m ⇓ .clos (ƛ n') δ)
  : ∃ (t : Term 1), m —↠ ƛ t
  := by
    have ⟨t, rn, σ, _, h⟩ := ev.clos_env_equiv ClosEnv.empty_equiv_ids
    subst h; rw [sub_ids] at rn; exists ⟪exts σ⟫ n'
end

-- https://plfa.github.io/BigStep/#exercise-big-alt-implies-multi-practice
namespace BySubst

inductive Eval : Term n → Term n → Prop where
| lam : ∀ {n : Nat} {t : Term (n + 1)}, Eval (ƛ t) (ƛ t)
| ap : Eval l (ƛ m) → Eval (m⟦n⟧) v → Eval (l ⬝ n) v

namespace Notation
  scoped infix:50 " ⇓' "=> Eval
end Notation

open Notation

theorem Eval.determ : m ⇓' v → m ⇓' v' → v = v' := by intro
| .lam, .lam => rfl
| .ap mc mc₁, .ap mc' mc₁' =>
  have h := mc.determ mc'
  injection h with _ hm
  subst hm
  exact mc₁.determ mc₁'

open Untyped.Reduce
open Untyped.Subst

/--
If call-by-name can produce a value,
then the program can be reduced to a λ-abstraction via β-rules.
-/
theorem Eval.reduce_of_cbn {t v : Term k} (ev : t ⇓' v) {n' : Term (k + 1)} (h : v = (ƛ n')) : t —↠ ƛ n' := by
  induction ev generalizing n' with
  | lam =>
    injection h with _ a_eq
    subst a_eq
    exact .refl
  | ap evl evmn ihl ihmn =>
    rename_i l m n _
    have h1 : l —↠ ƛ m := ihl rfl
    have h2 : m⟦n⟧ —↠ ƛ n' := ihmn h
    calc l ⬝ n
      _ —↠ (ƛ m) ⬝ n := ap_congr₁ h1
      _ —→ m⟦n⟧ := lamβ
      _ —↠ ƛ n' := h2
