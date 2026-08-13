module

-- https://plfa.github.io/Soundness/

public import Plfl.Untyped.Denotational.Compositional

@[expose] public section

namespace Soundness

open Untyped Untyped.Notation
open Untyped.Subst
open Substitution (Rename Subst)
open Denotational Denotational.Notation
open Compositional Compositional.Notation

-- https://plfa.github.io/Soundness/#simultaneous-substitution-preserves-denotations
namespace Env
  /--
  `Eval δ σ γ` means that for every variable `i`,
  `σ i` results in the same value as the one for `i` in the original environment `γ`.
  -/
  abbrev Eval (δ : Env m) (σ : Subst n m) (γ : Env n) : Prop := ∀ (i : Fin n), δ ⊢ σ i ￬ γ i
end Env

namespace Notation
  scoped notation:30 δ " `⊢ " σ " ￬ " γ:51 => Env.Eval δ σ γ
end Notation

open Notation

section
  variable {n m : Nat} {γ : Env n} {δ : Env m}

  lemma subst_ext (σ : Subst n m) (d : δ `⊢ σ ￬ γ) : δ`‚ v `⊢ exts σ ￬ (γ`‚ v) := by
    intro i; cases i using Fin.cases with
    | zero => exact .var
    | succ i => exact rename_pres Fin.succ (λ _ => .refl) (d i)

  /-- The result of evaluation is conserved after simultaneous substitution. -/
  theorem subst_pres (σ : Subst n m) (s : δ `⊢ σ ￬ γ) (d : γ ⊢ t ￬ v)
  : δ ⊢ subst σ t ￬ v
  := by induction d generalizing m with
  | var => apply s
  | ap _ _ ih ih'=> exact (ih σ s).ap (ih' σ s)
  | fn _ ih => refine .fn ?_; apply ih (exts σ); exact subst_ext σ s
  | bot => exact .bot
  | conj _ _ ih ih' => exact (ih σ s).conj (ih' σ s)
  | sub _ lt ih => exact (ih σ s).sub lt

  -- https://plfa.github.io/Soundness/#single-substitution-preserves-denotations
  /-- The result of evaluation is conserved after single substitution. -/
  theorem subst₁_pres {n_body : Term (n + 1)} {m_term : Term n} (dn : γ`‚ v ⊢ n_body ￬ w) (dm : γ ⊢ m_term ￬ v) : γ ⊢ n_body⟦m_term⟧ ￬ w
  := subst_pres (σ := subst₁σ m_term) (γ := γ`‚ v) (δ := γ) (by intro i; cases i using Fin.cases with | zero => exact dm | succ _ => exact .var) dn

  -- https://plfa.github.io/Soundness/#reduction-preserves-denotations
  theorem reduce_pres {t u : Term n} (d : γ ⊢ t ￬ v) (r : t —→ u) : γ ⊢ u ￬ v := by induction d with
  | var => contradiction
  | bot => exact .bot
  | fn _ ih => cases r with | lamζ r => exact (ih r).fn
  | conj _ _ ih ih' => exact (ih r).conj (ih' r)
  | sub _ lt ih => exact (ih r).sub lt
  | ap d d' ih ih' => cases r with
    | apξ₁ r => exact (ih r).ap d'
    | apξ₂ r => exact d.ap (ih' r)
    | lamβ => exact subst₁_pres (lam_inv d) d'

  -- https://plfa.github.io/Soundness/#renaming-reflects-meaning
  theorem rename_reflect {ρ : Rename n m} (lt : δ ∘ ρ `⊑ γ) (d : δ ⊢ rename ρ t ￬ v)
  : γ ⊢ t ￬ v
  := by
    generalize hx : rename ρ t = x at *
    induction d generalizing n with
    | bot => exact .bot
    | var => cases t with (injection hx; try subst_vars)
      | var i => exact .sub .var <| (var_inv .var).trans (lt i)
    | ap _ _ ih ih' => cases t with injection hx
      | app => rename_i hx hx'; exact (ih lt hx).ap (ih' lt hx')
    | fn _ ih => cases t with injection hx
      | abs => refine .fn ?_; apply ih (ρ := ext ρ) (ext_sub' ρ lt); trivial
    | conj _ _ ih ih' => exact (ih lt hx).conj (ih' lt hx)
    | sub _ lt' ih => exact (ih lt hx).sub lt'

  theorem rename_shift_reflect {t : Term n} (d : γ`‚ u ⊢ shift t ￬ v) : γ ⊢ t ￬ v :=
    rename_reflect (by rfl) d
end

section
  variable {n m : Nat}

  -- https://plfa.github.io/Soundness/#substitution-reflects-denotations-the-variable-case
  /-- `const` is an `Env` with a single non-trivial mapping entry: from `i` to `v`. -/
  def Env.const (i : Fin n) (v : Value) : Env n | j => if i = j then v else ⊥

  variable {γ δ : Env m}

  lemma subst_reflect_var {i : Fin n} {σ : Subst n m} (d : γ ⊢ σ i ￬ v)
  : ∃ (δ : Env n), (γ `⊢ σ ￬ δ) ∧ (δ ⊢ ‵ i ￬ v)
  := by
    exists Env.const i v; unfold Env.const; constructor
    · intro j; by_cases h : i = j <;> simp only [h] at *
      · exact d
      · exact .bot
    · convert Eval.var; simp only [ite_true]

  variable {γ₁ γ₂ : Env n} {σ : Subst n m}

  -- https://plfa.github.io/Soundness/#substitutions-and-environment-construction
  lemma subst_bot : γ `⊢ σ ￬ ⊥ | _ => .bot

  lemma subst_conj (d₁ : γ `⊢ σ ￬ γ₁) (d₂ : γ `⊢ σ ￬ γ₂) : γ `⊢ σ ￬ γ₁ ⊔ γ₂
  | i => (d₁ i).conj (d₂ i)
end

-- https://plfa.github.io/Soundness/#simultaneous-substitution-reflects-denotations
/-- Simultaneous substitution reflects denotations. -/
theorem subst_reflect {n m : Nat} {σ : Subst n m} {δ : Env m} {l : Term m} {v : Value} (d : δ ⊢ l ￬ v) {t : Term n} (h : ⟪σ⟫ t = l)
: ∃ (γ : Env n), (δ `⊢ σ ￬ γ) ∧ (γ ⊢ t ￬ v)
:= by
  induction d generalizing n with
  | bot => exists ⊥; exact ⟨subst_bot, .bot⟩
  | var => cases t with try contradiction
    | var j => apply subst_reflect_var; convert Eval.var using 1; exact h
  | ap d d' ih ih' => rename_i l' _ _ m'; cases t with try contradiction
    | var => apply subst_reflect_var; convert d.ap d' using 1; exact h
    | app =>
      injection h; rename_i h h'
      let ⟨γ, dγ, dm⟩ := ih h; let ⟨γ', dγ', dm'⟩ := ih' h'; exists γ ⊔ γ'; constructor
      · exact subst_conj dγ dγ'
      · exact (sub_env dm <| Env.Sub.conjR₁ γ γ').ap (sub_env dm' <| Env.Sub.conjR₂ γ γ')
  | fn d ih => cases t with try contradiction
    | var => apply subst_reflect_var; convert d.fn using 1; exact h
    | abs =>
      injection h; rename_i h; let ⟨γ, dγ, dm⟩ := ih h; exists γ.init; constructor
      · intro i; exact rename_shift_reflect <| dγ (Fin.succ i)
      · rw [Env.init_last γ] at dm; refine .fn (up_env dm ?_); exact var_inv <| dγ 0
  | conj _ _ ih ih' =>
    let ⟨γ, dγ, dm⟩ := ih h; let ⟨γ', dγ', dm'⟩ := ih' h; exists γ ⊔ γ'; constructor
    · exact subst_conj dγ dγ'
    · exact (sub_env dm <| Env.Sub.conjR₁ γ γ').conj (sub_env dm' <| Env.Sub.conjR₂ γ γ')
  | sub _ lt' ih => let ⟨γ, dγ, dm⟩ := ih h; exact ⟨γ, dγ, dm.sub lt'⟩

-- https://plfa.github.io/Soundness/#single-substitution-reflects-denotations
lemma subst₁σ_reflect {m : Nat} {m_term : Term m} {δ : Env m} {γ : Env (m + 1)} (d : δ `⊢ subst₁σ m_term ￬ γ)
: ∃ w, (γ `⊑ δ`‚ w) ∧ (δ ⊢ m_term ￬ w)
:= by
  exists γ.last; constructor
  · intro i; cases i using Fin.cases with
    | zero => rfl
    | succ i => apply var_inv (d (Fin.succ i))
  · exact d 0

/-- Single substitution reflects denotations. -/
theorem subst₁_reflect {n : Nat} {n_body : Term (n + 1)} {m_term : Term n} {δ : Env n} {v : Value} (d : δ ⊢ n_body⟦m_term⟧ ￬ v) : ∃ w, (δ ⊢ m_term ￬ w) ∧ (δ`‚ w ⊢ n_body ￬ v)
:= by
  have ⟨γ, dγ, dn⟩ := subst_reflect d rfl; have ⟨w, ltw, dw⟩ := subst₁σ_reflect dγ
  exists w, dw; exact sub_env dn ltw

-- https://plfa.github.io/Soundness/#reduction-reflects-denotations-1
theorem reduce_reflect {n : Nat} {t u : Term n} {γ : Env n} {v : Value} (d : γ ⊢ u ￬ v) (r : t —→ u) : γ ⊢ t ￬ v := by
  induction r generalizing v with
  | lamβ =>
    rename_i n u; generalize hx : n⟦u⟧ = x at *
    induction d with
    | var => apply beta; rw [hx]; exact .var
    | ap d d' => apply beta; rw [hx]; exact d.ap d'
    | fn d => apply beta; rw [hx]; exact d.fn
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih hx).conj (ih' hx)
    | sub _ lt ih => exact (ih hx).sub lt
  | lamζ r ihᵣ =>
    rename_i _ n'; generalize hx : (ƛ n') = x at *
    induction d with try contradiction
    | fn d ih => injection hx; subst_vars; exact (ihᵣ <| lam_inv d.fn).fn
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  | apξ₁ r ihᵣ =>
    rename_i l m; generalize hx : l ⬝ m = x at *
    induction d with try contradiction
    | ap d d' _ _ => injection hx; subst_vars; exact (ihᵣ d).ap d'
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  | apξ₂ r ihᵣ =>
    rename_i m l; generalize hx : l ⬝ m = x at *
    induction d with try contradiction
    | ap d d' _ _ => injection hx; subst_vars; exact d.ap <| ihᵣ d'
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  where
    beta {n : Nat} {n_body : Term (n + 1)} {m_term : Term n} {v : Value} {γ : Env n} (d : γ ⊢ n_body⟦m_term⟧ ￬ v) : γ ⊢ (ƛ n_body) ⬝ m_term ￬ v := by
      have ⟨w, dm, dn⟩ := subst₁_reflect d; exact dn.fn.ap dm

-- https://plfa.github.io/Soundness/#reduction-implies-denotational-equality
theorem reduce_eq {n : Nat} {t u : Term n} (r : t —→ u) : ℰ t = ℰ u := by
  ext; exact ⟨(reduce_pres · r), (reduce_reflect · r)⟩

theorem soundness {n : Nat} {t : Term n} {n_body : Term (n + 1)} (rs : t —↠ ƛ n_body) : ℰ t = ℰ (ƛ n_body) := by
  induction rs using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head r _ ih => convert ih using 1; exact reduce_eq r
