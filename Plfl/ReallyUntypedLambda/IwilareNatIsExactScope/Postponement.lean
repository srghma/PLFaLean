-- The eta postponement theorem.
--
-- Any beta-eta reduction can be rearranged so that all beta steps come first:
--
--     a —→βη* b   →   ∃ c, a —→* c  ∧  c —→η* b
--
-- The proof follows Takahashi's method: a *parallel* eta reduction `⇛η` is
-- introduced, one beta step is swapped past one parallel eta step
-- (`EtaPar.beta_swap`), and this is then iterated.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.BetaEta

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 0. Beta reduction is stable under renaming
-- ====================================================================

theorem Beta.ren_mono {a b : Scoped} (h : a —→ b) : ∀ ρ : Nat → Nat,
    Scoped.ren ρ a —→ Scoped.ren ρ b := by
  induction h with
  | appl L _ ih => intro ρ; exact Beta.appl _ (ih _)
  | appr L _ ih => intro ρ; exact Beta.appr _ (ih _)
  | abs _ ih => intro ρ; exact Beta.abs (ih _)
  | @basis m n P Q =>
      intro ρ
      have h := Beta.basis' (Scoped.ren (Scoped.upRen ρ) ⟨m, P⟩) (Scoped.ren ρ ⟨n, Q⟩)
      rw [← Scoped.ren_sub0] at h
      rw [Term.betaSubstSigma_eq_sub0]
      exact h

theorem BetaStar.ren_mono {a b : Scoped} (h : a —→* b) (ρ : Nat → Nat) :
    Scoped.ren ρ a —→* Scoped.ren ρ b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (step.ren_mono ρ)

-- ====================================================================
-- 1. Parallel eta reduction
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "⇛η" => EtaPar

/-- Parallel eta reduction: contract any set of eta redexes simultaneously. -/
inductive EtaPar : Scoped → Scoped → Prop
  | var (i : Nat)
      ---------
      : Scoped.var i ⇛η Scoped.var i
  | abs {M N : Scoped}
      : M ⇛η N
      ---------
      → M.abs ⇛η N.abs
  | app {M M' N N' : Scoped}
      : M ⇛η M' → N ⇛η N'
      ---------
      → M.app N ⇛η M'.app N'
  | eta {M N : Scoped}
      : M ⇛η N
      ---------
      → (Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0)).abs ⇛η N

theorem EtaPar.refl (a : Scoped) : a ⇛η a := by
  induction a using Scoped.ind with
  | var i => exact EtaPar.var i
  | abs p ih => exact EtaPar.abs ih
  | app a b iha ihb => exact EtaPar.app iha ihb

theorem Eta.to_etaPar {a b : Scoped} (h : a —→η b) : a ⇛η b := by
  induction h with
  | basis M => exact EtaPar.eta (EtaPar.refl M)
  | abs _ ih => exact EtaPar.abs ih
  | appr L _ ih => exact EtaPar.app ih (EtaPar.refl L)
  | appl L _ ih => exact EtaPar.app (EtaPar.refl L) ih

theorem EtaPar.to_etaStar {a b : Scoped} (h : a ⇛η b) : a —→η* b := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact eta_star_abs ih
  | app _ _ ih₁ ih₂ => exact (eta_star_appr _ ih₁).trans (eta_star_appl _ ih₂)
  | @eta M N _ ih =>
      refine Relation.ReflTransGen.trans ?_ (Relation.ReflTransGen.single (Eta.basis N))
      exact eta_star_abs (eta_star_appr _ (ih.ren_mono Nat.succ))

-- ====================================================================
-- 2. Parallel eta is stable under renaming and substitution
-- ====================================================================

theorem EtaPar.ren_mono {a b : Scoped} (h : a ⇛η b) : ∀ ρ : Nat → Nat,
    Scoped.ren ρ a ⇛η Scoped.ren ρ b := by
  induction h with
  | var i => intro ρ; exact EtaPar.var _
  | abs _ ih => intro ρ; exact EtaPar.abs (ih _)
  | app _ _ ih₁ ih₂ => intro ρ; exact EtaPar.app (ih₁ _) (ih₂ _)
  | @eta M N _ ih =>
      intro ρ
      have e : Scoped.ren (Scoped.upRen ρ) (Scoped.ren Nat.succ M)
          = Scoped.ren Nat.succ (Scoped.ren ρ M) := by
        rw [Scoped.ren_ren, Scoped.ren_ren]
        rfl
      have := EtaPar.eta (M := Scoped.ren ρ M) (N := Scoped.ren ρ N) (ih ρ)
      simp_all only [Scoped.ren_abs, Scoped.ren_app, Scoped.ren_var]
      obtain ⟨fst, snd⟩ := a
      obtain ⟨fst_1, snd_1⟩ := b
      obtain ⟨fst_2, snd_2⟩ := M
      obtain ⟨fst_3, snd_3⟩ := N
      exact this

theorem EtaPar.sub_congr {σ τ : Nat → Scoped} (hστ : ∀ i, σ i ⇛η τ i)
    {a b : Scoped} (h : a ⇛η b) : Scoped.sub σ a ⇛η Scoped.sub τ b := by
  induction h generalizing σ τ with
  | var i => simpa using hστ i
  | abs _ ih =>
      refine EtaPar.abs (ih ?_)
      intro i
      cases i with
      | zero => exact EtaPar.var 0
      | succ i => exact (hστ i).ren_mono Nat.succ
  | app _ _ ih₁ ih₂ => exact EtaPar.app (ih₁ hστ) (ih₂ hστ)
  | @eta M N _ ih =>
      have e : Scoped.sub (Scoped.upSub σ) (Scoped.ren Nat.succ M)
          = Scoped.ren Nat.succ (Scoped.sub σ M) := Scoped.sub_upSub_ren_succ σ M
      have := EtaPar.eta (M := Scoped.sub σ M) (N := Scoped.sub τ N) (ih hστ)
      simp_all only [Scoped.sub_abs, Scoped.sub_app, Scoped.sub_var']
      obtain ⟨fst, snd⟩ := a
      obtain ⟨fst_1, snd_1⟩ := b
      obtain ⟨fst_2, snd_2⟩ := M
      obtain ⟨fst_3, snd_3⟩ := N
      exact this

theorem EtaPar.sub0_congr {M M' N N' : Scoped} (hM : M ⇛η M') (hN : N ⇛η N') :
    Scoped.sub0 N M ⇛η Scoped.sub0 N' M' := by
  refine EtaPar.sub_congr ?_ hM
  intro i
  cases i with
  | zero => exact hN
  | succ i => exact EtaPar.var i

-- ====================================================================
-- 3. Sources of an abstraction
-- ====================================================================

/-- If `M` parallel-eta reduces to an abstraction, then `M` *beta*-reduces to an
    abstraction whose body parallel-eta reduces to the given one. -/
theorem EtaPar.abs_target {M X : Scoped} (h : M ⇛η X) :
    ∀ p : Scoped, X = Scoped.abs p → ∃ m, M —→* Scoped.abs m ∧ m ⇛η p := by
  induction h with
  | var i => intro p hp; exact absurd hp Scoped.var_ne_abs
  | @abs M₀ N₀ hMN _ =>
      intro p hp
      cases Scoped.abs_eq_abs.mp hp
      exact ⟨M₀, Relation.ReflTransGen.refl, hMN⟩
  | app _ _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | @eta M₀ N _ ih =>
      intro p hp
      obtain ⟨m, hm₁, hm₂⟩ := ih p hp
      refine ⟨m, ?_, hm₂⟩
      refine Relation.ReflTransGen.trans
        (beta_star_abs (beta_star_appr _ (hm₁.ren_mono Nat.succ))) ?_
      refine Relation.ReflTransGen.single ?_
      have hstep := Beta.abs (Beta.basis' (Scoped.ren (Scoped.upRen Nat.succ) m) (Scoped.var 0))
      rwa [Scoped.sub0_var_zero_ren_upRen_succ] at hstep

-- ====================================================================
-- 4. Swapping a beta step past a parallel eta step
-- ====================================================================

/-- **The key postponement step**: a parallel eta step followed by a beta step
    can be replaced by beta steps followed by a parallel eta step. -/
theorem EtaPar.beta_swap {M N : Scoped} (h : M ⇛η N) :
    ∀ P : Scoped, N —→ P → ∃ Q, M —→* Q ∧ Q ⇛η P := by
  induction h with
  | var i =>
      intro P hP
      exact absurd rfl (hP.var_inv (i := i))
  | @abs M₀ N₀ _ ih =>
      intro P hP
      obtain ⟨P₀, rfl, hP₀⟩ := hP.abs_inv'
      obtain ⟨Q₀, hQ₁, hQ₂⟩ := ih P₀ hP₀
      exact ⟨Scoped.abs Q₀, beta_star_abs hQ₁, EtaPar.abs hQ₂⟩
  | @app M₁ N₁ M₂ N₂ h₁ h₂ ih₁ ih₂ =>
      intro P hP
      rcases hP.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨Q₁, hQ₁, hQ₂⟩ := ih₁ a' ha'
        exact ⟨Scoped.app Q₁ M₂, beta_star_appr _ hQ₁, EtaPar.app hQ₂ h₂⟩
      · obtain ⟨Q₂, hQ₁, hQ₂⟩ := ih₂ b' hb'
        exact ⟨Scoped.app M₁ Q₂, beta_star_appl _ hQ₁, EtaPar.app h₁ hQ₂⟩
      · obtain ⟨m, hm₁, hm₂⟩ := h₁.abs_target p hp
        refine ⟨Scoped.sub0 M₂ m, ?_, EtaPar.sub0_congr hm₂ h₂⟩
        exact Relation.ReflTransGen.tail (beta_star_appr _ hm₁) (Beta.basis' m M₂)
  | @eta M₀ N₀ _ ih =>
      intro P hP
      obtain ⟨Q₀, hQ₁, hQ₂⟩ := ih P hP
      refine ⟨Scoped.abs (Scoped.app (Scoped.ren Nat.succ Q₀) (Scoped.var 0)), ?_,
        EtaPar.eta hQ₂⟩
      exact beta_star_abs (beta_star_appr _ (hQ₁.ren_mono Nat.succ))

/-- A parallel eta step followed by any number of beta steps. -/
theorem EtaPar.betaStar_swap {M N : Scoped} (h : M ⇛η N) :
    ∀ P : Scoped, N —→* P → ∃ Q, M —→* Q ∧ Q ⇛η P := by
  intro P hP
  induction hP with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, h⟩
  | @tail P' P _ hstep ih =>
      obtain ⟨Q', hQ₁, hQ₂⟩ := ih
      obtain ⟨Q, hR₁, hR₂⟩ := hQ₂.beta_swap P hstep
      exact ⟨Q, hQ₁.trans hR₁, hR₂⟩

-- ====================================================================
-- 5. The postponement theorem
-- ====================================================================

/-- Eta steps can be postponed past beta steps. -/
theorem etaStar_betaStar_postpone {M N : Scoped} (h : M —→η* N) :
    ∀ P : Scoped, N —→* P → ∃ Q, M —→* Q ∧ Q —→η* P := by
  induction h with
  | refl => intro P hP; exact ⟨P, hP, Relation.ReflTransGen.refl⟩
  | @tail N' N _ hstep ih =>
      intro P hP
      obtain ⟨Q₁, hQ₁, hQ₂⟩ := hstep.to_etaPar.betaStar_swap P hP
      obtain ⟨Q, hR₁, hR₂⟩ := ih Q₁ hQ₁
      exact ⟨Q, hR₁, hR₂.trans hQ₂.to_etaStar⟩

/-- **The eta postponement theorem**: every beta-eta reduction can be
    rearranged into a beta reduction followed by an eta reduction. -/
theorem eta_postponement {a b : Scoped} (h : a —→βη* b) :
    ∃ c, a —→* c ∧ c —→η* b := by
  induction h with
  | refl => exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail b' b _ hstep ih =>
      obtain ⟨c', hc₁, hc₂⟩ := ih
      rcases hstep with hstep | hstep
      · obtain ⟨Q, hQ₁, hQ₂⟩ :=
          etaStar_betaStar_postpone hc₂ b (Relation.ReflTransGen.single hstep)
        exact ⟨Q, hc₁.trans hQ₁, hQ₂⟩
      · exact ⟨c', hc₁, hc₂.tail hstep⟩

/-- Beta-eta reduction is exactly: beta reduction, then eta reduction. -/
theorem betaEtaStar_iff_beta_then_eta {a b : Scoped} :
    a —→βη* b ↔ ∃ c, a —→* c ∧ c —→η* b := by
  refine ⟨eta_postponement, ?_⟩
  rintro ⟨c, hac, hcb⟩
  exact (BetaStar.to_betaEtaStar hac).trans (EtaStar.to_betaEtaStar hcb)

end IwilareNatIsExactScope
