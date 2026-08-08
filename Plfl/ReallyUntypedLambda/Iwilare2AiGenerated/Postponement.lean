-- The eta postponement theorem, for the scope-bounded (`Fin`-indexed) calculus.
--
-- Any beta-eta reduction can be rearranged so that all beta steps come first:
--
--     a —→βη* b   →   ∃ c, a —→* c  ∧  c —→η* b
--
-- The proof follows Takahashi's method: a *parallel* eta reduction `⇛η` is
-- introduced, one beta step is swapped past one parallel eta step
-- (`EtaPar.beta_swap`), and this is then iterated.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.BetaEta

@[expose] public section

namespace FinScope

open Term

/-! ## 0. Beta reduction is stable under renaming -/

theorem Beta.ren_mono {n : Nat} {a b : Term n} (h : a —→ b) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ a —→ ren ρ b := by
  induction h with
  | basis M N => intro m ρ; simpa [ren_betaSubst] using Beta.basis (ren (ext ρ) M) (ren ρ N)
  | abs _ ih => intro m ρ; exact Beta.abs (ih _)
  | appL _ ih => intro m ρ; exact Beta.appL (ih _)
  | appR _ ih => intro m ρ; exact Beta.appR (ih _)

theorem BetaStar.ren_mono {n m : Nat} {a b : Term n} (h : a —→* b) (ρ : Fin n → Fin m) :
    ren ρ a —→* ren ρ b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.ren_mono ρ)

/-! ## 1. Parallel eta reduction -/

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " ⇛η " => EtaPar

/-- Parallel eta reduction: contract any set of eta redexes simultaneously. -/
inductive EtaPar : {n : Nat} → Term n → Term n → Prop
  | var {n : Nat} (i : Fin n)
      ---------
      : v# i ⇛η v# i
  | abs {n : Nat} {M N : Term (n + 1)}
      : M ⇛η N
      ---------
      → ƛ M ⇛η ƛ N
  | app {n : Nat} {M M' N N' : Term n}
      : M ⇛η M' → N ⇛η N'
      ---------
      → M ⬝ N ⇛η M' ⬝ N'
  | eta {n : Nat} {M N : Term n}
      : M ⇛η N
      ---------
      → ƛ (wk M ⬝ v# 0) ⇛η N

@[refl] theorem EtaPar.refl {n : Nat} (a : Term n) : a ⇛η a := by
  induction a with
  | var i => exact EtaPar.var i
  | abs p ih => exact EtaPar.abs ih
  | app a b iha ihb => exact EtaPar.app iha ihb

theorem Eta.to_etaPar {n : Nat} {a b : Term n} (h : a —→η b) : a ⇛η b := by
  induction h with
  | basis M => exact EtaPar.eta (EtaPar.refl M)
  | abs _ ih => exact EtaPar.abs ih
  | appL _ ih => exact EtaPar.app ih (EtaPar.refl _)
  | appR _ ih => exact EtaPar.app (EtaPar.refl _) ih

theorem EtaPar.to_etaStar {n : Nat} {a b : Term n} (h : a ⇛η b) : a —→η* b := by
  induction h with
  | var i => exact .refl
  | abs _ ih => exact ih.abs
  | app _ _ ih₁ ih₂ => exact (ih₁.appL).trans (ih₂.appR)
  | @eta n M N _ ih =>
      refine Relation.ReflTransGen.trans ?_ (Relation.ReflTransGen.single (Eta.basis N))
      exact (EtaStar.appL (ih.ren_mono Fin.succ)).abs

/-! ## 2. Parallel eta is stable under renaming and substitution -/

theorem EtaPar.ren_mono {n : Nat} {a b : Term n} (h : a ⇛η b) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ a ⇛η ren ρ b := by
  induction h with
  | var i => intro m ρ; exact EtaPar.var _
  | abs _ ih => intro m ρ; exact EtaPar.abs (ih _)
  | app _ _ ih₁ ih₂ => intro m ρ; exact EtaPar.app (ih₁ _) (ih₂ _)
  | @eta n M N _ ih =>
      intro m ρ
      have e : ren (ext ρ) (wk M) = wk (ren ρ M) := by
        simp only [wk, ren_ren]
        congr 1
      have := EtaPar.eta (M := ren ρ M) (N := ren ρ N) (ih ρ)
      simpa [e] using this

/-- Weakening commutes with substitution under a binder. -/
theorem sub_exts_wk {n m : Nat} (σ : Fin n → Term m) (M : Term n) :
    sub (exts σ) (wk M) = wk (sub σ M) := by
  simp only [wk, sub_ren, ren_sub]
  congr 1

theorem EtaPar.sub_congr {n m : Nat} {σ τ : Fin n → Term m} (hστ : ∀ i, σ i ⇛η τ i)
    {a b : Term n} (h : a ⇛η b) : sub σ a ⇛η sub τ b := by
  induction h generalizing m with
  | var i => simpa using hστ i
  | @abs n M N _ ih =>
      refine EtaPar.abs (ih ?_)
      intro i
      induction i using Fin.cases with
      | zero => simpa using EtaPar.var (0 : Fin (m + 1))
      | succ i => simpa using (hστ i).ren_mono Fin.succ
  | app _ _ ih₁ ih₂ => exact EtaPar.app (ih₁ hστ) (ih₂ hστ)
  | @eta n M N _ ih =>
      have := EtaPar.eta (M := sub σ M) (N := sub τ N) (ih hστ)
      simpa [sub_exts_wk] using this

theorem EtaPar.betaSubst_congr {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇛η M') (hN : N ⇛η N') : M [ N ] ⇛η M' [ N' ] := by
  refine EtaPar.sub_congr (τ := Fin.cons N' Term.var) ?_ hM
  intro i
  induction i using Fin.cases with
  | zero => simpa using hN
  | succ i => simpa using EtaPar.var i

/-! ## 3. Sources of an abstraction -/

/-- If `M` parallel-eta reduces to an abstraction, then `M` *beta*-reduces to an
    abstraction whose body parallel-eta reduces to the given one. -/
theorem EtaPar.abs_target {n : Nat} {M X : Term n} (h : M ⇛η X) :
    ∀ p : Term (n + 1), X = ƛ p → ∃ m, M —→* ƛ m ∧ m ⇛η p := by
  induction h with
  | var i => intro p hp; exact absurd hp (by simp)
  | @abs n M₀ N₀ hMN _ =>
      intro p hp
      cases (by simpa using hp : N₀ = p)
      exact ⟨M₀, .refl, hMN⟩
  | app _ _ _ _ => intro p hp; exact absurd hp (by simp)
  | @eta n M₀ N _ ih =>
      intro p hp
      obtain ⟨m, hm₁, hm₂⟩ := ih p hp
      refine ⟨m, ?_, hm₂⟩
      refine Relation.ReflTransGen.trans
        (BetaStar.abs (BetaStar.appL (hm₁.ren_mono Fin.succ))) ?_
      refine Relation.ReflTransGen.single ?_
      have hstep := Beta.abs (Beta.basis (ren (ext Fin.succ) m) (v# 0))
      rwa [betaSubst_var_zero_ren_ext_succ] at hstep

/-! ## 4. Swapping a beta step past a parallel eta step -/

/-- **The key postponement step**: a parallel eta step followed by a beta step
    can be replaced by beta steps followed by a parallel eta step. -/
theorem EtaPar.beta_swap {n : Nat} {M N : Term n} (h : M ⇛η N) :
    ∀ P : Term n, N —→ P → ∃ Q, M —→* Q ∧ Q ⇛η P := by
  induction h with
  | var i =>
      intro P hP
      exact absurd hP (fun h => h.var_inv)
  | @abs n M₀ N₀ _ ih =>
      intro P hP
      obtain ⟨P₀, rfl, hP₀⟩ := hP.abs_inv
      obtain ⟨Q₀, hQ₁, hQ₂⟩ := ih P₀ hP₀
      exact ⟨ƛ Q₀, hQ₁.abs, EtaPar.abs hQ₂⟩
  | @app n M₁ M₁' M₂ M₂' h₁ h₂ ih₁ ih₂ =>
      intro P hP
      rcases hP.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨m, hm₁, hm₂⟩ := h₁.abs_target p hp
        refine ⟨m [ M₂ ], ?_, EtaPar.betaSubst_congr hm₂ h₂⟩
        exact Relation.ReflTransGen.tail (BetaStar.appL hm₁) (Beta.basis m M₂)
      · obtain ⟨Q₁, hQ₁, hQ₂⟩ := ih₁ a' ha'
        exact ⟨Q₁ ⬝ M₂, hQ₁.appL, EtaPar.app hQ₂ h₂⟩
      · obtain ⟨Q₂, hQ₁, hQ₂⟩ := ih₂ b' hb'
        exact ⟨M₁ ⬝ Q₂, hQ₁.appR, EtaPar.app h₁ hQ₂⟩
  | @eta n M₀ N₀ _ ih =>
      intro P hP
      obtain ⟨Q₀, hQ₁, hQ₂⟩ := ih P hP
      refine ⟨ƛ (wk Q₀ ⬝ v# 0), ?_, EtaPar.eta hQ₂⟩
      exact (BetaStar.appL (hQ₁.ren_mono Fin.succ)).abs

/-- A parallel eta step followed by any number of beta steps. -/
theorem EtaPar.betaStar_swap {n : Nat} {M N : Term n} (h : M ⇛η N) :
    ∀ P : Term n, N —→* P → ∃ Q, M —→* Q ∧ Q ⇛η P := by
  intro P hP
  induction hP with
  | refl => exact ⟨M, .refl, h⟩
  | @tail P' P _ hstep ih =>
      obtain ⟨Q', hQ₁, hQ₂⟩ := ih
      obtain ⟨Q, hR₁, hR₂⟩ := hQ₂.beta_swap P hstep
      exact ⟨Q, hQ₁.trans hR₁, hR₂⟩

/-! ## 5. The postponement theorem -/

/-- Eta steps can be postponed past beta steps. -/
theorem etaStar_betaStar_postpone {n : Nat} {M N : Term n} (h : M —→η* N) :
    ∀ P : Term n, N —→* P → ∃ Q, M —→* Q ∧ Q —→η* P := by
  induction h with
  | refl => intro P hP; exact ⟨P, hP, .refl⟩
  | @tail N' N _ hstep ih =>
      intro P hP
      obtain ⟨Q₁, hQ₁, hQ₂⟩ := hstep.to_etaPar.betaStar_swap P hP
      obtain ⟨Q, hR₁, hR₂⟩ := ih Q₁ hQ₁
      exact ⟨Q, hR₁, hR₂.trans hQ₂.to_etaStar⟩

/-- **The eta postponement theorem**: every beta-eta reduction can be
    rearranged into a beta reduction followed by an eta reduction. -/
theorem eta_postponement {n : Nat} {a b : Term n} (h : a —→βη* b) :
    ∃ c, a —→* c ∧ c —→η* b := by
  induction h with
  | refl => exact ⟨a, .refl, .refl⟩
  | @tail b' b _ hstep ih =>
      obtain ⟨c', hc₁, hc₂⟩ := ih
      rcases hstep with hstep | hstep
      · obtain ⟨Q, hQ₁, hQ₂⟩ :=
          etaStar_betaStar_postpone hc₂ b (Relation.ReflTransGen.single hstep)
        exact ⟨Q, hc₁.trans hQ₁, hQ₂⟩
      · exact ⟨c', hc₁, hc₂.tail hstep⟩

/-- Beta-eta reduction is exactly: beta reduction, then eta reduction. -/
theorem betaEtaStar_iff_beta_then_eta {n : Nat} {a b : Term n} :
    a —→βη* b ↔ ∃ c, a —→* c ∧ c —→η* b := by
  refine ⟨eta_postponement, ?_⟩
  rintro ⟨c, hac, hcb⟩
  exact (BetaStar.to_betaEtaStar hac).trans (EtaStar.to_betaEtaStar hcb)

end FinScope
