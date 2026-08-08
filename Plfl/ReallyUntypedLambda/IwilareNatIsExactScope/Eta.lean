-- Eta reduction.
--
-- In de Bruijn form the eta rule contracts `ƛ (M #0)` to `M` when the bound
-- index does not occur in `M`, i.e. when `M` is a shifted term:
--
--     ƛ ((ren succ M) #0)  —→η  M
--
-- This file develops the basic theory of `—→η`: it is stable under renaming and
-- substitution, it is reflected by renamings, and it is *subcommutative*, hence
-- confluent (`eta_church_rosser`).
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms

@[expose] public section

namespace IwilareNatIsExactScope

namespace Scoped

-- ====================================================================
-- 0. Renamings: shape reflection and the pullback property
-- ====================================================================

theorem ren_eq_var {ρ : Nat → Nat} {s : Scoped} {i : Nat} (h : ren ρ s = var i) :
    ∃ j, s = var j ∧ ρ j = i := by
  rcases Scoped.cases' s with ⟨j, rfl⟩ | ⟨p, rfl⟩ | ⟨a, b, rfl⟩
  · rw [ren_var] at h
    exact ⟨j, rfl, var_eq_var.mp h⟩
  · rw [ren_abs] at h; exact absurd h abs_ne_var
  · rw [ren_app] at h; exact absurd h app_ne_var

theorem ren_eq_abs {ρ : Nat → Nat} {s u : Scoped} (h : ren ρ s = abs u) :
    ∃ q, s = abs q ∧ u = ren (upRen ρ) q := by
  rcases Scoped.cases' s with ⟨j, rfl⟩ | ⟨p, rfl⟩ | ⟨a, b, rfl⟩
  · rw [ren_var] at h; exact absurd h var_ne_abs
  · rw [ren_abs] at h
    exact ⟨p, rfl, (abs_eq_abs.mp h).symm⟩
  · rw [ren_app] at h; exact absurd h app_ne_abs

theorem ren_eq_app {ρ : Nat → Nat} {s u v : Scoped} (h : ren ρ s = app u v) :
    ∃ a b, s = app a b ∧ u = ren ρ a ∧ v = ren ρ b := by
  rcases Scoped.cases' s with ⟨j, rfl⟩ | ⟨p, rfl⟩ | ⟨a, b, rfl⟩
  · rw [ren_var] at h; exact absurd h var_ne_app
  · rw [ren_abs] at h; exact absurd h abs_ne_app
  · rw [ren_app] at h
    obtain ⟨h₁, h₂⟩ := app_eq_app.mp h
    exact ⟨a, b, rfl, h₁.symm, h₂.symm⟩

/-- The condition making the square `α ∘ γ = β ∘ δ` a pullback of index maps. -/
def IsRenPullback (α β γ δ : Nat → Nat) : Prop :=
  ∀ i j, α i = β j → ∃ k, i = γ k ∧ j = δ k

theorem IsRenPullback.up {α β γ δ : Nat → Nat} (h : IsRenPullback α β γ δ) :
    IsRenPullback (upRen α) (upRen β) (upRen γ) (upRen δ) := by
  intro i j hij
  cases i with
  | zero =>
      cases j with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ j => exact Nat.noConfusion hij
  | succ i =>
      cases j with
      | zero => exact Nat.noConfusion hij
      | succ j =>
          have : α i = β j := Nat.succ.inj hij
          obtain ⟨k, hk₁, hk₂⟩ := h i j this
          exact ⟨k + 1, by simp [upRen, hk₁], by simp [upRen, hk₂]⟩

/-- Two renamings of terms that agree factor through the pullback. -/
theorem ren_pullback (x : Scoped) : ∀ (z : Scoped) (α β γ δ : Nat → Nat),
    IsRenPullback α β γ δ → ren α x = ren β z → ∃ w, x = ren γ w ∧ z = ren δ w := by
  induction x using Scoped.ind with
  | var i =>
      intro z α β γ δ hpb h
      obtain ⟨j, rfl, hj⟩ := ren_eq_var (ρ := β) (s := z) (i := α i) (by rw [← h, ren_var])
      obtain ⟨k, hk₁, hk₂⟩ := hpb i j hj.symm
      exact ⟨var k, by rw [ren_var, ← hk₁], by rw [ren_var, ← hk₂]⟩
  | abs p ih =>
      intro z α β γ δ hpb h
      rw [ren_abs] at h
      obtain ⟨q, rfl, hq⟩ := ren_eq_abs (ρ := β) (s := z) h.symm
      obtain ⟨w, hw₁, hw₂⟩ := ih q (upRen α) (upRen β) (upRen γ) (upRen δ) hpb.up hq
      exact ⟨abs w, by rw [ren_abs, ← hw₁], by rw [ren_abs, ← hw₂]⟩
  | app a b iha ihb =>
      intro z α β γ δ hpb h
      rw [ren_app] at h
      obtain ⟨u, v, rfl, hu, hv⟩ := ren_eq_app (ρ := β) (s := z) h.symm
      obtain ⟨w₁, hw₁, hw₁'⟩ := iha u α β γ δ hpb hu
      obtain ⟨w₂, hw₂, hw₂'⟩ := ihb v α β γ δ hpb hv
      exact ⟨app w₁ w₂, by rw [ren_app, ← hw₁, ← hw₂], by rw [ren_app, ← hw₁', ← hw₂']⟩

/-- The special case needed for the eta rule: if a term shifted past one binder
    is the shift of `z`, then both come from a common `w`. -/
theorem ren_upRen_succ_pullback {x z : Scoped}
    (h : ren (upRen Nat.succ) x = ren Nat.succ z) :
    ∃ w, x = ren Nat.succ w ∧ z = ren Nat.succ w := by
  refine ren_pullback x z (upRen Nat.succ) Nat.succ Nat.succ Nat.succ ?_ h
  intro i j hij
  cases i with
  | zero => exact Nat.noConfusion hij
  | succ i => exact ⟨i, rfl, (Nat.succ.inj hij).symm⟩

theorem ren_succ_inj {a b : Scoped} (h : ren Nat.succ a = ren Nat.succ b) : a = b := by
  have := congrArg (sub0 (var 0)) h
  rwa [sub0_ren_succ, sub0_ren_succ] at this

/-- Contracting the beta redex `(ƛ (ren (upRen succ) Q)) #0` gives back `Q`. -/
theorem sub0_var_zero_ren_upRen_succ (Q : Scoped) :
    sub0 (var 0) (ren (upRen Nat.succ) Q) = Q := by
  rw [sub0, sub_ren]
  have : (fun i => cons (var 0) var (upRen Nat.succ i)) = var := by
    funext i
    cases i with
    | zero => rfl
    | succ i => rfl
  rw [this, sub_var]

end Scoped

-- ====================================================================
-- 1. Eta reduction
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→η" => Eta

/-- Eta reduction: `ƛ (M #0) —→η M` when the bound index does not occur in `M`,
    that is, when the function part is a shifted term. -/
inductive Eta : Scoped → Scoped → Prop
  | basis (M : Scoped) :
      --------------------
      Scoped.abs (Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0)) —→η M
  | abs {M N : Scoped} :
      M —→η N
      --------------------
      → M.abs —→η N.abs
  | appr (L : Scoped) {M N : Scoped} :
      M —→η N
      --------------------
      → M.app L —→η N.app L
  | appl (L : Scoped) {M N : Scoped} :
      M —→η N
      --------------------
      → L.app M —→η L.app N

/-- Multi-step eta reduction. -/
abbrev EtaStar : Scoped → Scoped → Prop := Relation.ReflTransGen Eta

infix:64 " —→η* " => EtaStar

theorem eta_star_abs {M N : Scoped} (h : M —→η* N) : M.abs —→η* N.abs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.abs step)

theorem eta_star_appr {M M' : Scoped} (N : Scoped) (h : M —→η* M') :
    M.app N —→η* M'.app N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.appr N step)

theorem eta_star_appl {N N' : Scoped} (M : Scoped) (h : N —→η* N') :
    M.app N —→η* M.app N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.appl M step)

-- ====================================================================
-- 2. Inversion
-- ====================================================================

theorem Eta.var_inv {x s : Scoped} (h : x —→η s) : ∀ {i : Nat}, x ≠ Scoped.var i := by
  induction h with
  | basis M => intro i; exact Scoped.abs_ne_var
  | abs _ _ => intro i; exact Scoped.abs_ne_var
  | appr _ _ _ => intro i; exact Scoped.app_ne_var
  | appl _ _ _ => intro i; exact Scoped.app_ne_var

theorem Eta.abs_inv {x s : Scoped} (h : x —→η s) :
    ∀ {p : Scoped}, x = Scoped.abs p →
      (∃ M, p = Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0) ∧ s = M)
      ∨ (∃ p', s = Scoped.abs p' ∧ p —→η p') := by
  induction h with
  | basis M =>
      intro p hp
      exact Or.inl ⟨M, (Scoped.abs_eq_abs.mp hp).symm, rfl⟩
  | @abs M N hMN _ =>
      intro p hp
      cases Scoped.abs_eq_abs.mp hp
      exact Or.inr ⟨N, rfl, hMN⟩
  | appr _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | appl _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs

theorem Eta.abs_inv' {p s : Scoped} (h : Scoped.abs p —→η s) :
    (∃ M, p = Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0) ∧ s = M)
    ∨ (∃ p', s = Scoped.abs p' ∧ p —→η p') := h.abs_inv rfl

theorem Eta.app_inv {x s : Scoped} (h : x —→η s) :
    ∀ {a b : Scoped}, x = Scoped.app a b →
      (∃ a', s = Scoped.app a' b ∧ a —→η a')
      ∨ (∃ b', s = Scoped.app a b' ∧ b —→η b') := by
  induction h with
  | basis M => intro a b hab; exact absurd hab Scoped.abs_ne_app
  | abs _ _ => intro a b hab; exact absurd hab Scoped.abs_ne_app
  | @appr L M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inl ⟨N, rfl, hMN⟩
  | @appl L M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr ⟨N, rfl, hMN⟩

theorem Eta.app_inv' {a b s : Scoped} (h : Scoped.app a b —→η s) :
    (∃ a', s = Scoped.app a' b ∧ a —→η a')
    ∨ (∃ b', s = Scoped.app a b' ∧ b —→η b') := h.app_inv rfl

-- ====================================================================
-- 3. Stability under renaming and substitution
-- ====================================================================

theorem Eta.ren_mono {a b : Scoped} (h : a —→η b) : ∀ ρ : Nat → Nat,
    Scoped.ren ρ a —→η Scoped.ren ρ b := by
  induction h with
  | basis M =>
      intro ρ
      have e : Scoped.ren (Scoped.upRen ρ) (Scoped.ren Nat.succ M)
          = Scoped.ren Nat.succ (Scoped.ren ρ M) := by
        rw [Scoped.ren_ren, Scoped.ren_ren]
        rfl
      have e2 : Scoped.upRen ρ 0 = 0 := rfl
      simpa [e, e2] using Eta.basis (Scoped.ren ρ M)
  | abs _ ih => intro ρ; exact Eta.abs (ih _)
  | appr L _ ih => intro ρ; exact Eta.appr _ (ih _)
  | appl L _ ih => intro ρ; exact Eta.appl _ (ih _)

theorem Eta.sub_mono {a b : Scoped} (h : a —→η b) : ∀ σ : Nat → Scoped,
    Scoped.sub σ a —→η Scoped.sub σ b := by
  induction h with
  | basis M =>
      intro σ
      have e : Scoped.sub (Scoped.upSub σ) (Scoped.ren Nat.succ M)
          = Scoped.ren Nat.succ (Scoped.sub σ M) := Scoped.sub_upSub_ren_succ σ M
      have e2 : Scoped.upSub σ 0 = Scoped.var 0 := rfl
      simpa [e, e2] using Eta.basis (Scoped.sub σ M)
  | abs _ ih => intro σ; exact Eta.abs (ih _)
  | appr L _ ih => intro σ; exact Eta.appr _ (ih _)
  | appl L _ ih => intro σ; exact Eta.appl _ (ih _)

theorem EtaStar.ren_mono {a b : Scoped} (h : a —→η* b) (ρ : Nat → Nat) :
    Scoped.ren ρ a —→η* Scoped.ren ρ b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (step.ren_mono ρ)

/-- Substituting eta-related terms gives eta-related terms. -/
theorem Eta.sub_congr {σ τ : Nat → Scoped} (h : ∀ i, σ i —→η* τ i) (s : Scoped) :
    Scoped.sub σ s —→η* Scoped.sub τ s := by
  induction s using Scoped.ind generalizing σ τ with
  | var i => simpa using h i
  | abs p ih =>
      refine eta_star_abs (ih ?_)
      intro i
      cases i with
      | zero => exact Relation.ReflTransGen.refl
      | succ i => exact (h i).ren_mono Nat.succ
  | app a b iha ihb =>
      exact (eta_star_appr _ (iha h)).trans (eta_star_appl _ (ihb h))

theorem Eta.sub0_congr {N N' : Scoped} (h : N —→η N') (M : Scoped) :
    Scoped.sub0 N M —→η* Scoped.sub0 N' M := by
  refine Eta.sub_congr ?_ M
  intro i
  cases i with
  | zero => exact Relation.ReflTransGen.single h
  | succ i => exact Relation.ReflTransGen.refl

-- ====================================================================
-- 4. Renamings reflect eta and beta steps
-- ====================================================================

/-- The pullback square used by the eta rule under a binder: if `upRen ρ i` is a
    successor `j + 1`, then `i` is a successor `k + 1` and `j = ρ k`. -/
theorem Scoped.upRen_succ_pullback (ρ : Nat → Nat) :
    Scoped.IsRenPullback (Scoped.upRen ρ) Nat.succ Nat.succ ρ := by
  intro i j hij
  cases i with
  | zero => exact Nat.noConfusion hij
  | succ i => exact ⟨i, rfl, (Nat.succ.inj hij).symm⟩

theorem Scoped.upRen_eq_zero {ρ : Nat → Nat} {j : Nat} (h : Scoped.upRen ρ j = 0) : j = 0 := by
  cases j with
  | zero => rfl
  | succ j => exact absurd h (by simp [Scoped.upRen])

/-- Renamings reflect eta steps. -/
theorem Eta.ren_reflect_gen (M : Scoped) : ∀ (ρ : Nat → Nat) (Y : Scoped),
    Scoped.ren ρ M —→η Y → ∃ M', Y = Scoped.ren ρ M' ∧ M —→η M' := by
  induction M using Scoped.ind with
  | var i =>
      intro ρ Y h
      rw [Scoped.ren_var] at h
      exact absurd rfl (h.var_inv (i := ρ i))
  | abs p ih =>
      intro ρ Y h
      rw [Scoped.ren_abs] at h
      rcases h.abs_inv' with ⟨Z, hZ, hYZ⟩ | ⟨p', rfl, hp'⟩
      · -- the eta redex is at the top
        obtain ⟨a, b, rfl, ha, hb⟩ := Scoped.ren_eq_app (ρ := Scoped.upRen ρ) (s := p) hZ
        obtain ⟨j, rfl, hj⟩ := Scoped.ren_eq_var (ρ := Scoped.upRen ρ) (s := b) hb.symm
        cases Scoped.upRen_eq_zero hj
        obtain ⟨w, hw₁, hw₂⟩ :=
          Scoped.ren_pullback a Z (Scoped.upRen ρ) Nat.succ Nat.succ ρ
            (Scoped.upRen_succ_pullback ρ) ha.symm
        refine ⟨w, by rw [hYZ, hw₂], ?_⟩
        rw [hw₁]
        exact Eta.basis w
      · obtain ⟨q, rfl, hq⟩ := ih (Scoped.upRen ρ) p' hp'
        exact ⟨Scoped.abs q, by rw [Scoped.ren_abs], Eta.abs hq⟩
  | app a b iha ihb =>
      intro ρ Y h
      rw [Scoped.ren_app] at h
      rcases h.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨a₁, rfl, ha₁⟩ := iha ρ a' ha'
        exact ⟨Scoped.app a₁ b, by rw [Scoped.ren_app], Eta.appr b ha₁⟩
      · obtain ⟨b₁, rfl, hb₁⟩ := ihb ρ b' hb'
        exact ⟨Scoped.app a b₁, by rw [Scoped.ren_app], Eta.appl a hb₁⟩

theorem Eta.ren_reflect {M Y : Scoped} (h : Scoped.ren Nat.succ M —→η Y) :
    ∃ M', Y = Scoped.ren Nat.succ M' ∧ M —→η M' :=
  Eta.ren_reflect_gen M Nat.succ Y h

/-- Renamings reflect beta steps. -/
theorem Beta.ren_reflect_gen (M : Scoped) : ∀ (ρ : Nat → Nat) (Y : Scoped),
    Scoped.ren ρ M —→ Y → ∃ M', Y = Scoped.ren ρ M' ∧ M —→ M' := by
  induction M using Scoped.ind with
  | var i =>
      intro ρ Y h
      rw [Scoped.ren_var] at h
      exact absurd rfl (h.var_inv (i := ρ i))
  | abs p ih =>
      intro ρ Y h
      rw [Scoped.ren_abs] at h
      obtain ⟨p', rfl, hp'⟩ := h.abs_inv'
      obtain ⟨q, rfl, hq⟩ := ih (Scoped.upRen ρ) p' hp'
      exact ⟨Scoped.abs q, by rw [Scoped.ren_abs], Beta.abs hq⟩
  | app a b iha ihb =>
      intro ρ Y h
      rw [Scoped.ren_app] at h
      rcases h.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨a₁, rfl, ha₁⟩ := iha ρ a' ha'
        exact ⟨Scoped.app a₁ b, by rw [Scoped.ren_app], Beta.appr b ha₁⟩
      · obtain ⟨b₁, rfl, hb₁⟩ := ihb ρ b' hb'
        exact ⟨Scoped.app a b₁, by rw [Scoped.ren_app], Beta.appl a hb₁⟩
      · obtain ⟨q, rfl, rfl⟩ := Scoped.ren_eq_abs (ρ := ρ) (s := a) hp
        refine ⟨Scoped.sub0 b q, ?_, ?_⟩
        · rw [Scoped.ren_sub0]
        · exact Beta.basis' q b

theorem Beta.ren_reflect {ρ : Nat → Nat} {M Y : Scoped} (h : Scoped.ren ρ M —→ Y) :
    ∃ M', Y = Scoped.ren ρ M' ∧ M —→ M' :=
  Beta.ren_reflect_gen M ρ Y h

-- ====================================================================
-- 5. Eta is subcommutative, hence confluent
-- ====================================================================

theorem Eta.reflGen_abs {x y : Scoped} (h : Relation.ReflGen Eta x y) :
    Relation.ReflGen Eta x.abs y.abs := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.abs h)

theorem Eta.reflGen_appr {x y : Scoped} (L : Scoped) (h : Relation.ReflGen Eta x y) :
    Relation.ReflGen Eta (x.app L) (y.app L) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.appr L h)

theorem Eta.reflGen_appl {x y : Scoped} (L : Scoped) (h : Relation.ReflGen Eta x y) :
    Relation.ReflGen Eta (L.app x) (L.app y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.appl L h)

/-- **Eta reduction is subcommutative**: two eta reducts of a term are joinable
    in at most one step each. -/
theorem Eta.subcommutative {a b : Scoped} (h₁ : a —→η b) : ∀ c : Scoped, a —→η c →
    ∃ d, Relation.ReflGen Eta b d ∧ Relation.ReflGen Eta c d := by
  induction h₁ with
  | basis M =>
      intro c h₂
      rcases h₂.abs_inv' with ⟨M₂, hM₂, rfl⟩ | ⟨p', rfl, hp'⟩
      · obtain ⟨he, _⟩ := Scoped.app_eq_app.mp hM₂
        cases Scoped.ren_succ_inj he
        exact ⟨M, Relation.ReflGen.refl, Relation.ReflGen.refl⟩
      · rcases hp'.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩
        · obtain ⟨M₂, rfl, hM₂⟩ := Eta.ren_reflect ha'
          exact ⟨M₂, Relation.ReflGen.single hM₂, Relation.ReflGen.single (Eta.basis M₂)⟩
        · exact absurd rfl (hb'.var_inv (i := 0))
  | @abs M N hMN ih =>
      intro c h₂
      rcases h₂.abs_inv' with ⟨Z, hZ, rfl⟩ | ⟨p', rfl, hp'⟩
      · subst hZ
        rcases hMN.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩
        · obtain ⟨Z', rfl, hZ'⟩ := Eta.ren_reflect ha'
          exact ⟨Z', Relation.ReflGen.single (Eta.basis Z'), Relation.ReflGen.single hZ'⟩
        · exact absurd rfl (hb'.var_inv (i := 0))
      · obtain ⟨d, hd₁, hd₂⟩ := ih p' hp'
        exact ⟨d.abs, Eta.reflGen_abs hd₁, Eta.reflGen_abs hd₂⟩
  | @appr L M N hMN ih =>
      intro c h₂
      rcases h₂.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih a' ha'
        exact ⟨d.app L, Eta.reflGen_appr L hd₁, Eta.reflGen_appr L hd₂⟩
      · exact ⟨N.app b', Relation.ReflGen.single (Eta.appl N hb'),
          Relation.ReflGen.single (Eta.appr b' hMN)⟩
  | @appl L M N hMN ih =>
      intro c h₂
      rcases h₂.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · exact ⟨a'.app N, Relation.ReflGen.single (Eta.appr N ha'),
          Relation.ReflGen.single (Eta.appl a' hMN)⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih b' hb'
        exact ⟨L.app d, Eta.reflGen_appl L hd₁, Eta.reflGen_appl L hd₂⟩

/-- **The Church-Rosser theorem for eta reduction.** -/
theorem eta_church_rosser {a b c : Scoped} (hab : a —→η* b) (hac : a —→η* c) :
    ∃ d, b —→η* d ∧ c —→η* d := by
  have h := Relation.church_rosser
    (r := Eta)
    (fun x y z hxy hxz => by
      obtain ⟨d, hd₁, hd₂⟩ := Eta.subcommutative hxy z hxz
      exact ⟨d, hd₁, hd₂.to_reflTransGen⟩)
    hab hac
  obtain ⟨d, hbd, hcd⟩ := h
  exact ⟨d, hbd, hcd⟩

end IwilareNatIsExactScope
