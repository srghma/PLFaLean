-- The Standardization Theorem for the exactly-scoped lambda calculus.
--
-- A *standard* reduction sequence is one that never contracts a redex to the
-- left of a redex it has already contracted: it first performs head reduction
-- steps (the head redex is the leftmost-outermost one), and only then reduces
-- the subterms, left to right, recursively.  This is exactly the inductive
-- relation `StdRed` below (`—→ₛ`):
--
--   * `head` : do a head reduction step first, then continue standardly;
--   * `abs` / `app` / `var` : otherwise reduce the immediate subterms standardly.
--
-- The Standardization Theorem says that every reduction can be rearranged into
-- a standard one:  `M —→* N  ↔  M —→ₛ N`  (`standardization`).
--
-- The proof is Kashima's: the standard reductions absorb a beta step at the end
-- (`StdRed.append_beta`), whose crucial case is `StdRed.app_abs`.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Basic

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 1. Head reduction: contract the leftmost-outermost redex
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→ₕ" => HeadBeta

/-- Head reduction: the redex contracted is the head redex, i.e. the leftmost
    outermost one.  Note that no rule goes under an abstraction or into the
    argument of an application. -/
inductive HeadBeta : Scoped → Scoped → Prop
  | basis (M N : Scoped) :
      --------------------
      Scoped.app (Scoped.abs M) N —→ₕ Scoped.sub0 N M
  | appr (L : Scoped) {M N : Scoped} :
      M —→ₕ N
      --------------------
      → M.app L —→ₕ N.app L

theorem HeadBeta.to_beta {a b : Scoped} (h : a —→ₕ b) : a —→ b := by
  induction h with
  | basis M N => exact Beta.basis' M N
  | appr L _ ih => exact Beta.appr L ih

/-- Head reduction is stable under renaming. -/
theorem HeadBeta.ren_mono {a b : Scoped} (h : a —→ₕ b) (ρ : Nat → Nat) :
    Scoped.ren ρ a —→ₕ Scoped.ren ρ b := by
  induction h generalizing ρ with
  | basis M N =>
      rw [Scoped.ren_app, Scoped.ren_abs, Scoped.ren_sub0]
      exact HeadBeta.basis _ _
  | appr L _ ih => exact HeadBeta.appr _ (ih ρ)

/-- Head reduction is stable under parallel substitution. -/
theorem HeadBeta.sub_mono {a b : Scoped} (h : a —→ₕ b) (σ : Nat → Scoped) :
    Scoped.sub σ a —→ₕ Scoped.sub σ b := by
  induction h generalizing σ with
  | basis M N =>
      rw [Scoped.sub_app, Scoped.sub_abs, Scoped.sub_sub0]
      exact HeadBeta.basis _ _
  | appr L _ ih => exact HeadBeta.appr _ (ih σ)

-- ====================================================================
-- 2. Standard reductions
-- ====================================================================

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→ₛ" => StdRed

/-- `M —→ₛ N` : there is a *standard* reduction sequence from `M` to `N`. -/
inductive StdRed : Scoped → Scoped → Prop
  | var (i : Nat) :
      --------------------
      Scoped.var i —→ₛ Scoped.var i
  | abs {M N : Scoped} :
      M —→ₛ N
      --------------------
      → M.abs —→ₛ N.abs
  | app {M M' N N' : Scoped} :
      M —→ₛ M'
      → N —→ₛ N'
      --------------------
      → M.app N —→ₛ M'.app N'
  | head {L M N : Scoped} :
      L —→ₕ M
      → M —→ₛ N
      --------------------
      → L —→ₛ N

/-- The empty reduction sequence is standard. -/
theorem StdRed.refl (M : Scoped) : M —→ₛ M := by
  induction M using Scoped.ind with
  | var i => exact StdRed.var i
  | abs M ih => exact StdRed.abs ih
  | app M N ihM ihN => exact StdRed.app ihM ihN

/-- **Soundness**: a standard reduction sequence is a reduction sequence. -/
theorem StdRed.to_betastar {a b : Scoped} (h : a —→ₛ b) : a —→* b := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact beta_star_abs ih
  | app _ _ ihM ihN =>
      exact Relation.ReflTransGen.trans (beta_star_appr _ ihM) (beta_star_appl _ ihN)
  | head hLM _ ih => exact Relation.ReflTransGen.head hLM.to_beta ih

/-- Standard reductions are stable under renaming. -/
theorem StdRed.ren_mono {a b : Scoped} (h : a —→ₛ b) : ∀ ρ : Nat → Nat,
    Scoped.ren ρ a —→ₛ Scoped.ren ρ b := by
  induction h with
  | var i => intro ρ; exact StdRed.var _
  | abs _ ih => intro ρ; exact StdRed.abs (ih _)
  | app _ _ ihM ihN => intro ρ; exact StdRed.app (ihM _) (ihN _)
  | head hLM _ ih => intro ρ; exact StdRed.head (hLM.ren_mono ρ) (ih ρ)

/-- Standard reductions are stable under parallel substitution. -/
theorem StdRed.sub_mono {a b : Scoped} (h : a —→ₛ b) :
    ∀ {σ σ' : Nat → Scoped}, (∀ i, σ i —→ₛ σ' i) →
      Scoped.sub σ a —→ₛ Scoped.sub σ' b := by
  induction h with
  | var i => intro σ σ' hσ; exact hσ i
  | abs _ ih =>
      intro σ σ' hσ
      refine StdRed.abs (ih ?_)
      intro i
      cases i with
      | zero => exact StdRed.var 0
      | succ j => exact (hσ j).ren_mono _
  | app _ _ ihM ihN => intro σ σ' hσ; exact StdRed.app (ihM hσ) (ihN hσ)
  | @head L M N hLM _ ih =>
      intro σ σ' hσ
      exact StdRed.head (hLM.sub_mono σ) (ih hσ)

theorem StdRed.sub0_mono {p p' q q' : Scoped} (hp : p —→ₛ p') (hq : q —→ₛ q') :
    Scoped.sub0 q p —→ₛ Scoped.sub0 q' p' := by
  refine hp.sub_mono ?_
  intro i
  cases i with
  | zero => exact hq
  | succ j => exact StdRed.var j

/-- The crucial case of the standardization proof: if `a` standardly reduces to
    an abstraction `ƛ p`, then `a b` standardly reduces to the contractum
    `p[b']` -- the head redex being contracted *first*. -/
theorem StdRed.app_abs {a x : Scoped} (h : a —→ₛ x) :
    ∀ {p b b' : Scoped}, x = Scoped.abs p → b —→ₛ b' →
      Scoped.app a b —→ₛ Scoped.sub0 b' p := by
  induction h with
  | var i => intro p b b' hx _; exact absurd hx Scoped.var_ne_abs
  | @abs M N hMN _ =>
      intro p b b' hx hb
      cases Scoped.abs_eq_abs.mp hx
      exact StdRed.head (HeadBeta.basis M b) (StdRed.sub0_mono hMN hb)
  | app _ _ _ _ => intro p b b' hx _; exact absurd hx Scoped.app_ne_abs
  | @head L M N hLM _ ih =>
      intro p b b' hx hb
      exact StdRed.head (HeadBeta.appr b hLM) (ih hx hb)

-- ====================================================================
-- 3. Inversion lemmas for single-step beta reduction
-- ====================================================================

theorem Beta.var_inv {x s : Scoped} (h : x —→ s) : ∀ {i : Nat}, x ≠ Scoped.var i := by
  induction h with
  | appl _ _ _ => intro i; exact Scoped.app_ne_var
  | appr _ _ _ => intro i; exact Scoped.app_ne_var
  | abs _ _ => intro i; exact Scoped.abs_ne_var
  | basis M N => intro i; exact Scoped.app_ne_var

theorem Beta.abs_inv {x s : Scoped} (h : x —→ s) :
    ∀ {p : Scoped}, x = Scoped.abs p → ∃ p', s = Scoped.abs p' ∧ p —→ p' := by
  induction h with
  | appl _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | appr _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | @abs M N hMN _ =>
      intro p hp
      cases Scoped.abs_eq_abs.mp hp
      exact ⟨N, rfl, hMN⟩
  | basis M N => intro p hp; exact absurd hp Scoped.app_ne_abs

theorem Beta.abs_inv' {p s : Scoped} (h : Scoped.abs p —→ s) :
    ∃ p', s = Scoped.abs p' ∧ p —→ p' := h.abs_inv rfl

theorem Beta.app_inv {x s : Scoped} (h : x —→ s) :
    ∀ {a b : Scoped}, x = Scoped.app a b →
      (∃ a', s = Scoped.app a' b ∧ a —→ a')
      ∨ (∃ b', s = Scoped.app a b' ∧ b —→ b')
      ∨ (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p) := by
  induction h with
  | @appl L M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr (Or.inl ⟨N, rfl, hMN⟩)
  | @appr L M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inl ⟨N, rfl, hMN⟩
  | abs _ _ => intro a b hab; exact absurd hab Scoped.abs_ne_app
  | @basis m n M N =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr (Or.inr ⟨⟨m, M⟩, rfl, Term.betaSubstSigma_eq_sub0 M N⟩)

theorem Beta.app_inv' {a b s : Scoped} (h : Scoped.app a b —→ s) :
    (∃ a', s = Scoped.app a' b ∧ a —→ a')
    ∨ (∃ b', s = Scoped.app a b' ∧ b —→ b')
    ∨ (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p) := h.app_inv rfl

-- ====================================================================
-- 4. Standard reductions absorb a beta step, and the theorem
-- ====================================================================

/-- **Kashima's lemma**: appending a beta step to a standard reduction sequence
    gives (after rearranging) a standard reduction sequence again. -/
theorem StdRed.append_beta {a b : Scoped} (h : a —→ₛ b) :
    ∀ {c : Scoped}, b —→ c → a —→ₛ c := by
  induction h with
  | var i => intro c hc; exact absurd rfl hc.var_inv
  | @abs M N _ ih =>
      intro c hc
      obtain ⟨N', rfl, hstep⟩ := hc.abs_inv'
      exact StdRed.abs (ih hstep)
  | @app M M' N N' hM hN ihM ihN =>
      intro c hc
      rcases hc.app_inv' with ⟨a', rfl, hstep⟩ | ⟨b', rfl, hstep⟩ | ⟨p, hp, rfl⟩
      · exact StdRed.app (ihM hstep) hN
      · exact StdRed.app hM (ihN hstep)
      · exact StdRed.app_abs hM hp hN
  | head hLM _ ih => intro c hc; exact StdRed.head hLM (ih hc)

/-- **Completeness**: every reduction sequence can be rearranged into a standard
    one. -/
theorem stdRed_of_betastar {a b : Scoped} (h : a —→* b) : a —→ₛ b := by
  induction h with
  | refl => exact StdRed.refl _
  | tail _ step ih => exact ih.append_beta step

/-- **The Standardization Theorem**: `M` reduces to `N` if and only if there is a
    *standard* reduction sequence from `M` to `N`, i.e. one that contracts the
    head redex first and then reduces the subterms, left to right. -/
theorem standardization {a b : Scoped} : a —→* b ↔ a —→ₛ b :=
  ⟨stdRed_of_betastar, StdRed.to_betastar⟩

/-- Multi-step head reduction. -/
abbrev HeadBetaStar : Scoped → Scoped → Prop := Relation.ReflTransGen HeadBeta

infix:64 " —→ₕ* " => HeadBetaStar

theorem StdRed.abs_target {a x : Scoped} (h : a —→ₛ x) :
    ∀ {N : Scoped}, x = Scoped.abs N → ∃ P, a —→ₕ* Scoped.abs P ∧ P —→* N := by
  induction h with
  | var i => intro N hN; exact absurd hN Scoped.var_ne_abs
  | @abs M M' hMM' _ =>
      intro N hN
      cases Scoped.abs_eq_abs.mp hN
      exact ⟨M, Relation.ReflTransGen.refl, hMM'.to_betastar⟩
  | app _ _ _ _ => intro N hN; exact absurd hN Scoped.app_ne_abs
  | head hLM _ ih =>
      intro N hN
      obtain ⟨P, hhead, hbeta⟩ := ih hN
      exact ⟨P, Relation.ReflTransGen.head hLM hhead, hbeta⟩

/-- A typical consequence of standardization: if a term reduces to an
    abstraction, then it *head*-reduces to an abstraction. -/
theorem head_reduces_to_abs {M N : Scoped} (h : M —→* Scoped.abs N) :
    ∃ P, M —→ₕ* Scoped.abs P ∧ P —→* N :=
  (stdRed_of_betastar h).abs_target rfl

end IwilareNatIsExactScope
