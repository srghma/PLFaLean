-- Weak head reduction, weak head normal forms, and the Weak Head
-- Normalization Theorem.
--
-- The head reduction `—→ₕ` of `Standardization.lean` never goes under an
-- abstraction nor into an argument, so its normal forms are the *weak head
-- normal forms*: the abstractions and the terms whose head is a variable
-- (`whnf_iff`).  Weak head reduction is deterministic (`HeadBeta.deterministic`)
-- and it is normalizing for weak head normal forms:
--
--   `whnf_normalization : M —→* N → Whnf N → ∃ P, M —→ₕ* P ∧ Whnf P ∧ P —→* N`
--
-- so a term that reduces to a weak head normal form already *head*-reduces to
-- one: call-by-name evaluation cannot miss it.  The corresponding evaluator
-- `Scoped.evalCBN` is proved sound and complete.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Leftmost

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 1. Weak head normal forms
-- ====================================================================

/-- A term is in *weak head normal form* when no head step applies to it. -/
def Whnf (M : Scoped) : Prop := ∀ N, ¬ M —→ₕ N

/-- Terms whose head is a variable. -/
inductive HeadVar : Scoped → Prop
  | var (i : Nat) : HeadVar (Scoped.var i)
  | app {a : Scoped} (b : Scoped) : HeadVar a → HeadVar (Scoped.app a b)

/-- Inversion for a head step out of an application. -/
theorem HeadBeta.app_inv {x s : Scoped} (h : x —→ₕ s) :
    ∀ {a b : Scoped}, x = Scoped.app a b →
      (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p)
      ∨ (∃ a', s = Scoped.app a' b ∧ a —→ₕ a') := by
  induction h with
  | basis M N =>
      intro a b hab
      obtain ⟨ha, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inl ⟨M, ha.symm ▸ rfl, rfl⟩
  | @appr L M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr ⟨N, rfl, hMN⟩

theorem HeadBeta.app_inv' {a b s : Scoped} (h : Scoped.app a b —→ₕ s) :
    (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p)
    ∨ (∃ a', s = Scoped.app a' b ∧ a —→ₕ a') := h.app_inv rfl

theorem Whnf.var (i : Nat) : Whnf (Scoped.var i) :=
  fun _ h => h.to_beta.var_inv rfl

theorem Whnf.abs (M : Scoped) : Whnf (Scoped.abs M) :=
  fun _ h => HeadBeta.not_isAbs h ⟨M, rfl⟩

theorem Whnf.app_inv {a b : Scoped} (h : Whnf (Scoped.app a b)) : Whnf a ∧ ¬ IsAbs a := by
  refine ⟨fun x hx => h _ (HeadBeta.appr b hx), ?_⟩
  rintro ⟨p, rfl⟩
  exact h _ (HeadBeta.basis p b)

theorem Whnf.app {a b : Scoped} (ha : Whnf a) (hna : ¬ IsAbs a) : Whnf (Scoped.app a b) := by
  intro N h
  rcases h.app_inv' with ⟨p, hp, _⟩ | ⟨a', _, hstep⟩
  · exact hna ⟨p, hp⟩
  · exact ha _ hstep

theorem HeadVar.not_isAbs {a : Scoped} (h : HeadVar a) : ¬ IsAbs a := by
  cases h with
  | var i => rintro ⟨p, hp⟩; exact absurd hp Scoped.var_ne_abs
  | app b _ => rintro ⟨p, hp⟩; exact absurd hp Scoped.app_ne_abs

theorem HeadVar.to_whnf {a : Scoped} (h : HeadVar a) : Whnf a := by
  induction h with
  | var i => exact Whnf.var i
  | app b hv ih => exact ih.app hv.not_isAbs

/-- **The weak head normal forms** are exactly the abstractions and the terms
    headed by a variable. -/
theorem whnf_iff {a : Scoped} : Whnf a ↔ IsAbs a ∨ HeadVar a := by
  refine ⟨fun h => ?_, fun h => h.elim (fun ⟨p, hp⟩ => hp ▸ Whnf.abs p) HeadVar.to_whnf⟩
  induction a using Scoped.ind with
  | var i => exact Or.inr (HeadVar.var i)
  | abs s _ => exact Or.inl ⟨s, rfl⟩
  | app x y ihx _ =>
      obtain ⟨hx, hnx⟩ := h.app_inv
      rcases ihx hx with habs | hv
      · exact absurd habs hnx
      · exact Or.inr (HeadVar.app y hv)

/-- Weak head reduction is deterministic. -/
theorem HeadBeta.deterministic {a b c : Scoped} (h₁ : a —→ₕ b) (h₂ : a —→ₕ c) : b = c := by
  induction h₁ generalizing c with
  | basis M N =>
      rcases h₂.app_inv' with ⟨p, hp, rfl⟩ | ⟨a', rfl, hstep⟩
      · cases Scoped.abs_eq_abs.mp hp; rfl
      · exact absurd ⟨M, rfl⟩ (HeadBeta.not_isAbs hstep)
  | @appr L M N hMN ih =>
      rcases h₂.app_inv' with ⟨p, hp, rfl⟩ | ⟨a', rfl, hstep⟩
      · exact absurd ⟨p, hp⟩ (HeadBeta.not_isAbs hMN)
      · exact Scoped.app_eq_app.mpr ⟨ih hstep, rfl⟩

/-- Every term is either in weak head normal form or admits a head step. -/
theorem whnf_progress (M : Scoped) : Whnf M ∨ ∃ N, M —→ₕ N := by
  induction M using Scoped.ind with
  | var i => exact Or.inl (Whnf.var i)
  | abs s _ => exact Or.inl (Whnf.abs s)
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        exact Or.inr ⟨Scoped.sub0 b p, HeadBeta.basis p b⟩
      · rcases iha with hna | ⟨a', ha'⟩
        · exact Or.inl (hna.app hab)
        · exact Or.inr ⟨Scoped.app a' b, HeadBeta.appr b ha'⟩

-- ====================================================================
-- 2. The Weak Head Normalization Theorem
-- ====================================================================

theorem headBetaStar_appr {M M' : Scoped} (N : Scoped) (h : M —→ₕ* M') :
    Scoped.app M N —→ₕ* Scoped.app M' N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (HeadBeta.appr N step)

/-- A standard reduction to a weak head normal form starts with head steps that
    already reach a weak head normal form. -/
theorem StdRed.abs_source {p x : Scoped} (h : Scoped.abs p —→ₛ x) : IsAbs x := by
  generalize hs : Scoped.abs p = a at h
  induction h generalizing p with
  | var i => exact absurd hs.symm Scoped.var_ne_abs
  | @abs M N _ _ => exact ⟨N, rfl⟩
  | app _ _ _ _ => exact absurd hs Scoped.abs_ne_app
  | @head L M N hLM _ _ =>
      cases hs
      exact absurd ⟨p, rfl⟩ (HeadBeta.not_isAbs hLM)

/-- A standard reduction to a weak head normal form starts with head steps that
    already reach a weak head normal form. -/
theorem StdRed.whnf_target {a b : Scoped} (h : a —→ₛ b) : Whnf b →
    ∃ P, a —→ₕ* P ∧ P —→ₛ b ∧ Whnf P := by
  induction h with
  | var i => intro hb; exact ⟨Scoped.var i, Relation.ReflTransGen.refl, StdRed.var i, Whnf.var i⟩
  | @abs M N hMN _ =>
      intro _
      exact ⟨Scoped.abs M, Relation.ReflTransGen.refl, StdRed.abs hMN, Whnf.abs M⟩
  | @app M M' N N' hM hN ihM _ =>
      intro hb
      obtain ⟨hM', hna⟩ := hb.app_inv
      obtain ⟨P, hhead, hstd, hP⟩ := ihM hM'
      have hPna : ¬ IsAbs P := by
        rintro ⟨q, rfl⟩
        exact hna (StdRed.abs_source hstd)
      exact ⟨Scoped.app P N, headBetaStar_appr N hhead, StdRed.app hstd hN, hP.app hPna⟩
  | @head L M N hLM _ ih =>
      intro hb
      obtain ⟨P, hhead, hstd, hP⟩ := ih hb
      exact ⟨P, Relation.ReflTransGen.head hLM hhead, hstd, hP⟩

/-- **The Weak Head Normalization Theorem**: if a term reduces to a weak head
    normal form, then it *head*-reduces to one. -/
theorem whnf_normalization {M N : Scoped} (h : M —→* N) (hN : Whnf N) :
    ∃ P, M —→ₕ* P ∧ Whnf P ∧ P —→* N := by
  obtain ⟨P, hhead, hstd, hP⟩ := (stdRed_of_betastar h).whnf_target hN
  exact ⟨P, hhead, hP, hstd.to_betastar⟩

-- ====================================================================
-- 3. Call-by-name evaluation
-- ====================================================================

namespace Term

/-- Contract the head redex, if there is one. -/
def whstepT : {n : Nat} → Term n → Option Scoped
  | _, .var _ => none
  | _, .abs _ => none
  | _, .app (.abs p) q => some (Scoped.sub0 ⟨_, q⟩ ⟨_, p⟩)
  | _, .app a b =>
      match whstepT a with
      | some a' => some (Scoped.app a' ⟨_, b⟩)
      | none => none

end Term

namespace Scoped

/-- Contract the head redex, if there is one. -/
def whstep (s : Scoped) : Option Scoped := Term.whstepT s.2

@[simp] theorem whstep_var (i : Nat) : whstep (var i) = none := rfl
@[simp] theorem whstep_abs (s : Scoped) : whstep (abs s) = none := rfl
@[simp] theorem whstep_app_abs (p q : Scoped) : whstep (app (abs p) q) = some (sub0 q p) := rfl

theorem whstep_app_of_not_isAbs {a : Scoped} (ha : ¬ IsAbs a) (b : Scoped) :
    whstep (app a b) =
      match whstep a with
      | some a' => some (app a' b)
      | none => none := by
  obtain ⟨n, t⟩ := a
  cases t with
  | var i => rfl
  | abs t => exact absurd ⟨⟨_, t⟩, rfl⟩ ha
  | app x y => rfl

/-- Call-by-name evaluation: contract the head redex at most `fuel` times. -/
def evalCBN : Nat → Scoped → Option Scoped
  | 0, _ => none
  | fuel + 1, s =>
      match s.whstep with
      | none => some s
      | some t => evalCBN fuel t

end Scoped

theorem Scoped.whstep_none_whnf {s : Scoped} (h : s.whstep = none) : Whnf s := by
  induction s using Scoped.ind with
  | var i => exact Whnf.var i
  | abs s _ => exact Whnf.abs s
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        rw [Scoped.whstep_app_abs] at h
        exact absurd h (by simp)
      · rw [Scoped.whstep_app_of_not_isAbs hab] at h
        cases ha : a.whstep with
        | some a' => rw [ha] at h; exact absurd h (by simp)
        | none => exact (iha ha).app hab

theorem Scoped.whstep_some {s t : Scoped} (h : s.whstep = some t) : s —→ₕ t := by
  induction s using Scoped.ind generalizing t with
  | var i => simp at h
  | abs s _ => simp at h
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        rw [Scoped.whstep_app_abs] at h
        cases h
        exact HeadBeta.basis p b
      · rw [Scoped.whstep_app_of_not_isAbs hab] at h
        cases ha : a.whstep with
        | some a' =>
            rw [ha] at h
            cases h
            exact HeadBeta.appr b (iha ha)
        | none => rw [ha] at h; exact absurd h (by simp)

theorem Scoped.whstep_eq_some_iff {s t : Scoped} : s.whstep = some t ↔ s —→ₕ t := by
  refine ⟨Scoped.whstep_some, fun h => ?_⟩
  cases hs : s.whstep with
  | none => exact absurd h (Scoped.whstep_none_whnf hs t)
  | some u => rw [(Scoped.whstep_some hs).deterministic h]

theorem Scoped.evalCBN_succ (fuel : Nat) (s : Scoped) :
    Scoped.evalCBN (fuel + 1) s =
      match s.whstep with
      | none => some s
      | some t => Scoped.evalCBN fuel t := rfl

/-- **Soundness of call-by-name evaluation**. -/
theorem evalCBN_sound : ∀ (fuel : Nat) {s t : Scoped}, Scoped.evalCBN fuel s = some t →
    s —→ₕ* t ∧ Whnf t := by
  intro fuel
  induction fuel with
  | zero => intro s t h; exact absurd h (by simp [Scoped.evalCBN])
  | succ fuel ih =>
      intro s t h
      rw [Scoped.evalCBN_succ] at h
      cases hs : s.whstep with
      | none =>
          rw [hs] at h
          cases h
          exact ⟨Relation.ReflTransGen.refl, Scoped.whstep_none_whnf hs⟩
      | some u =>
          rw [hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Scoped.whstep_some hs) hred, hnorm⟩

/-- **Completeness of call-by-name evaluation**. -/
theorem evalCBN_complete {s t : Scoped} (h : s —→ₕ* t) (ht : Whnf t) :
    ∃ fuel, Scoped.evalCBN fuel s = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, ?_⟩
      rw [Scoped.evalCBN_succ]
      cases hs : t.whstep with
      | none => rfl
      | some u => exact absurd (Scoped.whstep_some hs) (ht u)
  | head hstep _ ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [Scoped.evalCBN_succ, Scoped.whstep_eq_some_iff.mpr hstep]
      exact hfuel

/-- **Having a weak head normal form is semi-decidable**, by call-by-name
    evaluation. -/
theorem has_whnf_iff_evalCBN {s : Scoped} :
    (∃ t, s —→* t ∧ Whnf t) ↔ ∃ fuel t, Scoped.evalCBN fuel s = some t := by
  constructor
  · rintro ⟨t, hred, ht⟩
    obtain ⟨P, hhead, hP, _⟩ := whnf_normalization hred ht
    obtain ⟨fuel, hfuel⟩ := evalCBN_complete hhead hP
    exact ⟨fuel, P, hfuel⟩
  · rintro ⟨fuel, t, h⟩
    obtain ⟨hred, ht⟩ := evalCBN_sound fuel h
    refine ⟨t, ?_, ht⟩
    clear ht h
    induction hred with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.tail ih step.to_beta

end IwilareNatIsExactScope
