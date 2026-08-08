-- Weak head reduction, weak head normal forms, and the Weak Head
-- Normalization Theorem, for the scope-bounded (`Fin`-indexed) calculus.
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
-- `evalCBN` is proved sound and complete.
--
-- Here the evaluator has the pleasant type `Term n → Option (Term n)`: the
-- scope is preserved by evaluation, so nothing has to be packed into a Sigma
-- type as in the exactly-scoped development.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Leftmost

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Weak head normal forms -/

/-- A term is in *weak head normal form* when no head step applies to it. -/
def Whnf {n : Nat} (M : Term n) : Prop := ∀ N, ¬ M —→ₕ N

/-- Terms whose head is a variable. -/
inductive HeadVar : {n : Nat} → Term n → Prop
  | var {n : Nat} (i : Fin n) : HeadVar (v# i)
  | app {n : Nat} {a : Term n} (b : Term n) : HeadVar a → HeadVar (a ⬝ b)

/-- Inversion for a head step out of an application. -/
theorem HeadBeta.app_inv {n : Nat} {a b s : Term n} (h : a ⬝ b —→ₕ s) :
    (∃ p : Term (n + 1), a = ƛ p ∧ s = p [ b ])
    ∨ (∃ a', s = a' ⬝ b ∧ a —→ₕ a') := by
  cases h with
  | basis M N => exact Or.inl ⟨M, rfl, rfl⟩
  | appL L hMN => exact Or.inr ⟨_, rfl, hMN⟩

theorem Whnf.var {n : Nat} (i : Fin n) : Whnf (v# i : Term n) :=
  fun _ h => h.to_beta.var_inv

theorem Whnf.abs {n : Nat} (M : Term (n + 1)) : Whnf (ƛ M) :=
  fun _ h => HeadBeta.not_isAbs h ⟨M, rfl⟩

theorem Whnf.app_inv {n : Nat} {a b : Term n} (h : Whnf (a ⬝ b)) : Whnf a ∧ ¬ IsAbs a := by
  refine ⟨fun x hx => h _ (HeadBeta.appL b hx), ?_⟩
  rintro ⟨p, rfl⟩
  exact h _ (HeadBeta.basis p b)

theorem Whnf.app {n : Nat} {a b : Term n} (ha : Whnf a) (hna : ¬ IsAbs a) : Whnf (a ⬝ b) := by
  intro N h
  rcases h.app_inv with ⟨p, hp, _⟩ | ⟨a', _, hstep⟩
  · exact hna ⟨p, hp⟩
  · exact ha _ hstep

theorem HeadVar.not_isAbs {n : Nat} {a : Term n} (h : HeadVar a) : ¬ IsAbs a := by
  cases h with
  | var i => rintro ⟨p, hp⟩; exact absurd hp (by simp)
  | app b _ => rintro ⟨p, hp⟩; exact absurd hp (by simp)

theorem HeadVar.to_whnf {n : Nat} {a : Term n} (h : HeadVar a) : Whnf a := by
  induction h with
  | var i => exact Whnf.var i
  | app b hv ih => exact ih.app hv.not_isAbs

/-- **The weak head normal forms** are exactly the abstractions and the terms
    headed by a variable. -/
theorem whnf_iff {n : Nat} {a : Term n} : Whnf a ↔ IsAbs a ∨ HeadVar a := by
  refine ⟨fun h => ?_, fun h => h.elim (fun ⟨p, hp⟩ => hp ▸ Whnf.abs p) HeadVar.to_whnf⟩
  induction a with
  | var i => exact Or.inr (HeadVar.var i)
  | abs s _ => exact Or.inl ⟨s, rfl⟩
  | app x y ihx _ =>
      obtain ⟨hx, hnx⟩ := h.app_inv
      rcases ihx hx with habs | hv
      · exact absurd habs hnx
      · exact Or.inr (HeadVar.app y hv)

/-- Weak head reduction is deterministic. -/
theorem HeadBeta.deterministic {n : Nat} {a b c : Term n} (h₁ : a —→ₕ b) (h₂ : a —→ₕ c) :
    b = c := by
  induction h₁ generalizing c with
  | basis M N =>
      rcases h₂.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, hstep⟩
      · cases (by simpa using hp : M = p); rfl
      · exact absurd ⟨M, rfl⟩ (HeadBeta.not_isAbs hstep)
  | appL L hMN ih =>
      rcases h₂.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, hstep⟩
      · exact absurd ⟨p, hp⟩ (HeadBeta.not_isAbs hMN)
      · exact congrArg (· ⬝ L) (ih hstep)

/-- Every term is either in weak head normal form or admits a head step. -/
theorem whnf_progress {n : Nat} (M : Term n) : Whnf M ∨ ∃ N, M —→ₕ N := by
  induction M with
  | var i => exact Or.inl (Whnf.var i)
  | abs s _ => exact Or.inl (Whnf.abs s)
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        exact Or.inr ⟨p [ b ], HeadBeta.basis p b⟩
      · rcases iha with hna | ⟨a', ha'⟩
        · exact Or.inl (hna.app hab)
        · exact Or.inr ⟨a' ⬝ b, HeadBeta.appL b ha'⟩

/-! ## 2. The Weak Head Normalization Theorem -/

theorem HeadBetaStar.appL {n : Nat} {M M' : Term n} (N : Term n) (h : M —→ₕ* M') :
    M ⬝ N —→ₕ* M' ⬝ N := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (HeadBeta.appL N step)

/-- A standard reduction out of an abstraction lands in an abstraction. -/
theorem StdRed.abs_source {n : Nat} {p : Term (n + 1)} {x : Term n} (h : ƛ p —→ₛ x) :
    IsAbs x := by
  generalize hs : (ƛ p : Term n) = a at h
  induction h with
  | var i => exact absurd hs (by simp)
  | @abs n M N _ _ => exact ⟨N, rfl⟩
  | app _ _ _ _ => exact absurd hs (by simp)
  | head hLM _ _ =>
      cases hs
      exact absurd ⟨p, rfl⟩ (HeadBeta.not_isAbs hLM)

/-- A standard reduction to a weak head normal form starts with head steps that
    already reach a weak head normal form. -/
theorem StdRed.whnf_target {n : Nat} {a b : Term n} (h : a —→ₛ b) : Whnf b →
    ∃ P, a —→ₕ* P ∧ P —→ₛ b ∧ Whnf P := by
  induction h with
  | var i => intro hb; exact ⟨v# i, .refl, StdRed.var i, Whnf.var i⟩
  | @abs n M N hMN _ =>
      intro _
      exact ⟨ƛ M, .refl, StdRed.abs hMN, Whnf.abs M⟩
  | @app n M M' N N' hM hN ihM _ =>
      intro hb
      obtain ⟨hM', hna⟩ := hb.app_inv
      obtain ⟨P, hhead, hstd, hP⟩ := ihM hM'
      have hPna : ¬ IsAbs P := by
        rintro ⟨q, rfl⟩
        exact hna (StdRed.abs_source hstd)
      exact ⟨P ⬝ N, HeadBetaStar.appL N hhead, StdRed.app hstd hN, hP.app hPna⟩
  | head hLM _ ih =>
      intro hb
      obtain ⟨P, hhead, hstd, hP⟩ := ih hb
      exact ⟨P, Relation.ReflTransGen.head hLM hhead, hstd, hP⟩

/-- **The Weak Head Normalization Theorem**: if a term reduces to a weak head
    normal form, then it *head*-reduces to one. -/
theorem whnf_normalization {n : Nat} {M N : Term n} (h : M —→* N) (hN : Whnf N) :
    ∃ P, M —→ₕ* P ∧ Whnf P ∧ P —→* N := by
  obtain ⟨P, hhead, hstd, hP⟩ := (stdRed_of_betaStar h).whnf_target hN
  exact ⟨P, hhead, hP, hstd.to_betaStar⟩

/-! ## 3. Call-by-name evaluation -/

namespace Term

/-- Contract the head redex, if there is one.  Note the type: evaluation cannot
    change the scope. -/
def whstep : {n : Nat} → Term n → Option (Term n)
  | _, .var _ => none
  | _, .abs _ => none
  | _, .app (.abs p) q => some (p [ q ])
  | _, .app a b =>
      match whstep a with
      | some a' => some (a' ⬝ b)
      | none => none

@[simp] theorem whstep_var {n : Nat} (i : Fin n) : whstep (v# i) = none := by simp [whstep]
@[simp] theorem whstep_abs {n : Nat} (s : Term (n + 1)) : whstep (ƛ s) = none := by simp [whstep]
@[simp] theorem whstep_app_abs {n : Nat} (p : Term (n + 1)) (q : Term n) :
    whstep ((ƛ p) ⬝ q) = some (p [ q ]) := by simp [whstep]

theorem whstep_app_of_not_isAbs {n : Nat} {a : Term n} (ha : ¬ IsAbs a) (b : Term n) :
    whstep (a ⬝ b) =
      match whstep a with
      | some a' => some (a' ⬝ b)
      | none => none := by
  cases a with
  | var i => simp [whstep]
  | abs t => exact absurd ⟨t, rfl⟩ ha
  | app x y => simp [whstep]

/-- Call-by-name evaluation: contract the head redex at most `fuel` times. -/
def evalCBN {n : Nat} : Nat → Term n → Option (Term n)
  | 0, _ => none
  | fuel + 1, s =>
      match whstep s with
      | none => some s
      | some t => evalCBN fuel t

end Term

theorem Term.whstep_none_whnf {n : Nat} {s : Term n} (h : whstep s = none) : Whnf s := by
  induction s with
  | var i => exact Whnf.var i
  | abs s _ => exact Whnf.abs s
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        rw [Term.whstep_app_abs] at h
        exact absurd h (by simp)
      · rw [Term.whstep_app_of_not_isAbs hab] at h
        cases ha : whstep a with
        | some a' => rw [ha] at h; exact absurd h (by simp)
        | none => exact (iha ha).app hab

theorem Term.whstep_some {n : Nat} {s t : Term n} (h : whstep s = some t) : s —→ₕ t := by
  induction s with
  | var i => simp at h
  | abs s _ => simp at h
  | app a b iha _ =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        rw [Term.whstep_app_abs] at h
        cases h
        exact HeadBeta.basis p b
      · rw [Term.whstep_app_of_not_isAbs hab] at h
        cases ha : whstep a with
        | some a' =>
            rw [ha] at h
            cases h
            exact HeadBeta.appL b (iha ha)
        | none => rw [ha] at h; exact absurd h (by simp)

theorem Term.whstep_eq_some_iff {n : Nat} {s t : Term n} : whstep s = some t ↔ s —→ₕ t := by
  refine ⟨Term.whstep_some, fun h => ?_⟩
  cases hs : whstep s with
  | none => exact absurd h (Term.whstep_none_whnf hs t)
  | some u => rw [(Term.whstep_some hs).deterministic h]

theorem Term.evalCBN_succ {n : Nat} (fuel : Nat) (s : Term n) :
    evalCBN (fuel + 1) s =
      match whstep s with
      | none => some s
      | some t => evalCBN fuel t := rfl

/-- **Soundness of call-by-name evaluation**. -/
theorem evalCBN_sound {n : Nat} : ∀ (fuel : Nat) {s t : Term n}, evalCBN fuel s = some t →
    s —→ₕ* t ∧ Whnf t := by
  intro fuel
  induction fuel with
  | zero => intro s t h; exact absurd h (by simp [Term.evalCBN])
  | succ fuel ih =>
      intro s t h
      rw [Term.evalCBN_succ] at h
      cases hs : Term.whstep s with
      | none =>
          rw [hs] at h
          cases h
          exact ⟨.refl, Term.whstep_none_whnf hs⟩
      | some u =>
          rw [hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Term.whstep_some hs) hred, hnorm⟩

/-- **Completeness of call-by-name evaluation**. -/
theorem evalCBN_complete {n : Nat} {s t : Term n} (h : s —→ₕ* t) (ht : Whnf t) :
    ∃ fuel, Term.evalCBN fuel s = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, ?_⟩
      rw [Term.evalCBN_succ]
      cases hs : Term.whstep t with
      | none => rfl
      | some u => exact absurd (Term.whstep_some hs) (ht u)
  | head hstep _ ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [Term.evalCBN_succ, Term.whstep_eq_some_iff.mpr hstep]
      exact hfuel

/-- **Having a weak head normal form is semi-decidable**, by call-by-name
    evaluation. -/
theorem has_whnf_iff_evalCBN {n : Nat} {s : Term n} :
    (∃ t, s —→* t ∧ Whnf t) ↔ ∃ fuel t, Term.evalCBN fuel s = some t := by
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
    | refl => exact .refl
    | tail _ step ih => exact ih.tail step.to_beta

end FinScope
