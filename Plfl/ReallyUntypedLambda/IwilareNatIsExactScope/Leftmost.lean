-- Leftmost-outermost (normal order) reduction, and the Normalization Theorem.
--
-- The *leftmost* redex of a term is the one whose lambda occurs leftmost in the
-- term; contracting it is normal order evaluation.  The relation `—→ₗ` below is
-- deterministic (`Leftmost.deterministic`), and it is *normalizing*:
--
--   `leftmost_normalization : M —→* N → Normal N → M —→ₗ* N`
--
-- so if a term has a normal form at all, repeatedly contracting the leftmost
-- redex reaches it.  This is the classical corollary of Standardization.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.DecEq

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 1. Leftmost reduction
-- ====================================================================

/-- `IsAbs s` : the term `s` is an abstraction, so that applying it makes a redex. -/
def IsAbs (s : Scoped) : Prop := ∃ p, s = Scoped.abs p

theorem IsAbs.abs (p : Scoped) : IsAbs (Scoped.abs p) := ⟨p, rfl⟩

/-- Being an abstraction is *decidable*, so a case split on `IsAbs` needs no
    classical reasoning (`by_cases` would silently use `Classical.propDecidable`
    and hence the axiom of choice). -/
theorem isAbs_or_not (s : Scoped) : IsAbs s ∨ ¬ IsAbs s := Scoped.isAbs_cases s

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→ₗ" => Leftmost

/-- Leftmost-outermost reduction: contract the leftmost redex.  One may descend
    into the function part of an application only when that part is not itself
    an abstraction (otherwise the application is the leftmost redex), and into
    the argument only when the function part is already normal. -/
inductive Leftmost : Scoped → Scoped → Prop
  | basis (M N : Scoped) :
      --------------------
      Scoped.app (Scoped.abs M) N —→ₗ Scoped.sub0 N M
  | abs {M N : Scoped} :
      M —→ₗ N
      --------------------
      → M.abs —→ₗ N.abs
  | appr (L : Scoped) {M N : Scoped} (hM : ¬ IsAbs M) :
      M —→ₗ N
      --------------------
      → M.app L —→ₗ N.app L
  | appl {L : Scoped} (hL : Normal L) (hLna : ¬ IsAbs L) {M N : Scoped} :
      M —→ₗ N
      --------------------
      → L.app M —→ₗ L.app N

/-- Multi-step leftmost reduction. -/
abbrev LeftmostStar : Scoped → Scoped → Prop := Relation.ReflTransGen Leftmost

infix:64 " —→ₗ* " => LeftmostStar

/-- A leftmost step is a beta step. -/
theorem Leftmost.to_beta {a b : Scoped} (h : a —→ₗ b) : a —→ b := by
  induction h with
  | basis M N => exact Beta.basis' M N
  | abs _ ih => exact Beta.abs ih
  | appr L _ _ ih => exact Beta.appr L ih
  | appl _ _ _ ih => exact Beta.appl _ ih

theorem LeftmostStar.to_betastar {a b : Scoped} (h : a —→ₗ* b) : a —→* b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih step.to_beta

/-- A term that head-reduces is an application, never an abstraction. -/
theorem HeadBeta.not_isAbs {a b : Scoped} (h : a —→ₕ b) : ¬ IsAbs a := by
  cases h with
  | basis M N => rintro ⟨p, hp⟩; exact absurd hp Scoped.app_ne_abs
  | appr L h => rintro ⟨p, hp⟩; exact absurd hp Scoped.app_ne_abs

/-- A head step is a leftmost step. -/
theorem HeadBeta.to_leftmost {a b : Scoped} (h : a —→ₕ b) : a —→ₗ b := by
  induction h with
  | basis M N => exact Leftmost.basis M N
  | @appr L M N hMN ih => exact Leftmost.appr L hMN.not_isAbs ih

-- ====================================================================
-- 2. Determinism
-- ====================================================================

theorem Leftmost.not_of_normal {a b : Scoped} (hn : Normal a) (h : a —→ₗ b) : False :=
  hn _ h.to_beta

-- Inversion lemmas, in the same style as those for `Beta`.

theorem Leftmost.var_inv {x s : Scoped} (h : x —→ₗ s) : ∀ {i : Nat}, x ≠ Scoped.var i :=
  fun {_} => h.to_beta.var_inv

theorem Leftmost.abs_inv {x s : Scoped} (h : x —→ₗ s) :
    ∀ {p : Scoped}, x = Scoped.abs p → ∃ p', s = Scoped.abs p' ∧ p —→ₗ p' := by
  induction h with
  | basis M N => intro p hp; exact absurd hp Scoped.app_ne_abs
  | @abs M N hMN _ =>
      intro p hp
      cases Scoped.abs_eq_abs.mp hp
      exact ⟨N, rfl, hMN⟩
  | appr _ _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs
  | appl _ _ _ _ => intro p hp; exact absurd hp Scoped.app_ne_abs

theorem Leftmost.abs_inv' {p s : Scoped} (h : Scoped.abs p —→ₗ s) :
    ∃ p', s = Scoped.abs p' ∧ p —→ₗ p' := h.abs_inv rfl

theorem Leftmost.app_inv {x s : Scoped} (h : x —→ₗ s) :
    ∀ {a b : Scoped}, x = Scoped.app a b →
      (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p)
      ∨ (∃ a', s = Scoped.app a' b ∧ ¬ IsAbs a ∧ a —→ₗ a')
      ∨ (∃ b', s = Scoped.app a b' ∧ Normal a ∧ ¬ IsAbs a ∧ b —→ₗ b') := by
  induction h with
  | basis M N =>
      intro a b hab
      obtain ⟨ha, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inl ⟨M, ha.symm ▸ rfl, rfl⟩
  | abs _ _ => intro a b hab; exact absurd hab Scoped.abs_ne_app
  | @appr L M N hM hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr (Or.inl ⟨N, rfl, hM, hMN⟩)
  | @appl L hL hLna M N hMN _ =>
      intro a b hab
      obtain ⟨rfl, rfl⟩ := Scoped.app_eq_app.mp hab
      exact Or.inr (Or.inr ⟨N, rfl, hL, hLna, hMN⟩)

theorem Leftmost.app_inv' {a b s : Scoped} (h : Scoped.app a b —→ₗ s) :
    (∃ p, a = Scoped.abs p ∧ s = Scoped.sub0 b p)
    ∨ (∃ a', s = Scoped.app a' b ∧ ¬ IsAbs a ∧ a —→ₗ a')
    ∨ (∃ b', s = Scoped.app a b' ∧ Normal a ∧ ¬ IsAbs a ∧ b —→ₗ b') := h.app_inv rfl

/-- **Leftmost reduction is deterministic**: a term has at most one leftmost
    reduct. -/
theorem Leftmost.deterministic {a b c : Scoped} (h₁ : a —→ₗ b) (h₂ : a —→ₗ c) : b = c := by
  induction h₁ generalizing c with
  | basis M N =>
      rcases h₂.app_inv' with ⟨p, hp, rfl⟩ | ⟨a', rfl, hna, _⟩ | ⟨b', rfl, _, hna, _⟩
      · cases Scoped.abs_eq_abs.mp hp; rfl
      · exact absurd (IsAbs.abs M) hna
      · exact absurd (IsAbs.abs M) hna
  | @abs M N _ ih =>
      obtain ⟨p', rfl, hstep⟩ := h₂.abs_inv'
      exact Scoped.abs_eq_abs.mpr (ih hstep)
  | @appr L M N hM hMN ih =>
      rcases h₂.app_inv' with ⟨p, hp, rfl⟩ | ⟨a', rfl, _, hstep⟩ | ⟨b', rfl, hn, _, _⟩
      · exact absurd ⟨p, hp⟩ hM
      · exact Scoped.app_eq_app.mpr ⟨ih hstep, rfl⟩
      · exact absurd hMN.to_beta (hn N)
  | @appl L hL hLna M N hMN ih =>
      rcases h₂.app_inv' with ⟨p, hp, rfl⟩ | ⟨a', rfl, _, hstep⟩ | ⟨b', rfl, _, _, hstep⟩
      · exact absurd ⟨p, hp⟩ hLna
      · exact absurd hstep.to_beta (hL a')
      · exact Scoped.app_eq_app.mpr ⟨rfl, ih hstep⟩

-- ====================================================================
-- 3. Congruences for multi-step leftmost reduction
-- ====================================================================

theorem LeftmostStar.isAbs {a b : Scoped} (h : a —→ₗ* b) (ha : IsAbs a) : IsAbs b := by
  induction h with
  | refl => exact ha
  | tail _ step ih =>
      obtain ⟨p, rfl⟩ := ih
      obtain ⟨p', rfl, _⟩ := step.abs_inv'
      exact IsAbs.abs p'

theorem leftmost_star_abs {M N : Scoped} (h : M —→ₗ* N) : M.abs —→ₗ* N.abs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Leftmost.abs step)

/-- Reducing the function part, as long as the final function part is not an
    abstraction (so that no leftmost redex was skipped on the way). -/
theorem leftmost_star_appr {M M' : Scoped} (N : Scoped) (h : M —→ₗ* M')
    (hM' : ¬ IsAbs M') : M.app N —→ₗ* M'.app N := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep hrest ih =>
      refine Relation.ReflTransGen.head (Leftmost.appr N ?_ hstep) ih
      intro habs
      exact hM' (LeftmostStar.isAbs (Relation.ReflTransGen.head hstep hrest) habs)

/-- Reducing the argument of an application whose function part is normal. -/
theorem leftmost_star_appl {L : Scoped} (hL : Normal L) (hLna : ¬ IsAbs L) {N N' : Scoped}
    (h : N —→ₗ* N') :
    L.app N —→ₗ* L.app N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Leftmost.appl hL hLna step)

-- ====================================================================
-- 4. The Normalization Theorem
-- ====================================================================

/-- Inversion for normal applications. -/
theorem Normal.app_inv {a b : Scoped} (h : Normal (a.app b)) :
    Normal a ∧ Normal b ∧ ¬ IsAbs a := by
  refine ⟨fun z hz => h _ (Beta.appr b hz), fun z hz => h _ (Beta.appl a hz), ?_⟩
  rintro ⟨p, rfl⟩
  exact h _ (Beta.basis' p b)

/-- A standard reduction to a normal form is a leftmost reduction. -/
theorem StdRed.to_leftmostStar {a b : Scoped} (h : a —→ₛ b) : Normal b → a —→ₗ* b := by
  induction h with
  | var i => intro _; exact Relation.ReflTransGen.refl
  | abs _ ih => intro hb; exact leftmost_star_abs (ih hb.of_abs)
  | @app M M' N N' _ _ ihM ihN =>
      intro hb
      obtain ⟨hM', hN', hna⟩ := hb.app_inv
      exact Relation.ReflTransGen.trans (leftmost_star_appr N (ihM hM') hna)
        (leftmost_star_appl hM' hna (ihN hN'))
  | head hLM _ ih => intro hb; exact Relation.ReflTransGen.head hLM.to_leftmost (ih hb)

/-- **The Normalization Theorem**: if a term reduces to a normal form, then the
    leftmost-outermost (normal order) reduction reaches that normal form. -/
theorem leftmost_normalization {M N : Scoped} (h : M —→* N) (hN : Normal N) : M —→ₗ* N :=
  (stdRed_of_betastar h).to_leftmostStar hN

/-- Reaching a normal form and reaching it leftmost are the same thing. -/
theorem betastar_iff_leftmost_of_normal {M N : Scoped} (hN : Normal N) :
    M —→* N ↔ M —→ₗ* N :=
  ⟨fun h => leftmost_normalization h hN, LeftmostStar.to_betastar⟩

/-- Normal order evaluation is complete for conversion: a term convertible with
    a normal form leftmost-reduces to it. -/
theorem leftmost_of_betaeq {M N : Scoped} (h : M ≡β N) (hN : Normal N) : M —→ₗ* N :=
  leftmost_normalization (betaeq_normal_reduces h hN) hN

-- ====================================================================
-- 5. Progress: a term is either normal or has a (unique) leftmost step
-- ====================================================================

/-- Every term is either normal, or admits a leftmost step. -/
theorem leftmost_progress (M : Scoped) : Normal M ∨ ∃ N, M —→ₗ N := by
  induction M using Scoped.ind with
  | var i => exact Or.inl (Normal.var i)
  | abs s ih =>
      rcases ih with hn | ⟨N, hN⟩
      · exact Or.inl hn.abs
      · exact Or.inr ⟨N.abs, Leftmost.abs hN⟩
  | app a b iha ihb =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        exact Or.inr ⟨Scoped.sub0 b p, Leftmost.basis p b⟩
      · rcases iha with hna | ⟨a', ha'⟩
        · rcases ihb with hnb | ⟨b', hb'⟩
          · exact Or.inl (hna.app hnb (fun p hp => hab ⟨p, hp⟩))
          · exact Or.inr ⟨a.app b', Leftmost.appl hna hab hb'⟩
        · exact Or.inr ⟨a'.app b, Leftmost.appr b hab ha'⟩

/-- A term is normal exactly when no leftmost step applies to it. -/
theorem normal_iff_no_leftmost {M : Scoped} : Normal M ↔ ∀ N, ¬ M —→ₗ N := by
  refine ⟨fun h N hN => h N hN.to_beta, fun h => ?_⟩
  rcases leftmost_progress M with hn | ⟨N, hN⟩
  · exact hn
  · exact absurd hN (h N)

end IwilareNatIsExactScope
