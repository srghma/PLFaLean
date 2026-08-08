-- Leftmost-outermost (normal order) reduction, and the Normalization Theorem,
-- for the scope-bounded (`Fin`-indexed) calculus.
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

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Standardization

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Leftmost reduction -/

/-- `IsAbs s` : the term `s` is an abstraction, so that applying it makes a redex. -/
def IsAbs {n : Nat} (s : Term n) : Prop := ∃ p, s = ƛ p

theorem IsAbs.abs {n : Nat} (p : Term (n + 1)) : IsAbs (ƛ p) := ⟨p, rfl⟩

/-- Being an abstraction is *decidable*, so a case split on `IsAbs` needs no
    classical reasoning (`by_cases` would silently use `Classical.propDecidable`
    and hence the axiom of choice).  Here, unlike in the exactly-scoped
    development, this is an immediate case analysis on the term. -/
theorem isAbs_or_not {n : Nat} (s : Term n) : IsAbs s ∨ ¬ IsAbs s := by
  cases s with
  | var i => exact Or.inr (by rintro ⟨p, hp⟩; exact absurd hp (by simp))
  | abs p => exact Or.inl (IsAbs.abs p)
  | app a b => exact Or.inr (by rintro ⟨p, hp⟩; exact absurd hp (by simp))

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " —→ₗ " => Leftmost

/-- Leftmost-outermost reduction: contract the leftmost redex.  One may descend
    into the function part of an application only when that part is not itself
    an abstraction (otherwise the application is the leftmost redex), and into
    the argument only when the function part is already normal. -/
inductive Leftmost : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) :
      --------------------
      (ƛ M) ⬝ N —→ₗ M [ N ]
  | abs {n : Nat} {M N : Term (n + 1)} :
      M —→ₗ N
      --------------------
      → ƛ M —→ₗ ƛ N
  | appL {n : Nat} (L : Term n) {M N : Term n} (hM : ¬ IsAbs M) :
      M —→ₗ N
      --------------------
      → M ⬝ L —→ₗ N ⬝ L
  | appR {n : Nat} {L : Term n} (hL : Normal L) (hLna : ¬ IsAbs L) {M N : Term n} :
      M —→ₗ N
      --------------------
      → L ⬝ M —→ₗ L ⬝ N

/-- Multi-step leftmost reduction. -/
abbrev LeftmostStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Leftmost

@[inherit_doc] infix:60 " —→ₗ* " => LeftmostStar

/-- A leftmost step is a beta step. -/
theorem Leftmost.to_beta {n : Nat} {a b : Term n} (h : a —→ₗ b) : a —→ b := by
  induction h with
  | basis M N => exact Beta.basis M N
  | abs _ ih => exact Beta.abs ih
  | appL L _ _ ih => exact Beta.appL ih
  | appR _ _ _ ih => exact Beta.appR ih

theorem LeftmostStar.to_betaStar {n : Nat} {a b : Term n} (h : a —→ₗ* b) : a —→* b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.to_beta

/-- A term that head-reduces is an application, never an abstraction. -/
theorem HeadBeta.not_isAbs {n : Nat} {a b : Term n} (h : a —→ₕ b) : ¬ IsAbs a := by
  cases h with
  | basis M N => rintro ⟨p, hp⟩; exact absurd hp (by simp)
  | appL L h => rintro ⟨p, hp⟩; exact absurd hp (by simp)

/-- A head step is a leftmost step. -/
theorem HeadBeta.to_leftmost {n : Nat} {a b : Term n} (h : a —→ₕ b) : a —→ₗ b := by
  induction h with
  | basis M N => exact Leftmost.basis M N
  | appL L hMN ih => exact Leftmost.appL L hMN.not_isAbs ih

/-! ## 2. Determinism -/

theorem Leftmost.not_of_normal {n : Nat} {a b : Term n} (hn : Normal a) (h : a —→ₗ b) : False :=
  hn _ h.to_beta

theorem Leftmost.var_inv {n : Nat} {i : Fin n} {s : Term n} (h : v# i —→ₗ s) : False :=
  h.to_beta.var_inv

theorem Leftmost.abs_inv {n : Nat} {p : Term (n + 1)} {s : Term n} (h : ƛ p —→ₗ s) :
    ∃ p', s = ƛ p' ∧ p —→ₗ p' := by
  cases h with
  | abs h' => exact ⟨_, rfl, h'⟩

theorem Leftmost.app_inv {n : Nat} {a b s : Term n} (h : a ⬝ b —→ₗ s) :
    (∃ p : Term (n + 1), a = ƛ p ∧ s = p [ b ])
    ∨ (∃ a', s = a' ⬝ b ∧ ¬ IsAbs a ∧ a —→ₗ a')
    ∨ (∃ b', s = a ⬝ b' ∧ Normal a ∧ ¬ IsAbs a ∧ b —→ₗ b') := by
  cases h with
  | basis M N => exact Or.inl ⟨M, rfl, rfl⟩
  | appL L hM hMN => exact Or.inr (Or.inl ⟨_, rfl, hM, hMN⟩)
  | appR hL hLna hMN => exact Or.inr (Or.inr ⟨_, rfl, hL, hLna, hMN⟩)

/-- **Leftmost reduction is deterministic**: a term has at most one leftmost
    reduct. -/
theorem Leftmost.deterministic {n : Nat} {a b c : Term n} (h₁ : a —→ₗ b) (h₂ : a —→ₗ c) :
    b = c := by
  induction h₁ with
  | basis M N =>
      rcases h₂.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, hna, _⟩ | ⟨b', rfl, _, hna, _⟩
      · cases (by simpa using hp : M = p); rfl
      · exact absurd (IsAbs.abs M) hna
      · exact absurd (IsAbs.abs M) hna
  | abs _ ih =>
      obtain ⟨p', rfl, hstep⟩ := h₂.abs_inv
      exact congrArg Term.abs (ih hstep)
  | @appL n L M N hM hMN ih =>
      rcases h₂.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, _, hstep⟩ | ⟨b', rfl, hn, _, _⟩
      · exact absurd ⟨p, hp⟩ hM
      · exact congrArg (· ⬝ L) (ih hstep)
      · exact absurd hMN.to_beta (hn N)
  | @appR n L hL hLna M N hMN ih =>
      rcases h₂.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, _, hstep⟩ | ⟨b', rfl, _, _, hstep⟩
      · exact absurd ⟨p, hp⟩ hLna
      · exact absurd hstep.to_beta (hL a')
      · exact congrArg (L ⬝ ·) (ih hstep)

/-! ## 3. Congruences for multi-step leftmost reduction -/

theorem LeftmostStar.isAbs {n : Nat} {a b : Term n} (h : a —→ₗ* b) (ha : IsAbs a) : IsAbs b := by
  induction h with
  | refl => exact ha
  | tail _ step ih =>
      obtain ⟨p, rfl⟩ := ih
      obtain ⟨p', rfl, _⟩ := step.abs_inv
      exact IsAbs.abs p'

theorem LeftmostStar.abs {n : Nat} {M N : Term (n + 1)} (h : M —→ₗ* N) : ƛ M —→ₗ* ƛ N := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Leftmost.abs step)

/-- Reducing the function part, as long as the final function part is not an
    abstraction (so that no leftmost redex was skipped on the way). -/
theorem LeftmostStar.appL {n : Nat} {M M' : Term n} (N : Term n) (h : M —→ₗ* M')
    (hM' : ¬ IsAbs M') : M ⬝ N —→ₗ* M' ⬝ N := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep hrest ih =>
      refine Relation.ReflTransGen.head (Leftmost.appL N ?_ hstep) ih
      intro habs
      exact hM' (LeftmostStar.isAbs (Relation.ReflTransGen.head hstep hrest) habs)

/-- Reducing the argument of an application whose function part is normal. -/
theorem LeftmostStar.appR {n : Nat} {L : Term n} (hL : Normal L) (hLna : ¬ IsAbs L)
    {N N' : Term n} (h : N —→ₗ* N') : L ⬝ N —→ₗ* L ⬝ N' := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Leftmost.appR hL hLna step)

/-! ## 4. The Normalization Theorem -/

/-- Inversion for normal applications. -/
theorem Normal.app_inv {n : Nat} {a b : Term n} (h : Normal (a ⬝ b)) :
    Normal a ∧ Normal b ∧ ¬ IsAbs a := by
  refine ⟨fun z hz => h _ (Beta.appL hz), fun z hz => h _ (Beta.appR hz), ?_⟩
  rintro ⟨p, rfl⟩
  exact h _ (Beta.basis p b)

/-- A standard reduction to a normal form is a leftmost reduction. -/
theorem StdRed.to_leftmostStar {n : Nat} {a b : Term n} (h : a —→ₛ b) :
    Normal b → a —→ₗ* b := by
  induction h with
  | var i => intro _; exact .refl
  | abs _ ih => intro hb; exact (ih hb.of_abs).abs
  | @app n M M' N N' _ _ ihM ihN =>
      intro hb
      obtain ⟨hM', hN', hna⟩ := hb.app_inv
      exact (LeftmostStar.appL N (ihM hM') hna).trans
        (LeftmostStar.appR hM' hna (ihN hN'))
  | head hLM _ ih => intro hb; exact Relation.ReflTransGen.head hLM.to_leftmost (ih hb)

/-- **The Normalization Theorem**: if a term reduces to a normal form, then the
    leftmost-outermost (normal order) reduction reaches that normal form. -/
theorem leftmost_normalization {n : Nat} {M N : Term n} (h : M —→* N) (hN : Normal N) :
    M —→ₗ* N :=
  (stdRed_of_betaStar h).to_leftmostStar hN

/-- Reaching a normal form and reaching it leftmost are the same thing. -/
theorem betaStar_iff_leftmost_of_normal {n : Nat} {M N : Term n} (hN : Normal N) :
    M —→* N ↔ M —→ₗ* N :=
  ⟨fun h => leftmost_normalization h hN, LeftmostStar.to_betaStar⟩

/-- Normal order evaluation is complete for conversion: a term convertible with
    a normal form leftmost-reduces to it. -/
theorem leftmost_of_betaeq {n : Nat} {M N : Term n} (h : M ≡β N) (hN : Normal N) : M —→ₗ* N :=
  leftmost_normalization (betaeq_normal_reduces h hN) hN

/-! ## 5. Progress: a term is either normal or has a (unique) leftmost step -/

/-- Every term is either normal, or admits a leftmost step. -/
theorem leftmost_progress {n : Nat} (M : Term n) : Normal M ∨ ∃ N, M —→ₗ N := by
  induction M with
  | var i => exact Or.inl (Normal.var i)
  | abs s ih =>
      rcases ih with hn | ⟨N, hN⟩
      · exact Or.inl hn.abs
      · exact Or.inr ⟨ƛ N, Leftmost.abs hN⟩
  | app a b iha ihb =>
      rcases isAbs_or_not a with hab | hab
      · obtain ⟨p, rfl⟩ := hab
        exact Or.inr ⟨p [ b ], Leftmost.basis p b⟩
      · rcases iha with hna | ⟨a', ha'⟩
        · rcases ihb with hnb | ⟨b', hb'⟩
          · exact Or.inl (hna.app hnb (fun p hp => hab ⟨p, hp⟩))
          · exact Or.inr ⟨a ⬝ b', Leftmost.appR hna hab hb'⟩
        · exact Or.inr ⟨a' ⬝ b, Leftmost.appL b hab ha'⟩

/-- A term is normal exactly when no leftmost step applies to it. -/
theorem normal_iff_no_leftmost {n : Nat} {M : Term n} : Normal M ↔ ∀ N, ¬ M —→ₗ N := by
  refine ⟨fun h N hN => h N hN.to_beta, fun h => ?_⟩
  rcases leftmost_progress M with hn | ⟨N, hN⟩
  · exact hn
  · exact absurd hN (h N)

end FinScope
