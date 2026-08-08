-- Two more evaluation strategies for the scope-bounded (`Fin`-indexed)
-- calculus: *leftmost-innermost* reduction (the depth-first strategy, which
-- contracts the leftmost of the redexes that contain no other redex) and
-- *applicative order* / call-by-value (arguments are evaluated to values before
-- the body of a function is expanded).
--
-- `FinScope/Leftmost.lean` already provides the leftmost-*outermost* (normal
-- order) strategy; the two relations of this module are its innermost
-- counterparts.  Both are deterministic, both are contained in `—→`, and both
-- come with an executable one-step function (`istep`, `vstep`) which is proved
-- to compute exactly the relation, plus a fuelled evaluator.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Evaluator

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Leftmost-innermost (depth-first) reduction -/

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " —→ᵢ " => Innermost

/-- Leftmost-innermost reduction: contract the leftmost redex that contains no
    other redex.  A redex `(ƛ M) ⬝ N` may be contracted only when both `M` and
    `N` are already normal; in an application one descends into the function
    part while it is not normal, and into the argument only once the function
    part is normal. -/
inductive Innermost : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} {M : Term (n + 1)} {N : Term n} (hM : Normal M) (hN : Normal N) :
      --------------------
      (ƛ M) ⬝ N —→ᵢ M [ N ]
  | abs {n : Nat} {M N : Term (n + 1)} :
      M —→ᵢ N
      --------------------
      → ƛ M —→ᵢ ƛ N
  | appL {n : Nat} (L : Term n) {M N : Term n} (hM : ¬ Normal M) :
      M —→ᵢ N
      --------------------
      → M ⬝ L —→ᵢ N ⬝ L
  | appR {n : Nat} {L : Term n} (hL : Normal L) {M N : Term n} :
      M —→ᵢ N
      --------------------
      → L ⬝ M —→ᵢ L ⬝ N

/-- Many steps of leftmost-innermost reduction. -/
abbrev InnermostStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Innermost

@[inherit_doc] infix:60 " —→ᵢ* " => InnermostStar

/-- An innermost step is a beta step. -/
theorem Innermost.to_beta {n : Nat} {a b : Term n} (h : a —→ᵢ b) : a —→ b := by
  induction h with
  | basis hM hN => exact Beta.basis _ _
  | abs _ ih => exact Beta.abs ih
  | appL L _ _ ih => exact Beta.appL ih
  | appR _ _ ih => exact Beta.appR ih

theorem InnermostStar.to_betaStar {n : Nat} {a b : Term n} (h : a —→ᵢ* b) : a —→* b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.to_beta

theorem Innermost.not_normal {n : Nat} {a b : Term n} (h : a —→ᵢ b) : ¬ Normal a :=
  fun hn => hn b h.to_beta

/-! ### Inversion -/

theorem Innermost.var_inv {n : Nat} {i : Fin n} {s : Term n} (h : v# i —→ᵢ s) : False :=
  h.to_beta.var_inv

theorem Innermost.abs_inv {n : Nat} {p : Term (n + 1)} {s : Term n} (h : ƛ p —→ᵢ s) :
    ∃ q, s = ƛ q ∧ p —→ᵢ q := by
  cases h with
  | abs h' => exact ⟨_, rfl, h'⟩

theorem Innermost.app_inv {n : Nat} {a b s : Term n} (h : a ⬝ b —→ᵢ s) :
    (∃ p, a = ƛ p ∧ Normal p ∧ Normal b ∧ s = p [ b ])
      ∨ (∃ a', ¬ Normal a ∧ a —→ᵢ a' ∧ s = a' ⬝ b)
      ∨ (∃ b', Normal a ∧ b —→ᵢ b' ∧ s = a ⬝ b') := by
  cases h with
  | basis hM hN => exact Or.inl ⟨_, rfl, hM, hN, rfl⟩
  | appL L hM h' => exact Or.inr (Or.inl ⟨_, hM, h', rfl⟩)
  | appR hL h' => exact Or.inr (Or.inr ⟨_, hL, h', rfl⟩)

/-! ### Determinism -/

theorem Innermost.deterministic {n : Nat} {a b c : Term n} (h₁ : a —→ᵢ b) (h₂ : a —→ᵢ c) :
    b = c := by
  induction h₁ with
  | @basis n M N hM hN =>
      rcases h₂.app_inv with ⟨p, hp, _, _, rfl⟩ | ⟨a', hna, _, rfl⟩ | ⟨b', _, hstep, rfl⟩
      · cases (by simpa using hp : M = p); rfl
      · exact absurd hM.abs hna
      · exact absurd hstep.to_beta (hN _)
  | abs _ ih =>
      obtain ⟨q, rfl, hstep⟩ := h₂.abs_inv
      exact congrArg Term.abs (ih hstep)
  | @appL n L M N hM hMN ih =>
      rcases h₂.app_inv with ⟨p, hp, hpn, _, rfl⟩ | ⟨a', _, hstep, rfl⟩ | ⟨b', hn, hstep, rfl⟩
      · exact absurd (hp ▸ hpn.abs) hM
      · exact congrArg (· ⬝ L) (ih hstep)
      · exact absurd hMN.to_beta (hn N)
  | @appR n L hL M N hMN ih =>
      rcases h₂.app_inv with ⟨p, _, _, hbn, rfl⟩ | ⟨a', hna, _, rfl⟩ | ⟨b', _, hstep, rfl⟩
      · exact absurd hMN.to_beta (hbn N)
      · exact absurd hL hna
      · exact congrArg (L ⬝ ·) (ih hstep)

/-! ## 2. Applicative order (call-by-value) -/

/-- A *value* of the call-by-value calculus: an abstraction, or a variable
    applied to values (a neutral term all of whose arguments are values).  On
    closed terms these are exactly the abstractions. -/
inductive Value : {n : Nat} → Term n → Prop
  | var {n : Nat} (i : Fin n) : Value (v# i)
  | abs {n : Nat} (M : Term (n + 1)) : Value (ƛ M)
  | app {n : Nat} {a b : Term n} : Value a → ¬ IsAbs a → Value b → Value (a ⬝ b)

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " —→ᵥ " => Cbv

/-- Applicative order (call-by-value) reduction: a redex `(ƛ M) ⬝ N` may be
    contracted only once the argument `N` is a value, and reduction never goes
    under a binder.  The function part is evaluated first, then the argument,
    and only then is the body of the abstraction expanded. -/
inductive Cbv : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} (M : Term (n + 1)) {N : Term n} (hN : Value N) :
      --------------------
      (ƛ M) ⬝ N —→ᵥ M [ N ]
  | appL {n : Nat} (L : Term n) {M N : Term n} :
      M —→ᵥ N
      --------------------
      → M ⬝ L —→ᵥ N ⬝ L
  | appR {n : Nat} {L : Term n} (hL : Value L) {M N : Term n} :
      M —→ᵥ N
      --------------------
      → L ⬝ M —→ᵥ L ⬝ N

/-- Many steps of applicative order reduction. -/
abbrev CbvStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Cbv

@[inherit_doc] infix:60 " —→ᵥ* " => CbvStar

/-- A call-by-value step is a beta step. -/
theorem Cbv.to_beta {n : Nat} {a b : Term n} (h : a —→ᵥ b) : a —→ b := by
  induction h with
  | basis M hN => exact Beta.basis _ _
  | appL L _ ih => exact Beta.appL ih
  | appR _ _ ih => exact Beta.appR ih

theorem CbvStar.to_betaStar {n : Nat} {a b : Term n} (h : a —→ᵥ* b) : a —→* b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.to_beta

/-- Values are irreducible for `—→ᵥ`. -/
theorem Value.not_cbv {n : Nat} {a b : Term n} (hv : Value a) (h : a —→ᵥ b) : False := by
  induction h with
  | basis M hN => cases hv with | app _ hna _ => exact hna (IsAbs.abs M)
  | appL L _ ih => cases hv with | app hva _ _ => exact ih hva
  | appR _ _ ih => cases hv with | app _ _ hvb => exact ih hvb

/-- Inversion for a call-by-value step out of an application. -/
theorem Cbv.app_inv {n : Nat} {a b s : Term n} (h : a ⬝ b —→ᵥ s) :
    (∃ p, a = ƛ p ∧ Value b ∧ s = p [ b ])
      ∨ (∃ a', a —→ᵥ a' ∧ s = a' ⬝ b)
      ∨ (∃ b', Value a ∧ b —→ᵥ b' ∧ s = a ⬝ b') := by
  cases h with
  | basis M hN => exact Or.inl ⟨M, rfl, hN, rfl⟩
  | appL L h' => exact Or.inr (Or.inl ⟨_, h', rfl⟩)
  | appR hL h' => exact Or.inr (Or.inr ⟨_, hL, h', rfl⟩)

theorem Cbv.deterministic {n : Nat} {a b c : Term n} (h₁ : a —→ᵥ b) (h₂ : a —→ᵥ c) : b = c := by
  induction h₁ generalizing c with
  | basis M hN =>
      rcases h₂.app_inv with ⟨p, hp, _, rfl⟩ | ⟨a', hstep, rfl⟩ | ⟨b', _, hstep, rfl⟩
      · cases (by simpa using hp : M = p); rfl
      · exact absurd hstep (Value.abs M).not_cbv
      · exact absurd hstep hN.not_cbv
  | appL L hMN ih =>
      rcases h₂.app_inv with ⟨p, hp, _, rfl⟩ | ⟨a', hstep, rfl⟩ | ⟨b', hv, _, rfl⟩
      · exact absurd (hp ▸ hMN) (Value.abs p).not_cbv
      · exact congrArg (· ⬝ L) (ih hstep)
      · exact absurd hMN hv.not_cbv
  | appR hL hMN ih =>
      rcases h₂.app_inv with ⟨p, _, hvb, rfl⟩ | ⟨a', hstep, rfl⟩ | ⟨b', _, hstep, rfl⟩
      · exact absurd hMN hvb.not_cbv
      · exact absurd hstep hL.not_cbv
      · exact congrArg (_ ⬝ ·) (ih hstep)

/-! ## 3. The executable one-step functions -/

namespace Term

/-- Contract the application `a ⬝ b` at its root, if it is a redex. -/
def contract : {n : Nat} → Term n → Term n → Option (Term n)
  | _, .abs p, b => some (p [ b ])
  | _, _, _ => none

/-- Contract the leftmost-innermost redex, if there is one. -/
def istep : {n : Nat} → Term n → Option (Term n)
  | _, .var _ => none
  | _, .abs t => (istep t).map Term.abs
  | _, .app a b =>
      match istep a with
      | some a' => some (a' ⬝ b)
      | none =>
        match istep b with
        | some b' => some (a ⬝ b')
        | none => contract a b

/-- Is the term a call-by-value value? -/
def isValueB : {n : Nat} → Term n → Bool
  | _, .var _ => true
  | _, .abs _ => true
  | _, .app a b => !isAbsB a && isValueB a && isValueB b

/-- Perform the applicative-order (call-by-value) step, if there is one. -/
def vstep : {n : Nat} → Term n → Option (Term n)
  | _, .var _ => none
  | _, .abs _ => none
  | _, .app a b =>
      match vstep a with
      | some a' => some (a' ⬝ b)
      | none =>
        match vstep b with
        | some b' => some (a ⬝ b')
        | none => contract a b

@[simp] theorem istep_var {n : Nat} (i : Fin n) : istep (v# i) = none := rfl
@[simp] theorem istep_abs {n : Nat} (t : Term (n + 1)) :
    istep (ƛ t) = (istep t).map Term.abs := rfl
@[simp] theorem vstep_var {n : Nat} (i : Fin n) : vstep (v# i) = none := rfl
@[simp] theorem vstep_abs {n : Nat} (t : Term (n + 1)) : vstep (ƛ t) = none := rfl
@[simp] theorem isValueB_var {n : Nat} (i : Fin n) : isValueB (v# i) = true := rfl
@[simp] theorem isValueB_abs {n : Nat} (t : Term (n + 1)) : isValueB (ƛ t) = true := rfl
@[simp] theorem isValueB_app {n : Nat} (a b : Term n) :
    isValueB (a ⬝ b) = (!isAbsB a && isValueB a && isValueB b) := rfl

@[simp] theorem contract_var {n : Nat} (i : Fin n) (b : Term n) : contract (v# i) b = none := rfl
@[simp] theorem contract_abs {n : Nat} (p : Term (n + 1)) (b : Term n) :
    contract (ƛ p) b = some (p [ b ]) := rfl
@[simp] theorem contract_app {n : Nat} (x y b : Term n) : contract (x ⬝ y) b = none := rfl

theorem istep_app_some_left {n : Nat} {a b a' : Term n} (h : istep a = some a') :
    istep (a ⬝ b) = some (a' ⬝ b) := by simp [istep, h]

theorem istep_app_some_right {n : Nat} {a b b' : Term n} (ha : istep a = none)
    (hb : istep b = some b') : istep (a ⬝ b) = some (a ⬝ b') := by simp [istep, ha, hb]

theorem istep_app_of_none {n : Nat} {a b : Term n} (ha : istep a = none) (hb : istep b = none) :
    istep (a ⬝ b) = contract a b := by simp [istep, ha, hb]

theorem vstep_app_some_left {n : Nat} {a b a' : Term n} (h : vstep a = some a') :
    vstep (a ⬝ b) = some (a' ⬝ b) := by simp [vstep, h]

theorem vstep_app_some_right {n : Nat} {a b b' : Term n} (ha : vstep a = none)
    (hb : vstep b = some b') : vstep (a ⬝ b) = some (a ⬝ b') := by simp [vstep, ha, hb]

theorem vstep_app_of_none {n : Nat} {a b : Term n} (ha : vstep a = none) (hb : vstep b = none) :
    vstep (a ⬝ b) = contract a b := by simp [vstep, ha, hb]

/-- `isValueB` decides `Value`. -/
theorem isValueB_iff {n : Nat} {s : Term n} : isValueB s = true ↔ Value s := by
  induction s with
  | var i => exact ⟨fun _ => Value.var i, fun _ => rfl⟩
  | abs t => exact ⟨fun _ => Value.abs t, fun _ => rfl⟩
  | app a b iha ihb =>
      constructor
      · intro h
        simp only [isValueB_app, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine Value.app (iha.mp h2) (fun hab => ?_) (ihb.mp h3)
        rw [Term.isAbsB_iff.mpr hab] at h1
        exact absurd h1 (by simp)
      · intro hv
        cases hv with
        | app hva hna hvb =>
            simp only [isValueB_app, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
            refine ⟨⟨?_, iha.mpr hva⟩, ihb.mpr hvb⟩
            cases hb : isAbsB a with
            | false => rfl
            | true => exact absurd (Term.isAbsB_iff.mp hb) hna

/-- `istep` finds a step exactly when the term is not normal. -/
theorem istep_none_iff_normal {n : Nat} {s : Term n} : istep s = none ↔ Normal s := by
  induction s with
  | var i => exact ⟨fun _ => Normal.var i, fun _ => rfl⟩
  | abs t ih =>
      constructor
      · intro h
        simp only [istep_abs, Option.map_eq_none_iff] at h
        exact (ih.mp h).abs
      · intro h
        simp [istep, ih.mpr h.of_abs]
  | app a b iha ihb =>
      cases ha : istep a with
      | some a' =>
          constructor
          · intro h; rw [istep_app_some_left ha] at h; exact absurd h (by simp)
          · intro hn
            rw [iha.mpr hn.app_inv.1] at ha
            exact absurd ha (by simp)
      | none =>
        cases hb : istep b with
        | some b' =>
            constructor
            · intro h; rw [istep_app_some_right ha hb] at h; exact absurd h (by simp)
            · intro hn
              rw [ihb.mpr hn.app_inv.2.1] at hb
              exact absurd hb (by simp)
        | none =>
            rw [istep_app_of_none ha hb]
            cases a with
            | abs p =>
                constructor
                · intro h; exact absurd h (by simp)
                · intro hn; exact absurd (Beta.basis p b) (hn _)
            | var i => exact ⟨fun _ => (iha.mp ha).app (ihb.mp hb) (by simp), fun _ => rfl⟩
            | app x y => exact ⟨fun _ => (iha.mp ha).app (ihb.mp hb) (by simp), fun _ => rfl⟩

/-- `istep` computes the leftmost-innermost step. -/
theorem istep_eq_some_iff {n : Nat} {s t : Term n} : istep s = some t ↔ s —→ᵢ t := by
  induction s with
  | var i => exact ⟨fun h => absurd h (by simp), fun h => h.var_inv.elim⟩
  | abs u ih =>
      constructor
      · intro h
        simp only [istep_abs, Option.map_eq_some_iff] at h
        obtain ⟨q, hq, rfl⟩ := h
        exact Innermost.abs (ih.mp hq)
      · intro h
        obtain ⟨q, rfl, hstep⟩ := h.abs_inv
        simp [istep, ih.mpr hstep]
  | app a b iha ihb =>
      cases ha : istep a with
      | some a' =>
          have hna : ¬ Normal a := fun hn => by
            rw [istep_none_iff_normal.mpr hn] at ha; exact absurd ha (by simp)
          constructor
          · intro h
            rw [istep_app_some_left ha] at h
            obtain rfl : t = a' ⬝ b := by simpa using h.symm
            exact Innermost.appL b hna (iha.mp ha)
          · intro h
            rcases h.app_inv with ⟨p, hp, hpn, _, rfl⟩ | ⟨a'', _, hstep, rfl⟩ | ⟨b', hn, _, rfl⟩
            · exact absurd (hp ▸ hpn.abs) hna
            · have h2 := iha.mpr hstep
              rw [ha] at h2
              rw [istep_app_some_left ha, Option.some.inj h2]
            · exact absurd hn hna
      | none =>
        cases hb : istep b with
        | some b' =>
            have hnA : Normal a := istep_none_iff_normal.mp ha
            constructor
            · intro h
              rw [istep_app_some_right ha hb] at h
              obtain rfl : t = a ⬝ b' := by simpa using h.symm
              exact Innermost.appR hnA (ihb.mp hb)
            · intro h
              rcases h.app_inv with ⟨p, _, _, hbn, rfl⟩ | ⟨a'', hna', _, rfl⟩ | ⟨b'', _, hstep, rfl⟩
              · exact absurd (ihb.mp hb).to_beta (hbn _)
              · exact absurd hnA hna'
              · have h2 := ihb.mpr hstep
                rw [hb] at h2
                rw [istep_app_some_right ha hb, Option.some.inj h2]
        | none =>
            have hnA : Normal a := istep_none_iff_normal.mp ha
            have hnB : Normal b := istep_none_iff_normal.mp hb
            rw [istep_app_of_none ha hb]
            cases a with
            | abs p =>
                constructor
                · intro h
                  obtain rfl : t = p [ b ] := by simpa using h.symm
                  exact Innermost.basis hnA.of_abs hnB
                · intro h
                  rcases h.app_inv with ⟨q, hq, _, _, rfl⟩ | ⟨a'', hna', _, rfl⟩ | ⟨b'', _, hstep, rfl⟩
                  · cases (by simpa using hq : p = q); rfl
                  · exact absurd hnA hna'
                  · exact absurd hstep.to_beta (hnB _)
            | var i =>
                exact ⟨fun h => absurd h (by simp),
                  fun h => absurd h.to_beta ((hnA.app hnB (by simp)) t)⟩
            | app x y =>
                exact ⟨fun h => absurd h (by simp),
                  fun h => absurd h.to_beta ((hnA.app hnB (by simp)) t)⟩

/-- `vstep` finds a step exactly when the term is not a value. -/
theorem vstep_none_iff_value {n : Nat} {s : Term n} : vstep s = none ↔ Value s := by
  induction s with
  | var i => exact ⟨fun _ => Value.var i, fun _ => rfl⟩
  | abs t => exact ⟨fun _ => Value.abs t, fun _ => rfl⟩
  | app a b iha ihb =>
      cases ha : vstep a with
      | some a' =>
          constructor
          · intro h; rw [vstep_app_some_left ha] at h; exact absurd h (by simp)
          · intro hv
            cases hv with
            | app hva _ _ => rw [iha.mpr hva] at ha; exact absurd ha (by simp)
      | none =>
        cases hb : vstep b with
        | some b' =>
            constructor
            · intro h; rw [vstep_app_some_right ha hb] at h; exact absurd h (by simp)
            · intro hv
              cases hv with
              | app _ _ hvb => rw [ihb.mpr hvb] at hb; exact absurd hb (by simp)
        | none =>
            rw [vstep_app_of_none ha hb]
            cases a with
            | abs p =>
                constructor
                · intro h; exact absurd h (by simp)
                · intro hv
                  cases hv with
                  | app _ hna _ => exact absurd (IsAbs.abs p) hna
            | var i =>
                exact ⟨fun _ => Value.app (iha.mp ha) (by rintro ⟨p, hp⟩; exact absurd hp (by simp))
                  (ihb.mp hb), fun _ => rfl⟩
            | app x y =>
                exact ⟨fun _ => Value.app (iha.mp ha) (by rintro ⟨p, hp⟩; exact absurd hp (by simp))
                  (ihb.mp hb), fun _ => rfl⟩

/-- `vstep` computes the applicative-order step. -/
theorem vstep_eq_some_iff {n : Nat} {s t : Term n} : vstep s = some t ↔ s —→ᵥ t := by
  induction s with
  | var i => exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | abs u => exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | app a b iha ihb =>
      cases ha : vstep a with
      | some a' =>
          have hna : ¬ Value a := fun hv => by
            rw [vstep_none_iff_value.mpr hv] at ha; exact absurd ha (by simp)
          constructor
          · intro h
            rw [vstep_app_some_left ha] at h
            obtain rfl : t = a' ⬝ b := by simpa using h.symm
            exact Cbv.appL b (iha.mp ha)
          · intro h
            rcases h.app_inv with ⟨p, hp, _, rfl⟩ | ⟨a'', hstep, rfl⟩ | ⟨b', hv, _, rfl⟩
            · exact absurd (hp ▸ Value.abs p) hna
            · have h2 := iha.mpr hstep
              rw [ha] at h2
              rw [vstep_app_some_left ha, Option.some.inj h2]
            · exact absurd hv hna
      | none =>
        cases hb : vstep b with
        | some b' =>
            have hvA : Value a := vstep_none_iff_value.mp ha
            constructor
            · intro h
              rw [vstep_app_some_right ha hb] at h
              obtain rfl : t = a ⬝ b' := by simpa using h.symm
              exact Cbv.appR hvA (ihb.mp hb)
            · intro h
              rcases h.app_inv with ⟨p, _, hvb, rfl⟩ | ⟨a'', hstep, rfl⟩ | ⟨b'', _, hstep, rfl⟩
              · exact absurd (ihb.mp hb) hvb.not_cbv
              · exact absurd hstep hvA.not_cbv
              · have h2 := ihb.mpr hstep
                rw [hb] at h2
                rw [vstep_app_some_right ha hb, Option.some.inj h2]
        | none =>
            have hvA : Value a := vstep_none_iff_value.mp ha
            have hvB : Value b := vstep_none_iff_value.mp hb
            rw [vstep_app_of_none ha hb]
            cases a with
            | abs p =>
                constructor
                · intro h
                  obtain rfl : t = p [ b ] := by simpa using h.symm
                  exact Cbv.basis p hvB
                · intro h
                  rcases h.app_inv with ⟨q, hq, _, rfl⟩ | ⟨a'', hstep, rfl⟩ | ⟨b'', _, hstep, rfl⟩
                  · cases (by simpa using hq : p = q); rfl
                  · exact absurd hstep hvA.not_cbv
                  · exact absurd hstep hvB.not_cbv
            | var i =>
                refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
                exact absurd h (Value.app hvA (by rintro ⟨p, hp⟩; exact absurd hp (by simp))
                  hvB).not_cbv
            | app x y =>
                refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
                exact absurd h (Value.app hvA (by rintro ⟨p, hp⟩; exact absurd hp (by simp))
                  hvB).not_cbv

end Term

/-! ## 4. Progress -/

/-- Either the term is normal, or it has a (unique) innermost step. -/
theorem innermost_progress {n : Nat} (M : Term n) : Normal M ∨ ∃ N, M —→ᵢ N := by
  cases h : Term.istep M with
  | none => exact Or.inl (Term.istep_none_iff_normal.mp h)
  | some N => exact Or.inr ⟨N, Term.istep_eq_some_iff.mp h⟩

theorem normal_iff_no_innermost {n : Nat} {M : Term n} : Normal M ↔ ∀ N, ¬ M —→ᵢ N := by
  refine ⟨fun h N hN => h N hN.to_beta, fun h => ?_⟩
  rcases innermost_progress M with hn | ⟨N, hN⟩
  · exact hn
  · exact absurd hN (h N)

/-- Either the term is a value, or it has a (unique) applicative-order step. -/
theorem cbv_progress {n : Nat} (M : Term n) : Value M ∨ ∃ N, M —→ᵥ N := by
  cases h : Term.vstep M with
  | none => exact Or.inl (Term.vstep_none_iff_value.mp h)
  | some N => exact Or.inr ⟨N, Term.vstep_eq_some_iff.mp h⟩

theorem value_iff_no_cbv {n : Nat} {M : Term n} : Value M ↔ ∀ N, ¬ M —→ᵥ N := by
  refine ⟨fun h N hN => h.not_cbv hN, fun h => ?_⟩
  rcases cbv_progress M with hv | ⟨N, hN⟩
  · exact hv
  · exact absurd hN (h N)

/-! ## 5. The fuelled evaluators -/

namespace Term

/-- The applicative-order (leftmost-innermost) evaluator. -/
def evalAO {n : Nat} : Nat → Term n → Option (Term n)
  | 0, s => if istep s = none then some s else none
  | fuel + 1, s =>
    match istep s with
    | none => some s
    | some t => evalAO fuel t

/-- The call-by-value evaluator. -/
def evalCBV {n : Nat} : Nat → Term n → Option (Term n)
  | 0, s => if vstep s = none then some s else none
  | fuel + 1, s =>
    match vstep s with
    | none => some s
    | some t => evalCBV fuel t

end Term

/-- The applicative-order evaluator returns a normal form reached by innermost
    steps, hence by beta steps. -/
theorem evalAO_sound {n : Nat} : ∀ (fuel : Nat) {s t : Term n}, Term.evalAO fuel s = some t →
    s —→ᵢ* t ∧ Normal t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      cases hs : Term.istep s with
      | none =>
          rw [Term.evalAO, if_pos hs] at h
          cases h
          exact ⟨.refl, Term.istep_none_iff_normal.mp hs⟩
      | some u =>
          rw [Term.evalAO, if_neg (by rw [hs]; exact fun hc => absurd hc (by simp))] at h
          exact absurd h (by simp)
  | succ f ih =>
      intro s t h
      cases hs : Term.istep s with
      | none =>
          rw [Term.evalAO, hs] at h
          cases h
          exact ⟨.refl, Term.istep_none_iff_normal.mp hs⟩
      | some u =>
          rw [Term.evalAO, hs] at h
          obtain ⟨hred, hnorm⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Term.istep_eq_some_iff.mp hs) hred, hnorm⟩

/-- The call-by-value evaluator returns a value reached by call-by-value steps,
    hence by beta steps. -/
theorem evalCBV_sound {n : Nat} : ∀ (fuel : Nat) {s t : Term n}, Term.evalCBV fuel s = some t →
    s —→ᵥ* t ∧ Value t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      cases hs : Term.vstep s with
      | none =>
          rw [Term.evalCBV, if_pos hs] at h
          cases h
          exact ⟨.refl, Term.vstep_none_iff_value.mp hs⟩
      | some u =>
          rw [Term.evalCBV, if_neg (by rw [hs]; exact fun hc => absurd hc (by simp))] at h
          exact absurd h (by simp)
  | succ f ih =>
      intro s t h
      cases hs : Term.vstep s with
      | none =>
          rw [Term.evalCBV, hs] at h
          cases h
          exact ⟨.refl, Term.vstep_none_iff_value.mp hs⟩
      | some u =>
          rw [Term.evalCBV, hs] at h
          obtain ⟨hred, hval⟩ := ih h
          exact ⟨Relation.ReflTransGen.head (Term.vstep_eq_some_iff.mp hs) hred, hval⟩

/-! ## 6. The strategies at work -/

/-- `(λx. (λy. x) x) 𝟙`, evaluated by the applicative-order evaluator. -/
example : Term.evalAO 10 sample = some sid := by rfl

/-- The same term, evaluated by the call-by-value evaluator. -/
example : Term.evalCBV 10 sample = some sid := by rfl

end FinScope
