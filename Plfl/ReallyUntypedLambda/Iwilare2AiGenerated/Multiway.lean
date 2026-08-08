-- Multiway (non-deterministic, all-paths) evaluation.
--
-- Instead of committing to one redex, one may contract *all* of them: from a
-- set of terms, one step of the multiway system produces the set of all terms
-- reachable by a single beta step from one of them.  `allSteps t` computes the
-- list of all one-step reducts of `t` and is proved to be exactly the beta
-- reducts of `t` (`mem_allSteps_iff`), `multiwayEdges` gives the edges of the
-- multiway graph, and `multiway k` iterates the construction.
--
-- The Church-Rosser theorem then says that the multiway graph is *confluent*:
-- any two of its vertices reachable from a common term can be joined again
-- (`multiway_confluent`).
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Strategies

@[expose] public section

namespace FinScope

open Term

/-! ## 1. All one-step reducts of a term -/

namespace Term

/-- The list of all terms obtained from `t` by contracting one redex. -/
def allSteps : {n : Nat} → Term n → List (Term n)
  | _, .var _ => []
  | _, .abs t => (allSteps t).map Term.abs
  | _, .app a b =>
      (contract a b).toList ++ (allSteps a).map (· ⬝ b) ++ (allSteps b).map (a ⬝ ·)

@[simp] theorem allSteps_var {n : Nat} (i : Fin n) : allSteps (v# i) = [] := rfl
@[simp] theorem allSteps_abs {n : Nat} (t : Term (n + 1)) :
    allSteps (ƛ t) = (allSteps t).map Term.abs := rfl
@[simp] theorem allSteps_app {n : Nat} (a b : Term n) :
    allSteps (a ⬝ b) =
      (contract a b).toList ++ (allSteps a).map (· ⬝ b) ++ (allSteps b).map (a ⬝ ·) := rfl

end Term

/-- `allSteps` computes exactly the one-step beta reducts. -/
theorem mem_allSteps_iff {n : Nat} {t t' : Term n} : t' ∈ Term.allSteps t ↔ t —→ t' := by
  induction t with
  | var i => exact ⟨fun h => absurd h (by simp), fun h => h.var_inv.elim⟩
  | abs u ih =>
      simp only [Term.allSteps_abs, List.mem_map]
      constructor
      · rintro ⟨q, hq, rfl⟩; exact Beta.abs (ih.mp hq)
      · intro h
        obtain ⟨q, rfl, hstep⟩ := h.abs_inv
        exact ⟨q, ih.mpr hstep, rfl⟩
  | app a b iha ihb =>
      simp only [Term.allSteps_app, List.mem_append, List.mem_map, Option.mem_toList]
      constructor
      · rintro ((h | ⟨a', ha', rfl⟩) | ⟨b', hb', rfl⟩)
        · cases a with
          | var i => exact absurd h (by simp)
          | app x y => exact absurd h (by simp)
          | abs p =>
              obtain rfl : t' = p [ b ] := by simpa using (Option.mem_def.mp h).symm
              exact Beta.basis p b
        · exact Beta.appL (iha.mp ha')
        · exact Beta.appR (ihb.mp hb')
      · intro h
        rcases h.app_inv with ⟨P, rfl, rfl⟩ | ⟨a', rfl, hstep⟩ | ⟨b', rfl, hstep⟩
        · exact Or.inl (Or.inl (by simp))
        · exact Or.inl (Or.inr ⟨a', iha.mpr hstep, rfl⟩)
        · exact Or.inr ⟨b', ihb.mpr hstep, rfl⟩

/-- A term is normal exactly when it has no reducts at all. -/
theorem allSteps_eq_nil_iff_normal {n : Nat} {t : Term n} :
    Term.allSteps t = [] ↔ Normal t := by
  constructor
  · intro h t' hstep
    have : t' ∈ Term.allSteps t := mem_allSteps_iff.mpr hstep
    rw [h] at this
    exact absurd this (by simp)
  · intro hn
    cases h : Term.allSteps t with
    | nil => rfl
    | cons u us =>
        have hmem : u ∈ Term.allSteps t := by rw [h]; exact List.mem_cons_self ..
        exact absurd (mem_allSteps_iff.mp hmem) (hn u)

/-! ## 2. The multiway graph -/

/-- Remove the repetitions from a list of terms (the multiway system merges
    identical states). -/
def dedupTerms : {n : Nat} → List (Term n) → List (Term n)
  | _, [] => []
  | _, t :: ts => let r := dedupTerms ts; if t ∈ r then r else t :: r

theorem mem_dedupTerms {n : Nat} {t : Term n} : ∀ {l : List (Term n)},
    t ∈ dedupTerms l ↔ t ∈ l := by
  intro l
  induction l with
  | nil => simp [dedupTerms]
  | cons u us ih =>
      simp only [dedupTerms, List.mem_cons]
      cases hu : decide (u ∈ dedupTerms us) with
      | true =>
          have hu' : u ∈ dedupTerms us := of_decide_eq_true hu
          rw [if_pos hu']
          constructor
          · intro h; exact Or.inr (ih.mp h)
          · rintro (rfl | h)
            · exact hu'
            · exact ih.mpr h
      | false =>
          have hu' : u ∉ dedupTerms us := of_decide_eq_false hu
          rw [if_neg hu']
          simp only [List.mem_cons, ih]

/-- One step of the multiway system: all terms reachable in one beta step from
    one of the given terms, without repetitions. -/
def multiwayStep {n : Nat} (S : List (Term n)) : List (Term n) :=
  dedupTerms (S.flatMap Term.allSteps)

/-- The edges of the multiway graph out of a list of states. -/
def multiwayEdges {n : Nat} (S : List (Term n)) : List (Term n × Term n) :=
  S.flatMap (fun s => (Term.allSteps s).map (fun t => (s, t)))

/-- The states of the multiway system after `k` steps. -/
def multiway {n : Nat} : Nat → List (Term n) → List (Term n)
  | 0, S => S
  | k + 1, S => multiway k (multiwayStep S)

/-- The states of the multiway system after `k` steps, started from a single
    term. -/
def multiwayFrom {n : Nat} (k : Nat) (s : Term n) : List (Term n) :=
  multiway k (List.cons s List.nil)

/-- The edges of the multiway graph are beta steps, and every beta step out of
    a listed state is an edge. -/
theorem mem_multiwayEdges_iff {n : Nat} {S : List (Term n)} {s t : Term n} :
    (s, t) ∈ multiwayEdges S ↔ s ∈ S ∧ s —→ t := by
  simp only [multiwayEdges, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, hu, t', ht', rfl, rfl⟩
    exact ⟨hu, mem_allSteps_iff.mp ht'⟩
  · rintro ⟨hs, hstep⟩
    exact ⟨s, hs, t, mem_allSteps_iff.mpr hstep, rfl, rfl⟩

/-- A state of the next generation is a one-step reduct of a state of this
    one. -/
theorem mem_multiwayStep_iff {n : Nat} {S : List (Term n)} {t : Term n} :
    t ∈ multiwayStep S ↔ ∃ s ∈ S, s —→ t := by
  rw [multiwayStep, mem_dedupTerms, List.mem_flatMap]
  exact ⟨fun ⟨s, hs, ht⟩ => ⟨s, hs, mem_allSteps_iff.mp ht⟩,
    fun ⟨s, hs, ht⟩ => ⟨s, hs, mem_allSteps_iff.mpr ht⟩⟩

/-- Every state reachable in the multiway system is reachable by beta
    reduction. -/
theorem multiway_sound {n : Nat} : ∀ (k : Nat) {S : List (Term n)} {t : Term n},
    t ∈ multiway k S → ∃ s ∈ S, s —→* t := by
  intro k
  induction k with
  | zero => exact fun {_} {t} h => ⟨t, h, .refl⟩
  | succ k ih =>
      intro S t h
      rw [multiway] at h
      obtain ⟨u, hu, hut⟩ := ih h
      obtain ⟨s, hs, hsu⟩ := mem_multiwayStep_iff.mp hu
      exact ⟨s, hs, (Relation.ReflTransGen.single hsu).trans hut⟩

/-- `BetaSteps k s t`: `t` is reached from `s` in exactly `k` beta steps. -/
inductive BetaSteps : {n : Nat} → Nat → Term n → Term n → Prop
  | refl {n : Nat} (s : Term n) : BetaSteps 0 s s
  | head {n : Nat} {k : Nat} {s t u : Term n} : s —→ t → BetaSteps k t u → BetaSteps (k + 1) s u

/-- Every term reachable from a state in exactly `k` beta steps occurs in the
    `k`-th generation of the multiway system. -/
theorem mem_multiway_of_betaSteps {n : Nat} : ∀ (k : Nat) {S : List (Term n)} {s t : Term n},
    s ∈ S → BetaSteps k s t → t ∈ multiway k S := by
  intro k
  induction k with
  | zero =>
      intro S s t hs hst
      cases hst
      exact hs
  | succ k ih =>
      intro S s t hs hst
      cases hst with
      | head hstep hrest =>
          rw [multiway]
          exact ih (mem_multiwayStep_iff.mpr ⟨s, hs, hstep⟩) hrest

/-! ## 3. The multiway graph is confluent

This is the Church-Rosser theorem, read on the multiway graph: whichever
trajectories two states were reached by, they can always be brought back
together. -/

theorem multiway_confluent {n : Nat} {j k : Nat} {s u v : Term n}
    (hu : u ∈ multiwayFrom j s) (hv : v ∈ multiwayFrom k s) :
    ∃ w, u —→* w ∧ v —→* w := by
  obtain ⟨s₁, hs₁, h₁⟩ := multiway_sound j hu
  obtain ⟨s₂, hs₂, h₂⟩ := multiway_sound k hv
  obtain rfl : s₁ = s := by simpa using hs₁
  obtain rfl : s₂ = s₁ := by simpa using hs₂
  exact beta_church_rosser h₁ h₂

/-! ## 4. The multiway system at work -/

/-- `sample = (λx. (λy. x) x) 𝟙` has two redexes, so the multiway system
    branches immediately. -/
example : Term.allSteps sample = [(ƛ (wk sid)) ⬝ sid, sid ⬝ sid] := by rfl

/-- Both trajectories meet again at `𝟙` after two steps. -/
example : sid ∈ multiwayFrom 2 sample := by
  refine mem_multiway_of_betaSteps 2 (List.mem_cons_self ..) ?_
  refine BetaSteps.head (((ƛ v# 1) ⬝ v# 0) —→-β sid) ?_
  refine BetaSteps.head ?_ (BetaSteps.refl sid)
  simpa [betaSubst_app, betaSubst_abs, betaSubst_var_succ, betaSubst_wk] using (wk sid) —→-β sid

end FinScope
