-- The Standardization Theorem, for the scope-bounded (`Fin`-indexed) calculus.
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
--
-- Compared with the exactly-scoped development, the inversion lemmas for `—→`
-- do not have to be restated here: `Beta.var_inv`, `Beta.abs_inv` and
-- `Beta.app_inv` are already available in the scope-bounded core.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Postponement

@[expose] public section

namespace FinScope

open Term

/-! ## 1. Head reduction: contract the leftmost-outermost redex -/

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " —→ₕ " => HeadBeta

/-- Head reduction: the redex contracted is the head redex, i.e. the leftmost
    outermost one.  Note that no rule goes under an abstraction or into the
    argument of an application. -/
inductive HeadBeta : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) :
      --------------------
      (ƛ M) ⬝ N —→ₕ M [ N ]
  | appL {n : Nat} (L : Term n) {M N : Term n} :
      M —→ₕ N
      --------------------
      → M ⬝ L —→ₕ N ⬝ L

theorem HeadBeta.to_beta {n : Nat} {a b : Term n} (h : a —→ₕ b) : a —→ b := by
  induction h with
  | basis M N => exact Beta.basis M N
  | appL L _ ih => exact Beta.appL ih

/-- Head reduction is stable under renaming. -/
theorem HeadBeta.ren_mono {n : Nat} {a b : Term n} (h : a —→ₕ b) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ a —→ₕ ren ρ b := by
  induction h with
  | basis M N =>
      intro m ρ
      rw [ren_app, ren_abs, ren_betaSubst]
      exact HeadBeta.basis _ _
  | appL L _ ih => intro m ρ; exact HeadBeta.appL _ (ih ρ)

/-- Head reduction is stable under parallel substitution. -/
theorem HeadBeta.sub_mono {n : Nat} {a b : Term n} (h : a —→ₕ b) :
    ∀ {m : Nat} (σ : Fin n → Term m), sub σ a —→ₕ sub σ b := by
  induction h with
  | basis M N =>
      intro m σ
      rw [sub_app, sub_abs, sub_betaSubst]
      exact HeadBeta.basis _ _
  | appL L _ ih => intro m σ; exact HeadBeta.appL _ (ih σ)

/-! ## 2. Standard reductions -/

set_option hygiene false in
set_option quotPrecheck false in
infix:60 " —→ₛ " => StdRed

/-- `M —→ₛ N` : there is a *standard* reduction sequence from `M` to `N`. -/
inductive StdRed : {n : Nat} → Term n → Term n → Prop
  | var {n : Nat} (i : Fin n) :
      --------------------
      v# i —→ₛ v# i
  | abs {n : Nat} {M N : Term (n + 1)} :
      M —→ₛ N
      --------------------
      → ƛ M —→ₛ ƛ N
  | app {n : Nat} {M M' N N' : Term n} :
      M —→ₛ M'
      → N —→ₛ N'
      --------------------
      → M ⬝ N —→ₛ M' ⬝ N'
  | head {n : Nat} {L M N : Term n} :
      L —→ₕ M
      → M —→ₛ N
      --------------------
      → L —→ₛ N

/-- The empty reduction sequence is standard. -/
@[refl] theorem StdRed.refl {n : Nat} (M : Term n) : M —→ₛ M := by
  induction M with
  | var i => exact StdRed.var i
  | abs M ih => exact StdRed.abs ih
  | app M N ihM ihN => exact StdRed.app ihM ihN

/-- **Soundness**: a standard reduction sequence is a reduction sequence. -/
theorem StdRed.to_betaStar {n : Nat} {a b : Term n} (h : a —→ₛ b) : a —→* b := by
  induction h with
  | var i => exact .refl
  | abs _ ih => exact ih.abs
  | app _ _ ihM ihN => exact BetaStar.app ihM ihN
  | head hLM _ ih => exact Relation.ReflTransGen.head hLM.to_beta ih

/-- Standard reductions are stable under renaming. -/
theorem StdRed.ren_mono {n : Nat} {a b : Term n} (h : a —→ₛ b) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ a —→ₛ ren ρ b := by
  induction h with
  | var i => intro m ρ; exact StdRed.var _
  | abs _ ih => intro m ρ; exact StdRed.abs (ih _)
  | app _ _ ihM ihN => intro m ρ; exact StdRed.app (ihM _) (ihN _)
  | head hLM _ ih => intro m ρ; exact StdRed.head (hLM.ren_mono ρ) (ih ρ)

/-- Standard reductions are stable under parallel substitution. -/
theorem StdRed.sub_mono {n : Nat} {a b : Term n} (h : a —→ₛ b) :
    ∀ {m : Nat} {σ σ' : Fin n → Term m}, (∀ i, σ i —→ₛ σ' i) →
      sub σ a —→ₛ sub σ' b := by
  induction h with
  | var i => intro m σ σ' hσ; exact hσ i
  | abs _ ih =>
      intro m σ σ' hσ
      refine StdRed.abs (ih ?_)
      intro i
      induction i using Fin.cases with
      | zero => simpa using StdRed.var (0 : Fin (m + 1))
      | succ j => simpa using (hσ j).ren_mono Fin.succ
  | app _ _ ihM ihN => intro m σ σ' hσ; exact StdRed.app (ihM hσ) (ihN hσ)
  | head hLM _ ih =>
      intro m σ σ' hσ
      exact StdRed.head (hLM.sub_mono σ) (ih hσ)

theorem StdRed.betaSubst_mono {n : Nat} {p p' : Term (n + 1)} {q q' : Term n}
    (hp : p —→ₛ p') (hq : q —→ₛ q') : p [ q ] —→ₛ p' [ q' ] := by
  refine hp.sub_mono (σ' := Fin.cons q' Term.var) ?_
  intro i
  induction i using Fin.cases with
  | zero => simpa using hq
  | succ j => simpa using StdRed.var j

/-- The crucial case of the standardization proof: if `a` standardly reduces to
    an abstraction `ƛ p`, then `a ⬝ b` standardly reduces to the contractum
    `p [ b' ]` -- the head redex being contracted *first*. -/
theorem StdRed.app_abs {n : Nat} {a x : Term n} (h : a —→ₛ x) :
    ∀ {p : Term (n + 1)} {b b' : Term n}, x = ƛ p → b —→ₛ b' →
      a ⬝ b —→ₛ p [ b' ] := by
  induction h with
  | var i => intro p b b' hx _; exact absurd hx (by simp)
  | @abs n M N hMN _ =>
      intro p b b' hx hb
      cases (by simpa using hx : N = p)
      exact StdRed.head (HeadBeta.basis M b) (StdRed.betaSubst_mono hMN hb)
  | app _ _ _ _ => intro p b b' hx _; exact absurd hx (by simp)
  | head hLM _ ih =>
      intro p b b' hx hb
      exact StdRed.head (HeadBeta.appL b hLM) (ih hx hb)

/-! ## 3. Standard reductions absorb a beta step, and the theorem -/

/-- **Kashima's lemma**: appending a beta step to a standard reduction sequence
    gives (after rearranging) a standard reduction sequence again. -/
theorem StdRed.append_beta {n : Nat} {a b : Term n} (h : a —→ₛ b) :
    ∀ {c : Term n}, b —→ c → a —→ₛ c := by
  induction h with
  | var i => intro c hc; exact absurd hc (fun h => h.var_inv)
  | abs _ ih =>
      intro c hc
      obtain ⟨N', rfl, hstep⟩ := hc.abs_inv
      exact StdRed.abs (ih hstep)
  | @app n M M' N N' hM hN ihM ihN =>
      intro c hc
      rcases hc.app_inv with ⟨p, hp, rfl⟩ | ⟨a', rfl, hstep⟩ | ⟨b', rfl, hstep⟩
      · exact StdRed.app_abs hM hp hN
      · exact StdRed.app (ihM hstep) hN
      · exact StdRed.app hM (ihN hstep)
  | head hLM _ ih => intro c hc; exact StdRed.head hLM (ih hc)

/-- **Completeness**: every reduction sequence can be rearranged into a standard
    one. -/
theorem stdRed_of_betaStar {n : Nat} {a b : Term n} (h : a —→* b) : a —→ₛ b := by
  induction h with
  | refl => exact StdRed.refl _
  | tail _ step ih => exact ih.append_beta step

/-- **The Standardization Theorem**: `M` reduces to `N` if and only if there is a
    *standard* reduction sequence from `M` to `N`, i.e. one that contracts the
    head redex first and then reduces the subterms, left to right. -/
theorem standardization {n : Nat} {a b : Term n} : a —→* b ↔ a —→ₛ b :=
  ⟨stdRed_of_betaStar, StdRed.to_betaStar⟩

/-- Multi-step head reduction. -/
abbrev HeadBetaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen HeadBeta

@[inherit_doc] infix:60 " —→ₕ* " => HeadBetaStar

theorem StdRed.abs_target {n : Nat} {a x : Term n} (h : a —→ₛ x) :
    ∀ {N : Term (n + 1)}, x = ƛ N → ∃ P, a —→ₕ* ƛ P ∧ P —→* N := by
  induction h with
  | var i => intro N hN; exact absurd hN (by simp)
  | @abs n M M' hMM' _ =>
      intro N hN
      cases (by simpa using hN : M' = N)
      exact ⟨M, .refl, hMM'.to_betaStar⟩
  | app _ _ _ _ => intro N hN; exact absurd hN (by simp)
  | head hLM _ ih =>
      intro N hN
      obtain ⟨P, hhead, hbeta⟩ := ih hN
      exact ⟨P, Relation.ReflTransGen.head hLM hhead, hbeta⟩

/-- A typical consequence of standardization: if a term reduces to an
    abstraction, then it *head*-reduces to an abstraction. -/
theorem head_reduces_to_abs {n : Nat} {M : Term n} {N : Term (n + 1)} (h : M —→* ƛ N) :
    ∃ P, M —→ₕ* ƛ P ∧ P —→* N :=
  (stdRed_of_betaStar h).abs_target rfl

end FinScope
