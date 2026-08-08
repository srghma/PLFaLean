module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.BetaEta

@[expose] public section

/-!
# η-postponement

**η-postponement** says that in a βη-reduction sequence all η-steps may be
postponed to the end:

`M —→βη* N` implies `∃ L, M —→β* L —→η* N`.

The proof follows the classical argument through a *parallel* η-reduction
`EtaPar` (`⇛η`): a single parallel η-step commutes with a β-step in the
postponing direction (`etaPar_beta_postpone`), and parallel η is reflexive and
sits between `—→η` and `—→η*`, so the general statement follows by two
inductions.

Nothing here uses `Classical.choice`.
-/

namespace IwilareFinsetNOfFreeIsExact

/-! ### β-reduction is preserved by renaming -/

/-- β-reduction is preserved by renaming. -/
theorem beta_rename {n m : Nat} (w : RenameWeaken n m) {M N : Term n} (h : M —→ N) :
    renameWeaken w M —→ renameWeaken w N := by
  induction h generalizing m with
  | appl L _ ih => exact Beta.appl _ (ih w)
  | appr L _ ih => exact Beta.appr _ (ih w)
  | abs _ ih => exact Beta.abs (ih w.ext)
  | basis A B =>
    show renameWeaken w ((ƛ A) ⬝ B) —→ renameWeaken w (A[B])
    rw [rename_betaSubst]
    exact Beta.basis _ _

theorem beta_shift {n : Nat} {M N : Term n} (h : M —→ N) : shift M —→ shift N :=
  beta_rename (RenameWeaken.succ n) h

theorem betaStar_shift {n : Nat} {M N : Term n} (h : M —→* N) : shift M —→* shift N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (beta_shift step)

/-! ### Parallel η-reduction -/

set_option hygiene false in
set_option quotPrecheck false in
/-- Parallel η-reduction. -/
infixl:65 " ⇛η " => EtaPar

/-- Parallel η-reduction: contract any number of η-redexes simultaneously. -/
inductive EtaPar : ∀ {n : Nat}, Term n → Term n → Prop
  | var {n : Nat} (i : Fin n) : v#i ⇛η v#i
  | abs {n : Nat} {M N : Term (n + 1)} : M ⇛η N → ƛ M ⇛η ƛ N
  | app {n : Nat} {M M' N N' : Term n} : M ⇛η M' → N ⇛η N' → M ⬝ N ⇛η M' ⬝ N'
  | elim {n : Nat} {P P' : Term n} : P ⇛η P' → ƛ (shift P ⬝ v#0) ⇛η P'

theorem etaPar_refl {n : Nat} (M : Term n) : M ⇛η M := by
  induction M with
  | var i => exact EtaPar.var i
  | abs A ih => exact EtaPar.abs ih
  | app A B ihA ihB => exact EtaPar.app ihA ihB

theorem etaPar_of_eta {n : Nat} {M N : Term n} (h : M —→η N) : M ⇛η N := by
  induction h with
  | appl L _ ih => exact EtaPar.app (etaPar_refl L) ih
  | appr L _ ih => exact EtaPar.app ih (etaPar_refl L)
  | abs _ ih => exact EtaPar.abs ih
  | basis P => exact EtaPar.elim (etaPar_refl P)

theorem etaPar_to_etaStar {n : Nat} {M N : Term n} (h : M ⇛η N) : M —→η* N := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact eta_star_abs ih
  | app _ _ ihM ihN => exact eta_star_app ihM ihN
  | @elim n P P' _ ih =>
    refine Relation.ReflTransGen.trans ?_ (Relation.ReflTransGen.single (Eta.basis P'))
    exact eta_star_abs (eta_star_appr _ (etaStar_shift ih))

/-! ### Parallel η is stable under renaming and substitution -/

theorem etaPar_rename {n m : Nat} (w : RenameWeaken n m) {M N : Term n} (h : M ⇛η N) :
    renameWeaken w M ⇛η renameWeaken w N := by
  induction h generalizing m with
  | var i => exact EtaPar.var _
  | abs _ ih => exact EtaPar.abs (ih w.ext)
  | app _ _ ihM ihN => exact EtaPar.app (ihM w) (ihN w)
  | @elim n P P' _ ih =>
    show renameWeaken w (ƛ (shift P ⬝ v#0)) ⇛η renameWeaken w P'
    show ƛ (renameWeaken w.ext (shift P) ⬝ v#0) ⇛η renameWeaken w P'
    rw [rename_succ_ext_comm w P]
    exact EtaPar.elim (ih w)

theorem etaPar_subst {n m : Nat} (σ σ' : SubstContract n m)
    (hσ : ∀ i, σ.map i ⇛η σ'.map i) {M M' : Term n} (h : M ⇛η M') :
    substContract σ M ⇛η substContract σ' M' := by
  induction h generalizing m with
  | var i => exact hσ i
  | abs _ ih =>
    refine EtaPar.abs (ih σ.ext σ'.ext ?_)
    intro i
    refine Fin.cases ?_ ?_ i
    · exact EtaPar.var 0
    · intro j
      exact etaPar_rename (RenameWeaken.succ m) (hσ j)
  | app _ _ ihM ihN => exact EtaPar.app (ihM σ σ' hσ) (ihN σ σ' hσ)
  | @elim n P P' _ ih =>
    show substContract σ (ƛ (shift P ⬝ v#0)) ⇛η substContract σ' P'
    show ƛ (substContract σ.ext (shift P) ⬝ v#0) ⇛η substContract σ' P'
    rw [substContract_shift]
    exact EtaPar.elim (ih σ σ' hσ)

theorem etaPar_betaSubst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇛η M') (hN : N ⇛η N') : M[N] ⇛η M'[N'] := by
  refine etaPar_subst (Term.mkSubstZero N) (Term.mkSubstZero N') ?_ hM
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hN
  · intro j
    exact EtaPar.var j

/-! ### Postponing a parallel η-step past a β-step -/

/-- Contracting the η-redex `ƛ (P↑ ⬝ #0)` applied to an argument is one
β-step. -/
theorem beta_etaRedex_app {n : Nat} (P N : Term n) : (ƛ (shift P ⬝ v#0)) ⬝ N —→ P ⬝ N := by
  have h : Term.betaSubst (shift P ⬝ v#0) N = P ⬝ N := by
    show Term.betaSubst (shift P) N ⬝ Term.betaSubst (v#0) N = P ⬝ N
    rw [rename_succ_subst_cancel]
    rfl
  have := Beta.basis (shift P ⬝ v#0) N
  rwa [h] at this

private theorem etaPar_beta_postpone_aux : ∀ (s : Nat) {n : Nat} {M N K : Term n},
    size M ≤ s → M ⇛η N → N —→ K → ∃ L, M —→* L ∧ L ⇛η K := by
  intro s
  induction s with
  | zero =>
    intro n M N K hs _ _
    exact absurd hs (by cases M <;> simp [size])
  | succ s ih =>
    intro n M N K hs h hstep
    cases h with
    | var i => exact absurd hstep not_beta_var
    | @abs n A B hAB =>
      obtain ⟨B', rfl, hB⟩ := beta_abs_inv hstep
      have hsA : size A ≤ s := by
        simp only [size] at hs; omega
      obtain ⟨L, hL, hLB⟩ := ih hsA hAB hB
      exact ⟨ƛ L, beta_star_abs hL, EtaPar.abs hLB⟩
    | @app n M1 N1 M2 N2 h1 h2 =>
      have hs1 : size M1 ≤ s := by
        simp only [size] at hs
        have := Nat.one_le_iff_ne_zero.mpr (by cases M2 <;> simp [size] : size M2 ≠ 0)
        omega
      have hs2 : size M2 ≤ s := by
        simp only [size] at hs
        have := Nat.one_le_iff_ne_zero.mpr (by cases M1 <;> simp [size] : size M1 ≠ 0)
        omega
      rcases beta_app_inv hstep with ⟨N1', rfl, hN1⟩ | ⟨N2', rfl, hN2⟩ | ⟨R, hR, rfl⟩
      · obtain ⟨L, hL, hLK⟩ := ih hs1 h1 hN1
        exact ⟨L ⬝ M2, beta_star_appr M2 hL, EtaPar.app hLK h2⟩
      · obtain ⟨L, hL, hLK⟩ := ih hs2 h2 hN2
        exact ⟨M1 ⬝ L, beta_star_appl M1 hL, EtaPar.app h1 hLK⟩
      · subst hR
        cases h1 with
        | abs hS =>
          exact ⟨_, Relation.ReflTransGen.single (Beta.basis _ M2), etaPar_betaSubst hS h2⟩
        | elim hP =>
          rename_i P
          have hsize : size (P ⬝ M2) ≤ s := by
            simp only [size, size_ren] at hs ⊢
            omega
          obtain ⟨L, hL, hLK⟩ := ih hsize (EtaPar.app hP h2) (Beta.basis R N2)
          exact ⟨L, Relation.ReflTransGen.head (beta_etaRedex_app P M2) hL, hLK⟩
    | @elim n P P' hP =>
      have hsP : size P ≤ s := by
        simp only [size, size_ren] at hs; omega
      obtain ⟨L, hL, hLK⟩ := ih hsP hP hstep
      refine ⟨ƛ (shift L ⬝ v#0), ?_, EtaPar.elim hLK⟩
      exact beta_star_abs (beta_star_appr _ (betaStar_shift hL))

/-- A parallel η-step followed by a β-step can be replaced by β-steps followed
by a parallel η-step. -/
theorem etaPar_beta_postpone {n : Nat} {M N K : Term n} (h : M ⇛η N) (hstep : N —→ K) :
    ∃ L, M —→* L ∧ L ⇛η K :=
  etaPar_beta_postpone_aux (size M) (Nat.le_refl _) h hstep

/-! ### η-postponement -/

/-- A parallel η-step followed by β-steps can be replaced by β-steps followed
by a parallel η-step. -/
theorem etaPar_betaStar_postpone {n : Nat} {M N K : Term n} (h : M ⇛η N) (hK : N —→* K) :
    ∃ L, M —→* L ∧ L ⇛η K := by
  induction hK generalizing M with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, h⟩
  | @tail B C _ hstep ih =>
    obtain ⟨L1, hL1, hL1B⟩ := ih h
    obtain ⟨L2, hL2, hL2C⟩ := etaPar_beta_postpone hL1B hstep
    exact ⟨L2, Relation.ReflTransGen.trans hL1 hL2, hL2C⟩

/-- η-steps can be postponed past β-steps. -/
theorem etaStar_betaStar_postpone {n : Nat} {M N : Term n} (h : M —→η* N) :
    ∀ {K : Term n}, N —→* K → ∃ L, M —→* L ∧ L —→η* K := by
  induction h with
  | refl => exact fun hK => ⟨_, hK, Relation.ReflTransGen.refl⟩
  | @tail B C hMB hstep ihB =>
    intro K hK
    obtain ⟨L1, hL1, hL1K⟩ := etaPar_betaStar_postpone (etaPar_of_eta hstep) hK
    obtain ⟨L2, hL2, hL2L1⟩ := ihB hL1
    exact ⟨L2, hL2, Relation.ReflTransGen.trans hL2L1 (etaPar_to_etaStar hL1K)⟩

/-- **η-postponement**: every βη-reduction sequence can be rearranged into
β-steps followed by η-steps. -/
theorem betaEtaStar_postponement {n : Nat} {M N : Term n} (h : M —→βη* N) :
    ∃ L, M —→* L ∧ L —→η* N := by
  induction h with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail N' N _ hstep ih =>
    obtain ⟨L, hL, hLN'⟩ := ih
    cases hstep with
    | inl hb =>
      obtain ⟨L2, hL2, hL2N⟩ :=
        etaStar_betaStar_postpone hLN' (Relation.ReflTransGen.single hb)
      exact ⟨L2, Relation.ReflTransGen.trans hL hL2, hL2N⟩
    | inr he =>
      exact ⟨L, hL, Relation.ReflTransGen.tail hLN' he⟩

theorem betaStar_to_betaEtaStar {n : Nat} {M N : Term n} (h : M —→* N) : M —→βη* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (betaEta_of_beta step)

theorem etaStar_to_betaEtaStar {n : Nat} {M N : Term n} (h : M —→η* N) : M —→βη* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (betaEta_of_eta step)

/-- βη-reduction is exactly β-reduction followed by η-reduction. -/
theorem betaEtaStar_iff_betaStar_etaStar {n : Nat} {M N : Term n} :
    M —→βη* N ↔ ∃ L, M —→* L ∧ L —→η* N := by
  constructor
  · exact betaEtaStar_postponement
  · rintro ⟨L, hL, hLN⟩
    exact Relation.ReflTransGen.trans (betaStar_to_betaEtaStar hL)
      (etaStar_to_betaEtaStar hLN)

end IwilareFinsetNOfFreeIsExact
