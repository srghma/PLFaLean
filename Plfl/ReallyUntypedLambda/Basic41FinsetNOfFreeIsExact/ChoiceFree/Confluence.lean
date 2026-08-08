module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Beta

@[expose] public section

/-!
# Church-Rosser, choice-free

Takahashi's proof: parallel reduction is stable under renaming and
substitution, the complete development `takahashi M` is a maximal parallel
reduct (triangle lemma), hence parallel reduction has the diamond property and
β-reduction is confluent.

Everything here is free of `Classical.choice` (see `ChoiceFree.Axioms`).
-/

namespace IwilareFinsetNOfFreeIsExact

/-- Takahashi's complete development: contract *all* the redexes of `M`. -/
def takahashi {n : Nat} : Term n → Term n
  | v#i          => v#i
  | (ƛ M) ⬝ N    => (takahashi M)[takahashi N]  -- fire the redex!
  | ƛ M          => ƛ (takahashi M)
  | M ⬝ N        => (takahashi M) ⬝ (takahashi N)

theorem betapar_abs_inv {n : Nat} {M N : Term (n + 1)} (h : ƛ M ⇉ ƛ N) : M ⇉ N := by
  cases h with
  | abs h0 => exact h0

theorem renameWeaken_betapar {n m : Nat} (w : RenameWeaken n m) {M M' : Term n} (h : M ⇉ M') :
    renameWeaken w M ⇉ renameWeaken w M' := by
  induction h generalizing m with
  | var i => exact BetaPar.var _
  | abs _ ih => exact BetaPar.abs (ih w.ext)
  | app _ _ ih1 ih2 => exact BetaPar.app (ih1 w) (ih2 w)
  | subst _ _ ih1 ih2 =>
    have h_step := BetaPar.subst (ih1 w.ext) (ih2 w)
    rw [rename_betaSubst]
    exact h_step

theorem substContract_ext_betapar {n m : Nat} {σ σ' : SubstContract n m}
    (hσ : ∀ i, σ.map i ⇉ σ'.map i) (i : Fin (n + 1)) :
    σ.ext.map i ⇉ σ'.ext.map i := by
  refine Fin.cases ?_ ?_ i
  · exact BetaPar.var 0
  · intro i'
    exact renameWeaken_betapar (RenameWeaken.succ m) (hσ i')

theorem betapar_subst_lemma {n m : Nat} (σ σ' : SubstContract n m)
    (hσ : ∀ i, σ.map i ⇉ σ'.map i) {M M' : Term n} (hM : M ⇉ M') :
    substContract σ M ⇉ substContract σ' M' := by
  induction hM generalizing m with
  | var i => exact hσ i
  | abs _ ih => exact BetaPar.abs (ih σ.ext σ'.ext (substContract_ext_betapar hσ))
  | app _ _ ih1 ih2 => exact BetaPar.app (ih1 σ σ' hσ) (ih2 σ σ' hσ)
  | subst _ _ ih1 ih2 =>
    have h1 := BetaPar.subst (ih1 σ.ext σ'.ext (substContract_ext_betapar hσ)) (ih2 σ σ' hσ)
    rw [subst_comm_lemma σ' _ _] at h1
    exact h1

/-- Parallel reduction is preserved by substitution. -/
theorem betapar_subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇉ M') (hN : N ⇉ N') : M[N] ⇉ M'[N'] := by
  have hσ : ∀ i : Fin (n + 1), (Term.mkSubstZero N).map i ⇉ (Term.mkSubstZero N').map i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hN
    · intro i'
      exact BetaPar.var i'
  exact betapar_subst_lemma (Term.mkSubstZero N) (Term.mkSubstZero N') hσ hM

/-- **Takahashi's triangle lemma**: every parallel reduct of `M` reduces in
parallel to the complete development of `M`. -/
theorem takahashi_triangle {n : Nat} {M N : Term n} (h : M ⇉ N) : N ⇉ takahashi M := by
  induction h with
  | var i => exact BetaPar.var i
  | abs _ ih => exact BetaPar.abs ih
  | app hM _ ihM ihN =>
    cases hM with
    | var i => exact BetaPar.app ihM ihN
    | abs _ => exact BetaPar.subst (betapar_abs_inv ihM) ihN
    | app _ _ => exact BetaPar.app ihM ihN
    | subst _ _ => exact BetaPar.app ihM ihN
  | subst _ _ ihM ihN => exact betapar_subst ihM ihN

/-- The **diamond property** of parallel reduction. -/
theorem betapar_diamond {n : Nat} {M N1 N2 : Term n} (h1 : M ⇉ N1) (h2 : M ⇉ N2) :
    ∃ D, N1 ⇉ D ∧ N2 ⇉ D :=
  ⟨takahashi M, takahashi_triangle h1, takahashi_triangle h2⟩

/-- The strip lemma, in the shape expected by `Relation.church_rosser`. -/
theorem beta_strip {n : Nat} (a b c : Term n) (hab : a ⇉ b) (hac : a ⇉ c) :
    ∃ d, Relation.ReflGen BetaPar b d ∧ Relation.ReflTransGen BetaPar c d := by
  obtain ⟨d, hbd, hcd⟩ := betapar_diamond hab hac
  exact ⟨d, Relation.ReflGen.single hbd, Relation.ReflTransGen.single hcd⟩

theorem betapar_church_rosser {n : Nat} {a b c : Term n} (hab : a ⇉* b) (hac : a ⇉* c) :
    Relation.Join (Relation.ReflTransGen BetaPar) b c :=
  Relation.church_rosser beta_strip hab hac

/-- **Confluence** of β-reduction. -/
theorem beta_confluence {n : Nat} {M N1 N2 : Term n} (h1 : M —→* N1) (h2 : M —→* N2) :
    BetaJoin N1 N2 := by
  obtain ⟨d, hbd, hcd⟩ := betapar_church_rosser
    (betapar_star_eq_betastar.mpr h1) (betapar_star_eq_betastar.mpr h2)
  exact ⟨d, betapar_star_eq_betastar.mp hbd, betapar_star_eq_betastar.mp hcd⟩

/-- Joinability is an equivalence relation, by confluence. -/
theorem betaJoin_equivalence {n : Nat} : Equivalence (BetaJoin (n := n)) :=
  Relation.equivalence_join (fun _ _ _ h1 h2 => beta_confluence h1 h2)

/-- **The Church-Rosser theorem**: β-convertible terms have a common reduct. -/
theorem church_rosser {n : Nat} {M N : Term n} (h : M ≡β N) : BetaJoin M N := by
  induction h with
  | rel _ _ step => exact ⟨_, Relation.ReflTransGen.single step, Relation.ReflTransGen.refl⟩
  | refl => exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih => exact betaJoin_equivalence.symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact betaJoin_equivalence.trans ih1 ih2

/-- Reduction implies conversion. -/
theorem betaEq_of_betaStar {n : Nat} {M N : Term n} (h : M —→* N) : M ≡β N := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

/-- Conversely, joinable terms are β-convertible. -/
theorem betaEq_of_betaJoin {n : Nat} {M N : Term n} (h : BetaJoin M N) : M ≡β N := by
  obtain ⟨d, h1, h2⟩ := h
  exact Relation.EqvGen.trans _ d _ (betaEq_of_betaStar h1)
    (Relation.EqvGen.symm _ _ (betaEq_of_betaStar h2))

/-- β-conversion is exactly joinability. -/
theorem betaEq_iff_betaJoin {n : Nat} {M N : Term n} : M ≡β N ↔ BetaJoin M N :=
  ⟨church_rosser, betaEq_of_betaJoin⟩

end IwilareFinsetNOfFreeIsExact
