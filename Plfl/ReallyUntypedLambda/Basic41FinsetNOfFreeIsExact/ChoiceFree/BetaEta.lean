module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Eta

@[expose] public section

/-!
# The Church-Rosser theorem for βη

Combining

* confluence of β (`beta_confluence`, Takahashi's proof),
* confluence of η (`eta_confluence`, from subcommutativity), and
* the commutation of the two (`betaStar_etaStar_commute`),

through the Hindley-Rosen lemma (`Relation.reflTransGen_union_confluent`) gives
**confluence of βη-reduction** and hence the Church-Rosser theorem for
βη-conversion.  Nothing here uses `Classical.choice`.
-/

namespace IwilareFinsetNOfFreeIsExact

/-- βη-reduction: a β-step or an η-step. -/
abbrev BetaEta {n : Nat} : Term n → Term n → Prop := Relation.UnionRel Beta Eta

@[inherit_doc] infix:65 " —→βη " => BetaEta

/-- Many-step βη-reduction. -/
abbrev BetaEtaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaEta

@[inherit_doc] infix:64 " —→βη* " => BetaEtaStar

/-- βη-conversion. -/
abbrev BetaEtaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen (BetaEta (n := n))

@[inherit_doc] infix:64 " ≡βη " => BetaEtaEq

/-- Joinability by βη-reduction. -/
abbrev BetaEtaJoin {n : Nat} : Term n → Term n → Prop :=
  Relation.Join (BetaEtaStar (n := n))

theorem betaEta_of_beta {n : Nat} {M N : Term n} (h : M —→ N) : M —→βη N := Or.inl h

theorem betaEta_of_eta {n : Nat} {M N : Term n} (h : M —→η N) : M —→βη N := Or.inr h

theorem betaEtaStar_of_betaStar {n : Nat} {M N : Term n} (h : M —→* N) : M —→βη* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (betaEta_of_beta step)

theorem betaEtaStar_of_etaStar {n : Nat} {M N : Term n} (h : M —→η* N) : M —→βη* N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (betaEta_of_eta step)

/-- **Confluence of βη-reduction** (the Church-Rosser property). -/
theorem betaEta_confluence {n : Nat} {M N1 N2 : Term n} (h1 : M —→βη* N1) (h2 : M —→βη* N2) :
    BetaEtaJoin N1 N2 :=
  Relation.reflTransGen_union_confluent
    (fun _ _ _ h1 h2 => beta_confluence h1 h2)
    (fun _ _ _ h1 h2 => eta_confluence h1 h2)
    (fun _ _ _ h1 h2 => betaStar_etaStar_commute h1 h2) h1 h2

/-- Joinability by βη is an equivalence relation. -/
theorem betaEtaJoin_equivalence {n : Nat} : Equivalence (BetaEtaJoin (n := n)) :=
  Relation.equivalence_join (fun _ _ _ h1 h2 => betaEta_confluence h1 h2)

/-- **The Church-Rosser theorem for βη**: βη-convertible terms have a common
βη-reduct. -/
theorem betaEta_church_rosser {n : Nat} {M N : Term n} (h : M ≡βη N) : BetaEtaJoin M N := by
  induction h with
  | rel _ _ step => exact ⟨_, Relation.ReflTransGen.single step, Relation.ReflTransGen.refl⟩
  | refl => exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih => exact betaEtaJoin_equivalence.symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact betaEtaJoin_equivalence.trans ih1 ih2

theorem betaEtaEq_of_betaEtaStar {n : Nat} {M N : Term n} (h : M —→βη* N) : M ≡βη N := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem betaEtaEq_of_betaEtaJoin {n : Nat} {M N : Term n} (h : BetaEtaJoin M N) : M ≡βη N := by
  obtain ⟨d, h1, h2⟩ := h
  exact Relation.EqvGen.trans _ d _ (betaEtaEq_of_betaEtaStar h1)
    (Relation.EqvGen.symm _ _ (betaEtaEq_of_betaEtaStar h2))

/-- βη-conversion is exactly joinability by βη-reduction. -/
theorem betaEtaEq_iff_betaEtaJoin {n : Nat} {M N : Term n} : M ≡βη N ↔ BetaEtaJoin M N :=
  ⟨betaEta_church_rosser, betaEtaEq_of_betaEtaJoin⟩

/-! ### βη-normal forms -/

/-- A term is βη-normal when neither a β- nor an η-step applies to it. -/
def NormalBetaEta {n : Nat} (M : Term n) : Prop := ∀ N, ¬ (M —→βη N)

theorem eq_of_betaEtaStar_of_normal {n : Nat} {M N : Term n} (hM : NormalBetaEta M)
    (h : M —→βη* N) : N = M := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (hM _)

/-- **Uniqueness of βη-normal forms**. -/
theorem betaEta_normalForm_unique {n : Nat} {M N1 N2 : Term n} (h1 : M —→βη* N1)
    (h2 : M —→βη* N2) (hN1 : NormalBetaEta N1) (hN2 : NormalBetaEta N2) : N1 = N2 := by
  obtain ⟨d, hd1, hd2⟩ := betaEta_confluence h1 h2
  exact (eq_of_betaEtaStar_of_normal hN1 hd1).symm.trans (eq_of_betaEtaStar_of_normal hN2 hd2)

/-- **Two βη-convertible βη-normal forms are equal**. -/
theorem eq_of_betaEtaEq_of_normal {n : Nat} {M N : Term n} (h : M ≡βη N)
    (hM : NormalBetaEta M) (hN : NormalBetaEta N) : M = N := by
  obtain ⟨d, hd1, hd2⟩ := betaEta_church_rosser h
  exact (eq_of_betaEtaStar_of_normal hM hd1).symm.trans (eq_of_betaEtaStar_of_normal hN hd2)

/-- The identity is βη-normal. -/
theorem normalBetaEta_id : NormalBetaEta Term.id := by
  rintro N (h | h)
  · exact normal_id N h
  · rcases eta_abs_inv h with ⟨A', _, hA⟩ | hA
    · exact eta_var_inv hA
    · exact absurd hA (by simp)

/-- `ƛx. ƛy. x` is βη-normal. -/
theorem normalBetaEta_const : NormalBetaEta Term.const := by
  rintro N (h | h)
  · exact normal_const N h
  · rcases eta_abs_inv h with ⟨A', _, hA⟩ | hA
    · rcases eta_abs_inv hA with ⟨A'', _, hA'⟩ | hA'
      · exact eta_var_inv hA'
      · exact absurd hA' (by simp)
    · exact absurd hA (by simp)

/-- **Consistency of the βη-theory**: `ƛx. x` and `ƛx. ƛy. x` are not
βη-convertible. -/
theorem betaEta_consistency : ¬ (Term.id ≡βη Term.const) := by
  intro h
  exact absurd (eq_of_betaEtaEq_of_normal h normalBetaEta_id normalBetaEta_const) (by decide)

end IwilareFinsetNOfFreeIsExact
