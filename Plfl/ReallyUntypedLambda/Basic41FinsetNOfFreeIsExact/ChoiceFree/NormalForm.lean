module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Confluence

@[expose] public section

/-!
# Normal forms, consistency, Ω and fixed points — choice-free

Consequences of the Church-Rosser theorem for the intrinsically scoped terms:

* a term has at most one normal form (`normalForm_unique`);
* two distinct normal forms are never β-convertible (`eq_of_betaEq_of_normal`),
  which is the consistency of the β-theory (`consistency`);
* `Ω` reduces to nothing but itself, so it has no normal form
  (`omega_hasNoNormalForm`);
* **the fixed point theorem**: every term `F` has a term `X` with `X —→ F ⬝ X`,
  in one step (`fixed_point`), hence `X ≡β F ⬝ X`.
-/

namespace IwilareFinsetNOfFreeIsExact

/-! ### Normal forms -/

/-- A term is normal (a β-normal form) when no β-step applies to it. -/
def Normal {n : Nat} (M : Term n) : Prop := ∀ N, ¬ (M —→ N)

theorem not_beta_var {n : Nat} {i : Fin n} {N : Term n} : ¬ (v#i —→ N) := by
  intro h; cases h

/-- Variables are normal. -/
theorem normal_var {n : Nat} (i : Fin n) : Normal (v#i : Term n) :=
  fun _ h => not_beta_var h

theorem beta_abs_inv {n : Nat} {M : Term (n + 1)} {N : Term n} (h : ƛ M —→ N) :
    ∃ M', N = ƛ M' ∧ M —→ M' := by
  cases h with
  | abs h0 => exact ⟨_, rfl, h0⟩

/-- `ƛ M` is normal iff `M` is. -/
theorem normal_abs_iff {n : Nat} {M : Term (n + 1)} : Normal (ƛ M) ↔ Normal M := by
  constructor
  · intro h N hN
    exact h (ƛ N) (Beta.abs hN)
  · intro h N hN
    obtain ⟨M', rfl, hM'⟩ := beta_abs_inv hN
    exact h M' hM'

/-- An application of a non-abstraction is normal as soon as both parts are. -/
theorem normal_app {n : Nat} {M N : Term n} (hM : Normal M) (hN : Normal N)
    (hMabs : ∀ (P : Term (n + 1)), M ≠ ƛ P) : Normal (M ⬝ N) := by
  intro K hK
  cases hK with
  | appl _ h => exact hN _ h
  | appr _ h => exact hM _ h
  | basis P Q => exact hMabs P rfl

/-- A normal form reduces only to itself. -/
theorem eq_of_betaStar_of_normal {n : Nat} {M N : Term n} (hM : Normal M) (h : M —→* N) :
    N = M := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (hM _)

/-- **Uniqueness of normal forms**: a term reduces to at most one normal form. -/
theorem normalForm_unique {n : Nat} {M N1 N2 : Term n} (h1 : M —→* N1) (h2 : M —→* N2)
    (hN1 : Normal N1) (hN2 : Normal N2) : N1 = N2 := by
  obtain ⟨d, hd1, hd2⟩ := beta_confluence h1 h2
  exact (eq_of_betaStar_of_normal hN1 hd1).symm.trans (eq_of_betaStar_of_normal hN2 hd2)

/-- **Two β-convertible normal forms are equal**. -/
theorem eq_of_betaEq_of_normal {n : Nat} {M N : Term n} (h : M ≡β N)
    (hM : Normal M) (hN : Normal N) : M = N := by
  obtain ⟨d, hd1, hd2⟩ := church_rosser h
  exact (eq_of_betaStar_of_normal hM hd1).symm.trans (eq_of_betaStar_of_normal hN hd2)

/-- Distinct normal forms are never convertible. -/
theorem not_betaEq_of_ne_normal {n : Nat} {M N : Term n} (hM : Normal M) (hN : Normal N)
    (hne : M ≠ N) : ¬ (M ≡β N) :=
  fun h => hne (eq_of_betaEq_of_normal h hM hN)

/-- `M` has a normal form. -/
def HasNormalForm {n : Nat} (M : Term n) : Prop := ∃ N, M —→* N ∧ Normal N

/-- Having a normal form is invariant along reduction. -/
theorem hasNormalForm_of_betaStar {n : Nat} {M N : Term n} (h : M —→* N)
    (hN : HasNormalForm N) : HasNormalForm M := by
  obtain ⟨K, hK, hKn⟩ := hN
  exact ⟨K, h.trans hK, hKn⟩

/-! ### Consistency of the β-theory -/

/-- The identity `ƛx. x` is a normal form. -/
theorem normal_id : Normal Term.id :=
  normal_abs_iff.mpr (normal_var _)

/-- `ƛx. ƛy. x` is a normal form. -/
theorem normal_const : Normal Term.const :=
  normal_abs_iff.mpr (normal_abs_iff.mpr (normal_var _))

/-- **Consistency**: the β-theory is not trivial — `ƛx. x` and `ƛx. ƛy. x` are
not β-convertible. -/
theorem consistency : ¬ (Term.id ≡β Term.const) :=
  not_betaEq_of_ne_normal normal_id normal_const (by decide)

/-! ### Ω has no normal form -/

/-- The self-application `ƛx. x x`. -/
def delta : Term 0 := ƛ (v#0 ⬝ v#0)

/-- `Ω = (ƛx. x x) (ƛx. x x)`. -/
def omega : Term 0 := delta ⬝ delta

theorem normal_delta : Normal delta :=
  normal_abs_iff.mpr (normal_app (normal_var _) (normal_var _) (fun _ h => by cases h))

/-- `Ω` β-reduces to nothing but itself. -/
theorem beta_omega_iff {N : Term 0} : omega —→ N ↔ N = omega := by
  constructor
  · intro h
    cases h with
    | appl _ h => exact absurd h (normal_delta _)
    | appr _ h => exact absurd h (normal_delta _)
    | basis M N => rfl
  · rintro rfl
    exact Beta.basis _ _

/-- `Ω` many-step reduces to nothing but itself. -/
theorem betaStar_omega_iff {N : Term 0} : omega —→* N ↔ N = omega := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ step ih =>
      subst ih
      exact beta_omega_iff.mp step
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- `Ω` is not normal. -/
theorem not_normal_omega : ¬ Normal omega :=
  fun h => h omega (beta_omega_iff.mpr rfl)

/-- **`Ω` has no normal form**: it is a term without a β-normal form. -/
theorem omega_hasNoNormalForm : ¬ HasNormalForm omega := by
  rintro ⟨N, hN, hNn⟩
  exact not_normal_omega (betaStar_omega_iff.mp hN ▸ hNn)

/-- `Ω` is not convertible to any normal form. -/
theorem omega_not_betaEq_normal {N : Term 0} (hN : Normal N) : ¬ (omega ≡β N) := by
  intro h
  obtain ⟨d, hd1, hd2⟩ := church_rosser h
  rw [betaStar_omega_iff.mp hd1] at hd2
  exact not_normal_omega (eq_of_betaStar_of_normal hN hd2 ▸ hN)

/-! ### The fixed point theorem -/

/-- **The fixed point theorem**: for every term `F` there is a term `X` which
β-reduces in a single step to `F ⬝ X`. -/
theorem fixed_point {n : Nat} (F : Term n) : ∃ X : Term n, X —→ F ⬝ X := by
  refine ⟨(ƛ (shift F ⬝ (v#0 ⬝ v#0))) ⬝ (ƛ (shift F ⬝ (v#0 ⬝ v#0))), ?_⟩
  have h := Beta.basis (shift F ⬝ (v#0 ⬝ v#0)) (ƛ (shift F ⬝ (v#0 ⬝ v#0)))
  have hsub : (shift F ⬝ (v#0 ⬝ v#0))[ƛ (shift F ⬝ (v#0 ⬝ v#0))]
      = F ⬝ ((ƛ (shift F ⬝ (v#0 ⬝ v#0))) ⬝ (ƛ (shift F ⬝ (v#0 ⬝ v#0)))) := by
    show ((shift F)[ƛ (shift F ⬝ (v#0 ⬝ v#0))]) ⬝ _ = _
    rw [rename_succ_subst_cancel]
    rfl
  rwa [hsub] at h

/-- Every term `F` has a fixed point up to β-conversion. -/
theorem fixed_point_betaEq {n : Nat} (F : Term n) : ∃ X : Term n, X ≡β F ⬝ X := by
  obtain ⟨X, hX⟩ := fixed_point F
  exact ⟨X, Relation.EqvGen.rel _ _ hX⟩

end IwilareFinsetNOfFreeIsExact
