module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.SimpleTypes

@[expose] public section

/-!
# Strong normalisation of the simply typed λ-calculus

This file proves, choice-free, that every simply typed term is strongly
normalising for β-reduction, by Tait's reducibility ("logical relations")
method.

Strong normalisation is expressed as accessibility of the *reversed*
β-reduction relation, `SN M := Acc (fun N K => K —→ N) M`: every reduction
sequence out of `M` terminates.

The reducibility predicate `Red A n M` is defined by recursion on the type `A`
and is closed under reduction (`Red.step`), contains all strongly normalising
neutral terms whose reducts are reducible (`Red.of_notAbs`), and only contains
strongly normalising terms (`Red.sn`).  The fundamental theorem
(`Typed.red_subst`) says that a typed term is reducible under every reducible
substitution, and strong normalisation (`Typed.strongly_normalizing`) follows.

As a constructive complement, `hasRedex` decides whether a term contains a
β-redex; combined with strong normalisation this gives that every typed term
really *has* a β-normal form (`Typed.hasNormalForm`), without any appeal to
classical logic.
-/

namespace IwilareFinsetNOfFreeIsExact

/-! ### Strong normalisation -/

/-- `SN M`: every β-reduction sequence starting from `M` terminates. -/
def SN {n : Nat} (M : Term n) : Prop := Acc (fun N K => K —→ N) M

theorem SN.step {n : Nat} {M N : Term n} (h : SN M) (hstep : M —→ N) : SN N :=
  h.inv hstep

theorem SN.intro' {n : Nat} {M : Term n} (h : ∀ N, M —→ N → SN N) : SN M :=
  Acc.intro M h

theorem SN.of_normal {n : Nat} {M : Term n} (h : Normal M) : SN M :=
  SN.intro' (fun N hN => absurd hN (h N))

/-- If `f` maps β-steps to β-steps, then `f M` strongly normalising forces `M`
strongly normalising. -/
theorem SN.of_map {n m : Nat} (f : Term n → Term m)
    (hf : ∀ {M N : Term n}, M —→ N → f M —→ f N) {M : Term n} (h : SN (f M)) : SN M := by
  generalize hx : f M = x at h
  induction h generalizing M with
  | intro x _ ih =>
    subst hx
    exact SN.intro' (fun N hN => ih (f N) (hf hN) rfl)

theorem SN.of_subst {n m : Nat} (σ : SubstContract n m) {M : Term n}
    (h : SN (substContract σ M)) : SN M :=
  SN.of_map (substContract σ) (fun hs => beta_subst_left σ hs) h

theorem SN.abs {n : Nat} {M : Term (n + 1)} (h : SN M) : SN (ƛ M) := by
  induction h with
  | intro M _ ih =>
    refine SN.intro' (fun K hK => ?_)
    obtain ⟨M', rfl, hstep⟩ := beta_abs_inv hK
    exact ih M' hstep

theorem SN.shift {n : Nat} {M : Term n} (h : SN M) : SN (shift M) := by
  induction h with
  | intro M _ ih =>
    refine SN.intro' (fun K hK => ?_)
    obtain ⟨M', rfl, hstep⟩ := beta_shift_inv hK
    exact ih M' hstep

/-! ### Reducibility -/

/-- `M` is not an abstraction (in the rewriting literature: `M` is *neutral*). -/
def NotAbs {n : Nat} (M : Term n) : Prop := ∀ A : Term (n + 1), M ≠ ƛ A

theorem notAbs_var {n : Nat} (i : Fin n) : NotAbs (v#i : Term n) := by
  intro A h; cases h

theorem notAbs_app {n : Nat} (M N : Term n) : NotAbs (M ⬝ N) := by
  intro A h; cases h

/-- Tait's reducibility predicate, by recursion on the type. -/
def Red : Ty → (n : Nat) → Term n → Prop
  | .base, _, M => SN M
  | .arrow A B, n, M => SN M ∧ ∀ N : Term n, Red A n N → Red B n (M ⬝ N)

theorem Red.base_iff {n : Nat} {M : Term n} : Red .base n M ↔ SN M := Iff.rfl

theorem Red.arrow_iff {A B : Ty} {n : Nat} {M : Term n} :
    Red (A ⇒ B) n M ↔ SN M ∧ ∀ N : Term n, Red A n N → Red B n (M ⬝ N) := Iff.rfl

/-- **CR1**: reducible terms are strongly normalising. -/
theorem Red.sn {A : Ty} {n : Nat} {M : Term n} (h : Red A n M) : SN M := by
  cases A with
  | base => exact h
  | arrow A B => exact h.1

/-- **CR2**: reducibility is preserved by reduction. -/
theorem Red.step {A : Ty} {n : Nat} {M N : Term n} (h : Red A n M) (hstep : M —→ N) :
    Red A n N := by
  induction A generalizing M N with
  | base => exact SN.step h hstep
  | arrow A B _ ihB =>
    exact ⟨SN.step h.1 hstep, fun K hK => ihB (h.2 K hK) (Beta.appr K hstep)⟩

/-- **CR3**: a neutral term all of whose reducts are reducible is reducible. -/
theorem Red.of_notAbs {A : Ty} {n : Nat} {M : Term n} (hne : NotAbs M)
    (h : ∀ N, M —→ N → Red A n N) : Red A n M := by
  induction A generalizing n M with
  | base => exact SN.intro' (fun N hN => (h N hN).sn)
  | arrow A B ihA ihB =>
    refine ⟨SN.intro' (fun N hN => (h N hN).sn), ?_⟩
    suffices H : ∀ N : Term n, SN N → Red A n N → Red B n (M ⬝ N) from
      fun N hN => H N hN.sn hN
    intro N hsn
    induction hsn with
    | intro N _ ihN =>
      intro hN
      refine ihB (notAbs_app _ _) (fun K hK => ?_)
      rcases beta_app_inv hK with ⟨M', rfl, hM⟩ | ⟨N', rfl, hN'⟩ | ⟨A', hA', _⟩
      · exact (h M' hM).2 N hN
      · exact ihN N' hN' (hN.step hN')
      · exact absurd hA' (hne A')

/-- Variables are reducible. -/
theorem Red.var {A : Ty} {n : Nat} (i : Fin n) : Red A n (v#i) :=
  Red.of_notAbs (notAbs_var i) (fun _ h => absurd h not_beta_var)

/-- Substituting into `substContract σ.ext M` under a binder. -/
def SubstContract.cons {n m : Nat} (σ : SubstContract n m) (N : Term m) :
    SubstContract (n + 1) m where
  gt := Nat.lt_succ_of_lt σ.gt
  map := Fin.cases N σ.map

theorem betaSubst_substContract_ext {n m : Nat} (σ : SubstContract n m) (M : Term (n + 1))
    (N : Term m) : (substContract σ.ext M)[N] = substContract (σ.cons N) M := by
  refine substContract_comp (Term.mkSubstZero N) σ.ext (σ.cons N) ?_ M
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact rename_succ_subst_cancel (σ.map j) N

/-- The key lemma for abstractions: an application `(ƛ P) ⬝ N` is reducible as
soon as every instance `P[N']` at a reducible argument is. -/
theorem Red.app_abs {A B : Ty} {n : Nat} {P : Term (n + 1)} (hP : SN P) :
    ∀ {N : Term n}, SN N → (∀ N' : Term n, Red A n N' → Red B n (P[N'])) →
      Red A n N → Red B n ((ƛ P) ⬝ N) := by
  induction hP with
  | intro P _ ihP =>
    intro N hN hsub
    induction hN with
    | intro N _ ihN =>
      intro hred
      refine Red.of_notAbs (notAbs_app _ _) (fun K hK => ?_)
      rcases beta_app_inv hK with ⟨L', rfl, hL⟩ | ⟨N', rfl, hN'⟩ | ⟨A', hA', hK'⟩
      · obtain ⟨P', rfl, hstep⟩ := beta_abs_inv hL
        refine ihP P' hstep hred.sn (fun N' hN' => ?_) hred
        exact (hsub N' hN').step (beta_subst_left (Term.mkSubstZero N') hstep)
      · exact ihN N' hN' (hred.step hN')
      · have : P = A' := by injection hA'
        subst this
        subst hK'
        exact hsub N hred

/-- Reducibility of abstractions. -/
theorem Red.abs {A B : Ty} {n : Nat} {P : Term (n + 1)} (hP : SN P)
    (hsub : ∀ N : Term n, Red A n N → Red B n (P[N])) : Red (A ⇒ B) n (ƛ P) :=
  ⟨hP.abs, fun _ hN => Red.app_abs hP hN.sn hsub hN⟩

/-- Every type has a reducible inhabitant in every scope — including the empty
scope, where no variable is available. -/
theorem Red.nonempty (A : Ty) (n : Nat) : ∃ M : Term n, Red A n M := by
  induction A generalizing n with
  | base =>
    refine ⟨ƛ v#0, SN.of_normal ?_⟩
    exact normal_abs_iff.mpr (normal_var 0)
  | arrow A B _ ihB =>
    obtain ⟨Q, hQ⟩ := ihB n
    refine ⟨ƛ (shift Q), Red.abs hQ.sn.shift (fun N _ => ?_)⟩
    rw [rename_succ_subst_cancel]
    exact hQ

/-! ### The fundamental theorem -/

/-- A substitution is reducible when each of its components is reducible at the
type the context assigns to the corresponding variable. -/
def RedSubst {n m : Nat} (Γ : Ctx n) (σ : SubstContract n m) : Prop :=
  ∀ i, Red (Γ i) m (σ.map i)

/-- **The fundamental theorem of logical relations**: a typed term is reducible
under every reducible substitution. -/
theorem Typed.red_subst {n : Nat} {Γ : Ctx n} {M : Term n} {A : Ty} (h : Typed Γ M A) :
    ∀ {m : Nat} (σ : SubstContract n m), RedSubst Γ σ → Red A m (substContract σ M) := by
  induction h with
  | var Γ i => exact fun σ hσ => hσ i
  | @abs n Γ A B M _ ih =>
    intro m σ hσ
    have hsub : ∀ N : Term m, Red A m N → Red B m ((substContract σ.ext M)[N]) := by
      intro N hN
      rw [betaSubst_substContract_ext]
      refine ih (σ.cons N) ?_
      intro i
      refine Fin.cases ?_ ?_ i
      · exact hN
      · intro j
        exact hσ j
    obtain ⟨N₀, hN₀⟩ := Red.nonempty A m
    have hP : SN (substContract σ.ext M) :=
      SN.of_subst (Term.mkSubstZero N₀) (hsub N₀ hN₀).sn
    exact Red.abs hP hsub
  | app _ _ ihM ihN => exact fun σ hσ => (ihM σ hσ).2 _ (ihN σ hσ)

/-- **Strong normalisation of the simply typed λ-calculus**: every typed term is
strongly normalising for β-reduction. -/
theorem Typed.strongly_normalizing {n : Nat} {Γ : Ctx n} {M : Term n} {A : Ty}
    (h : Typed Γ M A) : SN M := by
  obtain ⟨N₀, hN₀⟩ := Red.nonempty Ty.base n
  have hσ : RedSubst (Ctx.cons Ty.base Γ) (Term.mkSubstZero N₀) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hN₀
    · intro j
      exact Red.var j
  have hred := (h.shift (B := Ty.base)).red_subst (Term.mkSubstZero N₀) hσ
  have heq : substContract (Term.mkSubstZero N₀) (IwilareFinsetNOfFreeIsExact.shift M) = M :=
    rename_succ_subst_cancel M N₀
  rw [heq] at hred
  exact hred.sn

/-! ### Every typed term has a normal form, constructively -/

/-- Whether a term is an abstraction. -/
def isAbs {n : Nat} : Term n → Bool
  | ƛ _ => true
  | _   => false

theorem ne_abs_of_isAbs_false {n : Nat} {M : Term n} (h : isAbs M = false)
    (A : Term (n + 1)) : M ≠ ƛ A := by
  intro hM
  rw [hM] at h
  exact Bool.noConfusion h

/-- Whether a term contains a β-redex. -/
def hasRedex {n : Nat} : Term n → Bool
  | v#_   => false
  | ƛ M   => hasRedex M
  | M ⬝ N => isAbs M || hasRedex M || hasRedex N

theorem normal_of_hasRedex_false {n : Nat} {M : Term n} (h : hasRedex M = false) :
    Normal M := by
  induction M with
  | var i => exact normal_var i
  | abs A ih => exact normal_abs_iff.mpr (ih h)
  | app L N ihL ihN =>
    simp only [hasRedex, Bool.or_eq_false_iff] at h
    exact normal_app (ihL h.1.2) (ihN h.2) (ne_abs_of_isAbs_false h.1.1)

theorem beta_of_hasRedex_true {n : Nat} {M : Term n} (h : hasRedex M = true) :
    ∃ N, M —→ N := by
  induction M with
  | var i => exact absurd h (by simp [hasRedex])
  | abs A ih =>
    obtain ⟨N, hN⟩ := ih h
    exact ⟨ƛ N, Beta.abs hN⟩
  | app L N ihL ihN =>
    simp only [hasRedex, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · cases L with
      | var i => exact absurd h (by simp [isAbs])
      | app L1 L2 => exact absurd h (by simp [isAbs])
      | abs A => exact ⟨A[N], Beta.basis A N⟩
    · obtain ⟨L', hL'⟩ := ihL h
      exact ⟨L' ⬝ N, Beta.appr N hL'⟩
    · obtain ⟨N', hN'⟩ := ihN h
      exact ⟨L ⬝ N', Beta.appl _ hN'⟩

/-- A strongly normalising term has a normal form.  The argument is
constructive: `hasRedex` decides whether a term can still be reduced. -/
theorem SN.hasNormalForm {n : Nat} {M : Term n} (h : SN M) : HasNormalForm M := by
  induction h with
  | intro M _ ih =>
    cases hr : hasRedex M with
    | false => exact ⟨M, Relation.ReflTransGen.refl, normal_of_hasRedex_false hr⟩
    | true =>
      obtain ⟨N, hN⟩ := beta_of_hasRedex_true hr
      obtain ⟨K, hK, hKn⟩ := ih N hN
      exact ⟨K, Relation.ReflTransGen.head hN hK, hKn⟩

/-- **Weak normalisation of the simply typed λ-calculus**: every typed term has
a β-normal form. -/
theorem Typed.hasNormalForm {n : Nat} {Γ : Ctx n} {M : Term n} {A : Ty}
    (h : Typed Γ M A) : HasNormalForm M :=
  h.strongly_normalizing.hasNormalForm

/-- `Ω` is not typable. -/
theorem not_typed_omega {A : Ty} : ¬ Typed emptyCtx omega A := by
  intro h
  exact omega_hasNoNormalForm h.hasNormalForm

/-! ### Canonical forms -/

theorem normal_app_left {n : Nat} {L N : Term n} (h : Normal (L ⬝ N)) : Normal L :=
  fun L' hL' => h (L' ⬝ N) (Beta.appr N hL')

/-- A normal term that is not an abstraction has a variable at its head, so its
scope cannot be empty. -/
theorem nonempty_fin_of_normal_notAbs {n : Nat} {M : Term n} (hn : Normal M)
    (hna : NotAbs M) : Nonempty (Fin n) := by
  induction M with
  | var i => exact ⟨i⟩
  | abs P _ => exact absurd rfl (hna P)
  | app L N ihL _ =>
    refine ihL (normal_app_left hn) (fun P hP => ?_)
    subst hP
    exact hn _ (Beta.basis P N)

/-- **Canonical forms**: every closed normal term is an abstraction. -/
theorem closed_normal_is_abs {M : Term 0} (hn : Normal M) : ∃ P, M = ƛ P := by
  cases M with
  | var i => exact i.elim0
  | abs P => exact ⟨P, rfl⟩
  | app L N =>
    exact absurd (nonempty_fin_of_normal_notAbs hn (notAbs_app L N))
      (fun h => h.elim (fun i => i.elim0))

/-- Every closed simply typed term β-reduces to an abstraction. -/
theorem Typed.reduces_to_abs {M : Term 0} {A : Ty} (h : Typed emptyCtx M A) :
    ∃ P, M —→* ƛ P := by
  obtain ⟨K, hK, hKn⟩ := h.hasNormalForm
  obtain ⟨P, rfl⟩ := closed_normal_is_abs hKn
  exact ⟨P, hK⟩

/-! ### Sanity checks: the typing judgement is inhabited -/

/-- The identity is typable. -/
theorem typed_id : Typed emptyCtx Term.id (Ty.base ⇒ Ty.base) :=
  Typed.abs (Typed.var _ 0)

/-- The Church numeral `2` is typable. -/
theorem typed_two : Typed emptyCtx Term.two ((Ty.base ⇒ Ty.base) ⇒ (Ty.base ⇒ Ty.base)) := by
  refine Typed.abs (Typed.abs (Typed.app (A := Ty.base) ?_ (Typed.app (A := Ty.base) ?_ ?_)))
  · exact Typed.var _ (Fin.succ 0)
  · exact Typed.var _ (Fin.succ 0)
  · exact Typed.var _ 0

example : SN Term.two := typed_two.strongly_normalizing

end IwilareFinsetNOfFreeIsExact
