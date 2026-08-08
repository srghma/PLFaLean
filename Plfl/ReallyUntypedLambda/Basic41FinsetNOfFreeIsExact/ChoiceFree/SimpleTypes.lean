module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.BetaEta

@[expose] public section

/-!
# Simple types

Simply typed λ-terms over the intrinsically scoped syntax: a context for
`Term n` is just a function `Fin n → Ty`.  This file proves the structural
lemmas (renaming, substitution), **subject reduction** for β and for η, and
uniqueness of types.
-/

namespace IwilareFinsetNOfFreeIsExact

/-- Simple types over one base type. -/
inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

@[inherit_doc] infixr:70 " ⇒ " => Ty.arrow

/-- A typing context for `Term n`. -/
abbrev Ctx (n : Nat) := Fin n → Ty

/-- The empty context, for closed terms. -/
def emptyCtx : Ctx 0 := fun i => i.elim0

/-- Extend a context with a type for the new variable `0`. -/
def Ctx.cons {n : Nat} (A : Ty) (Γ : Ctx n) : Ctx (n + 1) := Fin.cases A Γ

@[simp] theorem Ctx.cons_zero {n : Nat} (A : Ty) (Γ : Ctx n) : Ctx.cons A Γ 0 = A := rfl

@[simp] theorem Ctx.cons_succ {n : Nat} (A : Ty) (Γ : Ctx n) (i : Fin n) :
    Ctx.cons A Γ i.succ = Γ i := rfl

/-- The typing judgement. -/
inductive Typed : ∀ {n : Nat}, Ctx n → Term n → Ty → Prop
  | var {n : Nat} (Γ : Ctx n) (i : Fin n) : Typed Γ (v#i) (Γ i)
  | abs {n : Nat} {Γ : Ctx n} {A B : Ty} {M : Term (n + 1)} :
      Typed (Ctx.cons A Γ) M B → Typed Γ (ƛ M) (A ⇒ B)
  | app {n : Nat} {Γ : Ctx n} {A B : Ty} {M N : Term n} :
      Typed Γ M (A ⇒ B) → Typed Γ N A → Typed Γ (M ⬝ N) B

/-! ### Inversion -/

theorem Typed.var_inv {n : Nat} {Γ : Ctx n} {i : Fin n} {A : Ty} (h : Typed Γ (v#i) A) :
    A = Γ i := by
  cases h; rfl

theorem Typed.abs_inv {n : Nat} {Γ : Ctx n} {M : Term (n + 1)} {C : Ty}
    (h : Typed Γ (ƛ M) C) : ∃ A B, C = A ⇒ B ∧ Typed (Ctx.cons A Γ) M B := by
  cases h with
  | abs h => exact ⟨_, _, rfl, h⟩

theorem Typed.app_inv {n : Nat} {Γ : Ctx n} {M N : Term n} {B : Ty}
    (h : Typed Γ (M ⬝ N) B) : ∃ A, Typed Γ M (A ⇒ B) ∧ Typed Γ N A := by
  cases h with
  | app hM hN => exact ⟨_, hM, hN⟩

/-! ### Renaming -/

theorem Typed.rename {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {M : Term n} {A : Ty}
    (h : Typed Γ M A) (w : RenameWeaken n m) (hw : ∀ i, Δ (w.map i) = Γ i) :
    Typed Δ (renameWeaken w M) A := by
  induction h generalizing m with
  | var Γ i =>
    have := Typed.var Δ (w.map i)
    rwa [hw i] at this
  | @abs n Γ A B M _ ih =>
    refine Typed.abs (ih (Δ := Ctx.cons A Δ) w.ext ?_)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      show Ctx.cons A Δ (w.map j).succ = Ctx.cons A Γ j.succ
      simpa using hw j
  | app _ _ ihM ihN => exact Typed.app (ihM w hw) (ihN w hw)

/-- Typing is reflected by renaming. -/
theorem Typed.of_rename {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} (M : Term n) {A : Ty}
    (w : RenameWeaken n m) (hw : ∀ i, Δ (w.map i) = Γ i)
    (h : Typed Δ (renameWeaken w M) A) : Typed Γ M A := by
  induction M generalizing m A with
  | var i =>
    have hA : A = Δ (w.map i) := h.var_inv
    rw [hA, hw i]
    exact Typed.var Γ i
  | abs M ih =>
    obtain ⟨A1, B1, rfl, hM⟩ := h.abs_inv
    refine Typed.abs (ih (Δ := Ctx.cons A1 Δ) w.ext ?_ hM)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      show Ctx.cons A1 Δ (w.map j).succ = Ctx.cons A1 Γ j.succ
      simpa using hw j
  | app M N ihM ihN =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    exact Typed.app (ihM w hw hM) (ihN w hw hN)

theorem Typed.shift {n : Nat} {Γ : Ctx n} {M : Term n} {A B : Ty} (h : Typed Γ M A) :
    Typed (Ctx.cons B Γ) (shift M) A :=
  h.rename (RenameWeaken.succ n) (fun _ => rfl)

/-! ### Substitution -/

/-- A substitution is well typed when each of its components is. -/
def TypedSubst {n m : Nat} (Γ : Ctx n) (σ : SubstContract n m) (Δ : Ctx m) : Prop :=
  ∀ i, Typed Δ (σ.map i) (Γ i)

theorem TypedSubst.ext {n m : Nat} {Γ : Ctx n} {σ : SubstContract n m} {Δ : Ctx m}
    (hσ : TypedSubst Γ σ Δ) (A : Ty) :
    TypedSubst (Ctx.cons A Γ) σ.ext (Ctx.cons A Δ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact Typed.var (Ctx.cons A Δ) 0
  · intro j
    exact (hσ j).shift

theorem Typed.subst {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {M : Term n} {A : Ty}
    (h : Typed Γ M A) {σ : SubstContract n m} (hσ : TypedSubst Γ σ Δ) :
    Typed Δ (substContract σ M) A := by
  induction h generalizing m with
  | var Γ i => exact hσ i
  | @abs n Γ A B M _ ih => exact Typed.abs (ih (hσ.ext A))
  | app _ _ ihM ihN => exact Typed.app (ihM hσ) (ihN hσ)

theorem Typed.betaSubst {n : Nat} {Γ : Ctx n} {M : Term (n + 1)} {N : Term n} {A B : Ty}
    (hM : Typed (Ctx.cons A Γ) M B) (hN : Typed Γ N A) : Typed Γ (M[N]) B := by
  refine hM.subst (σ := Term.mkSubstZero N) ?_
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hN
  · intro j
    exact Typed.var Γ j

/-! ### Subject reduction -/

/-- **Subject reduction** for β-reduction. -/
theorem Typed.preservation {n : Nat} {Γ : Ctx n} {M N : Term n} {A : Ty}
    (h : Typed Γ M A) (hstep : M —→ N) : Typed Γ N A := by
  induction hstep generalizing A with
  | appl L _ ih =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    exact Typed.app hM (ih hN)
  | appr L _ ih =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    exact Typed.app (ih hM) hN
  | abs _ ih =>
    obtain ⟨A1, B1, rfl, hM⟩ := h.abs_inv
    exact Typed.abs (ih hM)
  | basis M N =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    obtain ⟨A2, B2, hAB, hM'⟩ := hM.abs_inv
    injection hAB with h1 h2
    subst h1
    subst h2
    exact hM'.betaSubst hN

/-- **Subject reduction** for η-reduction. -/
theorem Typed.preservation_eta {n : Nat} {Γ : Ctx n} {M N : Term n} {A : Ty}
    (h : Typed Γ M A) (hstep : M —→η N) : Typed Γ N A := by
  induction hstep generalizing A with
  | appl L _ ih =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    exact Typed.app hM (ih hN)
  | appr L _ ih =>
    obtain ⟨A1, hM, hN⟩ := h.app_inv
    exact Typed.app (ih hM) hN
  | abs _ ih =>
    obtain ⟨A1, B1, rfl, hM⟩ := h.abs_inv
    exact Typed.abs (ih hM)
  | @basis n P =>
    obtain ⟨A1, B1, rfl, hbody⟩ := h.abs_inv
    obtain ⟨A2, hP, hzero⟩ := hbody.app_inv
    have hA2 : A2 = A1 := hzero.var_inv
    subst hA2
    exact Typed.of_rename P (RenameWeaken.succ n) (fun _ => rfl) hP

/-- **Subject reduction** for βη. -/
theorem Typed.preservation_betaEta {n : Nat} {Γ : Ctx n} {M N : Term n} {A : Ty}
    (h : Typed Γ M A) (hstep : M —→βη N) : Typed Γ N A := by
  cases hstep with
  | inl hstep => exact h.preservation hstep
  | inr hstep => exact h.preservation_eta hstep

theorem Typed.preservation_star {n : Nat} {Γ : Ctx n} {M N : Term n} {A : Ty}
    (h : Typed Γ M A) (hstep : M —→* N) : Typed Γ N A := by
  induction hstep with
  | refl => exact h
  | tail _ step ih => exact ih.preservation step

-- Note: types are *not* unique here, since this is a Curry-style system: the
-- untyped term `ƛ #0` has type `A ⇒ A` for every `A`.

end IwilareFinsetNOfFreeIsExact
