module
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# A choice-free formulation: intrinsically scoped de Bruijn terms

`Basic41Finset.Term` is indexed by the *exact* set of free variables, a
`Finset Nat`, and Mathlib's `Finset.erase`, `Finset.image` and `Finset.union`
(which occur in the very definition of that type) are proved correct using
`Classical.choice`.  Consequently *no* statement about `Basic41Finset.Term` can
avoid `Classical.choice`; see `ChoiceFree.Axioms` for the machine-checked
evidence.

This namespace therefore develops the Church-Rosser theorem again, for the
intrinsically *scoped* terms `Term : Nat → Type` of the Agda development this
project follows: a `Term n` is a λ-term whose free de Bruijn indices are `< n`.
The index is a `Nat`, variables are `Fin n`, and nothing in the development
touches `Finset`, so every result here is free of `Classical.choice`.

This file contains the syntax, renamings, substitutions and the substitution
calculus.
-/

namespace IwilareFinsetNOfFreeIsExact

-- we want to force the user to use `v##`: the default `v#synth OfNat (Fin 5) 10`
-- would reduce mod 5.  Disable the two instances that do this.
attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

/-- Intrinsically scoped λ-terms: `Term n` has free de Bruijn indices `< n`. -/
inductive Term : Nat → Type
  | var : ∀ {n : Nat}, Fin n → Term n
  | abs : ∀ {n : Nat}, Term (n + 1) → Term n
  | app : ∀ {n : Nat}, Term n → Term n → Term n
  deriving DecidableEq

@[inherit_doc] prefix:71 "ƛ " => Term.abs
@[inherit_doc] infixl:70 " ⬝ " => Term.app
@[inherit_doc] prefix:72 "v#" => Term.var
macro:72 "v##" n:term:max : term => `(Term.var (Fin.mk $n (by decide)))

namespace Term

/-- Identity function: `ƛx. x`. -/
def id : Term 0 := ƛ v#0

/-- Constant function: `ƛx. ƛy. x`. -/
def const : Term 0 := ƛ (ƛ v##1)

/-- Church numeral zero: `ƛf. ƛx. x`. -/
def zero : Term 0 := ƛ (ƛ (v#0))

/-- Church numeral one: `ƛf. ƛx. f x`. -/
def one : Term 0 := ƛ (ƛ (v##1 ⬝ v#0))

/-- Church numeral two: `ƛf. ƛx. f (f x)`. -/
def two : Term 0 := ƛ (ƛ (v##1 ⬝ (v##1 ⬝ v#0)))

/-- Church successor: `ƛn. ƛf. ƛx. f (n f x)`. -/
def succ : Term 0 :=
  ƛ (             -- n is var 2
    ƛ (           -- f is var 1
      ƛ (         -- x is var 0
        v##1 ⬝
        ((v##2 ⬝ v##1) ⬝ v#0)
      )
    )
  )

/-- A term with two free variables: `x₀ x₁`. -/
def freeTerm : Term 2 := v##0 ⬝ v##1

/-- A term with one free variable: `λy. (y x₀)`. -/
def boundAndFree : Term 1 := ƛ (v#0 ⬝ v##1)

end Term

/-! ### Renamings -/

/-- A weakening renaming (`n < m`): inserts new unused variables into scope. -/
structure RenameWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Fin m

/-- Extend a weakening renaming under a `λ`. -/
def RenameWeaken.ext {n m : Nat} (w : RenameWeaken n m) : RenameWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ w.lt
  map := Fin.cases 0 (fun i => (w.map i).succ)

/-- Apply a weakening renaming. -/
def renameWeaken {n m : Nat} (w : RenameWeaken n m) : Term n → Term m
  | Term.var i => Term.var (w.map i)
  | ƛ M        => ƛ (renameWeaken w.ext M)
  | M ⬝ N      => (renameWeaken w M) ⬝ (renameWeaken w N)

/-- The weakening that shifts every variable up by one. -/
def RenameWeaken.succ (m : Nat) : RenameWeaken m (m + 1) where
  lt  := Nat.lt_succ_self m
  map := Fin.succ

/-! ### Substitutions -/

/-- A weakening substitution (`n < m`). -/
structure SubstWeaken (n m : Nat) where
  lt  : n < m
  map : Fin n → Term m

/-- Extend a weakening substitution under a `λ`. -/
def SubstWeaken.ext {n m : Nat} (σ : SubstWeaken n m) : SubstWeaken (n + 1) (m + 1) where
  lt  := Nat.succ_lt_succ σ.lt
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

/-- Apply a weakening substitution. -/
def substWeaken {n m : Nat} (σ : SubstWeaken n m) : Term n → Term m
  | v#i   => σ.map i
  | ƛ M   => ƛ (substWeaken σ.ext M)
  | M ⬝ N => (substWeaken σ M) ⬝ (substWeaken σ N)

/-- A same-scope substitution. -/
structure SubstSame (n : Nat) where
  map : Fin n → Term n

/-- Extend a same-scope substitution under a `λ`. -/
def SubstSame.ext {n : Nat} (σ : SubstSame n) : SubstSame (n + 1) where
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ n) (σ.map i))

/-- Apply a same-scope substitution. -/
def substSame {n : Nat} (σ : SubstSame n) : Term n → Term n
  | v#i   => σ.map i
  | ƛ M   => ƛ (substSame σ.ext M)
  | M ⬝ N => (substSame σ M) ⬝ (substSame σ N)

/-- A contracting substitution (`n > m`). -/
structure SubstContract (n m : Nat) where
  gt  : n > m
  map : Fin n → Term m

/-- Extend a contracting substitution under a `λ`. -/
def SubstContract.ext {n m : Nat} (σ : SubstContract n m) : SubstContract (n + 1) (m + 1) where
  gt  := Nat.succ_lt_succ σ.gt
  map := Fin.cases (v#0) (fun i => renameWeaken (RenameWeaken.succ m) (σ.map i))

/-- Apply a contracting substitution. -/
def substContract {n m : Nat} (σ : SubstContract n m) : Term n → Term m
  | v#i   => σ.map i
  | ƛ M   => ƛ (substContract σ.ext M)
  | M ⬝ N => (substContract σ M) ⬝ (substContract σ N)

namespace Term

/-- Substitution of the top variable. -/
def mkSubstZero {n : Nat} (N : Term n) : SubstContract (n + 1) n where
  gt  := Nat.lt_succ_self n
  map := Fin.cases N (fun i => v#i)

/-- Single substitution `M[N]`. -/
def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  substContract (mkSubstZero N) M

end Term

@[inherit_doc] notation:70 M " [" N "]" => Term.betaSubst M N

/-- The shift of a term into a larger scope: insert a fresh variable at 0. -/
abbrev shift {n : Nat} (M : Term n) : Term (n + 1) := renameWeaken (RenameWeaken.succ n) M

/-! ### The substitution calculus -/

theorem renameWeaken_comm {n m m' k : Nat} (w1 : RenameWeaken n m) (w2 : RenameWeaken m k)
    (w3 : RenameWeaken n m') (w4 : RenameWeaken m' k)
    (h_map : ∀ i, w2.map (w1.map i) = w4.map (w3.map i)) (t : Term n) :
    renameWeaken w2 (renameWeaken w1 t) = renameWeaken w4 (renameWeaken w3 t) := by
  induction t generalizing m m' k with
  | var i =>
    dsimp [renameWeaken]
    rw [h_map i]
  | abs M ih =>
    dsimp [renameWeaken]
    congr 1
    apply ih (w1 := w1.ext) (w2 := w2.ext) (w3 := w3.ext) (w4 := w4.ext)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      dsimp [RenameWeaken.ext]
      have := h_map j
      rw [this]
  | app M N ihM ihN =>
    dsimp [renameWeaken]
    rw [ihM w1 w2 w3 w4 h_map, ihN w1 w2 w3 w4 h_map]

theorem rename_succ_ext_comm {n m : Nat} (w : RenameWeaken n m) (t : Term n) :
    renameWeaken w.ext (renameWeaken (RenameWeaken.succ n) t) =
    renameWeaken (RenameWeaken.succ m) (renameWeaken w t) :=
  renameWeaken_comm (RenameWeaken.succ n) w.ext w (RenameWeaken.succ m) (fun _ => rfl) t

theorem substContract_renameWeaken_comm {n m k l : Nat} (w : RenameWeaken n m)
    (w' : RenameWeaken k l) (σ : SubstContract m l) (σ' : SubstContract n k)
    (h_comm : ∀ i, σ.map (w.map i) = renameWeaken w' (σ'.map i)) (t : Term n) :
    substContract σ (renameWeaken w t) = renameWeaken w' (substContract σ' t) := by
  induction t generalizing m k l with
  | var i =>
    dsimp [renameWeaken, substContract]
    exact h_comm i
  | abs M ih =>
    dsimp [renameWeaken, substContract]
    congr 1
    apply ih (w := w.ext) (w' := w'.ext) (σ := σ.ext) (σ' := σ'.ext)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      dsimp [SubstContract.ext, RenameWeaken.ext]
      rw [h_comm j]
      exact (rename_succ_ext_comm w' (σ'.map j)).symm
  | app M K ihM ihK =>
    dsimp [renameWeaken, substContract]
    rw [ihM w w' σ σ' h_comm, ihK w w' σ σ' h_comm]

theorem subst_rename_id {n m : Nat} (σ : SubstContract n m) (w : RenameWeaken m n) (M : Term m)
    (h_eq : ∀ i, σ.map (w.map i) = v#i) :
    substContract σ (renameWeaken w M) = M := by
  induction M generalizing n with
  | var i =>
    dsimp [renameWeaken, substContract]
    exact h_eq i
  | abs M ih =>
    dsimp [renameWeaken, substContract]
    congr 1
    apply ih σ.ext w.ext
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      dsimp [SubstContract.ext, RenameWeaken.ext]
      rw [h_eq j]
      rfl
  | app M K ihM ihK =>
    dsimp [renameWeaken, substContract]
    rw [ihM σ w h_eq, ihK σ w h_eq]

theorem rename_succ_subst_cancel {m : Nat} (t : Term m) (N : Term m) :
    (renameWeaken (RenameWeaken.succ m) t)[N] = t :=
  subst_rename_id (Term.mkSubstZero N) (RenameWeaken.succ m) t (fun _ => rfl)

theorem rename_betaSubst {n m : Nat} (w : RenameWeaken n m) (M : Term (n + 1)) (N : Term n) :
    renameWeaken w (M[N]) = (renameWeaken w.ext M)[renameWeaken w N] := by
  have h_comm : ∀ i, (Term.mkSubstZero (renameWeaken w N)).map (w.ext.map i)
      = renameWeaken w ((Term.mkSubstZero N).map i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  exact (substContract_renameWeaken_comm w.ext w (Term.mkSubstZero (renameWeaken w N))
    (Term.mkSubstZero N) h_comm M).symm

theorem substContract_comp {n m k : Nat} (σ1 : SubstContract m k) (σ2 : SubstContract n m)
    (σ3 : SubstContract n k) (h_eq : ∀ i, substContract σ1 (σ2.map i) = σ3.map i) (t : Term n) :
    substContract σ1 (substContract σ2 t) = substContract σ3 t := by
  induction t generalizing m k with
  | var i => exact h_eq i
  | abs M ih =>
    dsimp [substContract]
    congr 1
    apply ih σ1.ext σ2.ext σ3.ext
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      have h1 := h_eq j
      have h2 := substContract_renameWeaken_comm (RenameWeaken.succ m) (RenameWeaken.succ k)
        σ1.ext σ1 (fun _ => rfl) (σ2.map j)
      change substContract σ1.ext (renameWeaken (RenameWeaken.succ m) (σ2.map j))
        = renameWeaken (RenameWeaken.succ k) (σ3.map j)
      rw [h2, h1]
  | app M K ihM ihK =>
    dsimp [substContract]
    rw [ihM σ1 σ2 σ3 h_eq, ihK σ1 σ2 σ3 h_eq]

/-- The substitution `Fin.cases (σ N) σ`, used to state the substitution lemma. -/
def substTargetComp {n m : Nat} (σ : SubstContract n m) (N : Term n) : SubstContract (n + 1) m where
  gt  := Nat.lt_trans σ.gt (Nat.lt_succ_self n)
  map := Fin.cases (substContract σ N) (fun i => σ.map i)

/-- The substitution lemma. -/
theorem subst_comm_lemma {n m : Nat} (σ : SubstContract n m) (M : Term (n + 1)) (N : Term n) :
    (substContract σ.ext M)[substContract σ N] = substContract σ (M[N]) := by
  have hL : substContract (Term.mkSubstZero (substContract σ N)) (substContract σ.ext M)
      = substContract (substTargetComp σ N) M := by
    apply substContract_comp (Term.mkSubstZero (substContract σ N)) σ.ext (substTargetComp σ N)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      dsimp [SubstContract.ext, substTargetComp]
      exact rename_succ_subst_cancel (σ.map j) (substContract σ N)
  have hR : substContract σ (substContract (Term.mkSubstZero N) M)
      = substContract (substTargetComp σ N) M := by
    apply substContract_comp σ (Term.mkSubstZero N) (substTargetComp σ N)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  exact hL.trans hR.symm

end IwilareFinsetNOfFreeIsExact
