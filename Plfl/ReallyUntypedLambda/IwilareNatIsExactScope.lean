-- https://github.com/iwilare/church-rosser/blob/main/DeBruijn.agda
module

public import Aesop
public import Mathlib.Logic.Relation

@[expose] public section

namespace IwilareNatIsExactScope

-- 1. Intrinsically exact-scoped Lambda terms parameterized by exact scope size `n : Nat`
--    n = 0 <==> 100% statically CLOSED term (uses 0 free variables)
--    n > 0 <==> 100% statically OPEN term (uses free variables with maximum index n - 1)
inductive Term : Nat → Type
  | var : (i : Nat) → Term (i + 1)
  | abs : ∀ {n : Nat}, Term n → Term (n - 1)
  | app : ∀ {n m : Nat}, Term n → Term m → Term (max n m)

prefix:71 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:72 "v#" => Term.var
macro:72 "v##" n:term:max : term => `(Term.var $n)

namespace Term

-- 1. Identity Function: ƛx. x
-- Statically 100% CLOSED: Term 0
def id : Term 0 := ƛ v#0

-- 2. Constant Function: ƛx. ƛy. x
-- Statically 100% CLOSED: Term 0
def const : Term 0 := ƛ (ƛ v##1)

-- 3. Church Numerals: ƛf. ƛx. f^n x
-- Zero: ƛf. ƛx. x (Term 0)
def zero : Term 0 := ƛ (ƛ (v#0))

-- One: ƛf. ƛx. f x (Term 0)
def one : Term 0 := ƛ (ƛ (v##1 ⬝ v#0))

-- Two: ƛf. ƛx. f (f x) (Term 0)
def two : Term 0 := ƛ (ƛ (v##1 ⬝ (v##1 ⬝ v#0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x) (Term 0)
def succ : Term 0 :=
  ƛ (
    ƛ (
      ƛ (
        v##1 ⬝
        ((v##2 ⬝ v##1) ⬝ v#0)
      )
    )
  )

-- A term with 2 free variables: (x0 x1) -> Statically OPEN (Term 2)
def freeTerm : Term 2 := v##0 ⬝ v##1

-- A term with 1 free variable (x0): λy. (y x0) -> Statically OPEN (Term 1)
def boundAndFree : Term 1 := ƛ (v#0 ⬝ v##1)

end Term

namespace Term

def betaSubst {n : Nat} (M : Term (n + 1)) (N : Term n) : Term n :=
  TODO

end Term

-- Notation for substitution
notation:70 M " [" N "]" => Term.betaSubst M N

-- https://github.com/iwilare/church-rosser/blob/main/Beta.agda

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "—→" => Beta -- the std → and -> have binding power 25

-- 2. Standard Single-Step Beta Reduction (Beta)
inductive Beta : ∀ {n : Nat}, Term n → Term n → Prop
  | appl {n : Nat} {M N : Term n} (L : Term n) :
      M —→ N
      --------------------
      → L ⬝ M —→ L ⬝ N
  | appr {n : Nat} {M N : Term n} (L : Term n) :
      M —→ N
      --------------------
      → M ⬝ L —→ N ⬝ L
  | abs {n : Nat} {M N : Term (n + 1)} :
      M —→ N
      --------------------
      → ƛ M —→ ƛ N
  | basis {n : Nat} (M : Term (n + 1)) (N : Term n) :
      --------------------
      ƛ M ⬝ N —→ M[N]

#print Beta.appr
#print Beta.appl
#print Beta.abs
#print Beta.basis

infixl:65 "—→-ξₗ" => Beta.appr
infixl:65 "—→-ξᵣ" => Beta.appl
prefix:65 "—→-ƛ " => Beta.abs
infixl:65 "—→-β"  => Beta.basis

theorem step_test {n : Nat} {t1 t2 : Term n} (h : t1 —→ t2) : True :=
  match h with
  | L —→-ξₗ h' => True.intro
  | L —→-ξᵣ h' => True.intro
  | —→-ƛ h'   => True.intro
  | M —→-β N  => True.intro

abbrev BetaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Beta
infix:64 " —→* " => BetaStar -- in original repo —↠

-- 3. Parallel Beta Reduction (BetaPar)
set_option hygiene false in
set_option quotPrecheck false in
infixl:65 "⇉" => BetaPar -- the std → and -> have binding power 25

inductive BetaPar : ∀ {n : Nat}, Term n → Term n → Prop
  | var {n : Nat} (x : Fin n)
      ---------
      : v#x ⇉ v#x
  | abs {n : Nat} {M N : Term (n + 1)}
      : M ⇉ N
      ---------
      → ƛ M ⇉ ƛ N
  | app {n : Nat} {M M' N N' : Term n}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → M ⬝ N ⇉ M' ⬝ N'
  | subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
      : M ⇉ M'
      → N ⇉ N'
      ---------
      → ƛ M ⬝ N ⇉ M'[N']

infixl:65 "⇉-c" => BetaPar.var
prefix:65 "⇉-ƛ " => BetaPar.abs
infixl:65 "⇉-ξ" => BetaPar.app
infixl:65 "⇉-β"  => BetaPar.subst

-- 4. Reflexivity of Parallel Reduction
-- Typeclass instance for Reflexivity of BetaP
instance : Std.Refl (BetaPar (n := n)) where
  refl N := by
    induction N with
    | var i => exact BetaPar.var i
    | abs M ih => exact BetaPar.abs ih
    | app M N ihM ihN => exact BetaPar.app ihM ihN

abbrev BetaParStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaPar
infix:64 " ⇉* " => BetaParStar

-- 1. Single-step implies parallel reduction:
theorem beta_to_betapar {n : Nat} {M N : Term n} (h : M —→ N) : M ⇉ N := by
  induction h with
  | appl L _ ih =>
    -- L ⬝ M —→ L ⬝ N
    exact BetaPar.app (refl L) ih
  | appr L _ ih =>
    -- M ⬝ L —→ N ⬝ L
    exact BetaPar.app ih (refl L)
  | abs _ ih =>
    -- ƛ M —→ ƛ N
    exact BetaPar.abs ih
  | basis M N =>
    -- ƛ M ⬝ N —→ M[N]
    exact BetaPar.subst (refl M) (refl N)

-- ====================================================================
-- Helper Congruence Lemmas for Multi-Step Reduction (BetaStar / —→*)
-- ====================================================================

theorem beta_star_abs {n : Nat} {M N : Term (n + 1)} (h : M —→* N) : ƛ M —→* ƛ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.abs step)

theorem beta_star_appr {n : Nat} {M M' : Term n} (N : Term n) (h : M —→* M') : M ⬝ N —→* M' ⬝ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appr N step)

theorem beta_star_appl {n : Nat} {N N' : Term n} (M : Term n) (h : N —→* N') : M ⬝ N —→* M ⬝ N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appl M step)

-- ====================================================================
-- Main Equivalence Theorems
-- ====================================================================

-- 2. Parallel reduction implies multi-step reduction:
theorem betapar_to_betastar {n : Nat} {M N : Term n} (h : M ⇉ N) : M —→* N := by
  induction h with
  | var i =>
    exact Relation.ReflTransGen.refl
  | abs _ ih =>
    exact beta_star_abs ih
  | app _ _ ihM ihN =>
    exact Relation.ReflTransGen.trans (beta_star_appr _ ihM) (beta_star_appl _ ihN)
  | subst _ _ ihM ihN =>
    have h1 : (ƛ _) ⬝ _ —→* (ƛ _) ⬝ _ :=
      Relation.ReflTransGen.trans (beta_star_appr _ (beta_star_abs ihM)) (beta_star_appl _ ihN)
    exact Relation.ReflTransGen.tail h1 (Beta.basis _ _)

-- 3. Their reflexive-transitive closures are identical!
theorem betapar_star_eq_betastar {n : Nat} {M N : Term n} :
  M ⇉* N ↔ M —→* N := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.trans ih (betapar_to_betastar step)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.tail ih (beta_to_betapar step)

-- --------------------------------------------------------------------
-- 3. Beta Equivalence / Conversion (BetaEq / ≡β)
-- --------------------------------------------------------------------
abbrev BetaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen (Beta (n := n))

infix:64 " ≡β " => BetaEq

-- --------------------------------------------------------------------
-- 4. Joinability / Confluence (BetaJoin)
-- --------------------------------------------------------------------
abbrev BetaJoin {n : Nat} : Term n → Term n → Prop := Relation.Join (BetaStar (n := n))

-- Abbreviation for at-most-1-step beta reduction (ReflGen Beta)
abbrev BetaRefl {n : Nat} : Term n → Term n → Prop := Relation.ReflGen (Beta (n := n))

-- Infix notation for 0 or 1 step reduction
infix:65 " —→≤1 " => BetaRefl

-- Takahashi's Complete Development Function (M*)
-- Performs maximal parallel reduction in 1 step
def takahashi {n : Nat} : Term n → Term n
  | v#i          => v#i
  | (ƛ M) ⬝ N    => (takahashi M)[takahashi N]  -- Fire redex!
  | ƛ M          => ƛ (takahashi M)
  | M ⬝ N        => (takahashi M) ⬝ (takahashi N)

-- ====================================================================
-- Substitution Lemma for Parallel Reduction
-- ====================================================================

theorem betapar_abs_inv {n : Nat} {M N : Term (n + 1)} (h : ƛ M ⇉ ƛ N) : M ⇉ N := by
  cases h with
  | abs h0 => exact h0

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

theorem substContract_renameWeaken_comm {n m k l : Nat} (w : RenameWeaken n m) (w' : RenameWeaken k l)
    (σ : SubstContract m l) (σ' : SubstContract n k)
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
  have h_comm : ∀ i, (Term.mkSubstZero (renameWeaken w N)).map (w.ext.map i) = renameWeaken w ((Term.mkSubstZero N).map i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  exact (substContract_renameWeaken_comm w.ext w (Term.mkSubstZero (renameWeaken w N)) (Term.mkSubstZero N) h_comm M).symm

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
      have h2 := substContract_renameWeaken_comm (RenameWeaken.succ m) (RenameWeaken.succ k) σ1.ext σ1 (fun _ => rfl) (σ2.map j)
      change substContract σ1.ext (renameWeaken (RenameWeaken.succ m) (σ2.map j)) = renameWeaken (RenameWeaken.succ k) (σ3.map j)
      rw [h2, h1]
  | app M K ihM ihK =>
    dsimp [substContract]
    rw [ihM σ1 σ2 σ3 h_eq, ihK σ1 σ2 σ3 h_eq]

def substTargetComp {n m : Nat} (σ : SubstContract n m) (N : Term n) : SubstContract (n + 1) m where
  gt  := Nat.lt_trans σ.gt (Nat.lt_succ_self n)
  map := Fin.cases (substContract σ N) (fun i => σ.map i)

theorem subst_comm_lemma {n m : Nat} (σ : SubstContract n m) (M : Term (n + 1)) (N : Term n) :
    (substContract σ.ext M)[substContract σ N] = substContract σ (M[N]) := by
  have hL : substContract (Term.mkSubstZero (substContract σ N)) (substContract σ.ext M) = substContract (substTargetComp σ N) M := by
    apply substContract_comp (Term.mkSubstZero (substContract σ N)) σ.ext (substTargetComp σ N)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      dsimp [SubstContract.ext, substTargetComp]
      exact rename_succ_subst_cancel (σ.map j) (substContract σ N)
  have hR : substContract σ (substContract (Term.mkSubstZero N) M) = substContract (substTargetComp σ N) M := by
    apply substContract_comp σ (Term.mkSubstZero N) (substTargetComp σ N)
    intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  exact hL.trans hR.symm

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

-- Parallel reduction is preserved under substitution
theorem betapar_subst {n : Nat} {M M' : Term (n + 1)} {N N' : Term n}
    (hM : M ⇉ M') (hN : N ⇉ N') : M[N] ⇉ M'[N'] := by
  have hσ : ∀ i : Fin (n + 1), (Term.mkSubstZero N).map i ⇉ (Term.mkSubstZero N').map i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hN
    · intro i'
      exact BetaPar.var i'
  exact betapar_subst_lemma (Term.mkSubstZero N) (Term.mkSubstZero N') hσ hM

-- ====================================================================
-- Takahashi's Triangle Lemma (Main Proof)
-- ====================================================================

theorem takahashi_triangle {n : Nat} {M N : Term n} (h : M ⇉ N) : N ⇉ takahashi M := by
  induction h with
  | var i => exact BetaPar.var i
  | abs _ ih => exact BetaPar.abs ih
  | app hM hN ihM ihN =>
    cases hM with
    | var i => exact BetaPar.app ihM ihN
    | abs h0 =>
      have ihM_inv : _ ⇉ takahashi _ := betapar_abs_inv ihM
      exact BetaPar.subst ihM_inv ihN
    | app h1 h2 => exact BetaPar.app ihM ihN
    | subst h1 h2 => exact BetaPar.app ihM ihN
  | subst hM hN ihM ihN =>
    exact betapar_subst ihM ihN

-- ====================================================================
-- Confluence Theorems
-- ====================================================================

-- Diamond Property for Parallel Reduction
theorem betapar_diamond {n : Nat} {M N1 N2 : Term n} (h1 : M ⇉ N1) (h2 : M ⇉ N2) :
    ∃ D, N1 ⇉ D ∧ N2 ⇉ D :=
  ⟨takahashi M, takahashi_triangle h1, takahashi_triangle h2⟩

theorem betapar_strip {n : Nat} {M N1 N2 : Term n} (h1 : M ⇉ N1) (h2 : M ⇉* N2) :
    ∃ D, N1 ⇉* D ∧ N2 ⇉ D := by
  induction h2 with
  | refl => exact ⟨N1, Relation.ReflTransGen.refl, h1⟩
  | tail h_head step ih =>
    rcases ih with ⟨D1, hN1_D1, hK_D1⟩
    rcases betapar_diamond step hK_D1 with ⟨D2, hN2_D2, hD1_D2⟩
    exact ⟨D2, Relation.ReflTransGen.tail hN1_D1 hD1_D2, hN2_D2⟩

-- Full Church-Rosser (Confluence) Theorem for BetaStar
theorem beta_confluence {n : Nat} {M N1 N2 : Term n}
    (h1 : M —→* N1) (h2 : M —→* N2) : BetaJoin N1 N2 := by
  have h1_par : M ⇉* N1 := betapar_star_eq_betastar.mpr h1
  have h2_par : M ⇉* N2 := betapar_star_eq_betastar.mpr h2
  clear h1 h2
  have h_join : ∃ D, N1 ⇉* D ∧ N2 ⇉* D := by
    induction h1_par generalizing N2 with
    | refl => exact ⟨N2, h2_par, Relation.ReflTransGen.refl⟩
    | tail h_head step ih =>
      rcases ih h2_par with ⟨D1, hM'_D1, hN2_D1⟩
      rcases betapar_strip step hM'_D1 with ⟨D2, hN1_D2, hD1_D2⟩
      exact ⟨D2, hN1_D2, Relation.ReflTransGen.tail hN2_D1 hD1_D2⟩
  rcases h_join with ⟨D, hN1_D, hN2_D⟩
  exact ⟨D, betapar_star_eq_betastar.mp hN1_D, betapar_star_eq_betastar.mp hN2_D⟩

/-- The Strip Lemma for Parallel Reduction:
    Matches Mathlib's Relation.church_rosser hypothesis structure. -/
theorem beta_strip {n : Nat} (a b c : Term n) (hab : a ⇉ b) (hac : a ⇉ c) :
    ∃ d, Relation.ReflGen BetaPar b d ∧ Relation.ReflTransGen BetaPar c d := by
  rcases betapar_diamond hab hac with ⟨d, hbd, hcd⟩
  exact ⟨d, Relation.ReflGen.single hbd, Relation.ReflTransGen.single hcd⟩

theorem betapar_church_rosser {n : Nat} {a b c : Term n}
    (hab : a ⇉* b) (hac : a ⇉* c) : Relation.Join (Relation.ReflTransGen BetaPar) b c :=
  Relation.church_rosser beta_strip hab hac

-- Church-Rosser for multi-step beta reduction on Terms
theorem beta_church_rosser {n : Nat} {a b c : Term n}
    (hab : a —→* b) (hac : a —→* c) : BetaJoin b c := by
  have hab_par : a ⇉* b := betapar_star_eq_betastar.mpr hab
  have hac_par : a ⇉* c := betapar_star_eq_betastar.mpr hac
  rcases betapar_church_rosser hab_par hac_par with ⟨d, hbd, hcd⟩
  exact ⟨d, betapar_star_eq_betastar.mp hbd, betapar_star_eq_betastar.mp hcd⟩
