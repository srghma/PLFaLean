module

-- https://plfa.github.io/Substitution/#plfa_plfa-part2-Substitution-2341

public import Plfl.Untyped
import Batteries.Tactic.Init
import Batteries.Logic
import Mathlib.Tactic

@[expose] public section

namespace Substitution

open Untyped Notation

abbrev Rename (n m : Nat) := Fin n → Fin m
abbrev Subst (n m : Nat) := Fin n → Term m

-- https://plfa.github.io/Substitution/#the-%CF%83-algebra-of-substitution
abbrev ids : Subst n n := Term.var
abbrev shift : Subst n (n + 1) := Term.var ∘ Fin.succ

abbrev cons (m : Term k) (σ : Subst n k) : Subst (n + 1) k :=
  Fin.cases m σ

abbrev seq (σ : Subst n m) (τ : Subst m k) : Subst n k := ⟪τ⟫ ∘ σ

namespace Notation
  scoped infixr:60 " ⦂⦂ " => cons
  scoped infixr:50 " ⨟ " => seq
end Notation

open Notation
open Subst

-- https://plfa.github.io/Substitution/#relating-the-σ-algebra-and-substitution-functions
def ren (ρ : Rename n m) : Subst n m := ids ∘ ρ

section
  variable {m : Term k} {σ : Subst n k} {τ : Subst k p}

  -- https://plfa.github.io/Substitution/#proofs-of-sub-head-sub-tail-sub-η-z-shift-sub-idl-sub-dist-and-sub-app
  @[simp] theorem sub_head : ⟪m ⦂⦂ σ⟫ (‵ 0) = m := rfl
  @[simp] theorem sub_tail : (shift ⨟ m ⦂⦂ σ) = σ := rfl
  @[simp] theorem sub_η {σ : Subst (n + 1) k} : (⟪σ⟫ (‵ 0) ⦂⦂ (shift ⨟ σ)) = σ := by funext i; cases i using Fin.cases <;> rfl
  @[simp] theorem z_shift : ((‵ 0) ⦂⦂ shift) = @ids (n + 1) := by funext i; cases i using Fin.cases <;> rfl
  @[simp] theorem ids_seq : (ids ⨟ σ) = σ := rfl
  @[simp] theorem sub_ap {l m : Term n} : ⟪σ⟫ (l ⬝ m) = (⟪σ⟫ l) ⬝ (⟪σ⟫ m) := rfl
  @[simp] theorem sub_dist : ((m ⦂⦂ σ) ⨟ τ) = ((⟪τ⟫ m) ⦂⦂ (σ ⨟ τ)) := by funext i; cases i using Fin.cases <;> rfl
end

section
  variable {m : Term n} {σ : Subst n k} {ρ : Rename n k}

  -- https://plfa.github.io/Substitution/#relating-rename-exts-ext-and-subst-zero-to-the-%CF%83-algebra
  @[simp] theorem ren_ext : ren (ext ρ) = exts (ren ρ) := by funext i; cases i using Fin.cases <;> rfl
  @[simp] theorem ren_shift : ren (n := n) Fin.succ = shift := rfl

  theorem rename_subst_ren {m : Term n} {ρ : Rename n k} : rename ρ m = ⟪ren ρ⟫ m := by
    induction m generalizing k with
    | var => rfl
    | abs t ih =>
      apply congr_arg Term.abs
      rw [ih]
      congr 1
      funext i
      exact congr_fun ren_ext i
    | app l m ihl ihm =>
      simp only [sub_ap]
      exact congr_arg₂ Term.app ihl ihm

  theorem rename_shift : rename Fin.succ m = ⟪shift⟫ m := by
    simp only [rename_subst_ren]; congr

  theorem exts_cons_shift : exts σ = (‵ 0 ⦂⦂ (σ ⨟ shift)) := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ x => simp [exts, seq, rename_shift]

  theorem ext_cons_z_shift : ren (ext ρ) = (‵ 0 ⦂⦂ (ren ρ ⨟ shift)) := by
    rw [ren_ext, exts_cons_shift]

  theorem subst_z_cons_ids {m : Term n} : subst₁σ m = (m ⦂⦂ ids) := by
    funext i; cases i using Fin.cases <;> rfl

  -- https://plfa.github.io/Substitution/#proofs-of-sub-abs-sub-id-and-rename-id
  theorem sub_lam {σ : Subst n k} {t : Term (n + 1)} : ⟪σ⟫ (ƛ t) = (ƛ ⟪(‵ 0) ⦂⦂ (σ ⨟ shift)⟫ t) := by
    change (ƛ ⟪exts σ⟫ t) = _; congr 1; rw [exts_cons_shift]

  @[simp] theorem exts_ids : exts (ids (n := n)) = ids := by ext i; cases i using Fin.cases <;> rfl

  theorem sub_ids {m : Term n} : ⟪ids (n := n)⟫ m = m := by
    induction m with
    | var => rfl
    | abs t ih =>
      apply congr_arg Term.abs
      convert ih
      simp_all only [exts_ids]
    | app l m ihl ihm => simp only [sub_ap]; apply congr_arg₂ Term.app <;> assumption

  theorem rename_id {m : Term n} : rename id m = m := by
    rw [rename_subst_ren]; exact sub_ids

  -- https://plfa.github.io/Substitution/#proof-of-sub-idr
  theorem seq_ids : (σ ⨟ ids) = σ := by
    ext; simp only [Function.comp_apply, sub_ids]
end

section
  variable {m : Term n} {ρ : Rename k p} {ρ' : Rename n k}

  -- https://plfa.github.io/Substitution/#proof-of-sub-sub
  @[simp] theorem comp_ext : (ext ρ) ∘ (ext ρ') = ext (ρ ∘ ρ') := by
    funext i; cases i using Fin.cases <;> rfl

  theorem comp_rename {m : Term n} {ρ : Rename k p} {ρ' : Rename n k}
  : rename ρ (rename ρ' m) = rename (ρ ∘ ρ') m := by
    induction m generalizing k p with
    | var => rfl
    | abs t ih => apply congr_arg Term.abs; convert ih; exact comp_ext.symm
    | app l m ihl ihm => apply congr_arg₂ Term.app <;> solve | exact ihl | exact ihm

  theorem comm_subst_rename {n k} {σ : Subst n k} {ρ : Rename n (n + 1)} {ρ' : Rename k (k + 1)}
  (r : ∀ {x : Fin n}, exts σ (ρ x) = rename ρ' (σ x)) {m : Term n}
  : ⟪exts σ⟫ (rename ρ m) = rename ρ' (⟪σ⟫ m)
  := by
    induction m generalizing k with
    | var => exact r
    | app l m ihl ihm => apply congr_arg₂ Term.app <;> solve | exact ihl r | exact ihm r
    | abs t ih =>
      apply congr_arg Term.abs
      have r' : ∀ {x : Fin _}, exts (exts σ) (ext ρ x) = rename (ext ρ') (exts σ x) := by
        intro x; cases x using Fin.cases with
        | zero => rfl
        | succ x =>
          have h1 := @r x
          change rename Fin.succ (exts σ (ρ x)) = rename (ext ρ') (exts σ (Fin.succ x))
          rw [h1]
          change rename Fin.succ (rename ρ' (σ x)) = rename (ext ρ') (rename Fin.succ (σ x))
          rw [comp_rename, comp_rename]
          have h2 : Fin.succ ∘ ρ' = ext ρ' ∘ Fin.succ := by funext y; rfl
          rw [h2]
      exact ih r'
end

section
  variable {ρ : Rename n k} {σ : Subst n k} {τ : Subst k p} {θ : Subst p q}

  theorem exts_seq_exts : (exts σ ⨟ exts τ) = exts (σ ⨟ τ) := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change ⟪exts τ⟫ (rename Fin.succ (σ i)) = rename Fin.succ (⟪τ⟫ (σ i))
      exact comm_subst_rename (m := σ i) (ρ := Fin.succ) (ρ' := Fin.succ) (r := rfl)

  theorem sub_sub {m : Term n} {σ : Subst n k} {τ : Subst k p}
  : ⟪τ⟫ (⟪σ⟫ m) = ⟪σ ⨟ τ⟫ m
  := by induction m generalizing k p with
  | var => rfl
  | app l m ihl ihm => apply congr_arg₂ Term.app <;> solve | exact ihl | exact ihm
  | abs t ih => calc ⟪τ⟫ (⟪σ⟫ (ƛ t))
    _ = (ƛ ⟪exts τ⟫ (⟪exts σ⟫ t)) := rfl
    _ = (ƛ (⟪exts σ ⨟ exts τ⟫ t)) := by apply congr_arg Term.abs; exact ih
    _ = (ƛ (⟪exts (σ ⨟ τ)⟫ t)) := by apply congr_arg Term.abs; congr 1; rw [exts_seq_exts]

  theorem rename_subst {m : Term n} : ⟪τ⟫ (rename ρ m) = ⟪τ ∘ ρ⟫ m := by
    simp only [rename_subst_ren, sub_sub]; congr

  -- https://plfa.github.io/Substitution/#proof-of-sub-assoc
  theorem sub_assoc : ((σ ⨟ τ) ⨟ θ) = (σ ⨟ (τ ⨟ θ)) := by
    funext i; simp only [Function.comp_apply, sub_sub]

  -- https://plfa.github.io/Substitution/#proof-of-subst-zero-exts-cons
  theorem subst₁σ_exts_cons {m : Term k} : (exts σ ⨟ subst₁σ m) = (m ⦂⦂ σ) := by
    funext i; cases i using Fin.cases with
    | zero => rfl
    | succ x =>
      change ⟪subst₁σ m⟫ (rename Fin.succ (σ x)) = σ x
      rw [rename_subst]
      have : (subst₁σ m ∘ Fin.succ) = ids := by funext y; rfl
      rw [this, sub_ids]

  variable {t : Term (n + 1)} {m : Term n}

  -- https://plfa.github.io/Substitution/#proof-of-the-substitution-lemma
  theorem subst_comm : (⟪exts σ⟫ t)⟦⟪σ⟫ m⟧ = ⟪σ⟫ (t⟦m⟧) := calc _
      _ = ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts σ⟫ t) := rfl
      _ = ⟪⟪σ⟫ m ⦂⦂ ids⟫ (⟪exts σ⟫ t) := by rw [subst_z_cons_ids]
      _ = ⟪(exts σ) ⨟ ((⟪σ⟫ m) ⦂⦂ ids)⟫ t := sub_sub
      _ = ⟪(‵ 0 ⦂⦂ (σ ⨟ shift)) ⨟ (⟪σ⟫ m ⦂⦂ ids)⟫ t := by rw [exts_cons_shift]
      _ = ⟪⟪⟪σ⟫ m ⦂⦂ ids⟫ (‵ 0) ⦂⦂ ((σ ⨟ shift) ⨟ (⟪σ⟫ m ⦂⦂ ids))⟫ t := by rw [sub_dist]
      _ = ⟪⟪σ⟫ m ⦂⦂ ((σ ⨟ shift) ⨟ (⟪σ⟫ m ⦂⦂ ids))⟫ t := rfl
      _ = ⟪⟪σ⟫ m ⦂⦂ (σ ⨟ shift ⨟ ⟪σ⟫ m ⦂⦂ ids)⟫ t := by rw [sub_assoc]
      _ = ⟪⟪σ⟫ m ⦂⦂ (σ ⨟ ids)⟫ t := by rw [sub_tail]
      _ = ⟪⟪σ⟫ m ⦂⦂ (ids ⨟ σ)⟫ t := by rw [seq_ids, ids_seq]
      _ = ⟪m ⦂⦂ ids ⨟ σ⟫ t := by rw [sub_dist]
      _ = ⟪σ⟫ (⟪m ⦂⦂ ids⟫ t) := sub_sub.symm
      _ = ⟪σ⟫ (t⟦m⟧) := by rw [←subst_z_cons_ids]

  theorem rename_subst_comm : (rename (ext ρ) t)⟦rename ρ m⟧ = rename ρ (t⟦m⟧) := calc _
      _ = (⟪ren (ext ρ)⟫ t)⟦⟪ren ρ⟫ m⟧ := by rw [rename_subst_ren, rename_subst_ren]
      _ = (⟪exts (ren ρ)⟫ t)⟦⟪ren ρ⟫ m⟧ := by rw [ren_ext]
      _ = ⟪ren ρ⟫ (t⟦m⟧) := subst_comm
      _ = rename ρ (t⟦m⟧) := rename_subst_ren.symm
end

/--
Substitute a term `m` for `1` within term `n`.
-/
abbrev subst₁_under₁ (m : Term k) (t : Term (k + 2)) : Term (k + 1) := ⟪exts (subst₁σ m)⟫ t

namespace Notation
  scoped notation:90 n "⟦" m "⟧₁" => subst₁_under₁ m n
end Notation

theorem substitution {t : Term (n + 2)} {n' : Term (n + 1)} {l : Term n} : t⟦n'⟧⟦l⟧ = t⟦l⟧₁⟦n'⟦l⟧⟧
:= subst_comm.symm
