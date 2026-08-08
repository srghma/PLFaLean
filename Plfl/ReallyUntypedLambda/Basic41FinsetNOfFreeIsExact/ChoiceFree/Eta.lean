module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Rename
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Confluence
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.Commutation

@[expose] public section

/-!
# η-reduction

η-reduction contracts `ƛ (M↑ ⬝ #0)` to `M`, where `M↑ = shift M`.  This file
develops η-reduction and its interaction with β-reduction, up to the
**confluence of βη** (`ChoiceFree.BetaEta`).
-/

namespace IwilareFinsetNOfFreeIsExact

set_option hygiene false in
set_option quotPrecheck false in
/-- Single-step η-reduction. -/
infixl:65 " —→η " => Eta

/-- Single-step η-reduction: `ƛ (M↑ ⬝ #0) —→η M`, plus the congruence rules. -/
inductive Eta : ∀ {n : Nat}, Term n → Term n → Prop
  | appl {n : Nat} {M N : Term n} (L : Term n) : M —→η N → L ⬝ M —→η L ⬝ N
  | appr {n : Nat} {M N : Term n} (L : Term n) : M —→η N → M ⬝ L —→η N ⬝ L
  | abs {n : Nat} {M N : Term (n + 1)} : M —→η N → ƛ M —→η ƛ N
  | basis {n : Nat} (M : Term n) : ƛ (shift M ⬝ v#0) —→η M

/-- Many-step η-reduction. -/
abbrev EtaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Eta

@[inherit_doc] infix:64 " —→η* " => EtaStar

/-! ### Inversion -/

theorem eta_var_inv {n : Nat} {i : Fin n} {K : Term n} (h : v#i —→η K) : False := by
  cases h

theorem eta_app_inv {n : Nat} {L M K : Term n} (h : L ⬝ M —→η K) :
    (∃ L', K = L' ⬝ M ∧ L —→η L') ∨ (∃ M', K = L ⬝ M' ∧ M —→η M') := by
  cases h with
  | appl _ h => exact Or.inr ⟨_, rfl, h⟩
  | appr _ h => exact Or.inl ⟨_, rfl, h⟩

theorem eta_abs_inv {n : Nat} {A : Term (n + 1)} {K : Term n} (h : ƛ A —→η K) :
    (∃ A', K = ƛ A' ∧ A —→η A') ∨ A = shift K ⬝ v#0 := by
  cases h with
  | abs h => exact Or.inl ⟨_, rfl, h⟩
  | basis => exact Or.inr rfl

theorem beta_var_inv {n : Nat} {i : Fin n} {K : Term n} (h : v#i —→ K) : False := by
  cases h

/-! ### Congruence rules for many-step η-reduction -/

theorem eta_star_abs {n : Nat} {M N : Term (n + 1)} (h : M —→η* N) : ƛ M —→η* ƛ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.abs step)

theorem eta_star_appr {n : Nat} {M M' : Term n} (N : Term n) (h : M —→η* M') :
    M ⬝ N —→η* M' ⬝ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.appr N step)

theorem eta_star_appl {n : Nat} {N N' : Term n} (M : Term n) (h : N —→η* N') :
    M ⬝ N —→η* M ⬝ N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Eta.appl M step)

theorem eta_star_app {n : Nat} {M M' N N' : Term n} (hM : M —→η* M') (hN : N —→η* N') :
    M ⬝ N —→η* M' ⬝ N' :=
  (eta_star_appr N hM).trans (eta_star_appl M' hN)

/-! ### Renaming and substitution -/

/-- Shifting commutes with substitution. -/
theorem substContract_shift {n m : Nat} (σ : SubstContract n m) (M : Term n) :
    substContract σ.ext (shift M) = shift (substContract σ M) :=
  substContract_renameWeaken_comm (RenameWeaken.succ n) (RenameWeaken.succ m) σ.ext σ
    (fun _ => rfl) M

/-- η-reduction is preserved by renaming. -/
theorem eta_rename {n m : Nat} (w : RenameWeaken n m) {M N : Term n} (h : M —→η N) :
    renameWeaken w M —→η renameWeaken w N := by
  induction h generalizing m with
  | appl L _ ih => exact Eta.appl _ (ih w)
  | appr L _ ih => exact Eta.appr _ (ih w)
  | abs _ ih => exact Eta.abs (ih w.ext)
  | basis P =>
    have h0 : renameWeaken w.ext (shift P) = shift (renameWeaken w P) :=
      rename_succ_ext_comm w P
    show renameWeaken w (ƛ (shift P ⬝ v#0)) —→η renameWeaken w P
    show ƛ (renameWeaken w.ext (shift P) ⬝ v#0) —→η renameWeaken w P
    rw [h0]
    exact Eta.basis _

/-- η-reduction is preserved by shifting. -/
theorem eta_shift {n : Nat} {M N : Term n} (h : M —→η N) : shift M —→η shift N :=
  eta_rename (RenameWeaken.succ n) h

theorem etaStar_shift {n : Nat} {M N : Term n} (h : M —→η* N) : shift M —→η* shift N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (eta_shift step)

/-- β-reduction is preserved by substitution. -/
theorem beta_subst_left {n m : Nat} (σ : SubstContract n m) {M N : Term n} (h : M —→ N) :
    substContract σ M —→ substContract σ N := by
  induction h generalizing m with
  | appl L _ ih => exact Beta.appl _ (ih σ)
  | appr L _ ih => exact Beta.appr _ (ih σ)
  | abs _ ih => exact Beta.abs (ih σ.ext)
  | basis A B =>
    show substContract σ ((ƛ A) ⬝ B) —→ substContract σ (A[B])
    rw [← subst_comm_lemma σ A B]
    exact Beta.basis _ _

/-- η-reduction is preserved by substitution. -/
theorem eta_subst_left {n m : Nat} (σ : SubstContract n m) {M N : Term n} (h : M —→η N) :
    substContract σ M —→η substContract σ N := by
  induction h generalizing m with
  | appl L _ ih => exact Eta.appl _ (ih σ)
  | appr L _ ih => exact Eta.appr _ (ih σ)
  | abs _ ih => exact Eta.abs (ih σ.ext)
  | basis P =>
    show substContract σ (ƛ (shift P ⬝ v#0)) —→η substContract σ P
    show ƛ (substContract σ.ext (shift P) ⬝ v#0) —→η substContract σ P
    rw [substContract_shift]
    exact Eta.basis _

/-- η-reduction inside a substitution. -/
theorem eta_subst_right {n m : Nat} {σ σ' : SubstContract n m}
    (hσ : ∀ i, σ.map i —→η* σ'.map i) (M : Term n) :
    substContract σ M —→η* substContract σ' M := by
  induction M generalizing m with
  | var i => exact hσ i
  | abs A ih =>
    refine eta_star_abs (ih (σ := σ.ext) (σ' := σ'.ext) ?_)
    intro i
    refine Fin.cases ?_ ?_ i
    · exact Relation.ReflTransGen.refl
    · intro j
      exact etaStar_shift (hσ j)
  | app A B ihA ihB => exact eta_star_app (ihA hσ) (ihB hσ)

/-- η-reduction in the argument of a substitution. -/
theorem eta_star_betaSubst_right {n : Nat} (M : Term (n + 1)) {N N' : Term n} (h : N —→η* N') :
    M[N] —→η* M[N'] := by
  refine eta_subst_right (σ := Term.mkSubstZero N) (σ' := Term.mkSubstZero N') ?_ M
  intro i
  refine Fin.cases ?_ ?_ i
  · exact h
  · intro j
    exact Relation.ReflTransGen.refl

/-! ### Inverting a step out of a renamed term -/

/-- A β-step out of a renamed term comes from a β-step of the original term. -/
theorem beta_ren_inv {m : Nat} {M Q : Term m} (h : M —→ Q) :
    ∀ {n : Nat} (w : RenameWeaken n m) (P : Term n), M = renameWeaken w P →
      ∃ P', Q = renameWeaken w P' ∧ P —→ P' := by
  induction h with
  | appl L _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | abs A => simp at hP
    | app P1 P2 =>
      simp only [renameWeaken_app, Term.app.injEq] at hP
      obtain ⟨h1, h2⟩ := hP
      obtain ⟨P2', hQ, hstep⟩ := ih w P2 h2
      exact ⟨P1 ⬝ P2', by simp [hQ, h1], Beta.appl _ hstep⟩
  | appr L _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | abs A => simp at hP
    | app P1 P2 =>
      simp only [renameWeaken_app, Term.app.injEq] at hP
      obtain ⟨h1, h2⟩ := hP
      obtain ⟨P1', hQ, hstep⟩ := ih w P1 h1
      exact ⟨P1' ⬝ P2, by simp [hQ, h2], Beta.appr _ hstep⟩
  | abs _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | app A B => simp at hP
    | abs P1 =>
      simp only [renameWeaken_abs, Term.abs.injEq] at hP
      obtain ⟨P1', hQ, hstep⟩ := ih w.ext P1 hP
      exact ⟨ƛ P1', by simp [hQ], Beta.abs hstep⟩
  | basis A B =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | abs C => simp at hP
    | app P1 P2 =>
      simp only [renameWeaken_app, Term.app.injEq] at hP
      obtain ⟨h1, h2⟩ := hP
      cases P1 with
      | var i => simp at h1
      | app C D => simp at h1
      | abs P11 =>
        simp only [renameWeaken_abs, Term.abs.injEq] at h1
        subst h1
        subst h2
        exact ⟨P11[P2], (rename_betaSubst w P11 P2).symm, Beta.basis _ _⟩

/-- An η-step out of a renamed term comes from an η-step of the original term. -/
theorem eta_ren_inv {m : Nat} {M Q : Term m} (h : M —→η Q) :
    ∀ {n : Nat} (w : RenameWeaken n m) (P : Term n), M = renameWeaken w P →
      ∃ P', Q = renameWeaken w P' ∧ P —→η P' := by
  induction h with
  | appl L _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | abs A => simp at hP
    | app P1 P2 =>
      simp only [renameWeaken_app, Term.app.injEq] at hP
      obtain ⟨h1, h2⟩ := hP
      obtain ⟨P2', hQ, hstep⟩ := ih w P2 h2
      exact ⟨P1 ⬝ P2', by simp [hQ, h1], Eta.appl _ hstep⟩
  | appr L _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | abs A => simp at hP
    | app P1 P2 =>
      simp only [renameWeaken_app, Term.app.injEq] at hP
      obtain ⟨h1, h2⟩ := hP
      obtain ⟨P1', hQ, hstep⟩ := ih w P1 h1
      exact ⟨P1' ⬝ P2, by simp [hQ, h2], Eta.appr _ hstep⟩
  | abs _ ih =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | app A B => simp at hP
    | abs P1 =>
      simp only [renameWeaken_abs, Term.abs.injEq] at hP
      obtain ⟨P1', hQ, hstep⟩ := ih w.ext P1 hP
      exact ⟨ƛ P1', by simp [hQ], Eta.abs hstep⟩
  | basis R =>
    intro n w P hP
    cases P with
    | var i => simp at hP
    | app A B => simp at hP
    | abs P1 =>
      simp only [renameWeaken_abs, Term.abs.injEq] at hP
      cases P1 with
      | var i => simp at hP
      | abs C => simp at hP
      | app A C =>
        simp only [renameWeaken_app, Term.app.injEq] at hP
        obtain ⟨hA, hC⟩ := hP
        cases C with
        | abs D => simp at hC
        | app D E => simp at hC
        | var c =>
          simp only [renameWeaken_var, Term.var.injEq] at hC
          have hc0 : c = 0 := w.ext_map_eq_zero hC.symm
          subst hc0
          obtain ⟨A', hA', hR⟩ := renameWeaken_ext_exchange w hA.symm
          subst hA'
          exact ⟨A', hR, Eta.basis A'⟩

/-- A β-step out of a shifted term comes from a β-step of the original term. -/
theorem beta_shift_inv {n : Nat} {P : Term n} {Q : Term (n + 1)} (h : shift P —→ Q) :
    ∃ P', Q = shift P' ∧ P —→ P' :=
  beta_ren_inv h (RenameWeaken.succ n) P rfl

/-- An η-step out of a shifted term comes from an η-step of the original term. -/
theorem eta_shift_inv {n : Nat} {P : Term n} {Q : Term (n + 1)} (h : shift P —→η Q) :
    ∃ P', Q = shift P' ∧ P —→η P' :=
  eta_ren_inv h (RenameWeaken.succ n) P rfl

/-! ### Confluence of η-reduction -/

/-- Shifting is injective. -/
theorem shift_inj {n : Nat} {M N : Term n} (h : shift M = shift N) : M = N := by
  have h0 : (shift M)[ƛ v#0] = (shift N)[ƛ v#0] := by rw [h]
  rwa [rename_succ_subst_cancel, rename_succ_subst_cancel] at h0

/-- η-reduction is subcommutative: two η-steps out of the same term can be
closed by at most one further η-step on each side. -/
theorem eta_subcommutative {n : Nat} {M N1 : Term n} (h1 : M —→η N1) :
    ∀ {N2 : Term n}, M —→η N2 →
      ∃ d, Relation.ReflGen Eta N1 d ∧ Relation.ReflTransGen Eta N2 d := by
  induction h1 with
  | appl L _ ih =>
    intro N2 h2
    rcases eta_app_inv h2 with ⟨L', rfl, hL⟩ | ⟨M0', rfl, hM⟩
    · exact ⟨L' ⬝ _, Relation.ReflGen.single (Eta.appr _ hL),
        Relation.ReflTransGen.single (Eta.appl _ (by assumption))⟩
    · obtain ⟨d0, hd1, hd2⟩ := ih hM
      refine ⟨L ⬝ d0, ?_, eta_star_appl L hd2⟩
      cases hd1 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Eta.appl _ h)
  | appr L _ ih =>
    intro N2 h2
    rcases eta_app_inv h2 with ⟨L', rfl, hL⟩ | ⟨M0', rfl, hM⟩
    · obtain ⟨d0, hd1, hd2⟩ := ih hL
      refine ⟨d0 ⬝ L, ?_, eta_star_appr L hd2⟩
      cases hd1 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Eta.appr _ h)
    · exact ⟨_ ⬝ M0', Relation.ReflGen.single (Eta.appl _ hM),
        Relation.ReflTransGen.single (Eta.appr _ (by assumption))⟩
  | @abs n A A' hstep ih =>
    intro N2 h2
    rcases eta_abs_inv h2 with ⟨A'', rfl, hA⟩ | hAeq
    · obtain ⟨d0, hd1, hd2⟩ := ih hA
      refine ⟨ƛ d0, ?_, eta_star_abs hd2⟩
      cases hd1 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Eta.abs h)
    · subst hAeq
      rcases eta_app_inv hstep with ⟨Q, rfl, hQ⟩ | ⟨M0', _, hM0⟩
      · obtain ⟨R', rfl, hR⟩ := eta_shift_inv hQ
        exact ⟨R', Relation.ReflGen.single (Eta.basis R'),
          Relation.ReflTransGen.single hR⟩
      · exact absurd hM0 (fun h => eta_var_inv h)
  | @basis n R =>
    intro N2 h2
    rcases eta_abs_inv h2 with ⟨A'', rfl, hA⟩ | hAeq
    · rcases eta_app_inv hA with ⟨Q, rfl, hQ⟩ | ⟨M0', _, hM0⟩
      · obtain ⟨R', rfl, hR⟩ := eta_shift_inv hQ
        exact ⟨R', Relation.ReflGen.single hR,
          Relation.ReflTransGen.single (Eta.basis R')⟩
      · exact absurd hM0 (fun h => eta_var_inv h)
    · have hRR : R = N2 := by
        simp only [Term.app.injEq] at hAeq
        exact shift_inj hAeq.1
      subst hRR
      exact ⟨_, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩

/-- **Confluence of η-reduction**. -/
theorem eta_confluence {n : Nat} {M N1 N2 : Term n} (h1 : M —→η* N1) (h2 : M —→η* N2) :
    Relation.Join (EtaStar (n := n)) N1 N2 :=
  Relation.church_rosser (fun _ _ _ hab hac => eta_subcommutative hab hac) h1 h2

/-! ### η-reduction terminates -/

/-- The size of a term. -/
def size {n : Nat} : Term n → Nat
  | v#_   => 1
  | ƛ M   => size M + 1
  | M ⬝ N => size M + size N + 1

@[simp] theorem size_ren {n m : Nat} (w : RenameWeaken n m) (M : Term n) :
    size (renameWeaken w M) = size M := by
  induction M generalizing m with
  | var i => rfl
  | abs A ih => simp [size, ih w.ext]
  | app A B ihA ihB => simp [size, ihA w, ihB w]

/-- An η-step strictly decreases the size of a term. -/
theorem size_lt_of_eta {n : Nat} {M N : Term n} (h : M —→η N) : size N < size M := by
  induction h with
  | appl L _ ih => simp only [size]; omega
  | appr L _ ih => simp only [size]; omega
  | abs _ ih => simp only [size]; omega
  | basis P => simp only [size, size_ren]; omega

/-- **η-reduction is strongly normalising**: every η-reduction sequence
terminates. -/
theorem eta_strongly_normalizing {n : Nat} (M : Term n) : Acc (fun N K => K —→η N) M := by
  have : ∀ (k : Nat) (M : Term n), size M ≤ k → Acc (fun N K => K —→η N) M := by
    intro k
    induction k with
    | zero =>
      intro M hM
      exact absurd hM (by cases M <;> simp [size])
    | succ k ih =>
      intro M hM
      refine Acc.intro _ (fun N hN => ih N ?_)
      have := size_lt_of_eta hN
      omega
  exact this (size M) M (Nat.le_refl _)

/-! ### β and η commute -/

theorem beta_app_inv {n : Nat} {L M K : Term n} (h : L ⬝ M —→ K) :
    (∃ L', K = L' ⬝ M ∧ L —→ L') ∨ (∃ M', K = L ⬝ M' ∧ M —→ M') ∨
      (∃ A : Term (n + 1), L = ƛ A ∧ K = A[M]) := by
  cases h with
  | appl _ h => exact Or.inr (Or.inl ⟨_, rfl, h⟩)
  | appr _ h => exact Or.inl ⟨_, rfl, h⟩
  | basis => exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)

/-- Substituting `#0` undoes a shift under a binder. -/
theorem betaSubst_zero_shift_ext {n : Nat} (R : Term (n + 1)) :
    (renameWeaken (RenameWeaken.succ n).ext R)[v#0] = R := by
  refine subst_rename_id (Term.mkSubstZero (v#0)) (RenameWeaken.succ n).ext R ?_
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

/-- **Strong commutation of β and η**: a β-step and an η-step out of the same
term can be closed by η-steps on one side and at most one β-step on the
other. -/
theorem beta_eta_commute_step {n : Nat} {M N1 : Term n} (h1 : M —→ N1) :
    ∀ {N2 : Term n}, M —→η N2 → ∃ d, N1 —→η* d ∧ Relation.ReflGen Beta N2 d := by
  induction h1 with
  | appl L hstep ih =>
    intro N2 h2
    rcases eta_app_inv h2 with ⟨L', rfl, hL⟩ | ⟨M0', rfl, hM⟩
    · exact ⟨L' ⬝ _, eta_star_appr _ (Relation.ReflTransGen.single hL),
        Relation.ReflGen.single (Beta.appl _ hstep)⟩
    · obtain ⟨d0, hd1, hd2⟩ := ih hM
      refine ⟨L ⬝ d0, eta_star_appl L hd1, ?_⟩
      cases hd2 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Beta.appl _ h)
  | appr L hstep ih =>
    intro N2 h2
    rcases eta_app_inv h2 with ⟨L', rfl, hL⟩ | ⟨M0', rfl, hM⟩
    · obtain ⟨d0, hd1, hd2⟩ := ih hL
      refine ⟨d0 ⬝ L, eta_star_appr L hd1, ?_⟩
      cases hd2 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Beta.appr _ h)
    · exact ⟨_ ⬝ M0', eta_star_appl _ (Relation.ReflTransGen.single hM),
        Relation.ReflGen.single (Beta.appr _ hstep)⟩
  | @abs n A A' hstep ih =>
    intro N2 h2
    rcases eta_abs_inv h2 with ⟨A'', rfl, hA⟩ | hAeq
    · obtain ⟨d0, hd1, hd2⟩ := ih hA
      refine ⟨ƛ d0, eta_star_abs hd1, ?_⟩
      cases hd2 with
      | refl => exact Relation.ReflGen.refl
      | single h => exact Relation.ReflGen.single (Beta.abs h)
    · subst hAeq
      rcases beta_app_inv hstep with ⟨Q, rfl, hQ⟩ | ⟨M', _, hM'⟩ | ⟨B, hB, hA'⟩
      · obtain ⟨R', rfl, hR⟩ := beta_shift_inv hQ
        exact ⟨R', Relation.ReflTransGen.single (Eta.basis R'), Relation.ReflGen.single hR⟩
      · exact absurd hM' (fun h => beta_var_inv h)
      · cases N2 with
        | var i => simp at hB
        | app C D => simp at hB
        | abs R0 =>
          simp only [renameWeaken_abs, Term.abs.injEq] at hB
          subst hA'
          subst hB
          rw [betaSubst_zero_shift_ext]
          exact ⟨ƛ R0, Relation.ReflTransGen.refl, Relation.ReflGen.refl⟩
  | basis A B =>
    intro N2 h2
    rcases eta_app_inv h2 with ⟨L', rfl, hL⟩ | ⟨B', rfl, hB⟩
    · rcases eta_abs_inv hL with ⟨A'', rfl, hA⟩ | hAeq
      · exact ⟨A''[B], Relation.ReflTransGen.single (eta_subst_left (Term.mkSubstZero B) hA),
          Relation.ReflGen.single (Beta.basis _ _)⟩
      · subst hAeq
        refine ⟨L' ⬝ B, ?_, Relation.ReflGen.refl⟩
        show ((shift L')[B]) ⬝ ((v#0 : Term _)[B]) —→η* L' ⬝ B
        rw [rename_succ_subst_cancel]
        exact Relation.ReflTransGen.refl
    · exact ⟨A[B'], eta_star_betaSubst_right A (Relation.ReflTransGen.single hB),
        Relation.ReflGen.single (Beta.basis _ _)⟩

/-- The closures of β- and η-reduction commute. -/
theorem betaStar_etaStar_commute {n : Nat} {M N1 N2 : Term n}
    (h1 : M —→* N1) (h2 : M —→η* N2) : ∃ d, N1 —→η* d ∧ N2 —→* d :=
  Relation.commute_reflTransGen (fun _ _ _ hab hac => beta_eta_commute_step hab hac) h1 h2

end IwilareFinsetNOfFreeIsExact
