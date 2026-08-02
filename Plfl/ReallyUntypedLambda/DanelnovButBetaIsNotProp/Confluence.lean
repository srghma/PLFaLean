module
public import Plfl.ReallyUntypedLambda.DanelnovButBetaIsNotProp.Defs
public import Plfl.ReallyUntypedLambda.DanelnovButBetaIsNotProp.Properties
public import Plfl.ReallyUntypedLambda.DanelnovButBetaIsNotProp.Diamond
public import Mathlib.Tactic
@[expose] public section

namespace DanelnovButBetaIsNotProp
open Lambda

@[simp]
theorem app_beta {N₁ N₂ N' : Lambda} : (N₁.app N₂).beta N' = (N₁.beta N').app (N₂.beta N') := by
    conv => lhs; unfold beta; simp; rw [← beta, ← beta]

def betap_appl {N₁ N₂ N' : Lambda} (h : N₁ →βp N₂) : N₁.app N' →βp N₂.app N' :=
    BetaP.app _ _ _ _ h betap_refl

def betap_appr {N₁ N₂ N' : Lambda} (h : N₁ →βp N₂) : N'.app N₁ →βp N'.app N₂ :=
    BetaP.app _ _ _ _ betap_refl h

def para_shift_conservation {i j : Nat} {N N' : Lambda} (h : N →βp N') : (↑) i j N →βp (↑) i j N' :=
  match h with
  | BetaP.var n => by simp only [Lambda.shift]; split_ifs <;> exact BetaP.var _
  | BetaP.abs N M ih => BetaP.abs _ _ (para_shift_conservation ih)
  | BetaP.app M M' N N' ih1 ih2 => BetaP.app _ _ _ _ (para_shift_conservation ih1) (para_shift_conservation ih2)
  | BetaP.subst M₁ M₂ N₁ N₂ ih1 ih2 => by
      simp [beta]
      rw [shift_unshift_swap (Nat.zero_le i) (shifted_subst' 0 M₂ N₂)]
      simp
      rw [← shift_shift_swap _ (Nat.zero_le i), ← beta]
      exact BetaP.subst _ _ _ _ (para_shift_conservation ih1) (para_shift_conservation ih2)

theorem para_shift_shifted {d c : Nat} {N₁ N₂ : Lambda}
    (h₁ : N₁ →βp N₂) (h₂ : Shifted d c N₁) : Shifted d c N₂ := by
    induction h₁ generalizing c d with
    | var n => exact h₂
    | app _ _ _ _ _ _ ih1 ih2 => cases h₂; apply Shifted.sapp <;> (first | apply ih1 | apply ih2) <;> assumption
    | abs _ _ _ ih => cases h₂; apply Shifted.sabs; apply ih; assumption
    | subst M₁ M₂ L₁ L₂ hm hl ihm ihl =>
        simp [beta]; cases h₂; rename_i h1 h2; cases h1
        nth_rw 2 [Eq.symm (Nat.zero_add 1)]
        rw [Eq.symm (Nat.zero_add c)]
        apply shifted_subst <;> (first | apply ihm | apply ihl)
        rw [Nat.zero_add, Nat.add_comm]
        all_goals assumption

def para_unshift_conservation {d c : Nat} {N₁ N₂ : Lambda}
    (h₁ : Shifted d c N₁) (h₂ : N₁ →βp N₂) : (↓) c d N₁ →βp (↓) c d N₂ :=
    match h₂ with
    | BetaP.var n => by dsimp [unshift]; split_ifs <;> exact BetaP.var _
    | BetaP.abs N M ih => by
        have sN : Shifted d (c + 1) N := by cases h₁; assumption
        dsimp [unshift]
        exact BetaP.abs _ _ (para_unshift_conservation sN ih)
    | BetaP.app M M' N N' hm hn => by
        have sM : Shifted d c M := by cases h₁; assumption
        have sN : Shifted d c N := by cases h₁; assumption
        dsimp [unshift]
        exact BetaP.app _ _ _ _ (para_unshift_conservation sM hm) (para_unshift_conservation sN hn)
    | BetaP.subst M₁ M₂ N₁ N₂ hm hn => by
        have sM : Shifted d (c + 1) M₁ := by cases h₁; rename_i h1 h2; cases h1; assumption
        have sN : Shifted d c N₁ := by cases h₁; rename_i h1 h2; assumption
        have hsn := para_shift_shifted hn sN
        have hsm := para_shift_shifted hm sM
        dsimp [unshift, beta]
        rw [unshift_unshift_swap (by omega) (by aesop) ?shifted]
        case shifted =>
            rw [Eq.symm (Nat.zero_add c)]
            nth_rw 2 [Eq.symm (Nat.zero_add 1)]
            apply shifted_subst <;> (try assumption)
            rw [Nat.zero_add, Nat.add_comm]; assumption
        rw [unshift_subst_swap2 (by omega) hsm ?shifted]
        case shifted =>
            rw [Nat.add_comm]; apply shift_shifted' <;> aesop

        rw [← unshift_shift_swap (by omega) hsn, ← beta]
        exact BetaP.subst _ _ _ _ (para_unshift_conservation sM hm) (para_unshift_conservation sN hn)

def para_subst' {n} {M N N' : Lambda} (h : N →βp N') : M[n := N] →βp M[n := N'] :=
  match M with
  | Lambda.var m => by simp; split_ifs; exact h; exact BetaP.var _
  | Lambda.app M₁ M₂ => by simp; exact BetaP.app _ _ _ _ (para_subst' h) (para_subst' h)
  | Lambda.abs M => by simp; exact BetaP.abs _ _ (para_subst' (para_shift_conservation h))

def para_subst {n} {M N M' N' : Lambda}
    (h₁ : M →βp M') (h₂ : N →βp N') : M[n := N] →βp M'[n := N'] :=
  match h₁ with
  | BetaP.var m => by simp; split_ifs; exact h₂; exact BetaP.var _
  | BetaP.app M M' N N' hm hn => by
      simp
      exact BetaP.app _ _ _ _ (para_subst hm h₂) (para_subst hn h₂)
  | BetaP.abs M M' hm => by
      simp
      exact BetaP.abs _ _ (para_subst hm (para_shift_conservation h₂))
  | BetaP.subst M M' P P' hm hp => by
      have h1 : 0 + 1 + n = n + 1 := by omega
      rw [beta, ← unshift_subst_swap' _ _ (shifted_subst' 0 M' P'), ← h1, substitution']
      have h2 : 1 + n = n + 1 := by omega
      rw [h2]
      rw [← shift_subst_swap' P' N' (by omega)]
      exact BetaP.subst _ _ _ _ (para_subst hm (para_shift_conservation h₂)) (para_subst hp h₂)

def para_beta {M N M' N' : Lambda}
    (hm : M →βp M') (hn : N →βp N') : M.beta N →βp M'.beta N' := by
    simp [beta]
    apply para_unshift_conservation
    . exact shifted_subst' 0 M N
    . exact (para_subst hm) (para_shift_conservation hn)

def para_diamond : Diamond BetaP :=
  fun {M M₁ M₂} h1 h2 =>
    match h1 with
    | BetaP.var n =>
        match h2 with
        | BetaP.var _ => ⟨var n, BetaP.var n, BetaP.var n⟩
    | BetaP.abs N₁ N₂ h1' =>
        match h2 with
        | BetaP.abs _ N₃ h2' =>
            let ⟨N₄, h3, h4⟩ := para_diamond h1' h2'
            ⟨λ N₄, .abs _ _ h3, .abs _ _ h4⟩
    | BetaP.app N₁ N₂ P₁ P₂ hn1 hp1 =>
        match h2 with
        | BetaP.app _ N₃ _ P₃ hn2 hp2 =>
            let ⟨N₄, hN3, hN4⟩ := para_diamond hn1 hn2
            let ⟨P₄, hP3, hP4⟩ := para_diamond hp1 hp2
            ⟨N₄.app P₄, .app _ _ _ _ hN3 hP3, .app _ _ _ _ hN4 hP4⟩
        | BetaP.subst L₁ L₃ _ P₃ hL1 hp2 =>
            match hn1 with
            | BetaP.abs _ L₂ hL2 =>
                let ⟨L₄, hL3, hL4⟩ := para_diamond hL2 hL1
                let ⟨P₄, hP3, hP4⟩ := para_diamond hp1 hp2
                ⟨L₄.beta P₄, .subst _ _ _ _ hL3 hP3, para_beta hL4 hP4⟩
    | BetaP.subst L₁ L₂ P₁ P₂ hL1 hp1 =>
        match h2 with
        | BetaP.app _ N₃ _ P₃ hn2 hp2 =>
            match hn2 with
            | BetaP.abs _ L₃ hL3 =>
                let ⟨L₄, hL3', hL4⟩ := para_diamond hL1 hL3
                let ⟨P₄, hP3, hP4⟩ := para_diamond hp1 hp2
                ⟨L₄.beta P₄, para_beta hL3' hP3, .subst _ _ _ _ hL4 hP4⟩
        | BetaP.subst _ L₃ _ P₃ hL2 hp2 =>
            let ⟨L₄, hL3, hL4⟩ := para_diamond hL1 hL2
            let ⟨P₄, hP3, hP4⟩ := para_diamond hp1 hp2
            ⟨L₄.beta P₄, para_beta hL3 hP3, para_beta hL4 hP4⟩

section BetaTRprops

def appr_cong {M₁ M₂ N : Lambda} (h : M₁ ⇒β M₂) : M₁.app N ⇒β M₂.app N :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h₁ h₂ => ReflTransGen.head (Beta.appr _ _ N h₁) (appr_cong h₂)

def appl_cong {M₁ M₂ N : Lambda} (h : M₁ ⇒β M₂) : N.app M₁ ⇒β N.app M₂ :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h₁ h₂ => ReflTransGen.head (Beta.appl _ _ N h₁) (appl_cong h₂)

@[simp]
def app_cong {M₁ M₂ N₁ N₂ : Lambda} (hm : M₁ ⇒β M₂) (hn : N₁ ⇒β N₂) :
    M₁.app N₁ ⇒β M₂.app N₂ :=
    ReflTransGen.trans (appr_cong hm) (appl_cong hn)

def abs_cong {M₁ M₂ : Lambda} (h : M₁ ⇒β M₂) : (λ M₁) ⇒β (λ M₂) :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h₁ h₂ => ReflTransGen.head (Beta.abs _ _ h₁) (abs_cong h₂)

def beta_shift_cong {M₁ M₂ : Lambda} {c d : ℕ} (h : M₁ →β M₂) : (↑) c d M₁ →β (↑) c d M₂ :=
  match h with
  | Beta.basis N₁ N₂ => by
      simp; unfold beta
      rw [shift_unshift_swap (Nat.zero_le c) (shifted_subst' 0 N₁ N₂)]
      simp
      rw [← shift_shift_swap _ (Nat.zero_le c), ← beta]
      exact Beta.basis _ _
  | Beta.appr M N L ih => by simp; exact Beta.appr _ _ _ (beta_shift_cong ih)
  | Beta.appl M N L ih => by simp; exact Beta.appl _ _ _ (beta_shift_cong ih)
  | Beta.abs N M ih => by simp; exact Beta.abs _ _ (beta_shift_cong ih)

def shift_cong {M₁ M₂ : Lambda} {c d : ℕ} (h : M₁ ⇒β M₂) : (↑) c d M₁ ⇒β (↑) c d M₂ :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h₁ h₂ => ReflTransGen.head (beta_shift_cong h₁) (shift_cong h₂)

def sub_reduction {i : ℕ} {N M₁ M₂ : Lambda} (h : M₁ ⇒β M₂) :
    N[i := M₁] ⇒β N[i := M₂] :=
  match N with
  | Lambda.var n => by
      simp; split_ifs
      . exact h
      . exact .refl
  | Lambda.app N₁ N₂ => by
      simp; exact app_cong (sub_reduction (N := N₁) h) (sub_reduction (N := N₂) h)
  | Lambda.abs N => by exact abs_cong (sub_reduction (N := N) (shift_cong h))

end BetaTRprops

def step_para {M₁ M₂ : Lambda} (step : M₁ →β M₂) : M₁ →βp M₂ :=
  match step with
  | Beta.basis M N => BetaP.subst M M N N betap_refl betap_refl
  | Beta.appr M N L ih => BetaP.app N M L L (step_para ih) betap_refl
  | Beta.appl M N L ih => BetaP.app L L N M betap_refl (step_para ih)
  | Beta.abs N M ih => BetaP.abs N M (step_para ih)

def para_betatr {M₁ M₂ : Lambda} (para : M₁ →βp M₂) : M₁ ⇒β M₂ :=
  match para with
  | BetaP.var n => .refl
  | BetaP.abs N₁ N₂ h => abs_cong (para_betatr h)
  | BetaP.app M M' N N' hm hn => app_cong (para_betatr hm) (para_betatr hn)
  | BetaP.subst P P' N N' hm hp =>
      let h1 : (λ P).app N ⇒β (λ P').app N' := app_cong (abs_cong (para_betatr hm)) (para_betatr hp)
      let h2 : (λ P').app N' ⇒β P'.beta N' := ReflTransGen.single (Beta.basis P' N')
      ReflTransGen.trans h1 h2

notation:65 M₁ " →β* " M₂ => ReflTransGen BetaP M₁ M₂

def paratr_to_betatr {M N : Lambda} (h : M →β* N) : M ⇒β N :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h1 h2 => ReflTransGen.trans (para_betatr h1) (paratr_to_betatr h2)

def betatr_to_paratr {M N : Lambda} (h : M ⇒β N) : M →β* N :=
  match h with
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head h1 h2 => ReflTransGen.head (step_para h1) (betatr_to_paratr h2)

def church_rosser : Diamond <| ReflTransGen Beta :=
  equiv_confluence (R' := ReflTransGen Beta) paratr_to_betatr betatr_to_paratr (confluence para_diamond)

end DanelnovButBetaIsNotProp
