-- Beta-eta reduction and the Church-Rosser theorem for `—→βη`, for the
-- scope-bounded (`Fin`-indexed) calculus.
--
-- With confluence of `—→` (beta) and of `—→η` (eta) already available, the
-- confluence of their union follows from a *commutation* property: a beta step
-- and an eta step out of the same term can always be closed, with at most one
-- beta step on one side and any number of eta steps on the other.  This is the
-- standard Hindley-Rosen argument.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.Eta

@[expose] public section

namespace FinScope

open Term

/-! ## 0. `ReflGen` congruences for beta -/

theorem Beta.reflGen_abs {n : Nat} {x y : Term (n + 1)} (h : Relation.ReflGen Beta x y) :
    Relation.ReflGen Beta (ƛ x) (ƛ y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.abs h)

theorem Beta.reflGen_appL {n : Nat} {x y : Term n} (L : Term n)
    (h : Relation.ReflGen Beta x y) : Relation.ReflGen Beta (x ⬝ L) (y ⬝ L) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.appL h)

theorem Beta.reflGen_appR {n : Nat} {x y : Term n} (L : Term n)
    (h : Relation.ReflGen Beta x y) : Relation.ReflGen Beta (L ⬝ x) (L ⬝ y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.appR h)

theorem reflGen_beta_to_betaStar {n : Nat} {x y : Term n} (h : Relation.ReflGen Beta x y) :
    x —→* y := by
  cases h with
  | refl => exact .refl
  | single h => exact Relation.ReflTransGen.single h

/-! ## 1. A beta step and an eta step commute -/

/-- **Commutation of one beta step with one eta step.**  If `a —→ b` and
`a —→η c`, then `b` eta-reduces to some `d` that `c` reaches in at most one
beta step. -/
theorem beta_eta_commute {n : Nat} {a b : Term n} (h₁ : a —→ b) : ∀ c : Term n, a —→η c →
    ∃ d, b —→η* d ∧ Relation.ReflGen Beta c d := by
  induction h₁ with
  | @basis n P Q =>
      intro c h₂
      rcases h₂.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · rcases ha'.abs_inv with ⟨M, hM, hcM⟩ | ⟨P', rfl, hP'⟩
        · refine ⟨M ⬝ Q, ?_, ?_⟩
          · rw [hM]
            simpa using Relation.ReflTransGen.refl
          · rw [hcM]
        · exact ⟨P' [ Q ], Relation.ReflTransGen.single (Eta.sub_mono hP' _),
            Relation.ReflGen.single (Beta.basis P' Q)⟩
      · exact ⟨P [ b' ], Eta.betaSubst_congr hb' _,
          Relation.ReflGen.single (Beta.basis P b')⟩
  | @abs n M N hMN ih =>
      intro c h₂
      rcases h₂.abs_inv with ⟨Z, hZ, rfl⟩ | ⟨p', rfl, hp'⟩
      · subst hZ
        rcases hMN.app_inv with ⟨P, hP, rfl⟩ | ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩
        · obtain ⟨Q, rfl, rfl⟩ := ren_eq_abs (ρ := Fin.succ) hP
          refine ⟨ƛ Q, ?_, Relation.ReflGen.refl⟩
          rw [betaSubst_var_zero_ren_ext_succ]
        · obtain ⟨Z', rfl, hZ'⟩ := Beta.ren_reflect ha'
          exact ⟨Z', Relation.ReflTransGen.single (Eta.basis Z'),
            Relation.ReflGen.single hZ'⟩
        · exact absurd hb' (fun h => h.var_inv)
      · obtain ⟨d, hd₁, hd₂⟩ := ih p' hp'
        exact ⟨ƛ d, EtaStar.abs hd₁, Beta.reflGen_abs hd₂⟩
  | @appL n x x' y hxx' ih =>
      intro c h₂
      rcases h₂.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih a' ha'
        exact ⟨d ⬝ y, EtaStar.appL hd₁, Beta.reflGen_appL y hd₂⟩
      · exact ⟨x' ⬝ b', Relation.ReflTransGen.single (Eta.appR hb'),
          Relation.ReflGen.single (Beta.appL hxx')⟩
  | @appR n x y y' hyy' ih =>
      intro c h₂
      rcases h₂.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · exact ⟨a' ⬝ y', Relation.ReflTransGen.single (Eta.appL ha'),
          Relation.ReflGen.single (Beta.appR hyy')⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih b' hb'
        exact ⟨x ⬝ d, EtaStar.appR hd₁, Beta.reflGen_appR x hd₂⟩

/-- One beta step commutes with a sequence of eta steps. -/
theorem beta_etaStar_commute {n : Nat} {a b c : Term n} (h₁ : a —→ b) (h₂ : a —→η* c) :
    ∃ d, b —→η* d ∧ Relation.ReflGen Beta c d := by
  induction h₂ with
  | refl => exact ⟨b, .refl, Relation.ReflGen.single h₁⟩
  | @tail c' c _ hstep ih =>
      obtain ⟨d, hd₁, hd₂⟩ := ih
      cases hd₂ with
      | refl => exact ⟨c, hd₁.tail hstep, Relation.ReflGen.refl⟩
      | single hcd =>
          obtain ⟨e, he₁, he₂⟩ := beta_eta_commute hcd c hstep
          exact ⟨e, hd₁.trans he₁, he₂⟩

/-- **Beta and eta reduction commute**: beta-reducing and eta-reducing the same
term can always be reconciled. -/
theorem betaStar_etaStar_commute {n : Nat} {a b c : Term n} (h₁ : a —→* b) (h₂ : a —→η* c) :
    ∃ d, b —→η* d ∧ c —→* d := by
  induction h₁ with
  | refl => exact ⟨c, h₂, .refl⟩
  | @tail b' b _ hstep ih =>
      obtain ⟨d', hd₁, hd₂⟩ := ih
      obtain ⟨d, he₁, he₂⟩ := beta_etaStar_commute hstep hd₁
      exact ⟨d, he₁, hd₂.trans (reflGen_beta_to_betaStar he₂)⟩

/-! ## 2. Beta-eta reduction and its Church-Rosser theorem -/

/-- A single beta-eta step: either a beta step or an eta step. -/
def BetaEta {n : Nat} (a b : Term n) : Prop := a —→ b ∨ a —→η b

/-- Multi-step beta-eta reduction. -/
abbrev BetaEtaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaEta

@[inherit_doc] infix:60 " —→βη* " => BetaEtaStar

theorem BetaStar.to_betaEtaStar {n : Nat} {a b : Term n} (h : a —→* b) : a —→βη* b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Or.inl step)

theorem EtaStar.to_betaEtaStar {n : Nat} {a b : Term n} (h : a —→η* b) : a —→βη* b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Or.inr step)

/-- The auxiliary relation used for the Hindley-Rosen argument: a full beta
sequence or a full eta sequence. -/
def BetaOrEtaStar {n : Nat} (a b : Term n) : Prop := a —→* b ∨ a —→η* b

theorem BetaOrEtaStar.to_betaEtaStar {n : Nat} {a b : Term n} (h : BetaOrEtaStar a b) :
    a —→βη* b := by
  rcases h with h | h
  · exact BetaStar.to_betaEtaStar h
  · exact EtaStar.to_betaEtaStar h

theorem betaEtaStar_iff {n : Nat} {a b : Term n} :
    a —→βη* b ↔ Relation.ReflTransGen BetaOrEtaStar a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih =>
        cases step with
        | inl h1 => exact Relation.ReflTransGen.tail ih (Or.inl (Relation.ReflTransGen.single h1))
        | inr h2 => exact Relation.ReflTransGen.tail ih (Or.inr (Relation.ReflTransGen.single h2))
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.trans ih (BetaOrEtaStar.to_betaEtaStar step)

/-- **The Church-Rosser theorem for beta-eta reduction.** -/
theorem betaeta_church_rosser {n : Nat} {a b c : Term n} (hab : a —→βη* b) (hac : a —→βη* c) :
    ∃ d, b —→βη* d ∧ c —→βη* d := by
  have key : ∀ x y z : Term n, BetaOrEtaStar x y → BetaOrEtaStar x z →
      ∃ d, Relation.ReflGen BetaOrEtaStar y d ∧ Relation.ReflTransGen BetaOrEtaStar z d := by
    intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · obtain ⟨d, hyd, hzd⟩ := beta_church_rosser hxy hxz
      exact ⟨d, Relation.ReflGen.single (Or.inl hyd),
        Relation.ReflTransGen.single (Or.inl hzd)⟩
    · obtain ⟨d, hyd, hzd⟩ := betaStar_etaStar_commute hxy hxz
      exact ⟨d, Relation.ReflGen.single (Or.inr hyd),
        Relation.ReflTransGen.single (Or.inl hzd)⟩
    · obtain ⟨d, hzd, hyd⟩ := betaStar_etaStar_commute hxz hxy
      exact ⟨d, Relation.ReflGen.single (Or.inl hyd),
        Relation.ReflTransGen.single (Or.inr hzd)⟩
    · obtain ⟨d, hyd, hzd⟩ := eta_church_rosser hxy hxz
      exact ⟨d, Relation.ReflGen.single (Or.inr hyd),
        Relation.ReflTransGen.single (Or.inr hzd)⟩
  obtain ⟨d, hbd, hcd⟩ :=
    Relation.church_rosser key (betaEtaStar_iff.mp hab) (betaEtaStar_iff.mp hac)
  exact ⟨d, betaEtaStar_iff.mpr hbd, betaEtaStar_iff.mpr hcd⟩

/-- Confluence of beta-eta reduction, in the `Relation.Join` formulation. -/
theorem betaeta_confluence {n : Nat} {a b c : Term n} (hab : a —→βη* b) (hac : a —→βη* c) :
    Relation.Join BetaEtaStar b c := by
  obtain ⟨d, hbd, hcd⟩ := betaeta_church_rosser hab hac
  exact ⟨d, hbd, hcd⟩

/-! ## 3. Beta-eta conversion -/

/-- Beta-eta conversion: the equivalence closure of a beta-eta step. -/
abbrev BetaEtaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen BetaEta

@[inherit_doc] infix:60 " =βη " => BetaEtaEq

theorem betaEtaStar_to_betaEtaEq {n : Nat} {a b : Term n} (h : a —→βη* b) : a =βη b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem BetaEtaEq.symm {n : Nat} {a b : Term n} (h : a =βη b) : b =βη a :=
  Relation.EqvGen.symm _ _ h

theorem BetaEtaEq.trans {n : Nat} {a b c : Term n} (h₁ : a =βη b) (h₂ : b =βη c) : a =βη c :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem BetaEtaEq.refl {n : Nat} (a : Term n) : a =βη a := Relation.EqvGen.refl _

/-- Beta-eta conversion is compatible with abstraction. -/
theorem BetaEtaEq.abs {n : Nat} {a b : Term (n + 1)} (h : a =βη b) : ƛ a =βη ƛ b := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.abs hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.abs hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta-eta conversion is compatible with the function part of an application. -/
theorem BetaEtaEq.appL {n : Nat} {a b : Term n} (L : Term n) (h : a =βη b) :
    a ⬝ L =βη b ⬝ L := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.appL hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.appL hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta-eta conversion is compatible with the argument of an application. -/
theorem BetaEtaEq.appR {n : Nat} {a b : Term n} (L : Term n) (h : a =βη b) :
    L ⬝ a =βη L ⬝ b := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.appR hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.appR hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Extensionality of beta-eta conversion**: if `M` and `N` agree on a fresh
variable, they are beta-eta convertible.  (This is the rule `ext`, and it is
exactly what eta adds to the beta theory.) -/
theorem betaeta_extensionality {n : Nat} {M N : Term n}
    (h : wk M ⬝ v# 0 =βη wk N ⬝ v# 0) : M =βη N := by
  have hM : (ƛ (wk M ⬝ v# 0)) =βη M := Relation.EqvGen.rel _ _ (Or.inr (Eta.basis M))
  have hN : (ƛ (wk N ⬝ v# 0)) =βη N := Relation.EqvGen.rel _ _ (Or.inr (Eta.basis N))
  exact (hM.symm.trans h.abs).trans hN

/-- **Beta-eta convertible terms are joinable.** -/
theorem betaeta_eq_join {n : Nat} {a b : Term n} (h : a =βη b) :
    ∃ d, a —→βη* d ∧ b —→βη* d := by
  induction h with
  | rel x y hxy => exact ⟨y, Relation.ReflTransGen.single hxy, .refl⟩
  | refl x => exact ⟨x, .refl, .refl⟩
  | symm x y _ ih => obtain ⟨d, h1, h2⟩ := ih; exact ⟨d, h2, h1⟩
  | trans x y z _ _ ih1 ih2 =>
      obtain ⟨d1, hx, hy1⟩ := ih1
      obtain ⟨d2, hy2, hz⟩ := ih2
      obtain ⟨d, hd1, hd2⟩ := betaeta_church_rosser hy1 hy2
      exact ⟨d, hx.trans hd1, hz.trans hd2⟩

end FinScope
