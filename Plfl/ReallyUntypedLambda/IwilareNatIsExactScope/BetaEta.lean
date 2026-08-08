-- Beta-eta reduction and the Church-Rosser theorem for `—→βη`.
--
-- With confluence of `—→` (beta) and of `—→η` (eta) already available, the
-- confluence of their union follows from a *commutation* property: a beta step
-- and an eta step out of the same term can always be closed, with at most one
-- beta step on one side and any number of eta steps on the other.  This is the
-- standard Hindley-Rosen argument.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.Eta

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 0. `ReflGen` congruences for beta
-- ====================================================================

theorem Beta.reflGen_abs {x y : Scoped} (h : Relation.ReflGen Beta x y) :
    Relation.ReflGen Beta x.abs y.abs := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.abs h)

theorem Beta.reflGen_appr {x y : Scoped} (L : Scoped) (h : Relation.ReflGen Beta x y) :
    Relation.ReflGen Beta (x.app L) (y.app L) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.appr L h)

theorem Beta.reflGen_appl {x y : Scoped} (L : Scoped) (h : Relation.ReflGen Beta x y) :
    Relation.ReflGen Beta (L.app x) (L.app y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Beta.appl L h)

theorem reflGen_beta_to_betaStar {x y : Scoped} (h : Relation.ReflGen Beta x y) :
    x —→* y := by
  cases h with
  | refl => exact Relation.ReflTransGen.refl
  | single h => exact Relation.ReflTransGen.single h

-- ====================================================================
-- 1. A beta step and an eta step commute
-- ====================================================================

/-- **Commutation of one beta step with one eta step.**  If `a —→ b` and
    `a —→η c`, then `b` eta-reduces to some `d` that `c` reaches in at most one
    beta step. -/
theorem beta_eta_commute {a b : Scoped} (h₁ : a —→ b) : ∀ c : Scoped, a —→η c →
    ∃ d, b —→η* d ∧ Relation.ReflGen Beta c d := by
  induction h₁ with
  | @appl L M N hMN ih =>
      intro c h₂
      rcases h₂.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · exact ⟨Scoped.app a' N,
          Relation.ReflTransGen.single (Eta.appr N ha'),
          Relation.ReflGen.single (Beta.appl a' hMN)⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih b' hb'
        exact ⟨Scoped.app L d, eta_star_appl L hd₁, Beta.reflGen_appl L hd₂⟩
  | @appr L M N hMN ih =>
      intro c h₂
      rcases h₂.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih a' ha'
        exact ⟨Scoped.app d L, eta_star_appr L hd₁, Beta.reflGen_appr L hd₂⟩
      · exact ⟨Scoped.app N b',
          Relation.ReflTransGen.single (Eta.appl N hb'),
          Relation.ReflGen.single (Beta.appr b' hMN)⟩
  | @abs M N hMN ih =>
      intro c h₂
      rcases h₂.abs_inv' with ⟨Z, hZ, rfl⟩ | ⟨p', rfl, hp'⟩
      · subst hZ
        rcases hMN.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩ | ⟨p, hp, rfl⟩
        · obtain ⟨Z', rfl, hZ'⟩ := Beta.ren_reflect ha'
          exact ⟨Z', Relation.ReflTransGen.single (Eta.basis Z'),
            Relation.ReflGen.single hZ'⟩
        · exact absurd rfl (hb'.var_inv (i := 0))
        · obtain ⟨Q, rfl, rfl⟩ := Scoped.ren_eq_abs (ρ := Nat.succ) hp
          refine ⟨Scoped.abs Q, ?_, Relation.ReflGen.refl⟩
          rw [Scoped.sub0_var_zero_ren_upRen_succ]
      · obtain ⟨d, hd₁, hd₂⟩ := ih p' hp'
        exact ⟨Scoped.abs d, eta_star_abs hd₁, Beta.reflGen_abs hd₂⟩
  | @basis m n P Q =>
      intro c h₂
      rw [Term.betaSubstSigma_eq_sub0]
      rcases h₂.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · rcases ha'.abs_inv' with ⟨M, hM, hcM⟩ | ⟨P', rfl, hP'⟩
        · refine ⟨Scoped.app M ⟨n, Q⟩, ?_, ?_⟩
          · have e : Scoped.sub0 (⟨n, Q⟩ : Scoped)
                  (Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0))
                = Scoped.app M ⟨n, Q⟩ := by
              rw [Scoped.sub0, Scoped.sub_app,
                show Scoped.sub (Scoped.cons (⟨n, Q⟩ : Scoped) Scoped.var)
                    (Scoped.ren Nat.succ M) = M from Scoped.sub0_ren_succ _ M]
              rfl
            rw [hM, e]
          · rw [hcM]
        · exact ⟨Scoped.sub0 (⟨n, Q⟩ : Scoped) P',
            Relation.ReflTransGen.single (Eta.sub_mono hP' _),
            Relation.ReflGen.single (Beta.basis' P' ⟨n, Q⟩)⟩
      · exact ⟨Scoped.sub0 b' (⟨m, P⟩ : Scoped),
          Eta.sub0_congr hb' _,
          Relation.ReflGen.single (Beta.basis' ⟨m, P⟩ b')⟩

/-- One beta step commutes with a sequence of eta steps. -/
theorem beta_etaStar_commute {a b c : Scoped} (h₁ : a —→ b) (h₂ : a —→η* c) :
    ∃ d, b —→η* d ∧ Relation.ReflGen Beta c d := by
  induction h₂ with
  | refl => exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflGen.single h₁⟩
  | @tail c' c _ hstep ih =>
      obtain ⟨d, hd₁, hd₂⟩ := ih
      cases hd₂ with
      | refl =>
          exact ⟨c, Relation.ReflTransGen.tail hd₁ hstep, Relation.ReflGen.refl⟩
      | single hcd =>
          obtain ⟨e, he₁, he₂⟩ := beta_eta_commute hcd c hstep
          exact ⟨e, hd₁.trans he₁, he₂⟩

/-- **Beta and eta reduction commute**: beta-reducing and eta-reducing the same
    term can always be reconciled. -/
theorem betaStar_etaStar_commute {a b c : Scoped} (h₁ : a —→* b) (h₂ : a —→η* c) :
    ∃ d, b —→η* d ∧ c —→* d := by
  induction h₁ with
  | refl => exact ⟨c, h₂, Relation.ReflTransGen.refl⟩
  | @tail b' b _ hstep ih =>
      obtain ⟨d', hd₁, hd₂⟩ := ih
      obtain ⟨d, he₁, he₂⟩ := beta_etaStar_commute hstep hd₁
      exact ⟨d, he₁, hd₂.trans (reflGen_beta_to_betaStar he₂)⟩

-- ====================================================================
-- 2. Beta-eta reduction and its Church-Rosser theorem
-- ====================================================================

/-- A single beta-eta step: either a beta step or an eta step. -/
def BetaEta (a b : Scoped) : Prop := a —→ b ∨ a —→η b

/-- Multi-step beta-eta reduction. -/
abbrev BetaEtaStar : Scoped → Scoped → Prop := Relation.ReflTransGen BetaEta

infix:64 " —→βη* " => BetaEtaStar

theorem BetaStar.to_betaEtaStar {a b : Scoped} (h : a —→* b) : a —→βη* b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Or.inl step)

theorem EtaStar.to_betaEtaStar {a b : Scoped} (h : a —→η* b) : a —→βη* b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Or.inr step)

/-- The auxiliary relation used for the Hindley-Rosen argument: a full beta
    sequence or a full eta sequence. -/
def BetaOrEtaStar (a b : Scoped) : Prop := a —→* b ∨ a —→η* b

theorem BetaOrEtaStar.to_betaEtaStar {a b : Scoped} (h : BetaOrEtaStar a b) : a —→βη* b := by
  rcases h with h | h
  · exact BetaStar.to_betaEtaStar h
  · exact EtaStar.to_betaEtaStar h

theorem betaEtaStar_iff {a b : Scoped} :
    a —→βη* b ↔ Relation.ReflTransGen BetaOrEtaStar a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih =>
        refine Relation.ReflTransGen.tail ih ?_
        rcases step with step | step
        · exact Or.inl (Relation.ReflTransGen.single step)
        · exact Or.inr (Relation.ReflTransGen.single step)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih =>
        refine Relation.ReflTransGen.trans ih ?_
        rcases step with step | step
        · exact BetaStar.to_betaEtaStar step
        · exact EtaStar.to_betaEtaStar step

/-- **The Church-Rosser theorem for beta-eta reduction.** -/
theorem betaeta_church_rosser {a b c : Scoped} (hab : a —→βη* b) (hac : a —→βη* c) :
    ∃ d, b —→βη* d ∧ c —→βη* d := by
  have key : ∀ x y z : Scoped, BetaOrEtaStar x y → BetaOrEtaStar x z →
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
theorem betaeta_confluence {a b c : Scoped} (hab : a —→βη* b) (hac : a —→βη* c) :
    Relation.Join BetaEtaStar b c := by
  obtain ⟨d, hbd, hcd⟩ := betaeta_church_rosser hab hac
  exact ⟨d, hbd, hcd⟩

-- ====================================================================
-- 3. Beta-eta conversion
-- ====================================================================

/-- Beta-eta conversion: the equivalence closure of `—→βη*`. -/
abbrev BetaEtaEq : Scoped → Scoped → Prop := Relation.EqvGen BetaEta

infix:63 " =βη " => BetaEtaEq

theorem betaEtaStar_to_betaEtaEq {a b : Scoped} (h : a —→βη* b) : a =βη b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

theorem BetaEtaEq.symm {a b : Scoped} (h : a =βη b) : b =βη a := Relation.EqvGen.symm _ _ h

theorem BetaEtaEq.trans {a b c : Scoped} (h₁ : a =βη b) (h₂ : b =βη c) : a =βη c :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem BetaEtaEq.refl (a : Scoped) : a =βη a := Relation.EqvGen.refl _

/-- Beta-eta conversion is compatible with abstraction. -/
theorem BetaEtaEq.abs {a b : Scoped} (h : a =βη b) : a.abs =βη b.abs := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.abs hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.abs hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta-eta conversion is compatible with the function part of an application. -/
theorem BetaEtaEq.appr {a b : Scoped} (L : Scoped) (h : a =βη b) : a.app L =βη b.app L := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.appr L hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.appr L hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Beta-eta conversion is compatible with the argument of an application. -/
theorem BetaEtaEq.appl {a b : Scoped} (L : Scoped) (h : a =βη b) : L.app a =βη L.app b := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact Relation.EqvGen.rel _ _ (Or.inl (Beta.appl L hxy))
      · exact Relation.EqvGen.rel _ _ (Or.inr (Eta.appl L hxy))
  | refl x => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Extensionality of beta-eta conversion**: if `M` and `N` agree on a fresh
    variable, they are beta-eta convertible.  (This is the rule `ext`, and it is
    exactly what eta adds to the beta theory.) -/
theorem betaeta_extensionality {M N : Scoped}
    (h : Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0)
      =βη Scoped.app (Scoped.ren Nat.succ N) (Scoped.var 0)) : M =βη N := by
  have hM : (Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0)).abs =βη M :=
    Relation.EqvGen.rel _ _ (Or.inr (Eta.basis M))
  have hN : (Scoped.app (Scoped.ren Nat.succ N) (Scoped.var 0)).abs =βη N :=
    Relation.EqvGen.rel _ _ (Or.inr (Eta.basis N))
  exact (hM.symm.trans h.abs).trans hN

/-- **Beta-eta convertible terms are joinable.** -/
theorem betaeta_eq_join {a b : Scoped} (h : a =βη b) : ∃ d, a —→βη* d ∧ b —→βη* d := by
  induction h with
  | rel x y hxy => exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
  | refl x => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm x y _ ih => obtain ⟨d, h1, h2⟩ := ih; exact ⟨d, h2, h1⟩
  | trans x y z _ _ ih1 ih2 =>
      obtain ⟨d1, hx, hy1⟩ := ih1
      obtain ⟨d2, hy2, hz⟩ := ih2
      obtain ⟨d, hd1, hd2⟩ := betaeta_church_rosser hy1 hy2
      exact ⟨d, Relation.ReflTransGen.trans hx hd1, Relation.ReflTransGen.trans hz hd2⟩

end IwilareNatIsExactScope
