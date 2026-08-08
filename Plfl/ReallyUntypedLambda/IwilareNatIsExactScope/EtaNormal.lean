-- Eta normal forms.
--
-- Every eta step strictly decreases the size of a term, so eta reduction is
-- *strongly normalizing*; together with confluence (`eta_church_rosser`) this
-- gives existence and uniqueness of eta normal forms.  The same confluence
-- argument, run for the union `—→βη*`, gives uniqueness of beta-eta normal
-- forms and the consistency of beta-eta conversion.
module

public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.BetaEta
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.DecEq
public import Plfl.ReallyUntypedLambda.IwilareNatIsExactScope.NormalForms

@[expose] public section

namespace IwilareNatIsExactScope

-- ====================================================================
-- 1. The size of a term
-- ====================================================================

namespace Term

/-- The number of nodes of a term tree. -/
def size : {n : Nat} → Term n → Nat
  | _, var _ => 1
  | _, abs t => t.size + 1
  | _, app a b => a.size + b.size + 1

end Term

namespace Scoped

/-- The number of nodes of an existentially scoped term. -/
def size (s : Scoped) : Nat := s.2.size

@[simp] theorem size_var (i : Nat) : (var i).size = 1 := rfl
@[simp] theorem size_abs (s : Scoped) : (abs s).size = s.size + 1 := rfl
@[simp] theorem size_app (s t : Scoped) : (app s t).size = s.size + t.size + 1 := rfl

/-- Renaming does not change the size of a term. -/
@[simp] theorem size_ren (ρ : Nat → Nat) (s : Scoped) : (ren ρ s).size = s.size := by
  induction s using Scoped.ind generalizing ρ with
  | var i => rfl
  | abs p ih => rw [ren_abs, size_abs, size_abs, ih]
  | app a b iha ihb => rw [ren_app, size_app, size_app, iha, ihb]

end Scoped

-- ====================================================================
-- 2. Eta reduction is strongly normalizing
-- ====================================================================

/-- An eta step strictly decreases the size. -/
theorem Eta.size_lt {a b : Scoped} (h : a —→η b) : b.size < a.size := by
  induction h with
  | basis M =>
      simp only [Scoped.size_abs, Scoped.size_app, Scoped.size_var, Scoped.size_ren]
      omega
  | abs _ ih => simpa using ih
  | appr L _ ih => simp only [Scoped.size_app]; omega
  | appl L _ ih => simp only [Scoped.size_app]; omega

/-- **Eta reduction is strongly normalizing**: there is no infinite eta
    reduction sequence. -/
theorem eta_strongly_normalizing : WellFounded (fun b a : Scoped => a —→η b) :=
  Subrelation.wf (fun h => Eta.size_lt h) (InvImage.wf Scoped.size Nat.lt_wfRel.wf)

/-- A term is in eta normal form when no eta step applies to it. -/
def EtaNormal (M : Scoped) : Prop := ∀ N, ¬ M —→η N

/-- Being the body `(ren succ M) #0` of an eta redex is decidable: the only
    possible `M` is `sub0 #0` of the function part, so one equality test settles
    it.  (Deciding this constructively is what keeps `eta_progress` -- and with
    it the existence of eta normal forms -- free of `Classical.choice`.) -/
theorem etaRedexBody_or_not (p : Scoped) :
    (∃ M, p = Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0))
    ∨ ¬ (∃ M, p = Scoped.app (Scoped.ren Nat.succ M) (Scoped.var 0)) := by
  rcases Scoped.cases' p with ⟨i, rfl⟩ | ⟨q, rfl⟩ | ⟨u, v, rfl⟩
  · exact Or.inr (fun ⟨_, hM⟩ => Scoped.var_ne_app hM)
  · exact Or.inr (fun ⟨_, hM⟩ => Scoped.abs_ne_app hM)
  · by_cases h : Scoped.app u v
        = Scoped.app (Scoped.ren Nat.succ (Scoped.sub0 (Scoped.var 0) u)) (Scoped.var 0)
    · exact Or.inl ⟨_, h⟩
    · refine Or.inr (fun ⟨M, hM⟩ => h ?_)
      obtain ⟨hu, hv⟩ := Scoped.app_eq_app.mp hM
      rw [hu, hv, Scoped.sub0_ren_succ]

/-- **Progress for eta**: every term either admits an eta step or is eta
    normal.  Proved by structural recursion, with no classical case split. -/
theorem eta_progress (a : Scoped) : (∃ b, a —→η b) ∨ EtaNormal a := by
  induction a using Scoped.ind with
  | var i => exact Or.inr (fun _ h => h.var_inv (i := i) rfl)
  | abs p ih =>
      rcases ih with ⟨b, hb⟩ | hp
      · exact Or.inl ⟨Scoped.abs b, Eta.abs hb⟩
      · rcases etaRedexBody_or_not p with ⟨M, rfl⟩ | hnr
        · exact Or.inl ⟨M, Eta.basis M⟩
        · refine Or.inr (fun N hN => ?_)
          rcases hN.abs_inv' with ⟨M', hM', rfl⟩ | ⟨p', rfl, hp'⟩
          · exact hnr ⟨_, hM'⟩
          · exact hp _ hp'
  | app u v ihu ihv =>
      rcases ihu with ⟨u', hu⟩ | hnu
      · exact Or.inl ⟨Scoped.app u' v, Eta.appr v hu⟩
      · rcases ihv with ⟨v', hv⟩ | hnv
        · exact Or.inl ⟨Scoped.app u v', Eta.appl u hv⟩
        · refine Or.inr (fun N hN => ?_)
          rcases hN.app_inv' with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
          · exact hnu _ ha'
          · exact hnv _ hb'

/-- **Existence of eta normal forms**: every term eta-reduces to an eta normal
    form. -/
theorem eta_normal_form_exists (a : Scoped) : ∃ n, a —→η* n ∧ EtaNormal n := by
  induction a using WellFounded.induction eta_strongly_normalizing with
  | _ a ih =>
      rcases eta_progress a with ⟨b, hb⟩ | h
      · obtain ⟨n, hn₁, hn₂⟩ := ih b hb
        exact ⟨n, Relation.ReflTransGen.head hb hn₁, hn₂⟩
      · exact ⟨a, Relation.ReflTransGen.refl, h⟩

/-- An eta normal term eta-reduces only to itself. -/
theorem EtaNormal.etaStar_eq {M N : Scoped} (h : EtaNormal M) (hMN : M —→η* N) : N = M := by
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of eta normal forms.** -/
theorem eta_normal_form_unique {a b c : Scoped} (hb : a —→η* b) (hc : a —→η* c)
    (hnb : EtaNormal b) (hnc : EtaNormal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := eta_church_rosser hb hc
  rw [← hnb.etaStar_eq hbd, ← hnc.etaStar_eq hcd]

-- ====================================================================
-- 3. Beta-eta normal forms
-- ====================================================================

/-- A term is in beta-eta normal form when neither a beta nor an eta step
    applies to it. -/
def BetaEtaNormal (M : Scoped) : Prop := ∀ N, ¬ BetaEta M N

theorem BetaEtaNormal.normal {M : Scoped} (h : BetaEtaNormal M) : Normal M :=
  fun N hN => h N (Or.inl hN)

theorem BetaEtaNormal.etaNormal {M : Scoped} (h : BetaEtaNormal M) : EtaNormal M :=
  fun N hN => h N (Or.inr hN)

theorem BetaEtaNormal.of {M : Scoped} (hb : Normal M) (he : EtaNormal M) : BetaEtaNormal M := by
  intro N hN
  rcases hN with hN | hN
  · exact hb N hN
  · exact he N hN

/-- A beta-eta normal term beta-eta reduces only to itself. -/
theorem BetaEtaNormal.betaEtaStar_eq {M N : Scoped} (h : BetaEtaNormal M) (hMN : M —→βη* N) :
    N = M := by
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of beta-eta normal forms.** -/
theorem betaeta_normal_form_unique {a b c : Scoped} (hb : a —→βη* b) (hc : a —→βη* c)
    (hnb : BetaEtaNormal b) (hnc : BetaEtaNormal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := betaeta_church_rosser hb hc
  rw [← hnb.betaEtaStar_eq hbd, ← hnc.betaEtaStar_eq hcd]

/-- Two convertible beta-eta normal terms are equal. -/
theorem betaetaEq_normal_eq {a b : Scoped} (h : a =βη b)
    (hna : BetaEtaNormal a) (hnb : BetaEtaNormal b) : a = b := by
  obtain ⟨d, had, hbd⟩ := betaeta_eq_join h
  rw [← hna.betaEtaStar_eq had, ← hnb.betaEtaStar_eq hbd]

-- ====================================================================
-- 4. Consistency of beta-eta conversion
-- ====================================================================

theorem etaNormal_ctrue : EtaNormal ctrue := by
  intro N hN
  rcases hN.abs_inv' with ⟨M, hM, _⟩ | ⟨p', _, hp'⟩
  · exact absurd hM Scoped.abs_ne_app
  · rcases hp'.abs_inv' with ⟨M, hM, _⟩ | ⟨p'', _, hp''⟩
    · exact absurd hM Scoped.var_ne_app
    · exact absurd rfl (hp''.var_inv (i := 1))

theorem etaNormal_cfalse : EtaNormal cfalse := by
  intro N hN
  rcases hN.abs_inv' with ⟨M, hM, _⟩ | ⟨p', _, hp'⟩
  · exact absurd hM Scoped.abs_ne_app
  · rcases hp'.abs_inv' with ⟨M, hM, _⟩ | ⟨p'', _, hp''⟩
    · exact absurd hM Scoped.var_ne_app
    · exact absurd rfl (hp''.var_inv (i := 0))

theorem betaEtaNormal_ctrue : BetaEtaNormal ctrue :=
  BetaEtaNormal.of normal_ctrue etaNormal_ctrue

theorem betaEtaNormal_cfalse : BetaEtaNormal cfalse :=
  BetaEtaNormal.of normal_cfalse etaNormal_cfalse

/-- **Consistency of the beta-eta theory**: `true` and `false` are not
    beta-eta convertible, so beta-eta conversion does not identify all terms. -/
theorem ctrue_not_betaetaEq_cfalse : ¬ (ctrue =βη cfalse) := fun h =>
  ctrue_ne_cfalse (betaetaEq_normal_eq h betaEtaNormal_ctrue betaEtaNormal_cfalse)

end IwilareNatIsExactScope
