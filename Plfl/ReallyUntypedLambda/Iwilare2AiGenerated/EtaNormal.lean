-- Eta normal forms, for the scope-bounded (`Fin`-indexed) calculus.
--
-- Every eta step strictly decreases the size of a term, so eta reduction is
-- *strongly normalizing*; together with confluence (`eta_church_rosser`) this
-- gives existence and uniqueness of eta normal forms.  The same confluence
-- argument, run for the union `—→βη*`, gives uniqueness of beta-eta normal
-- forms and the consistency of beta-eta conversion.
--
-- The decision procedure `etaRedexBody_or_not` is where `deriving DecidableEq`
-- pays off: in the exact-scope development the structural equality test on
-- terms had to be written and verified by hand.
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.BetaEta

@[expose] public section

namespace FinScope

open Term

/-! ## 1. The size of a term -/

/-- The number of nodes of a term tree. -/
def Term.size : {n : Nat} → Term n → Nat
  | _, .var _ => 1
  | _, .abs t => t.size + 1
  | _, .app a b => a.size + b.size + 1

@[simp] theorem Term.size_var {n : Nat} (i : Fin n) : (v# i).size = 1 := rfl
@[simp] theorem Term.size_abs {n : Nat} (t : Term (n + 1)) : (ƛ t).size = t.size + 1 := rfl
@[simp] theorem Term.size_app {n : Nat} (a b : Term n) :
    (a ⬝ b).size = a.size + b.size + 1 := rfl

/-- Renaming does not change the size of a term. -/
@[simp] theorem Term.size_ren {n : Nat} (t : Term n) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), (ren ρ t).size = t.size := by
  induction t with
  | var i => intro m ρ; rfl
  | abs p ih => intro m ρ; rw [ren_abs, size_abs, size_abs, ih]
  | app a b iha ihb => intro m ρ; rw [ren_app, size_app, size_app, iha, ihb]

/-! ## 2. Eta reduction is strongly normalizing -/

/-- An eta step strictly decreases the size. -/
theorem Eta.size_lt {n : Nat} {a b : Term n} (h : a —→η b) : b.size < a.size := by
  induction h with
  | basis M => simp only [Term.size_abs, Term.size_app, Term.size_var, Term.size_ren]; omega
  | abs _ ih => simpa using ih
  | appL _ ih => simp only [Term.size_app]; omega
  | appR _ ih => simp only [Term.size_app]; omega

/-- **Eta reduction is strongly normalizing**: there is no infinite eta
reduction sequence. -/
theorem eta_strongly_normalizing {n : Nat} :
    WellFounded (fun b a : Term n => a —→η b) :=
  Subrelation.wf (fun h => Eta.size_lt h) (InvImage.wf Term.size Nat.lt_wfRel.wf)

/-- A term is in eta normal form when no eta step applies to it. -/
def EtaNormal {n : Nat} (M : Term n) : Prop := ∀ N, ¬ M —→η N

/-- A canonical inhabitant of every scope, used only as a dummy argument. -/
def Term.dummy {n : Nat} : Term n := ƛ (v# 0)

/-- Being the body `(wk M) #0` of an eta redex is decidable: the only possible
`M` is obtained by substituting into the function part, so one equality test
settles it — and the equality test is the derived `DecidableEq`. -/
theorem etaRedexBody_or_not {n : Nat} (p : Term (n + 1)) :
    (∃ M : Term n, p = wk M ⬝ v# 0) ∨ ¬ (∃ M : Term n, p = wk M ⬝ v# 0) := by
  cases p with
  | var i => exact Or.inr (fun ⟨_, hM⟩ => absurd hM (by simp))
  | abs q => exact Or.inr (fun ⟨_, hM⟩ => absurd hM (by simp))
  | app u v =>
      by_cases h : u ⬝ v = wk (u [ (Term.dummy : Term n) ]) ⬝ v# 0
      · exact Or.inl ⟨_, h⟩
      · refine Or.inr (fun ⟨M, hM⟩ => h ?_)
        simp only [Term.app.injEq] at hM
        rw [hM.1, hM.2, betaSubst_wk]

/-- **Progress for eta**: every term either admits an eta step or is eta
normal.  Proved by structural recursion, with no classical case split. -/
theorem eta_progress {n : Nat} (a : Term n) : (∃ b, a —→η b) ∨ EtaNormal a := by
  induction a with
  | var i => exact Or.inr (fun _ h => h.var_inv)
  | abs p ih =>
      rcases ih with ⟨b, hb⟩ | hp
      · exact Or.inl ⟨ƛ b, Eta.abs hb⟩
      · rcases etaRedexBody_or_not p with ⟨M, rfl⟩ | hnr
        · exact Or.inl ⟨M, Eta.basis M⟩
        · refine Or.inr (fun N hN => ?_)
          rcases hN.abs_inv with ⟨M', hM', rfl⟩ | ⟨p', rfl, hp'⟩
          · exact hnr ⟨_, hM'⟩
          · exact hp _ hp'
  | app u v ihu ihv =>
      rcases ihu with ⟨u', hu⟩ | hnu
      · exact Or.inl ⟨u' ⬝ v, Eta.appL hu⟩
      · rcases ihv with ⟨v', hv⟩ | hnv
        · exact Or.inl ⟨u ⬝ v', Eta.appR hv⟩
        · refine Or.inr (fun N hN => ?_)
          rcases hN.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
          · exact hnu _ ha'
          · exact hnv _ hb'

/-- **Existence of eta normal forms**: every term eta-reduces to an eta normal
form. -/
theorem eta_normal_form_exists {n : Nat} (a : Term n) : ∃ b, a —→η* b ∧ EtaNormal b := by
  induction a using WellFounded.induction eta_strongly_normalizing with
  | _ a ih =>
      rcases eta_progress a with ⟨b, hb⟩ | h
      · obtain ⟨c, hc₁, hc₂⟩ := ih b hb
        exact ⟨c, Relation.ReflTransGen.head hb hc₁, hc₂⟩
      · exact ⟨a, .refl, h⟩

/-- An eta normal term eta-reduces only to itself. -/
theorem EtaNormal.etaStar_eq {n : Nat} {M N : Term n} (h : EtaNormal M) (hMN : M —→η* N) :
    N = M := by
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of eta normal forms.** -/
theorem eta_normal_form_unique {n : Nat} {a b c : Term n} (hb : a —→η* b) (hc : a —→η* c)
    (hnb : EtaNormal b) (hnc : EtaNormal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := eta_church_rosser hb hc
  rw [← hnb.etaStar_eq hbd, ← hnc.etaStar_eq hcd]

/-! ## 3. Beta-eta normal forms -/

/-- A term is in beta-eta normal form when neither a beta nor an eta step
applies to it. -/
def BetaEtaNormal {n : Nat} (M : Term n) : Prop := ∀ N, ¬ BetaEta M N

theorem BetaEtaNormal.normal {n : Nat} {M : Term n} (h : BetaEtaNormal M) : Normal M :=
  fun N hN => h N (Or.inl hN)

theorem BetaEtaNormal.etaNormal {n : Nat} {M : Term n} (h : BetaEtaNormal M) : EtaNormal M :=
  fun N hN => h N (Or.inr hN)

theorem BetaEtaNormal.of {n : Nat} {M : Term n} (hb : Normal M) (he : EtaNormal M) :
    BetaEtaNormal M := by
  intro N hN
  rcases hN with hN | hN
  · exact hb N hN
  · exact he N hN

/-- A beta-eta normal term beta-eta reduces only to itself. -/
theorem BetaEtaNormal.betaEtaStar_eq {n : Nat} {M N : Term n} (h : BetaEtaNormal M)
    (hMN : M —→βη* N) : N = M := by
  induction hMN with
  | refl => rfl
  | tail _ step ih => exact absurd (ih ▸ step) (h _)

/-- **Uniqueness of beta-eta normal forms.** -/
theorem betaeta_normal_form_unique {n : Nat} {a b c : Term n} (hb : a —→βη* b) (hc : a —→βη* c)
    (hnb : BetaEtaNormal b) (hnc : BetaEtaNormal c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := betaeta_church_rosser hb hc
  rw [← hnb.betaEtaStar_eq hbd, ← hnc.betaEtaStar_eq hcd]

/-- Two convertible beta-eta normal terms are equal. -/
theorem betaetaEq_normal_eq {n : Nat} {a b : Term n} (h : a =βη b)
    (hna : BetaEtaNormal a) (hnb : BetaEtaNormal b) : a = b := by
  obtain ⟨d, had, hbd⟩ := betaeta_eq_join h
  rw [← hna.betaEtaStar_eq had, ← hnb.betaEtaStar_eq hbd]

/-! ## 4. Consistency of beta-eta conversion -/

theorem etaNormal_ctrue {n : Nat} : EtaNormal (ctrue : Term n) := by
  intro N hN
  rcases hN.abs_inv with ⟨M, hM, _⟩ | ⟨p', _, hp'⟩
  · exact absurd hM (by simp)
  · rcases hp'.abs_inv with ⟨M, hM, _⟩ | ⟨p'', _, hp''⟩
    · exact absurd hM (by simp)
    · exact hp''.var_inv

theorem etaNormal_cfalse {n : Nat} : EtaNormal (cfalse : Term n) := by
  intro N hN
  rcases hN.abs_inv with ⟨M, hM, _⟩ | ⟨p', _, hp'⟩
  · exact absurd hM (by simp)
  · rcases hp'.abs_inv with ⟨M, hM, _⟩ | ⟨p'', _, hp''⟩
    · exact absurd hM (by simp)
    · exact hp''.var_inv

theorem betaEtaNormal_ctrue {n : Nat} : BetaEtaNormal (ctrue : Term n) :=
  BetaEtaNormal.of normal_ctrue etaNormal_ctrue

theorem betaEtaNormal_cfalse {n : Nat} : BetaEtaNormal (cfalse : Term n) :=
  BetaEtaNormal.of normal_cfalse etaNormal_cfalse

/-- **Consistency of the beta-eta theory**: `true` and `false` are not
beta-eta convertible, so beta-eta conversion does not identify all terms. -/
theorem ctrue_not_betaetaEq_cfalse {n : Nat} : ¬ ((ctrue : Term n) =βη cfalse) := fun h =>
  ctrue_ne_cfalse (betaetaEq_normal_eq h betaEtaNormal_ctrue betaEtaNormal_cfalse)

end FinScope
