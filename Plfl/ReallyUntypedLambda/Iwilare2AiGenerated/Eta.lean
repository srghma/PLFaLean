-- Eta reduction, for the scope-bounded (`Fin`-indexed) calculus.
--
-- In de Bruijn form the eta rule contracts `ƛ (M #0)` to `M` when the bound
-- index does not occur in `M`, i.e. when the function part is a weakened term:
--
--     ƛ ((wk M) #0)  —→η  M
--
-- This file develops the basic theory of `—→η`: it is stable under renaming and
-- substitution, it is *reflected* by renamings (via a pullback property of
-- index maps), and it is subcommutative, hence confluent
-- (`eta_church_rosser`).
module

public import Plfl.ReallyUntypedLambda.Iwilare2AiGenerated.NormalForms

@[expose] public section

namespace FinScope

open Term

/-! ## 0. Renamings: shape reflection and the pullback property -/

theorem ren_eq_var {n m : Nat} {ρ : Fin n → Fin m} {s : Term n} {i : Fin m}
    (h : ren ρ s = v# i) : ∃ j, s = v# j ∧ ρ j = i := by
  cases s with
  | var j => exact ⟨j, rfl, by simpa using h⟩
  | abs p => exact absurd h (by simp)
  | app a b => exact absurd h (by simp)

theorem ren_eq_abs {n m : Nat} {ρ : Fin n → Fin m} {s : Term n} {u : Term (m + 1)}
    (h : ren ρ s = ƛ u) : ∃ q, s = ƛ q ∧ u = ren (ext ρ) q := by
  cases s with
  | var j => exact absurd h (by simp)
  | abs p => exact ⟨p, rfl, by simpa using h.symm⟩
  | app a b => exact absurd h (by simp)

theorem ren_eq_app {n m : Nat} {ρ : Fin n → Fin m} {s : Term n} {u v : Term m}
    (h : ren ρ s = u ⬝ v) : ∃ a b, s = a ⬝ b ∧ u = ren ρ a ∧ v = ren ρ b := by
  cases s with
  | var j => exact absurd h (by simp)
  | abs p => exact absurd h (by simp)
  | app a b =>
      simp only [ren_app, Term.app.injEq] at h
      exact ⟨a, b, rfl, h.1.symm, h.2.symm⟩

/-- The condition making the square `α ∘ γ = β ∘ δ` a pullback of index maps. -/
def IsRenPullback {n m k l : Nat} (α : Fin n → Fin l) (β : Fin m → Fin l)
    (γ : Fin k → Fin n) (δ : Fin k → Fin m) : Prop :=
  ∀ i j, α i = β j → ∃ p, i = γ p ∧ j = δ p

theorem IsRenPullback.up {n m k l : Nat} {α : Fin n → Fin l} {β : Fin m → Fin l}
    {γ : Fin k → Fin n} {δ : Fin k → Fin m} (h : IsRenPullback α β γ δ) :
    IsRenPullback (ext α) (ext β) (ext γ) (ext δ) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ j =>
          rw [ext_zero, ext_succ] at hij
          exact absurd hij.symm (Fin.succ_ne_zero _)
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          rw [ext_zero, ext_succ] at hij
          exact absurd hij (Fin.succ_ne_zero _)
      | succ j =>
          have h' : α i = β j := Fin.succ_injective _ (by simpa using hij)
          obtain ⟨p, hp₁, hp₂⟩ := h i j h'
          exact ⟨p.succ, by simp [hp₁], by simp [hp₂]⟩

/-- Two renamings of terms that agree factor through the pullback. -/
theorem ren_pullback {n : Nat} (x : Term n) :
    ∀ {m k l : Nat} (z : Term m) (α : Fin n → Fin l) (β : Fin m → Fin l)
      (γ : Fin k → Fin n) (δ : Fin k → Fin m),
      IsRenPullback α β γ δ → ren α x = ren β z → ∃ w : Term k, x = ren γ w ∧ z = ren δ w := by
  induction x with
  | var i =>
      intro m k l z α β γ δ hpb h
      obtain ⟨j, rfl, hj⟩ := ren_eq_var (ρ := β) (s := z) (i := α i) (by rw [← h, ren_var])
      obtain ⟨p, hp₁, hp₂⟩ := hpb i j hj.symm
      exact ⟨v# p, by rw [ren_var, ← hp₁], by rw [ren_var, ← hp₂]⟩
  | abs p ih =>
      intro m k l z α β γ δ hpb h
      rw [ren_abs] at h
      obtain ⟨q, rfl, hq⟩ := ren_eq_abs (ρ := β) (s := z) h.symm
      obtain ⟨w, hw₁, hw₂⟩ := ih q (ext α) (ext β) (ext γ) (ext δ) hpb.up hq
      exact ⟨ƛ w, by rw [ren_abs, ← hw₁], by rw [ren_abs, ← hw₂]⟩
  | app a b iha ihb =>
      intro m k l z α β γ δ hpb h
      rw [ren_app] at h
      obtain ⟨u, v, rfl, hu, hv⟩ := ren_eq_app (ρ := β) (s := z) h.symm
      obtain ⟨w₁, hw₁, hw₁'⟩ := iha u α β γ δ hpb hu
      obtain ⟨w₂, hw₂, hw₂'⟩ := ihb v α β γ δ hpb hv
      exact ⟨w₁ ⬝ w₂, by rw [ren_app, ← hw₁, ← hw₂], by rw [ren_app, ← hw₁', ← hw₂']⟩

theorem ren_succ_inj {n : Nat} {a b : Term n} (h : wk a = wk b) : a = b := by
  have := congrArg (fun t : Term (n + 1) => t [ a ]) h
  simpa using this

/-- The pullback square used by the eta rule under a binder. -/
theorem ext_succ_pullback {n m : Nat} (ρ : Fin n → Fin m) :
    IsRenPullback (ext ρ) Fin.succ Fin.succ ρ := by
  intro i j hij
  induction i using Fin.cases with
  | zero => exact absurd hij.symm (by simp [Fin.succ_ne_zero])
  | succ i =>
      refine ⟨i, rfl, ?_⟩
      exact (Fin.succ_injective _ (by simpa using hij)).symm

/-- Contracting the beta redex `(ƛ (ren (ext succ) Q)) #0` gives back `Q`. -/
theorem betaSubst_var_zero_ren_ext_succ {n : Nat} (Q : Term (n + 1)) :
    (ren (ext Fin.succ) Q) [ (v# 0 : Term (n + 1)) ] = Q := by
  simp only [betaSubst, sub_ren]
  have e : (fun i => (Fin.cons (v# (0 : Fin (n + 1))) Term.var : Fin (n + 2) → Term (n + 1))
      (ext Fin.succ i)) = Term.var := by
    funext i
    induction i using Fin.cases <;> simp
  rw [e, sub_id]

/-! ## 1. Eta reduction -/

/-- Eta reduction: `ƛ (M #0) —→η M` when the bound index does not occur in `M`,
that is, when the function part is a weakened term. -/
inductive Eta : {n : Nat} → Term n → Term n → Prop
  | basis {n : Nat} (M : Term n) : Eta (ƛ (wk M ⬝ v# 0)) M
  | abs {n : Nat} {M N : Term (n + 1)} : Eta M N → Eta (ƛ M) (ƛ N)
  | appL {n : Nat} {M N L : Term n} : Eta M N → Eta (M ⬝ L) (N ⬝ L)
  | appR {n : Nat} {M N L : Term n} : Eta M N → Eta (L ⬝ M) (L ⬝ N)

@[inherit_doc] infix:60 " —→η " => Eta

/-- Multi-step eta reduction. -/
abbrev EtaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Eta

@[inherit_doc] infix:60 " —→η* " => EtaStar

theorem EtaStar.abs {n : Nat} {M N : Term (n + 1)} (h : M —→η* N) : ƛ M —→η* ƛ N := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Eta.abs step)

theorem EtaStar.appL {n : Nat} {M M' L : Term n} (h : M —→η* M') : M ⬝ L —→η* M' ⬝ L := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Eta.appL step)

theorem EtaStar.appR {n : Nat} {M M' L : Term n} (h : M —→η* M') : L ⬝ M —→η* L ⬝ M' := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Eta.appR step)

/-! ## 2. Inversion -/

theorem Eta.var_inv {n : Nat} {i : Fin n} {s : Term n} (h : v# i —→η s) : False := by
  cases h

theorem Eta.abs_inv {n : Nat} {p : Term (n + 1)} {s : Term n} (h : ƛ p —→η s) :
    (∃ M, p = wk M ⬝ v# 0 ∧ s = M) ∨ (∃ p', s = ƛ p' ∧ p —→η p') := by
  cases h with
  | basis => exact Or.inl ⟨_, rfl, rfl⟩
  | abs h' => exact Or.inr ⟨_, rfl, h'⟩

theorem Eta.app_inv {n : Nat} {a b : Term n} {s : Term n} (h : a ⬝ b —→η s) :
    (∃ a', s = a' ⬝ b ∧ a —→η a') ∨ (∃ b', s = a ⬝ b' ∧ b —→η b') := by
  cases h with
  | appL h' => exact Or.inl ⟨_, rfl, h'⟩
  | appR h' => exact Or.inr ⟨_, rfl, h'⟩

/-! ## 3. Stability under renaming and substitution -/

theorem Eta.ren_mono {n : Nat} {a b : Term n} (h : a —→η b) :
    ∀ {m : Nat} (ρ : Fin n → Fin m), ren ρ a —→η ren ρ b := by
  induction h with
  | basis M =>
      intro m ρ
      have e : ren (ext ρ) (wk M) = wk (ren ρ M) := by
        show ren (ext ρ) (ren Fin.succ M) = ren Fin.succ (ren ρ M)
        rw [ren_ren, ren_ren]
        congr 1
      simpa [e] using Eta.basis (ren ρ M)
  | abs _ ih => intro m ρ; exact Eta.abs (ih _)
  | appL _ ih => intro m ρ; exact Eta.appL (ih _)
  | appR _ ih => intro m ρ; exact Eta.appR (ih _)

theorem Eta.sub_mono {n : Nat} {a b : Term n} (h : a —→η b) :
    ∀ {m : Nat} (σ : Fin n → Term m), sub σ a —→η sub σ b := by
  induction h with
  | basis M =>
      intro m σ
      have e : sub (exts σ) (wk M) = wk (sub σ M) := by
        show sub (exts σ) (ren Fin.succ M) = ren Fin.succ (sub σ M)
        rw [sub_ren, ren_sub]
        congr 1
      simpa [e] using Eta.basis (sub σ M)
  | abs _ ih => intro m σ; exact Eta.abs (ih _)
  | appL _ ih => intro m σ; exact Eta.appL (ih _)
  | appR _ ih => intro m σ; exact Eta.appR (ih _)

theorem EtaStar.ren_mono {n m : Nat} {a b : Term n} (h : a —→η* b) (ρ : Fin n → Fin m) :
    ren ρ a —→η* ren ρ b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.ren_mono ρ)

/-- Substituting eta-related terms gives eta-related terms. -/
theorem Eta.sub_congr {n : Nat} (s : Term n) :
    ∀ {m : Nat} {σ τ : Fin n → Term m}, (∀ i, σ i —→η* τ i) → sub σ s —→η* sub τ s := by
  induction s with
  | var i => intro m σ τ h; simpa using h i
  | abs p ih =>
      intro m σ τ h
      refine EtaStar.abs (ih ?_)
      intro i
      induction i using Fin.cases with
      | zero => simpa using Relation.ReflTransGen.refl
      | succ i => simpa using (h i).ren_mono Fin.succ
  | app a b iha ihb =>
      intro m σ τ h
      exact (EtaStar.appL (iha h)).trans (EtaStar.appR (ihb h))

theorem Eta.betaSubst_congr {n : Nat} {N N' : Term n} (h : N —→η N') (M : Term (n + 1)) :
    M [ N ] —→η* M [ N' ] := by
  refine Eta.sub_congr M ?_
  intro i
  induction i using Fin.cases with
  | zero => simpa using Relation.ReflTransGen.single h
  | succ i => simpa using Relation.ReflTransGen.refl

/-! ## 4. Renamings reflect eta and beta steps -/

/-- Renamings reflect eta steps. -/
theorem Eta.ren_reflect_gen {n : Nat} (M : Term n) :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (Y : Term m),
      ren ρ M —→η Y → ∃ M', Y = ren ρ M' ∧ M —→η M' := by
  induction M with
  | var i => intro m ρ Y h; rw [ren_var] at h; exact absurd h (fun h => h.var_inv)
  | abs p ih =>
      intro m ρ Y h
      rw [ren_abs] at h
      rcases h.abs_inv with ⟨Z, hZ, hYZ⟩ | ⟨p', rfl, hp'⟩
      · obtain ⟨a, b, rfl, ha, hb⟩ := ren_eq_app (ρ := ext ρ) (s := p) hZ
        obtain ⟨j, rfl, hj⟩ := ren_eq_var (ρ := ext ρ) (s := b) hb.symm
        have hj0 : j = 0 := by
          induction j using Fin.cases with
          | zero => rfl
          | succ j => exact absurd hj (by simp [Fin.succ_ne_zero])
        subst hj0
        obtain ⟨w, hw₁, hw₂⟩ :=
          ren_pullback a Z (ext ρ) Fin.succ Fin.succ ρ (ext_succ_pullback ρ) ha.symm
        refine ⟨w, by rw [hYZ, hw₂], ?_⟩
        rw [hw₁]
        exact Eta.basis w
      · obtain ⟨q, rfl, hq⟩ := ih (ext ρ) p' hp'
        exact ⟨ƛ q, by rw [ren_abs], Eta.abs hq⟩
  | app a b iha ihb =>
      intro m ρ Y h
      rw [ren_app] at h
      rcases h.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨a₁, rfl, ha₁⟩ := iha ρ a' ha'
        exact ⟨a₁ ⬝ b, by rw [ren_app], Eta.appL ha₁⟩
      · obtain ⟨b₁, rfl, hb₁⟩ := ihb ρ b' hb'
        exact ⟨a ⬝ b₁, by rw [ren_app], Eta.appR hb₁⟩

theorem Eta.ren_reflect {n : Nat} {M : Term n} {Y : Term (n + 1)} (h : wk M —→η Y) :
    ∃ M', Y = wk M' ∧ M —→η M' :=
  Eta.ren_reflect_gen M Fin.succ Y h

/-- Renamings reflect beta steps. -/
theorem Beta.ren_reflect_gen {n : Nat} (M : Term n) :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (Y : Term m),
      ren ρ M —→ Y → ∃ M', Y = ren ρ M' ∧ M —→ M' := by
  induction M with
  | var i => intro m ρ Y h; rw [ren_var] at h; exact absurd h (fun h => h.var_inv)
  | abs p ih =>
      intro m ρ Y h
      rw [ren_abs] at h
      obtain ⟨p', rfl, hp'⟩ := h.abs_inv
      obtain ⟨q, rfl, hq⟩ := ih (ext ρ) _ hp'
      exact ⟨ƛ q, by rw [ren_abs], Beta.abs hq⟩
  | app a b iha ihb =>
      intro m ρ Y h
      rw [ren_app] at h
      rcases h.app_inv with ⟨P, hP, rfl⟩ | ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨q, rfl, hq⟩ := ren_eq_abs (ρ := ρ) (s := a) hP
        subst hq
        refine ⟨q [ b ], ?_, Beta.basis q b⟩
        rw [ren_betaSubst]
      · obtain ⟨a₁, rfl, ha₁⟩ := iha ρ _ ha'
        exact ⟨a₁ ⬝ b, by rw [ren_app], Beta.appL ha₁⟩
      · obtain ⟨b₁, rfl, hb₁⟩ := ihb ρ _ hb'
        exact ⟨a ⬝ b₁, by rw [ren_app], Beta.appR hb₁⟩

theorem Beta.ren_reflect {n m : Nat} {ρ : Fin n → Fin m} {M : Term n} {Y : Term m}
    (h : ren ρ M —→ Y) : ∃ M', Y = ren ρ M' ∧ M —→ M' :=
  Beta.ren_reflect_gen M ρ Y h

/-! ## 5. Eta is subcommutative, hence confluent -/

theorem Eta.reflGen_abs {n : Nat} {x y : Term (n + 1)} (h : Relation.ReflGen Eta x y) :
    Relation.ReflGen Eta (ƛ x) (ƛ y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.abs h)

theorem Eta.reflGen_appL {n : Nat} {x y : Term n} (L : Term n)
    (h : Relation.ReflGen Eta x y) : Relation.ReflGen Eta (x ⬝ L) (y ⬝ L) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.appL h)

theorem Eta.reflGen_appR {n : Nat} {x y : Term n} (L : Term n)
    (h : Relation.ReflGen Eta x y) : Relation.ReflGen Eta (L ⬝ x) (L ⬝ y) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (Eta.appR h)

/-- **Eta reduction is subcommutative**: two eta reducts of a term are joinable
in at most one step each. -/
theorem Eta.subcommutative {n : Nat} {a b : Term n} (h₁ : a —→η b) : ∀ c : Term n, a —→η c →
    ∃ d, Relation.ReflGen Eta b d ∧ Relation.ReflGen Eta c d := by
  induction h₁ with
  | basis M =>
      intro c h₂
      rcases h₂.abs_inv with ⟨M₂, hM₂, rfl⟩ | ⟨p', rfl, hp'⟩
      · simp only [Term.app.injEq] at hM₂
        cases ren_succ_inj hM₂.1
        exact ⟨M, Relation.ReflGen.refl, Relation.ReflGen.refl⟩
      · rcases hp'.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩
        · obtain ⟨M₂, rfl, hM₂⟩ := Eta.ren_reflect ha'
          exact ⟨M₂, Relation.ReflGen.single hM₂, Relation.ReflGen.single (Eta.basis M₂)⟩
        · exact absurd hb' (fun h => h.var_inv)
  | @abs n M N hMN ih =>
      intro c h₂
      rcases h₂.abs_inv with ⟨Z, hZ, rfl⟩ | ⟨p', rfl, hp'⟩
      · subst hZ
        rcases hMN.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', _, hb'⟩
        · obtain ⟨Z', rfl, hZ'⟩ := Eta.ren_reflect ha'
          exact ⟨Z', Relation.ReflGen.single (Eta.basis Z'), Relation.ReflGen.single hZ'⟩
        · exact absurd hb' (fun h => h.var_inv)
      · obtain ⟨d, hd₁, hd₂⟩ := ih p' hp'
        exact ⟨ƛ d, Eta.reflGen_abs hd₁, Eta.reflGen_abs hd₂⟩
  | @appL n M N L hMN ih =>
      intro c h₂
      rcases h₂.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih a' ha'
        exact ⟨d ⬝ L, Eta.reflGen_appL L hd₁, Eta.reflGen_appL L hd₂⟩
      · exact ⟨N ⬝ b', Relation.ReflGen.single (Eta.appR hb'),
          Relation.ReflGen.single (Eta.appL hMN)⟩
  | @appR n M N L hMN ih =>
      intro c h₂
      rcases h₂.app_inv with ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
      · exact ⟨a' ⬝ N, Relation.ReflGen.single (Eta.appL ha'),
          Relation.ReflGen.single (Eta.appR hMN)⟩
      · obtain ⟨d, hd₁, hd₂⟩ := ih b' hb'
        exact ⟨L ⬝ d, Eta.reflGen_appR L hd₁, Eta.reflGen_appR L hd₂⟩

/-- **The Church-Rosser theorem for eta reduction.** -/
theorem eta_church_rosser {n : Nat} {a b c : Term n} (hab : a —→η* b) (hac : a —→η* c) :
    ∃ d, b —→η* d ∧ c —→η* d := by
  obtain ⟨d, hbd, hcd⟩ := Relation.church_rosser
    (r := @Eta n)
    (fun x y z hxy hxz => by
      obtain ⟨d, hd₁, hd₂⟩ := Eta.subcommutative hxy z hxz
      exact ⟨d, hd₁, hd₂.to_reflTransGen⟩)
    hab hac
  exact ⟨d, hbd, hcd⟩

end FinScope
