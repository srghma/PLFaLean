module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.DeBruijn

@[expose] public section

/-!
# β-reduction and parallel reduction, choice-free

Single-step β-reduction `—→`, its reflexive-transitive closure `—→*`
(`Relation.ReflTransGen`), β-conversion `≡β` (`Relation.EqvGen`) and parallel
reduction `⇉`, together with the fact that `—→*` and `⇉*` coincide.
-/

namespace IwilareFinsetNOfFreeIsExact

set_option hygiene false in
set_option quotPrecheck false in
/-- Single-step β-reduction. -/
infixl:65 "—→" => Beta -- the std → and -> have binding power 25

/-- Standard single-step β-reduction. -/
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

@[inherit_doc] infixl:65 "—→-ξₗ" => Beta.appr
@[inherit_doc] infixl:65 "—→-ξᵣ" => Beta.appl
@[inherit_doc] prefix:65 "—→-ƛ " => Beta.abs
@[inherit_doc] infixl:65 "—→-β"  => Beta.basis

theorem step_test {n : Nat} {t1 t2 : Term n} (h : t1 —→ t2) : True :=
  match h with
  | _L —→-ξₗ _h' => True.intro
  | _L —→-ξᵣ _h' => True.intro
  | —→-ƛ _h'     => True.intro
  | _M —→-β _N   => True.intro

/-- Many-step β-reduction. -/
abbrev BetaStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen Beta

@[inherit_doc] infix:64 " —→* " => BetaStar -- in the original repo: —↠

set_option hygiene false in
set_option quotPrecheck false in
/-- Parallel β-reduction. -/
infixl:65 "⇉" => BetaPar

/-- Parallel β-reduction: contract any set of redexes present in the term. -/
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

@[inherit_doc] infixl:65 "⇉-c" => BetaPar.var
@[inherit_doc] prefix:65 "⇉-ƛ " => BetaPar.abs
@[inherit_doc] infixl:65 "⇉-ξ" => BetaPar.app
@[inherit_doc] infixl:65 "⇉-β"  => BetaPar.subst

/-- Parallel reduction is reflexive. -/
instance : Std.Refl (BetaPar (n := n)) where
  refl N := by
    induction N with
    | var i => exact BetaPar.var i
    | abs M ih => exact BetaPar.abs ih
    | app M N ihM ihN => exact BetaPar.app ihM ihN

/-- Many-step parallel reduction. -/
abbrev BetaParStar {n : Nat} : Term n → Term n → Prop := Relation.ReflTransGen BetaPar

@[inherit_doc] infix:64 " ⇉* " => BetaParStar

/-- Single-step β-reduction implies parallel reduction. -/
theorem beta_to_betapar {n : Nat} {M N : Term n} (h : M —→ N) : M ⇉ N := by
  induction h with
  | appl L _ ih => exact BetaPar.app (Std.Refl.refl L) ih
  | appr L _ ih => exact BetaPar.app ih (Std.Refl.refl L)
  | abs _ ih => exact BetaPar.abs ih
  | basis M N => exact BetaPar.subst (Std.Refl.refl M) (Std.Refl.refl N)

/-! ### Congruence rules for many-step reduction -/

theorem beta_star_abs {n : Nat} {M N : Term (n + 1)} (h : M —→* N) : ƛ M —→* ƛ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.abs step)

theorem beta_star_appr {n : Nat} {M M' : Term n} (N : Term n) (h : M —→* M') :
    M ⬝ N —→* M' ⬝ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appr N step)

theorem beta_star_appl {n : Nat} {N N' : Term n} (M : Term n) (h : N —→* N') :
    M ⬝ N —→* M ⬝ N' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (Beta.appl M step)

theorem beta_star_app {n : Nat} {M M' N N' : Term n} (hM : M —→* M') (hN : N —→* N') :
    M ⬝ N —→* M' ⬝ N' :=
  (beta_star_appr N hM).trans (beta_star_appl M' hN)

/-! ### The two closures agree -/

/-- Parallel reduction implies many-step β-reduction. -/
theorem betapar_to_betastar {n : Nat} {M N : Term n} (h : M ⇉ N) : M —→* N := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | abs _ ih => exact beta_star_abs ih
  | app _ _ ihM ihN => exact beta_star_app ihM ihN
  | subst _ _ ihM ihN =>
    exact Relation.ReflTransGen.tail (beta_star_app (beta_star_abs ihM) ihN) (Beta.basis _ _)

/-- The reflexive-transitive closures of β-reduction and of parallel reduction
coincide. -/
theorem betapar_star_eq_betastar {n : Nat} {M N : Term n} : M ⇉* N ↔ M —→* N := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.trans ih (betapar_to_betastar step)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step ih => exact Relation.ReflTransGen.tail ih (beta_to_betapar step)

/-- β-conversion: the equivalence relation generated by β-reduction. -/
abbrev BetaEq {n : Nat} : Term n → Term n → Prop := Relation.EqvGen (Beta (n := n))

@[inherit_doc] infix:64 " ≡β " => BetaEq

/-- Joinability of two terms by β-reduction. -/
abbrev BetaJoin {n : Nat} : Term n → Term n → Prop := Relation.Join (BetaStar (n := n))

/-- At most one β-step. -/
abbrev BetaRefl {n : Nat} : Term n → Term n → Prop := Relation.ReflGen (Beta (n := n))

@[inherit_doc] infix:65 " —→≤1 " => BetaRefl

end IwilareFinsetNOfFreeIsExact
