module

-- https://plfa.github.io/Untyped/

import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Basic

@[expose] public section

namespace Untyped

-- https://plfa.github.io/Untyped/#terms-and-the-scoping-judgment
inductive Term : Nat → Type
  | var : ∀ {n : Nat}, Fin n → Term n
  | abs : ∀ {n : Nat}, Term (n + 1) → Term n
  | app : ∀ {n : Nat}, Term n → Term n → Term n
  deriving DecidableEq, Repr

namespace Notation
  open Term

  scoped prefix:50 "ƛ " => abs
  scoped infixr:min " $ " => app
  scoped infixl:70 " ⬝ " => app
  scoped prefix:90 "‵" => var

  -- https://plfa.github.io/Untyped/#writing-variables-as-numerals
  scoped macro "#" n:term:90 : term => `(‵ $n)
end Notation

open Notation

namespace Term
  -- https://plfa.github.io/Untyped/#test-examples
  abbrev twoC : Term n := ƛ ƛ (#1 $ #1 $ #0)
  abbrev fourC : Term n := ƛ ƛ (#1 $ #1 $ #1 $ #1 $ #0)
  abbrev addC : Term n := ƛ ƛ ƛ ƛ (#3 ⬝ #1 $ #2 ⬝ #1 ⬝ #0)
  abbrev fourC' : Term n := addC ⬝ twoC ⬝ twoC

  def church (k : ℕ) : Term n := ƛ ƛ applyN k
  where
    applyN
    | 0 => #0
    | k + 1 => #1 ⬝ applyN k
end Term

namespace Subst
  -- https://plfa.github.io/Untyped/#renaming
  /--
  If one context maps to another,
  the mapping holds after adding a new variable to both contexts.
  -/
  def ext (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
    Fin.cases 0 (Fin.succ ∘ ρ)

  /--
  Renaming variables in a term.
  -/
  def rename (ρ : Fin n → Fin m) : Term n → Term m
    | ‵ x => ‵ (ρ x)
    | ƛ t => ƛ (rename (ext ρ) t)
    | l ⬝ m => rename ρ l ⬝ rename ρ m

  abbrev shift : Term n → Term (n + 1) := rename Fin.succ

  -- https://plfa.github.io/Untyped/#simultaneous-substitution
  def exts (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
    Fin.cases (‵ 0) (shift ∘ σ)

  /--
  General substitution for multiple free variables.
  -/
  def subst (σ : Fin n → Term m) : Term n → Term m
    | ‵ i => σ i
    | ƛ t => ƛ (subst (exts σ) t)
    | l ⬝ m => subst σ l ⬝ subst σ m

  -- https://plfa.github.io/Untyped/#single-substitution
  abbrev subst₁σ (v : Term n) : Fin (n + 1) → Term n :=
    Fin.cases v Term.var

  /--
  Substitution for one free variable `v` in the term `t`.
  -/
  abbrev subst₁ (v : Term n) (t : Term (n + 1)) : Term n :=
    subst (subst₁σ v) t
end Subst

open Subst

namespace Notation
  scoped notation:90 n "⟦" m "⟧" => subst₁ m n
  scoped macro " ⟪" σ:term "⟫ " : term => `(subst $σ)
end Notation

open Notation

-- https://plfa.github.io/Untyped/#neutral-and-normal-terms
mutual
  inductive Neutral : Term n → Type
  | var : (x : Fin n) → Neutral (‵ x)
  | ap : Neutral l → Normal m → Neutral (l ⬝ m)
  deriving Repr

  inductive Normal : Term n → Type
  | norm : Neutral m → Normal m
  | lam : Normal t → Normal (ƛ t)
  deriving Repr
end

namespace Notation
  open Neutral Normal

  scoped prefix:60 " ′" => Normal.norm
  scoped macro "#′" n:term:90 : term => `(var $n)

  scoped prefix:50 "ƛₙ " => lam
  scoped infixr:min " $ₙ " => ap
  scoped infixl:70 " ⬝ₙ " => ap
  scoped prefix:90 "‵ₙ" => var
end Notation

open Notation

example : Normal (Term.twoC (n := 0)) := ƛₙ ƛₙ (′#′1 ⬝ₙ (′#′1 ⬝ₙ (′#′0)))

-- https://plfa.github.io/Untyped/#reduction-step
/--
`Reduce t t'` says that `t` reduces to `t'` via a given step.
-/
inductive Reduce : Term n → Term n → Prop where
| lamβ : Reduce ((ƛ t) ⬝ v) (t⟦v⟧)
| lamζ : Reduce t t' → Reduce (ƛ t) (ƛ t')
| apξ₁ : Reduce l l' → Reduce (l ⬝ m) (l' ⬝ m)
| apξ₂ : Reduce m m' → Reduce (v ⬝ m) (v ⬝ m')

inductive Reduce' : Term n → Term n → Type where
| lamβ : Normal (ƛ t) → Normal v → Reduce' ((ƛ t) ⬝ v) (t⟦v⟧)
| lamζ : Reduce' t t' → Reduce' (ƛ t) (ƛ t')
| apξ₁ : Reduce' l l' → Reduce' (l ⬝ m) (l' ⬝ m)
| apξ₂ : Normal v → Reduce' m m' → Reduce' (v ⬝ m) (v ⬝ m')

inductive Reduce'' : Term n → Term n → Type where
| lamβ : Reduce'' ((ƛ t) ⬝ (ƛ v)) (t⟦ƛ v⟧)
| apξ₁ : Reduce'' l l' → Reduce'' (l ⬝ m) (l' ⬝ m)
| apξ₂ : Reduce'' m m' → Reduce'' (v ⬝ m) (v ⬝ m')

abbrev Reduce.Clos {n} := Relation.ReflTransGen (α := Term n) Reduce

namespace Notation
  -- https://plfa.github.io/DeBruijn/#reflexive-and-transitive-closure
  scoped infix:40 " —→ " => Reduce
  scoped infix:20 " —↠ " => Reduce.Clos
end Notation

open Notation

namespace Reduce.Clos
  @[refl] abbrev refl : m —↠ m := Relation.ReflTransGen.refl
  abbrev tail : (m —↠ n) → (n —→ n') → (m —↠ n') := Relation.ReflTransGen.tail
  abbrev head : (m —→ n) → (n —↠ n') → (m —↠ n') := Relation.ReflTransGen.head
  abbrev single : (m —→ n) → (m —↠ n) := Relation.ReflTransGen.single

  instance : Coe (m —→ n) (m —↠ n) where coe r := Relation.ReflTransGen.single r

  instance : Trans (α := Term n) Clos Clos Clos where trans := Relation.ReflTransGen.trans
  instance : Trans (α := Term n) Clos Reduce Clos where trans c r := Relation.ReflTransGen.tail c r
  instance : Trans (α := Term n) Reduce Reduce Clos where trans r r' := Relation.ReflTransGen.tail (Relation.ReflTransGen.single r) r'
  instance : Trans (α := Term n) Reduce Clos Clos where trans r c := Relation.ReflTransGen.head r c
end Reduce.Clos

namespace Reduce
  -- https://plfa.github.io/Untyped/#example-reduction-sequence
  open Term

  theorem test_shift_twoC : shift (shift (shift (twoC (n := 0)))) = twoC (n := 3) := rfl

  example : fourC' (n := 0) —↠ fourC := calc addC ⬝ twoC ⬝ twoC
    _ —→ (ƛ ƛ ƛ (twoC ⬝ #1 $ (#2 ⬝ #1 ⬝ #0))) ⬝ twoC := by
      apply apξ₁
      exact lamβ
    _ —→ ƛ ƛ (twoC ⬝ #1 $ (twoC ⬝ #1 ⬝ #0)) := by exact lamβ
    _ —→ ƛ ƛ ((ƛ (#2 $ #2 $ #0)) $ (twoC ⬝ #1 ⬝ #0)) := by apply_rules [lamζ, apξ₁, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ (twoC ⬝ #1 ⬝ #0)) := by apply_rules [lamζ, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ ((ƛ (#2 $ #2 $ #0)) ⬝ #0)) := by apply_rules [lamζ, apξ₁, apξ₂, lamβ]
    _ —→ ƛ ƛ (#1 $ #1 $ #1 $ #1 $ #0) := by apply_rules [lamζ, apξ₁, apξ₂, lamβ]
end Reduce

-- https://plfa.github.io/Untyped/#progress
inductive Progress (m : Term n) where
| step : (m —→ n') → Progress m
| done : Normal m → Progress m

namespace Progress

def progress : (m : Term n) → Progress m
  | ‵ x => .done (′ ‵ₙ x)
  | ƛ t =>
    match progress t with
    | .done t' => .done (ƛₙ t')
    | .step r => .step (Reduce.lamζ r)
  | ‵ x ⬝ m =>
    match progress m with
    | .done m' => .done (′ ‵ₙ x ⬝ₙ m')
    | .step r => .step (Reduce.apξ₂ (v := ‵ x) r)
  | (ƛ t) ⬝ m => .step Reduce.lamβ
  | (l' ⬝ l'') ⬝ m =>
    match progress (l' ⬝ l'') with
    | .step r => .step (Reduce.apξ₁ (m := m) r)
    | .done (′neutral_l) =>
      match progress m with
      | .done m' => .done (′neutral_l ⬝ₙ m')
      | .step r => .step (Reduce.apξ₂ (v := l' ⬝ l'') r)
termination_by m => sizeOf m
decreasing_by
  all_goals
    simp_wf
    omega

end Progress

open Progress (progress)

-- https://plfa.github.io/Untyped/#evaluation
inductive Result (n : Term m) where
| done (val : Normal n)
| dnf
deriving Repr

inductive Steps (l : Term m) where
| steps : ∀{n : Term m}, (l —↠ n) → Result n → Steps l

def eval (gas : ℕ) (l : Term 0) : Steps l :=
  if gas = 0 then
    ⟨.refl, .dnf⟩
  else
    match progress l with
    | .done v => .steps .refl <| .done v
    | .step r =>
      let ⟨rs, res⟩ := eval (gas - 1) _
      ⟨Trans.trans r rs, res⟩

namespace Term
  abbrev id : Term n := ƛ #0
  abbrev delta : Term n := ƛ #0 ⬝ #0
  abbrev omega : Term n := delta ⬝ delta

  abbrev zeroS : Term n := ƛ ƛ #0
  abbrev succS (m : Term n) : Term n := (ƛ ƛ ƛ (#1 ⬝ #2)) ⬝ m
  abbrev caseS (l : Term n) (m : Term n) (k : Term (n + 1)) : Term n := l ⬝ (ƛ k) ⬝ m

  abbrev mu (k : Term (n + 1)) : Term n := (ƛ (ƛ (#1 $ #0 $ #0)) ⬝ (ƛ (#1 $ #0 $ #0))) ⬝ (ƛ k)
end Term

namespace Notation
  open Term

  scoped prefix:50 "μ " => mu
  scoped prefix:80 "ι " => succS
  scoped notation "𝟘" => zeroS
  scoped notation "𝟘? " => caseS
end Notation

open Notation

-- https://plfa.github.io/Untyped/#example
section examples
  open Term

  abbrev addS : Term n := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 ⬝ #0 ⬝ #1)))
  abbrev mulS : Term n := μ ƛ ƛ (𝟘? (#1) 𝟘 (addS ⬝ #1 $ #3 ⬝ #0 ⬝ #1))

  abbrev oneS : Term n := ι 𝟘
  abbrev twoS : Term n := ι ι 𝟘
  abbrev twoS'' : Term n := mulS ⬝ twoS ⬝ oneS

  abbrev fourS : Term n := ι ι twoS
  abbrev fourS' : Term n := addS ⬝ twoS ⬝ twoS
  abbrev fourS'' : Term n := mulS ⬝ twoS ⬝ twoS

  abbrev evalRes (l : Term 0) (gas := 100) := (eval gas l).3

/--
info: Untyped.Result.dnf
-/
#guard_msgs in #eval evalRes (gas := 3) fourC'
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.norm
            (Untyped.Neutral.ap
              (Untyped.Neutral.var 1)
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.norm
                    (Untyped.Neutral.ap (Untyped.Neutral.var 1) (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))
-/
#guard_msgs in #eval evalRes fourC'
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))
-/
#guard_msgs in #eval evalRes oneS
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam
            (Untyped.Normal.lam
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.lam (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))
-/
#guard_msgs in #eval evalRes twoS
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam
            (Untyped.Normal.lam
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.lam (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))
-/
#guard_msgs in #eval evalRes twoS''
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam
            (Untyped.Normal.lam
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.lam
                    (Untyped.Normal.lam
                      (Untyped.Normal.norm
                        (Untyped.Neutral.ap
                          (Untyped.Neutral.var 1)
                          (Untyped.Normal.lam
                            (Untyped.Normal.lam
                              (Untyped.Normal.norm
                                (Untyped.Neutral.ap
                                  (Untyped.Neutral.var 1)
                                  (Untyped.Normal.lam
                                    (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))))))))))
-/
#guard_msgs in #eval evalRes fourS
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam
            (Untyped.Normal.lam
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.lam
                    (Untyped.Normal.lam
                      (Untyped.Normal.norm
                        (Untyped.Neutral.ap
                          (Untyped.Neutral.var 1)
                          (Untyped.Normal.lam
                            (Untyped.Normal.lam
                              (Untyped.Normal.norm
                                (Untyped.Neutral.ap
                                  (Untyped.Neutral.var 1)
                                  (Untyped.Normal.lam
                                    (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))))))))))
-/
#guard_msgs in #eval evalRes fourS'
/--
info: Untyped.Result.done
  (Untyped.Normal.lam
    (Untyped.Normal.lam
      (Untyped.Normal.norm
        (Untyped.Neutral.ap
          (Untyped.Neutral.var 1)
          (Untyped.Normal.lam
            (Untyped.Normal.lam
              (Untyped.Normal.norm
                (Untyped.Neutral.ap
                  (Untyped.Neutral.var 1)
                  (Untyped.Normal.lam
                    (Untyped.Normal.lam
                      (Untyped.Normal.norm
                        (Untyped.Neutral.ap
                          (Untyped.Neutral.var 1)
                          (Untyped.Normal.lam
                            (Untyped.Normal.lam
                              (Untyped.Normal.norm
                                (Untyped.Neutral.ap
                                  (Untyped.Neutral.var 1)
                                  (Untyped.Normal.lam
                                    (Untyped.Normal.lam (Untyped.Normal.norm (Untyped.Neutral.var 0))))))))))))))))))))
-/
#guard_msgs in #eval evalRes fourS''
end examples

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-transitive

/-
Nothing to do.
The `Trans` instance has been automatically generated by `Relation.ReflTransGen`.
See: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html#Relation.instIsTransReflTransGen>
-/

-- https://plfa.github.io/Untyped/#multi-step-reduction-is-a-congruence
/--
LEAN is being a bit weird here.
Default structural recursion cannot be used since it depends on sizeOf,
however this won't work for `Prop`.
We have to find another way.
-/
theorem Reduce.ap_congr₁ (rs : l —↠ l') : (l ⬝ m) —↠ (l' ⬝ m) := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact apξ₁ r

theorem Reduce.ap_congr₂ (rs : m —↠ m') : (l ⬝ m) —↠ (l ⬝ m') := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact apξ₂ r

theorem Reduce.lam_congr (rs : n —↠ n') : (ƛ n —↠ ƛ n') := by
  refine rs.head_induction_on .refl ?_
  · introv; intro r _ rs; refine .head ?_ rs; exact lamζ r
