module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChoiceFree.StrongNormalization

@[expose] public section

/-!
# Church numerals

The Church numeral `church k = ƛ ƛ (f (f … (f x)))` with `k` applications of
`f`.  We show that Church numerals are β-normal, that the map `k ↦ church k` is
injective, and hence — by uniqueness of normal forms — that **distinct Church
numerals are not β-convertible**: the λ-theory really does have infinitely many
distinct "numbers".  Church numerals are also simply typable, so they are
strongly normalising.
-/

namespace IwilareFinsetNOfFreeIsExact

/-- The body `f (f … (f x))` of a Church numeral, in the scope `f = #1`,
`x = #0`. -/
def churchBody : Nat → Term 2
  | 0     => v#0
  | k + 1 => v##1 ⬝ churchBody k

/-- The Church numeral `k`. -/
def church (k : Nat) : Term 0 := ƛ (ƛ (churchBody k))

theorem church_zero : church 0 = Term.zero := rfl

theorem church_one : church 1 = Term.one := rfl

theorem church_two : church 2 = Term.two := rfl

theorem normal_churchBody (k : Nat) : Normal (churchBody k) := by
  induction k with
  | zero => exact normal_var 0
  | succ k ih =>
    exact normal_app (normal_var _) ih (fun A h => by cases h)

/-- Church numerals are β-normal. -/
theorem normal_church (k : Nat) : Normal (church k) :=
  normal_abs_iff.mpr (normal_abs_iff.mpr (normal_churchBody k))

theorem churchBody_injective {j k : Nat} (h : churchBody j = churchBody k) : j = k := by
  induction j generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => exact absurd h (by simp [churchBody])
  | succ j ih =>
    cases k with
    | zero => exact absurd h (by simp [churchBody])
    | succ k =>
      simp only [churchBody, Term.app.injEq] at h
      exact congrArg Nat.succ (ih h.2)

/-- The Church numerals are pairwise distinct terms. -/
theorem church_injective {j k : Nat} (h : church j = church k) : j = k := by
  simp only [church, Term.abs.injEq] at h
  exact churchBody_injective h

/-- **Distinct Church numerals are not β-convertible.** -/
theorem church_not_betaEq {j k : Nat} (h : j ≠ k) : ¬ (church j ≡β church k) :=
  not_betaEq_of_ne_normal (normal_church j) (normal_church k)
    (fun heq => h (church_injective heq))

/-! ### Church numerals are simply typable -/

/-- The context in which the body of a Church numeral lives. -/
def churchCtx (A : Ty) : Ctx 2 := Ctx.cons A (Ctx.cons (A ⇒ A) emptyCtx)

theorem typed_churchBody (A : Ty) (k : Nat) : Typed (churchCtx A) (churchBody k) A := by
  induction k with
  | zero => exact Typed.var _ 0
  | succ k ih =>
    exact Typed.app (A := A) (Typed.var (churchCtx A) (Fin.succ 0)) ih

/-- Every Church numeral has the type `(A ⇒ A) ⇒ A ⇒ A`. -/
theorem typed_church (A : Ty) (k : Nat) : Typed emptyCtx (church k) ((A ⇒ A) ⇒ A ⇒ A) :=
  Typed.abs (Typed.abs (typed_churchBody A k))

/-- Church numerals are strongly normalising. -/
theorem sn_church (k : Nat) : SN (church k) :=
  (typed_church Ty.base k).strongly_normalizing

end IwilareFinsetNOfFreeIsExact
