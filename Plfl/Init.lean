module

public import Mathlib.Tactic

@[expose] public section

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

/--
`Decidable'` is like `Decidable`, but allows arbitrary sorts so it can hold data.
-/
class inductive Decidable' (α : Sort u) where
  /-- Proves that `α` is empty by supplying a proof of `IsEmpty α` -/
  | isFalse (h : IsEmpty α) : Decidable' α
  /-- Proves that `α` is inhabited by supplying a datum of `α` -/
  | isTrue (h : α) : Decidable' α

namespace Decidable'
  def toDecidable : Decidable' α → Decidable (Nonempty α)
  | .isTrue a => .isTrue ⟨a⟩
  | .isFalse na => .isFalse (fun ⟨a⟩ => na.false a)
end Decidable'

instance [Repr α] : Repr (Decidable' α) where
  reprPrec da n := match da with
  | .isTrue a => ".isTrue " ++ reprPrec a n
  | .isFalse _ => ".isFalse _"

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl
