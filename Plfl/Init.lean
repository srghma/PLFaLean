module

public import Mathlib.Logic.IsEmpty.Defs

@[expose] public section

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

/--
`PDecidable` is like `Decidable`, but allows arbitrary sorts so it can hold data.
-/
class inductive PDecidable (α : Sort _) where
  /-- Proves that `α` is empty by supplying a proof of `IsEmpty α` -/
  | isFalse (h : IsEmpty α) : PDecidable α
  /-- Proves that `α` is inhabited by supplying a datum of `α` -/
  | isTrue (h : α) : PDecidable α

namespace PDecidable
  def toDecidable : PDecidable α → Decidable (Nonempty α)
  | .isTrue a => .isTrue ⟨a⟩
  | .isFalse na => .isFalse (fun ⟨a⟩ => na.false a)

  /-- Safely extracts the data, but forces you to prove it isn't `isFalse` first. -/
  def get (d : PDecidable α) (h : Nonempty α) : α :=
    match d with
    | .isTrue a => a
    | .isFalse na => False.elim (h.elim na.false)
end PDecidable

instance [Repr α] : Repr (PDecidable α) where
  reprPrec da n := match da with
  | .isTrue a => ".isTrue " ++ reprPrec a n
  | .isFalse _ => ".isFalse _"

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl
