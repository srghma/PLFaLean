module

@[expose] public section

/-! ── Core ─────────────────────────────────────────────────────────────── -/

/--
`PDecidable` is like `Decidable`, but allows arbitrary sorts so it can hold data.
-/
class inductive PDecidable (α : Sort _) where
  /-- Proves that `α` is empty by supplying a proof of `IsEmpty α`
  (`IsEmpty` from `public import Mathlib.Logic.IsEmpty.Defs` is inlined)
  -/
  | isFalse (h : α → False) : PDecidable α
  /-- Proves that `α` is inhabited by supplying a datum of `α` -/
  | isTrue (h : α) : PDecidable α

namespace PDecidable
  def toDecidable : PDecidable α → Decidable (Nonempty α)
  | .isTrue a => .isTrue ⟨a⟩
  | .isFalse na => .isFalse (fun ⟨a⟩ => na a)

  /-- Safely extracts the data, but forces you to prove it isn't `isFalse` first. -/
  def get (d : PDecidable α) (h : Nonempty α) : α :=
    match d with
    | .isTrue a => a
    | .isFalse na => False.elim (h.elim na)
end PDecidable

instance [Repr α] : Repr (PDecidable α) where
  reprPrec da n := match da with
  | .isTrue a => ".isTrue " ++ reprPrec a n
  | .isFalse _ => ".isFalse _"
