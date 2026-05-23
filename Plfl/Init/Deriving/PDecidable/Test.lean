module

public import Plfl.Init.PDecidable
public meta import Plfl.Init.PDecidable
public import Plfl.Init.Deriving.PDecidable

/-! ── Tests ─────────────────────────────────────────────────────────────── -/

namespace Plfl.Init.Deriving.PDecidable.Tests
instance : PDecidable Nat    := .isTrue 0
instance : PDecidable String := .isTrue ""

inductive MyEmpty deriving PDecidable, Repr

/--
info: .isFalse _
-/
#guard_msgs in #eval (inferInstance : PDecidable MyEmpty)          -- .isFalse _

inductive MySum (α β : Type) | inl (a : α) | inr (b : β) deriving PDecidable, Repr

/--
info: .isTrue _private.Plfl.Init.Deriving.PDecidable.Test.0.Plfl.Init.Deriving.PDecidable.Tests.MySum.inr 0
-/
#guard_msgs in #eval (inferInstance : PDecidable (MySum MyEmpty Nat))  -- .isTrue (MySum.inr 0)

inductive Config | mk (port : Nat) (host : String)  deriving PDecidable, Repr

/--
info: .isTrue _private.Plfl.Init.Deriving.PDecidable.Test.0.Plfl.Init.Deriving.PDecidable.Tests.Config.mk 0 ""
-/
#guard_msgs in #eval (inferInstance : PDecidable Config)           -- .isTrue (Config.mk 0 "")

inductive MyList (α : Type) | nil | cons (head : α) (tail : MyList α) deriving PDecidable, Repr

/--
info: .isTrue _private.Plfl.Init.Deriving.PDecidable.Test.0.Plfl.Init.Deriving.PDecidable.Tests.MyList.nil
-/
#guard_msgs in #eval (inferInstance : PDecidable (MyList MyEmpty)) -- .isTrue MyList.nil
