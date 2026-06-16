-- from https://arxiv.org/pdf/1810.08380
import Mathlib.Tactic.Use
import Mathlib.Data.Nat.Pairing

namespace PartRec

-- 4.1 The Partity monad

/--
We define `Part α` as a dependent pair of a proposition `p`
and a function `p → α`. This is equivalent to `Σ' p : Prop, (p → α)`.
-/
-- same as mathlib Part
structure Part.{u} (α : Type u) : Type u where
  /-- The domain of a Part value -/
  Dom : Prop
  /-- Extract a value from a Part value given a proof of `Dom` -/
  get : Dom → α

namespace Part

/-- The `pure` operation for the `Part` monad. -/
@[simp] def pure {α : Type u} (a : α) : Part α :=
  ⟨True, fun _ => a⟩

/-- The `bind` operation. -/
@[simp] def bind {α β : Type u} (p : Part α) (f : α → Part β) : Part β :=
  ⟨(∀ h : p.Dom, (f (p.get h)).Dom) ∧ p.Dom, fun h =>
    (f (p.get h.right)).get (h.left h.right)⟩

/-- `map` operation to complete the `Monad` structure. -/
@[simp] def map {α β : Type u} (f : α → β) (p : Part α) : Part β :=
  ⟨p.Dom, f ∘ p.get⟩

instance : Monad Part where
  pure := pure
  bind := bind
  map := map

/-- Undefined value. -/
@[simp] def bottom {α : Type u} : Part α :=
  ⟨False, False.elim⟩

notation "⊥" => bottom

instance {α : Type u} : Inhabited (Part α) := ⟨bottom⟩

/-- Relational membership for `Part` (a ∈ p). -/
instance {α : Type u} : Membership α (Part α) where
  mem p a := ∃ h : p.Dom, p.get h = a

/-- Theorem relating bind and membership. -/
theorem mem_bind {α β : Type u} (p : Part α) (f : α → Part β) (b : β) :
    b ∈ p >>= f ↔ ∃ a ∈ p, b ∈ f a := by
  constructor
  · rintro ⟨h_exist, h_eq⟩
    use p.get h_exist.right
    constructor
    · exact ⟨h_exist.right, rfl⟩
    · exact ⟨h_exist.left h_exist.right, h_eq⟩
  · rintro ⟨a, ⟨h1, rfl⟩, ⟨h2, h_eq⟩⟩
    exact ⟨⟨fun _ => h2, h1⟩, h_eq⟩

end Part


-- Notation for Part functions
-- https://github.com/digama0/mathlib-ITP2019/blob/5cbd0362e04e671ef5db1284870592af6950197c/src/data/pfun.lean#L297
-- https://loogle.lean-lang.org/?q=%3Fa+-%3E+Part+%3Fa
-- !!!!!! https://github.com/leanprover-community/mathlib4/blob/878dc46fb98bc3a247541bd4d109dd65cd0092bc/Mathlib/Data/PFun.lean#L59-L62
infixr:50 " ⇀ " => fun α β => α → Part β

-- Computable unbounded recursion (`fix`)
-- https://github.com/digama0/mathlib-ITP2019/blob/5cbd0362e04e671ef5db1284870592af6950197c/src/data/pfun.lean#L416-L422
-- https://github.com/leanprover-community/mathlib4/blob/9dc39333aa89d5be59e8d7698237b31e496cf4ea/Mathlib/Data/PFun.lean#L216
opaque fix {α β : Type u} (f : α ⇀ Sum β α) : α ⇀ β

-- theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
--     b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
axiom mem_fix {α β : Type u} (f : α ⇀ Sum β α) (a : α) (b : β) :
  b ∈ fix f a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'


-- Figure 5: The definition of Part recursive on Nat in Lean

/-- Helper for prec that maps an uncurried function handling Nat.unpairs. -/
def Nat.unpaired (h : Nat → Nat → Part Nat) : Nat ⇀ Nat :=
  fun n => let n' := Nat.unpair n; h n'.1 n'.2

/--
The minimization operator `find p = µn. p(n)`, which finds the smallest
value satisfying the (Part) boolean predicate `p`.
-/
-- https://github.com/leanprover-community/mathlib4/blob/878dc46fb98bc3a247541bd4d109dd65cd0092bc/Mathlib/Computability/Partrec.lean#L89-L93
def find (p : Nat ⇀ Bool) : Part Nat :=
  fix (fun n =>
    p n >>= fun b =>
      if b then pure (Sum.inl n) else pure (Sum.inr (n + 1))) 0

-- this is not find, bc this is total search
-- def Nat.find{p : ℕ → Prop} [DecidablePred p] (H : ∃ (n : ℕ), p n) : ℕ
-- def PNat.find{p : ℕ+ → Prop} [DecidablePred p] (h : ∃ (n : ℕ+), p n) : ℕ+

-- https://github.com/leanprover-community/mathlib4/blob/878dc46fb98bc3a247541bd4d109dd65cd0092bc/Mathlib/Computability/Partrec.lean#L160
inductive Partrec : (Nat ⇀ Nat) → Prop
  | zero : Partrec (fun _ => pure 0)
  | succ : Partrec (fun n => pure (n + 1))
  | left : Partrec (fun n => pure n)
  | right : Partrec (fun n => pure n)
  | pair {f g} : Partrec f → Partrec g →
      Partrec (fun n =>
        f n >>= fun a =>
        g n >>= fun b =>
        pure (Nat.pair a b))
  | comp {f g} : Partrec f → Partrec g →
      Partrec (fun n => g n >>= f)
  | prec {f g} : Partrec f → Partrec g →
      Partrec (Nat.unpaired (fun a n =>
        Nat.recOn n
          (f a)
          (fun y IH =>
            IH >>= fun i =>
            g (Nat.pair a (Nat.pair y i)))))
  | find {f} : Partrec f →
      Partrec (fun a =>
        find (fun n =>
          (fun m => m == 0) <$> f (Nat.pair a n)))

end PartRec
