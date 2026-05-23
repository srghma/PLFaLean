module

-- https://plfa.github.io/Inference/

public meta import Plfl.Init
public import Plfl.More

@[expose] public section

namespace Inference

-- https://plfa.github.io/Inference/#syntax
open String

def Sym : Type := String deriving BEq, DecidableEq, Repr

inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| nat : Ty
/-- Arrow type. -/
| fn : Ty → Ty → Ty
/-- Product type. -/
| prod: Ty → Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Notation
  open Ty

  scoped notation "ℕt" => nat
  scoped infixr:70 " =⇒ " => fn

  instance : Mul Ty where mul := .prod
end Notation

open Notation

abbrev Context : Type := List (Sym × Ty)

namespace Context
  abbrev extend (c : Context) (s : Sym) (t : Ty) : Context := ⟨s, t⟩ :: c
end Context

namespace Notation
  open Context

 -- The goal is to make `_‚_⦂_` work like an `infixl`.
  -- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html#From-Precedence-to-Binding-Power
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  notation:50 c "‚ " s:51 " ⦂ " t:51 => extend c s t
end Notation

open Notation

/-
An attribute is said to be Synthesized,
if its parse tree node value is determined by the attribute value at its *child* nodes.

An attribute is said to be Inherited,
if its parse tree node value is determined by the attribute value at its *parent and/or siblings*.

<https://www.geeksforgeeks.org/differences-between-synthesized-and-inherited-attributes/>
-/

mutual
  /--
  A term with synthesized types.
  The main term in a constructor is typed via inheritance.
  -/
  inductive TermS where
  | var : Sym → TermS
  | ap : TermS → TermI → TermS
  | prod : TermS → TermS → TermS
  | syn : TermI → Ty → TermS
  deriving BEq, Repr
  -- * `DecidableEq` derivations are not yet supported in `mutual` blocks.
  -- See: <https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.22default.20handlers.22.20when.20deriving.20DecidableEq/near/275722237>

  /--
  A term with inherited types.
  The main term in an eliminator is typed via synthesis.
  -/
  inductive TermI where
  | lam : Sym → TermI → TermI
  | zero : TermI
  | succ : TermI → TermI
  | case : TermS → TermI → Sym → TermI → TermI
  | mu : Sym → TermI → TermI
  | fst : TermS → TermI
  | snd : TermS → TermI
  | inh : TermS → TermI
  deriving BEq, Repr
end

namespace Notation
  open TermS TermI

  scoped notation:50 "ƛ " v " : " d => lam v d
  scoped notation:50 " μ " v " : " d => mu v d
  scoped notation:max "𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  scoped infixr:min " $ " => ap
  -- scoped infix:60 " ↓ " => syn
  -- scoped postfix:60 "↑ " => inh
  scoped infixl:70 " □ " => ap
  scoped prefix:80 "ι " => succ
  scoped prefix:90 "‵" => var
  scoped notation "𝟘" => zero
end Notation

-- https://plfa.github.io/Inference/#example-terms
abbrev two : TermI := ι ι 𝟘

-- * The coercion can only happen in this direction,
-- since the other direction requires an extra type annotation.
instance : Coe TermS TermI where coe := TermI.inh

@[simp] abbrev TermI.the := TermS.syn

abbrev add : TermS :=
  (μ "+" : ƛ "m" : ƛ "n" :
    𝟘? ‵"m"
      [zero: ‵"n"
      |succ "m" : ι (‵"+" □ ‵"m" □ ‵"n")]
  ).the (ℕt =⇒ ℕt =⇒ ℕt)

abbrev mul : TermS :=
  (μ "*" : ƛ "m" : ƛ "n" :
    𝟘? ‵"m"
    [zero: 𝟘
    |succ "m": add □ ‵"n" $ ‵"*" □ ‵"m" □ ‵"n"]
  ).the (ℕt =⇒ ℕt =⇒ ℕt)

-- Note that the typing is only required for `add` due to the rule for `ap`.
abbrev four : TermS := add □ two □ two

/--
The Church numeral Ty.
-/
@[simp] abbrev Ch (t : Ty := ℕt) : Ty := (t =⇒ t) =⇒ t =⇒ t

-- Church encoding...
abbrev succC : TermI := ƛ "n" : ι ‵"n"
abbrev oneC : TermI := ƛ "s" : ƛ "z" : ‵"s" $ ‵"z"
abbrev twoC : TermI := ƛ "s" : ƛ "z" : ‵"s" $ ‵"s" $ ‵"z"
abbrev addC : TermS :=
  (ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : ‵"m" □ ‵"s" $ ‵"n" □ ‵"s" □ ‵"z"
  ).the (Ch =⇒ Ch =⇒ Ch)
-- Note that the typing is only required for `addC` due to the rule for `ap`.
abbrev four' : TermS := addC □ twoC □ twoC □ succC □ 𝟘

-- https://plfa.github.io/Inference/#bidirectional-type-checking
/--
A lookup judgement.
`Lookup c s ts` means that `s` is of type `ts` by _looking up_ the context `c`.
-/
inductive Lookup : Context → Sym → Ty → Type where
| z : Lookup (Γ‚ x ⦂ a) x a
| s : x ≠ y → Lookup Γ x a → Lookup (Γ‚ y ⦂ b) x a
deriving DecidableEq

namespace Lookup
  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/tactics.md#tactics-by-macro-expansion
  /--
  `elem` validates the type of a variable by looking it up in the current context.
  This tactic fails when the lookup fails.
  -/
  scoped syntax "elem" : tactic
  macro_rules
  | `(tactic| elem) =>
    `(tactic| repeat (first | apply Lookup.s (by trivial) | exact Lookup.z))

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic| exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s (by trivial); get_elem $(Lean.quote n))
end Lookup

namespace Notation
  open Context Lookup

  scoped notation:40 Γ " ∋ " m " ⦂ " a:51 => Lookup Γ m a
  scoped macro "♯ " n:term:90 : term => `(by get_elem $n)
end Notation

instance : Repr (Γ ∋ m ⦂ a) where reprPrec i n := "♯" ++ reprPrec n (sizeOf i)

/--
info: ♯0
-/
#guard_msgs in #eval @Lookup.z (∅‚ "x" ⦂ ℕt) "x" ℕt

mutual
  /--
  Typing of `TermS` terms.
  -/
  inductive TyS : Context → TermS → Ty → Type where
  | var : Γ ∋ x ⦂ a → TyS Γ (‵ x) a
  | ap: TyS Γ l (a =⇒ b) → TyI Γ m a → TyS Γ (l □ m) b
  | prod: TyS Γ m a → TyS Γ n b → TyS Γ (.prod m n) (a * b)
  | syn : TyI Γ m a → TyS Γ (m.the a) a
  deriving Repr

  /--
  Typing of `TermI` terms.
  -/
  inductive TyI : Context → TermI → Ty → Type where
  | lam : TyI (Γ‚ x ⦂ a) n b → TyI Γ (ƛ x : n) (a =⇒ b)
  | zero : TyI Γ 𝟘 ℕt
  | succ : TyI Γ m ℕt → TyI Γ (ι m) ℕt
  | case
  : TyS Γ l ℕt → TyI Γ m a → TyI (Γ‚ x ⦂ ℕt) n a
  → TyI Γ (𝟘? l [zero: m |succ x : n]) a
  | mu : TyI (Γ‚ x ⦂ a) n a → TyI Γ (μ x : n) a
  | fst: TyS Γ p (a * b) → TyI Γ (.fst p) a
  | snd: TyS Γ p (a * b) → TyI Γ (.snd p) b
  | inh : TyS Γ m a → TyI Γ m a
  deriving Repr
end

instance : Coe (TyI Γ m a) (TyS Γ (m.the a) a) where coe := TyS.syn
instance : Coe (TyS Γ m a) (TyI Γ m a) where coe := TyI.inh

namespace Notation
  scoped notation:40 Γ " ⊢ " m " ⇡ " a:51 => TyS Γ m a
  scoped notation:40 Γ " ⊢ " m " ↟ " a:51 => TyS Γ (TermS.syn m a) a
  scoped notation:40 Γ " ⊢ " m " ⇣ " a:51 => TyI Γ m a
end Notation

abbrev twoTy : Γ ⊢ two ↟ ℕt := open TyS TyI in by
  apply_rules [syn, succ, zero]

abbrev addTy : Γ ⊢ add ⇡ (ℕt =⇒ ℕt =⇒ ℕt) := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

-- https://plfa.github.io/Inference/#bidirectional-mul
abbrev mulTy : Γ ⊢ mul ⇡ (ℕt =⇒ ℕt =⇒ ℕt) := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy]
  <;> elem

abbrev twoCTy : Γ ⊢ twoC ⇣ Ch := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

abbrev addCTy : Γ ⊢ addC ⇡ (Ch =⇒ Ch =⇒ Ch) := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh]
  <;> elem

-- https://plfa.github.io/Inference/#bidirectional-products
example : Γ ⊢ .prod (two.the ℕt) add ⇡ ℕt * (ℕt =⇒ ℕt =⇒ ℕt)
:= open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    twoTy, addTy]
  <;> elem

example : Γ ⊢ .fst (.prod (two.the ℕt) add) ↟ ℕt
:= open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    twoTy]
  <;> elem

example : Γ ⊢ .snd (.prod (two.the ℕt) add) ↟ (ℕt =⇒ ℕt =⇒ ℕt)
:= open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy]
  <;> elem

-- https://plfa.github.io/Inference/#prerequisites

/-
Nothing to do. Relevant definitions have been derived.
-/

-- https://plfa.github.io/Inference/#unique-types
theorem Lookup.unique : (i : Γ ∋ x ⦂ a) → (j : Γ ∋ x ⦂ b) → a = b
| .z, .z => rfl
| .z, .s h _ => (h rfl).elim
| .s h _, .z => (h rfl).elim
| .s _ i, .s _ j => unique i j

theorem TyS.unique (t : Γ ⊢ x ⇡ a) (u : Γ ⊢ x ⇡ b) : a = b := by
  match t with
  | .var i => cases u with | var j => apply Lookup.unique <;> trivial
  | .ap l _ => cases u with | ap l' _ => injection unique l l'
  | .prod m n => cases u with | prod m' n' => congr; exact unique m m'; exact unique n n'
  | .syn _ => cases u with | syn _ => trivial

-- https://plfa.github.io/Inference/#lookup-type-of-a-variable-in-the-context
lemma Lookup.empty_ext_empty
: x ≠ y
→ IsEmpty (Σ a, Γ ∋ x ⦂ a)
→ IsEmpty (Σ a, Γ‚ y ⦂ b ∋ x ⦂ a)
:= by
  intro n ai; is_empty; intro ⟨a, i⟩; apply ai.false; exists a
  cases i <;> trivial

def Lookup.lookup (Γ : Context) (x : Sym) : Decidable' (Σ a, Γ ∋ x ⦂ a) :=
  match Γ with
  | [] => .inl (by is_empty; intro ⟨_, h⟩; cases h) -- Helper for False case
  | ⟨y, b⟩ :: Γ =>
    if h : x = y then
      .inr ⟨b, h ▸ .z⟩
    else
      match lookup Γ x with
      | .inr ⟨a, i⟩ => .inr ⟨a, .s h i⟩
      | .inl n => .inl (Lookup.empty_ext_empty h n)

-- https://plfa.github.io/Inference/#promoting-negations
lemma TyS.empty_arg
: Γ ⊢ l ⇡ a =⇒ b
→ IsEmpty (Γ ⊢ m ⇣ a)
→ IsEmpty (Σ b', Γ ⊢ l □ m ⇡ b')
:= by
  intro tl n; is_empty; intro ⟨b', .ap tl' tm'⟩
  injection tl.unique tl'; rename_i h _; apply n.false; rwa [←h] at tm'

lemma TyS.empty_switch : Γ ⊢ m ⇡ a → a ≠ b → IsEmpty (Γ ⊢ m ⇡ b) := by
  intro ta n; is_empty; intro tb; have := ta.unique tb; contradiction

protected theorem Ty.fn_inj_dom  : Ty.fn a b = Ty.fn c d → a = c := fun | rfl => rfl
protected theorem Ty.prod_inj_fst : Ty.prod a b = Ty.prod c d → a = c := fun | rfl => rfl
protected theorem Ty.prod_inj_snd : Ty.prod a b = Ty.prod c d → b = d := fun | rfl => rfl

mutual
  def TermS.infer (m : TermS) (Γ : Context) : Decidable' (Σ a, Γ ⊢ m ⇡ a) :=
    match m with
    | .var x =>
        match Lookup.lookup Γ x with
        | .inr ⟨a, i⟩ => .inr ⟨a, .var i⟩
        | .inl ne    => .inl ⟨fun ⟨_, .var i⟩ => ne.false ⟨_, i⟩⟩
    | .ap l m =>
        match TermS.infer l Γ with
        | .inr ⟨.fn a b, tab⟩ =>
            match TermI.infer m Γ a with
            | .inr ta => .inr ⟨b, .ap tab ta⟩
            | .inl ne => .inl ⟨fun ⟨_, .ap tl tm⟩ =>
                ne.false ((Ty.fn_inj_dom (tab.unique tl)) ▸ tm)⟩
        | .inr ⟨.nat,      tab⟩ => .inl ⟨fun ⟨_, .ap tl _⟩ => nomatch tab.unique tl⟩
        | .inr ⟨.prod _ _, tab⟩ => .inl ⟨fun ⟨_, .ap tl _⟩ => nomatch tab.unique tl⟩
        | .inl ne               => .inl ⟨fun ⟨_, .ap tl _⟩ => ne.false ⟨_, tl⟩⟩
    | .prod m n =>
        match TermS.infer m Γ, TermS.infer n Γ with
        | .inr ⟨a, tm⟩, .inr ⟨b, tn⟩ => .inr ⟨a * b, tm.prod tn⟩
        | .inr _,        .inl ne       => .inl ⟨fun ⟨_, .prod _ tn⟩ => ne.false ⟨_, tn⟩⟩
        | .inl ne,       _             => .inl ⟨fun ⟨_, .prod tm _⟩ => ne.false ⟨_, tm⟩⟩
    | .syn m a =>
        match TermI.infer m Γ a with
        | .inr t  => .inr ⟨a, .syn t⟩
        | .inl ne => .inl ⟨fun ⟨_, .syn t'⟩ => ne.false t'⟩

  def TermI.infer (m : TermI) (Γ : Context) (a : Ty) : Decidable' (Γ ⊢ m ⇣ a) :=
    match m with
    | .lam x n =>
        match a with
        | .fn a b =>
            match TermI.infer n (Γ‚ x ⦂ a) b with
            | .inr t  => .inr (.lam t)
            | .inl ne => .inl ⟨fun (.lam t) => ne.false t⟩
        | .nat      => .inl ⟨fun h => nomatch h⟩
        | .prod _ _ => .inl ⟨fun h => nomatch h⟩
    | .zero =>
        match a with
        | .nat      => .inr .zero
        | .fn _ _   => .inl ⟨fun h => nomatch h⟩
        | .prod _ _ => .inl ⟨fun h => nomatch h⟩
    | .succ n =>
        match a with
        | .nat =>
            match TermI.infer n Γ .nat with
            | .inr t  => .inr (.succ t)
            | .inl ne => .inl ⟨fun (.succ t) => ne.false t⟩
        | .fn _ _   => .inl ⟨fun h => nomatch h⟩
        | .prod _ _ => .inl ⟨fun h => nomatch h⟩
    | .case l mz x ms =>
        match TermS.infer l Γ with
        | .inr ⟨.nat, tl⟩ =>
            match TermI.infer mz Γ a with
            | .inr tm =>
                match TermI.infer ms (Γ‚ x ⦂ .nat) a with
                | .inr tn => .inr (.case tl tm tn)
                | .inl ne => .inl ⟨fun (.case _ _ tn') => ne.false tn'⟩
            | .inl ne => .inl ⟨fun (.case _ tm' _) => ne.false tm'⟩
        | .inr ⟨.fn _ _,   tl⟩ => .inl ⟨fun (.case tl' _ _) => nomatch tl.unique tl'⟩
        | .inr ⟨.prod _ _, tl⟩ => .inl ⟨fun (.case tl' _ _) => nomatch tl.unique tl'⟩
        | .inl ne               => .inl ⟨fun (.case tl' _ _) => ne.false ⟨_, tl'⟩⟩
    | .mu x n =>
        match TermI.infer n (Γ‚ x ⦂ a) a with
        | .inr t  => .inr (.mu t)
        | .inl ne => .inl ⟨fun (.mu t) => ne.false t⟩
    | .fst p =>
        match TermS.infer p Γ with
        | .inr ⟨.prod b _, tp⟩ =>
            if h : b = a then .inr (h ▸ .fst tp)
            else .inl ⟨fun (.fst tp') => h (Ty.prod_inj_fst (tp.unique tp'))⟩
        | .inr ⟨.nat,      tp⟩ => .inl ⟨fun (.fst tp') => nomatch tp.unique tp'⟩
        | .inr ⟨.fn _ _,   tp⟩ => .inl ⟨fun (.fst tp') => nomatch tp.unique tp'⟩
        | .inl ne               => .inl ⟨fun (.fst tp') => ne.false ⟨_, tp'⟩⟩
    | .snd p =>
        match TermS.infer p Γ with
        | .inr ⟨.prod _ c, tp⟩ =>
            if h : c = a then .inr (h ▸ .snd tp)
            else .inl ⟨fun (.snd tp') => h (Ty.prod_inj_snd (tp.unique tp'))⟩
        | .inr ⟨.nat,      tp⟩ => .inl ⟨fun (.snd tp') => nomatch tp.unique tp'⟩
        | .inr ⟨.fn _ _,   tp⟩ => .inl ⟨fun (.snd tp') => nomatch tp.unique tp'⟩
        | .inl ne               => .inl ⟨fun (.snd tp') => ne.false ⟨_, tp'⟩⟩
    | .inh m =>
        match TermS.infer m Γ with
        | .inr ⟨b, tm⟩ =>
            if h : b = a then .inr (h ▸ .inh tm)
            else .inl ⟨fun (.inh tm') => h (tm.unique tm')⟩
        | .inl ne => .inl ⟨fun (.inh tm') => ne.false ⟨_, tm'⟩⟩
end

-- https://plfa.github.io/Inference/#testing-the-example-terms
abbrev fourTy : Γ ⊢ four ⇡ ℕt := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addTy, twoTy]
  <;> elem

example : four.infer ∅ = .inr ⟨ℕt, fourTy⟩ := by rfl

abbrev four'Ty : Γ ⊢ four' ⇡ ℕt := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    addCTy, twoCTy]
  <;> elem

example : four'.infer ∅ = .inr ⟨ℕt, four'Ty⟩ := by rfl

abbrev four'': TermS := mul □ two □ two

abbrev four''Ty : Γ ⊢ four'' ⇡ ℕt := open TyS TyI Lookup in by
  repeat apply_rules
    [var, ap, prod, syn,
    lam, zero, succ, case, mu, fst, snd, inh,
    mulTy, twoTy]
  <;> elem

example : four''.infer ∅ = .inr ⟨ℕt, four''Ty⟩ := by rfl

-- https://plfa.github.io/Inference/#testing-the-error-cases

/-
This didn't work for before due to limitations with mutual recursions.
See: <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Proof.20of.20an.20inductive's.20variant.3F/near/358901115>
-/

example := show ((ƛ "x" : ‵"y").the (ℕt =⇒ ℕt)).infer ∅ = .inl _ by rfl

/-
This didn't work either, probably due to similar reasons...
-/

instance : Decidable (Nonempty (Σ a, Γ ⊢ m ⇡ a)) := (m.infer Γ).toDecidable

example := let m := (ƛ "x" : ‵"y").the (ℕt =⇒ ℕt); show IsEmpty (Σ a, ∅ ⊢ m ⇡ a) by
  rw [←not_nonempty_iff]; decide

-- Unbound variable:
/--
info: .inl _
-/
#guard_msgs in #eval ((ƛ "x" : ‵"y").the (ℕt =⇒ ℕt)).infer ∅

-- Argument in application is ill typed:
/--
info: .inl _
-/
#guard_msgs in #eval (add □ succC).infer ∅

-- Function in application is ill typed:
/--
info: .inl _
-/
#guard_msgs in #eval (add □ succC □ two).infer ∅

-- Function in application has type natural:
/--
info: .inl _
-/
#guard_msgs in #eval (two.the ℕt □ two).infer ∅

-- Abstraction inherits type natural:
/--
info: .inl _
-/
#guard_msgs in #eval (twoC.the ℕt).infer ∅

-- Zero inherits a function type:
/--
info: .inl _
-/
#guard_msgs in #eval (𝟘.the (ℕt =⇒ ℕt)).infer ∅

-- Successor inherits a function type:
/--
info: .inl _
-/
#guard_msgs in #eval (two.the (ℕt =⇒ ℕt)).infer ∅

-- Successor of an ill-typed term:
/--
info: .inl _
-/
#guard_msgs in #eval ((ι twoC).the ℕt).infer ∅

-- Case of a term with a function type:
/--
info: .inl _
-/
#guard_msgs in #eval ((𝟘? twoC.the Ch [zero: 𝟘 |succ "x" : ‵"x"]).the ℕt).infer ∅

-- Case of an ill-typed term:
/--
info: .inl _
-/
#guard_msgs in #eval ((𝟘? twoC.the ℕt [zero: 𝟘 |succ "x" : ‵"x"]).the ℕt).infer ∅

-- Inherited and synthesized types disagree in a switch:
/--
info: .inl _
-/
#guard_msgs in #eval ((ƛ "x" : ‵"x").the (ℕt =⇒ ℕt =⇒ ℕt)).infer ∅

-- https://plfa.github.io/Inference/#erasure
def Ty.erase : Ty → More.Ty
| ℕt => .nat
| a =⇒ b => .fn a.erase b.erase
| .prod a b => a.erase * b.erase

def Context.erase : Context → More.Context
| [] => ∅
| ⟨_, a⟩ :: Γ => a.erase :: Context.erase Γ

def Lookup.erase : Γ ∋ x ⦂ a → More.Lookup Γ.erase a.erase
| .z => .z
| .s _ i => .s i.erase

mutual
  def TyS.erase : Γ ⊢ m ⇡ a → More.Term Γ.erase a.erase
  | .var i => .var i.erase
  | .ap l m => .ap l.erase m.erase
  | .prod m n => .prod m.erase n.erase
  | .syn m => m.erase

  def TyI.erase : Γ ⊢ m ⇣ a → More.Term Γ.erase a.erase
  | .lam m => .lam m.erase
  | .zero => .zero
  | .succ m => .succ m.erase
  | .case l m n => .case l.erase m.erase n.erase
  | .mu m => .mu m.erase
  | .fst m => .fst m.erase
  | .snd m => .snd m.erase
  | .inh m => m.erase
end

example : fourTy.erase (Γ := ∅) = More.Term.four := by rfl

-- https://plfa.github.io/Inference/#exercise-inference-multiplication-recommended
example : mul.infer ∅ = .inr ⟨ℕt =⇒ ℕt =⇒ ℕt, mulTy⟩ := by rfl

-- ! BOOM! The commented lines below were very CPU/RAM-intensive, and might even make LEAN4 leak memory!
example : mulTy.erase (Γ := ∅) = More.Term.mul := by rfl
example : four'Ty.erase (Γ := ∅) = More.Term.four' := by rfl
example : four''Ty.erase (Γ := ∅) = More.Term.four'' := by rfl
