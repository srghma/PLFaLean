inductive Ty | base | arrow : Ty → Ty → Ty

infixr:70 " ⇒ " => Ty.arrow

abbrev Ctx := List Ty

-- Variable index in context
inductive Var : Ctx → Ty → Type
  | head : ∀ {Γ τ}, Var (τ :: Γ) τ
  | tail : ∀ {Γ τ1 τ2}, Var Γ τ1 → Var (τ2 :: Γ) τ1

inductive Term : Ctx → Ty → Type
  | var : ∀ {Γ τ}, Var Γ τ → Term Γ τ
  | abs : ∀ {Γ τ1 τ2}, Term (τ1 :: Γ) τ2 → Term Γ (τ1 ⇒ τ2)
  | app : ∀ {Γ τ1 τ2}, Term Γ (τ1 ⇒ τ2) → Term Γ τ1 → Term Γ τ2

-- Notation
prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app

-- Clean variable macros
notation "#0" => Term.var Var.head
notation "#1" => Term.var (Var.tail Var.head)
notation "#2" => Term.var (Var.tail (Var.tail Var.head))

namespace Term

-- Shortcut for Church Numeral Type: (α ⇒ α) ⇒ α ⇒ α
abbrev NatTy (α : Ty) : Ty := (α ⇒ α) ⇒ α ⇒ α

-- 1. Identity Function: ƛx. x
-- Type: τ ⇒ τ  (in empty context [])
def id {τ : Ty} : Term [] (τ ⇒ τ) :=
  ƛ #0

-- 2. Constant Function: ƛx. ƛy. x
-- Type: τ1 ⇒ τ2 ⇒ τ1  (in empty context [])
def const {τ1 τ2 : Ty} : Term [] (τ1 ⇒ τ2 ⇒ τ1) :=
  ƛ (ƛ #1)

-- 3. Church Numerals
-- Zero: ƛf. ƛx. x
def zero {α : Ty} : Term [] (NatTy α) :=
  ƛ (ƛ #0)

-- One: ƛf. ƛx. f x
def one {α : Ty} : Term [] (NatTy α) :=
  ƛ (ƛ (#1 ⬝ #0))

-- Two: ƛf. ƛx. f (f x)
def two {α : Ty} : Term [] (NatTy α) :=
  ƛ (ƛ (#1 ⬝ (#1 ⬝ #0)))

-- 4. Church Successor: ƛn. ƛf. ƛx. f (n f x)
def succ {α : Ty} : Term [] (NatTy α ⇒ NatTy α) :=
  ƛ (             -- n is #2 (NatTy α)
    ƛ (           -- f is #1 (α ⇒ α)
      ƛ (         -- x is #0 (α)
        #1 ⬝ ((#2 ⬝ #1) ⬝ #0)
      )
    )
  )

-- 5. Terms with Free Variables

-- A term with 2 free variables: (#1 ⬝ #0)
-- Context has 2 types: Γ = [α, α ⇒ β]
--   - #0 has type α       (free var 0)
--   - #1 has type α ⇒ β   (free var 1)
def freeTerm {α β : Ty} : Term [α, α ⇒ β] β :=
  #1 ⬝ #0

-- A term with 1 free variable: ƛy. (y ⬝ #1)
-- Top context has 1 type: Γ = [α] (free var x0)
-- Inside ƛ, context becomes: (α ⇒ β) :: [α]
--   - #0 is bound variable y of type α ⇒ β
--   - #1 is free variable x0 of type α
def boundAndFree {α β : Ty} : Term [α] ((α ⇒ β) ⇒ β) :=
  ƛ (#0 ⬝ #1)

end Term
