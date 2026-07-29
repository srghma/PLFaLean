import Mathlib.Logic.Relation

-- Припустимо, що у вас вже виdefined DBTerm та DBBetaStep
-- (Тут засліпка для робочого прикладу)
opaque DBTerm : Type
opaque DBBetaStep : DBTerm → DBTerm → Prop

-- Custom definition
inductive MyStepStar : DBTerm → DBTerm → Prop where
  | refl (t : DBTerm) : MyStepStar t t
  | step {t1 t2 t3 : DBTerm} : DBBetaStep t1 t2 → MyStepStar t2 t3 → MyStepStar t1 t3

-- Mathlib definition
def MathlibStepStar : DBTerm → DBTerm → Prop :=
  Relation.ReflTransGen DBBetaStep

namespace MyStepStar

-- 1. Допоміжна лема: транзитивність MyStepStar
theorem trans {t1 t2 t3 : DBTerm} (h1 : MyStepStar t1 t2) (h2 : MyStepStar t2 t3) :
    MyStepStar t1 t3 := by
  induction h1 with
  | refl => exact h2
  | step h_step _ ih => exact MyStepStar.step h_step (ih h2)

-- 2. Допоміжна лема: додавання одного кроку в кінець (tail)
theorem step_right {t1 t2 t3 : DBTerm} (h1 : MyStepStar t1 t2) (h2 : DBBetaStep t2 t3) :
    MyStepStar t1 t3 := by
  exact MyStepStar.trans h1 (MyStepStar.step h2 (MyStepStar.refl t3))

end MyStepStar

-- 3. Головна теорема про еквівалентність
theorem stepStar_eq_mathlib (t1 t2 : DBTerm) :
    MyStepStar t1 t2 ↔️ MathlibStepStar t1 t2 := by
  constructor
  · -- MyStepStar → MathlibStepStar
    intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | step h1 _ ih => exact Relation.ReflTransGen.head h1 ih
  · -- MathlibStepStar → MyStepStar
    intro h
    induction h with
    | refl => exact MyStepStar.refl _
    | tail _ h2 ih => exact MyStepStar.step_right ih h2



-- "Take step A → B, then attach the rest of the proof B →* C"
def proof_head : MyStepStar A C :=
  MyStepStar.step hAB (
    MyStepStar.step hBC (
      MyStepStar.refl C
    )
  )


-- "Start with A →* A, attach A → B, then attach B → C to the tail"
def proof_tail : Relation.ReflTransGen DBBetaStep A C :=
  Relation.ReflTransGen.tail (
    Relation.ReflTransGen.tail (
      Relation.ReflTransGen.refl
    ) hAB
  ) hBC


import Mathlib.Logic.Relation

-- 1. Multi-step reduction (⟶β*) via Reflexive-Transitive Closure
def DBBetaStepStar : DBTerm → DBTerm → Prop :=
  Relation.ReflTransGen DBBetaStep

infix:50 " ⟶β* " => DBBetaStepStar

-- 2. β-Conversion (=β) via Equivalence Closure (Reflexive-Symmetric-Transitive)
def DBBetaConv : DBTerm → DBTerm → Prop :=
  Relation.EquivGen DBBetaStep

infix:50 " =β " => DBBetaConv


-- Нотація для β-конверсії
infix:50 " =β " => DBBetaConv

/-- β-конверсія: рефлексивно-симетрично-транзитивне замикання DBBetaStep --/
inductive DBBetaConv : DBTerm → DBTerm → Prop where
  | step  {t1 t2 : DBTerm} (h : t1 ⟶β t2) : t1 =β t2
  | refl  (t : DBTerm)                    : t =β t
  | symm  {t1 t2 : DBTerm} (h : t1 =β t2) : t2 =β t1
  | trans {t1 t2 t3 : DBTerm} (h1 : t1 =β t2) (h2 : t2 =β t3) : t1 =β t3

-- Будь-яка багатокрокова редукція є конверсією
def DBBetaStepStar.toConv {t1 t2 : DBTerm} (h : t1 ⟶β* t2) : t1 =β t2 :=
  match h with
  | DBBetaStepStar.refl _ => DBBetaConv.refl _
  | DBBetaStepStar.step h1 h2 =>
      DBBetaConv.trans (DBBetaConv.step h1) (DBBetaStepStar.toConv h2)

-- Один крок є окремим випадком багатокрокової редукції
def DBBetaStepStar.single {t1 t2 : DBTerm} (h : t1 ⟶β t2) : t1 ⟶β* t2 :=
  DBBetaStepStar.step h (DBBetaStepStar.refl t2)

-- Транзитивність: якщо t1 ⟶β* t2 і t2 ⟶β* t3, то t1 ⟶β* t3
def DBBetaStepStar.trans {t1 t2 t3 : DBTerm}
    (h1 : t1 ⟶β* t2) (h2 : t2 ⟶β* t3) : t1 ⟶β* t3 :=
  match h1 with
  | DBBetaStepStar.refl _ => h2
  | DBBetaStepStar.step h1' h2' =>
      DBBetaStepStar.step h1' (DBBetaStepStar.trans h2' h2)

-- Нотація для типу однокомпонентного та багатокрокового відношення
infix:50 " ⟶β "  => DBBetaStep
infix:50 " ⟶β* " => DBBetaStepStar

-- Рефлексивно-транзитивне замикання DBBetaStep
inductive DBBetaStepStar : DBTerm → DBTerm → Prop where
  | refl (t : DBTerm) : t ⟶β* t
  | step {t1 t2 t3 : DBTerm} (h1 : t1 ⟶β t2) (h2 : t2 ⟶β* t3) : t1 ⟶β* t3


-- Нотації для термів та відношення
prefix:max "ƛ " => DBTerm.abs
prefix:max "#"  => DBTerm.var
infixl:70  " ⬝ " => DBTerm.app
infix:50 " ⟶β " => DBBetaStep

-- Визначення термів
def innerFn : DBTerm := ƛ (#1 ⬝ #0)
def outerFn : DBTerm := ƛ (innerFn ⬝ #1)
def initialTerm : DBTerm := outerFn ⬝ #1

--------------------------------------------------------------------------------
-- Шлях 1: Inner First
--------------------------------------------------------------------------------

-- Крок 1 (Inner): (λy. x y) z ⟶β x z  всередині  λx. ...
-- Повністю: ((λx. (λy. x y) z) v) ⟶β ((λx. x z) v)

def innerStep1 : (innerFn ⬝ #1) ⟶β (#0 ⬝ #1) :=
  DBBetaStep.head (#1 ⬝ #0) #1

def innerStep1_abs : outerFn ⟶β ƛ (#0 ⬝ #1) :=
  DBBetaStep.abs innerStep1

def path1_step1 : initialTerm ⟶β ((ƛ (#0 ⬝ #1)) ⬝ #1) :=
  DBBetaStep.app_left outerFn (ƛ (#0 ⬝ #1)) #1 innerStep1_abs

-- Крок 2 (Outer): (λx. x z) v ⟶β v z

def path1_step2 : ((ƛ (#0 ⬝ #1)) ⬝ #1) ⟶β (#1 ⬝ #0) :=
  DBBetaStep.head (#0 ⬝ #1) #1

--------------------------------------------------------------------------------
-- Шлях 2: Outer First
--------------------------------------------------------------------------------

-- Крок 1 (Outer): ((λx. (λy. x y) z) v) ⟶β (λy. v y) z

def path2_step1 : initialTerm ⟶β ((ƛ (#2 ⬝ #0)) ⬝ #0) :=
  DBBetaStep.head (innerFn ⬝ #1) #1

-- Крок 2 (Inner): (λy. v y) z ⟶β v z

def path2_step2 : ((ƛ (#2 ⬝ #0)) ⬝ #0) ⟶β (#1 ⬝ #0) :=
  DBBetaStep.head (#2 ⬝ #0) #0

--------------------------------------------------------------------------------
-- Перевірка
--------------------------------------------------------------------------------

-- Перевірка результату Шляху 1 (Крок 1)
#eval substDB 0 #1 (#1 ⬝ #0) == (#0 ⬝ #1)

-- Перевірка результату Шляху 2 (Крок 1)
#eval substDB 0 #1 (innerFn ⬝ #1) == ((ƛ (#2 ⬝ #0)) ⬝ #0)

-- Обидва шляхи приводять до одного і того ж результату v z: #1 ⬝ #0
example : substDB 0 #0 (#2 ⬝ #0) = (#1 ⬝ #0) := rfl


import Lean

open Lean Elab Tactic

-- Тактика для автоматичного доведення кроку DBBetaStep
syntax (name := betaStepTac) "beta_step" : tactic

macro_rules
  | `(tactic| beta_step) =>
    `(tactic| first
      | exact DBBetaStep.head _ _
      | apply DBBetaStep.abs; beta_step
      | apply DBBetaStep.app_left; beta_step
      | apply DBBetaStep.app_right; beta_step)
