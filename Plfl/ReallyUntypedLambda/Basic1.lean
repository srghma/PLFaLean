-- https://github.com/iwilare/church-rosser/blob/main/DeBruijn.agda

-- https://github.com/ernius/formalmetatheory-nominal-Church-Rosser/blob/master/Atom.lagda
-- https://github.com/ernius/formalmetatheory-nominal-Church-Rosser/blob/master/Term.lagda

-- https://github.com/Danelnov/Lambda-Calculus-Formalization/blob/master/Lambda/Defs.lean

inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | abs : Term → Term
  deriving Repr, DecidableEq

def shift (d : Nat) (c : Nat) : Term → Term
  | Term.var k   => if k ≥ c then Term.var (k + d) else Term.var k
  | Term.app P Q => Term.app (shift d c P) (shift d c Q)
  | Term.abs P   => Term.abs (shift d (c + 1) P)

def subst (j : Nat) (N : Term) : Term → Term
  | Term.var k =>
    if k == j then
      shift j 0 N
    else if k > j then
      Term.var (k - 1)
    else
      Term.var k
  | Term.app P Q => Term.app (subst j N P) (subst j N Q)
  | Term.abs P   => Term.abs (subst (j + 1) N P)

inductive BetaStep : Term → Term → Prop where
  -- Основне правило: (λ. P) N ⟶β P[0 := N]
  | head (P N : Term) :
      BetaStep (Term.app (Term.abs P) N) (subst 0 N P)

  -- Congruence rules (редукція в піддеревах):
  | app_left (P P' Q : Term) :
      BetaStep P P' →
      BetaStep (Term.app P Q) (Term.app P' Q)

  | app_right (P Q Q' : Term) :
      BetaStep Q Q' →
      BetaStep (Term.app P Q) (Term.app P Q')

  | abs_body (P P' : Term) :
      BetaStep P P' →
      BetaStep (Term.abs P) (Term.abs P')

-- Визначаємо простий do-блок для unit-тестів
def testSubst : Id Unit := do
  -- 1. Проста заміна: x_0[0 := N] ⟹ N
  -- Підставляємо Term.var 42 замість індексу 0 у простому термі (var 0)
  guard (subst 0 (Term.var 42) (Term.var 0) == Term.var 42)

  -- 2. Внутрішня змінна залишається без змін: x_0[1 := N] ⟹ x_0
  -- Оскільки шукаємо індекс 1, а маємо 0 (який < 1)
  guard (subst 1 (Term.var 42) (Term.var 0) == Term.var 0)

  -- 3. Декремент вільних змінних: x_2[0 := N] ⟹ x_1
  -- Змінна з індексом 2 при видаленні одного зовн. binder-а стає 1
  guard (subst 0 (Term.var 42) (Term.var 2) == Term.var 1)

  -- 4. Підстановка під λ-абстракцію: (λ. x_1)[0 := N] ⟹ λ. N_shifted
  -- Всередині λ індекс підстановки зростає до 1 (j+1), а x_1 відповідає 0 ззовні
  -- subst 0 (var 42) (abs (var 1)) = abs (shift 1 0 (var 42)) = abs (var 43)
  guard (subst 0 (Term.var 42) (Term.abs (Term.var 1)) == Term.abs (Term.var 43))

  -- 5. Затінення всередині λ: (λ. x_0)[0 := N] ⟹ λ. x_0
  -- Змінна 0 всередині λ зв'язана саме цим λ, тому вона не змінюється
  guard (subst 0 (Term.var 42) (Term.abs (Term.var 0)) == Term.abs (Term.var 0))

  -- 6. Реальний β-step для β-редукції: ((λ. x_0 x_1) (var 99))
  -- Реалізуємо (x_0 x_1)[0 := var 99] ⟹ var 99 var 0
  let body := Term.app (Term.var 0) (Term.var 1)
  let arg  := Term.var 99
  let expected := Term.app (Term.var 99) (Term.var 0)
  guard (subst 0 arg body == expected)

-- Запускаємо тести під час компіляції / перевірки файлу
#eval testSubst
