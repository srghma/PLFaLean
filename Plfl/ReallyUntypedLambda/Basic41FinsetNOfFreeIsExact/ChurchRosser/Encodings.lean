module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Church
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.Combinators

@[expose] public section

/-!
# Church encodings: booleans, the conditional, pairs, and zero-testing

Further "programming" theorems about the pure λ-calculus, all proved as
reductions of packaged terms:

* `Basic41Finset.tru_app`, `Basic41Finset.fls_app` — the Church booleans select
  their first, resp. second, argument;
* `Basic41Finset.ifte_tru`, `Basic41Finset.ifte_fls` — correctness of the
  conditional;
* `Basic41Finset.fst_pair`, `Basic41Finset.snd_pair` — correctness of the
  Church pairing and its projections;
* `Basic41Finset.iszero_church_zero`, `Basic41Finset.iszero_church_succ` —
  correctness of the zero test on Church numerals;
* `Basic41Finset.tru_not_betaEqS_fls` — `true` and `false` are not
  β-convertible.
-/

namespace Basic41FinsetNOfFreeIsExact

open SigmaTerm

/-! ### Booleans -/

/-- The Church boolean `true = λx. λy. x`. -/
def tru : SigmaTerm := abs (abs (var 1))

/-- The Church boolean `false = λx. λy. y`. -/
def fls : SigmaTerm := abs (abs (var 0))

@[simp] theorem shift_tru (c : Nat) : SigmaTerm.shift c tru = tru := by simp [tru]

@[simp] theorem subst_tru (j : Nat) (N : SigmaTerm) : SigmaTerm.subst j N tru = tru := by
  simp [tru]

@[simp] theorem shift_fls (c : Nat) : SigmaTerm.shift c fls = fls := by simp [fls]

@[simp] theorem subst_fls (j : Nat) (N : SigmaTerm) : SigmaTerm.subst j N fls = fls := by
  simp [fls]

/-- Substituting at index `1` in a doubly shifted term removes one shift. -/
@[simp] theorem subst_one_shift_shift (X B : SigmaTerm) :
    SigmaTerm.subst 1 X (SigmaTerm.shift 0 (SigmaTerm.shift 0 B)) = SigmaTerm.shift 0 B := by
  rw [← SigmaTerm.shift_shift B 0 0 (Nat.le_refl 0), SigmaTerm.subst_shift]

/-- `true M N` reduces to `M`. -/
theorem tru_app (M N : SigmaTerm) : app (app tru M) N ⇒βs* M := by
  refine Relation.ReflTransGen.head (b := app (abs (SigmaTerm.shift 0 M)) N) ?_ ?_
  · refine StepS.app_left ?_ N
    have h := StepS.head (abs (var 1)) M
    simpa [tru] using h
  · refine Relation.ReflTransGen.single ?_
    have h := StepS.head (SigmaTerm.shift 0 M) N
    simpa [SigmaTerm.subst_shift] using h

/-- `false M N` reduces to `N`. -/
theorem fls_app (M N : SigmaTerm) : app (app fls M) N ⇒βs* N := by
  refine Relation.ReflTransGen.head (b := app (abs (var 0)) N) ?_ ?_
  · refine StepS.app_left ?_ N
    have h := StepS.head (abs (var 0)) M
    simpa [fls] using h
  · refine Relation.ReflTransGen.single ?_
    have h := StepS.head (var 0) N
    simpa using h

/-! ### The conditional -/

/-- The conditional `ifte = λb. λt. λe. b t e`. -/
def ifteTerm : SigmaTerm := abs (abs (abs (app (app (var 2) (var 1)) (var 0))))

/-- `ifte B M N` reduces to `B M N`. -/
theorem ifte_app (B M N : SigmaTerm) :
    app (app (app ifteTerm B) M) N ⇒βs* app (app B M) N := by
  have step1 : app ifteTerm B →βs
      abs (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 B)) (var 1)) (var 0))) := by
    have h := StepS.head (abs (abs (app (app (var 2) (var 1)) (var 0)))) B
    simpa [ifteTerm] using h
  have step2 : app (abs (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 B)) (var 1))
        (var 0)))) M →βs
      abs (app (app (SigmaTerm.shift 0 B) (SigmaTerm.shift 0 M)) (var 0)) := by
    have h := StepS.head (abs (app (app (SigmaTerm.shift 0 (SigmaTerm.shift 0 B)) (var 1))
      (var 0))) M
    simpa using h
  refine Relation.ReflTransGen.head (StepS.app_left (StepS.app_left step1 M) N)
    (Relation.ReflTransGen.head (StepS.app_left step2 N) (Relation.ReflTransGen.single ?_))
  have h := StepS.head (app (app (SigmaTerm.shift 0 B) (SigmaTerm.shift 0 M)) (var 0)) N
  simpa [SigmaTerm.subst_shift] using h

/-- `ifte true M N` reduces to `M`. -/
theorem ifte_tru (M N : SigmaTerm) : app (app (app ifteTerm tru) M) N ⇒βs* M :=
  (ifte_app tru M N).trans (tru_app M N)

/-- `ifte false M N` reduces to `N`. -/
theorem ifte_fls (M N : SigmaTerm) : app (app (app ifteTerm fls) M) N ⇒βs* N :=
  (ifte_app fls M N).trans (fls_app M N)

/-! ### Pairs -/

/-- Church pairing `pair = λx. λy. λf. f x y`. -/
def pairTerm : SigmaTerm := abs (abs (abs (app (app (var 0) (var 2)) (var 1))))

/-- First projection `fst = λp. p true`. -/
def fstTerm : SigmaTerm := abs (app (var 0) tru)

/-- Second projection `snd = λp. p false`. -/
def sndTerm : SigmaTerm := abs (app (var 0) fls)

/-- The value of `pair M N`: the term `λf. f M N`. -/
def pairS (M N : SigmaTerm) : SigmaTerm :=
  abs (app (app (var 0) (SigmaTerm.shift 0 M)) (SigmaTerm.shift 0 N))

/-- `pair M N` reduces to the pair value `λf. f M N`. -/
theorem pair_app (M N : SigmaTerm) : app (app pairTerm M) N ⇒βs* pairS M N := by
  have step1 : app pairTerm M →βs
      abs (abs (app (app (var 0) (SigmaTerm.shift 0 (SigmaTerm.shift 0 M))) (var 1))) := by
    have h := StepS.head (abs (abs (app (app (var 0) (var 2)) (var 1)))) M
    simpa [pairTerm] using h
  refine Relation.ReflTransGen.head (StepS.app_left step1 N) (Relation.ReflTransGen.single ?_)
  have h := StepS.head
    (abs (app (app (var 0) (SigmaTerm.shift 0 (SigmaTerm.shift 0 M))) (var 1))) N
  simpa [pairS] using h

/-- The first projection of a pair value. -/
theorem fst_pairS (M N : SigmaTerm) : app fstTerm (pairS M N) ⇒βs* M := by
  refine Relation.ReflTransGen.head (b := app (pairS M N) tru) ?_ ?_
  · have h := StepS.head (app (var 0) tru) (pairS M N)
    simpa [fstTerm] using h
  · refine Relation.ReflTransGen.head (b := app (app tru M) N) ?_ (tru_app M N)
    have h := StepS.head (app (app (var 0) (SigmaTerm.shift 0 M)) (SigmaTerm.shift 0 N)) tru
    simpa [pairS, SigmaTerm.subst_shift] using h

/-- The second projection of a pair value. -/
theorem snd_pairS (M N : SigmaTerm) : app sndTerm (pairS M N) ⇒βs* N := by
  refine Relation.ReflTransGen.head (b := app (pairS M N) fls) ?_ ?_
  · have h := StepS.head (app (var 0) fls) (pairS M N)
    simpa [sndTerm] using h
  · refine Relation.ReflTransGen.head (b := app (app fls M) N) ?_ (fls_app M N)
    have h := StepS.head (app (app (var 0) (SigmaTerm.shift 0 M)) (SigmaTerm.shift 0 N)) fls
    simpa [pairS, SigmaTerm.subst_shift] using h

/-- The first projection of a pair: `fst (pair M N) ⇒β* M`. -/
theorem fst_pair (M N : SigmaTerm) : app fstTerm (app (app pairTerm M) N) ⇒βs* M :=
  (betaStarS_app_right fstTerm (pair_app M N)).trans (fst_pairS M N)

/-- The second projection of a pair: `snd (pair M N) ⇒β* N`. -/
theorem snd_pair (M N : SigmaTerm) : app sndTerm (app (app pairTerm M) N) ⇒βs* N :=
  (betaStarS_app_right sndTerm (pair_app M N)).trans (snd_pairS M N)

/-! ### Testing for zero -/

/-- The zero test `iszero = λn. n (λx. false) true`. -/
def iszeroTerm : SigmaTerm := abs (app (app (var 0) (abs fls)) tru)

theorem stepS_iszero_church (n : Nat) :
    app iszeroTerm (church n) →βs app (app (church n) (abs fls)) tru := by
  have h := StepS.head (app (app (var 0) (abs fls)) tru) (church n)
  simpa [iszeroTerm] using h

/-- `iszero ⌜0⌝` reduces to `true`. -/
theorem iszero_church_zero : app iszeroTerm (church 0) ⇒βs* tru :=
  Relation.ReflTransGen.head (stepS_iszero_church 0) (church_app 0 (abs fls) tru)

/-- `iszero ⌜n+1⌝` reduces to `false`. -/
theorem iszero_church_succ (n : Nat) : app iszeroTerm (church (n + 1)) ⇒βs* fls := by
  refine Relation.ReflTransGen.head (stepS_iszero_church (n + 1))
    (Relation.ReflTransGen.trans (church_app (n + 1) (abs fls) tru)
      (Relation.ReflTransGen.single ?_))
  have h := StepS.head fls (iterApp n (abs fls) tru)
  simpa using h

/-! ### The booleans are distinct -/

theorem normalS_tru : NormalS tru := ((normalS_var 1).abs).abs

theorem normalS_fls : NormalS fls := ((normalS_var 0).abs).abs

/-- Variables are distinguished by their index. -/
theorem var_inj {i j : Nat} (h : SigmaTerm.var i = SigmaTerm.var j) : i = j := by
  have h1 : ({i} : Finset Nat) = {j} := (pack_eq_iff.mp h).1
  simpa using h1

/-- `true` and `false` are not β-convertible. -/
theorem tru_not_betaEqS_fls : ¬ (tru ≡βs fls) :=
  not_betaEqS_of_ne_normal normalS_tru normalS_fls (by
    intro h
    exact absurd (var_inj (abs_inj.mp (abs_inj.mp h))) (by decide))

/-! ### The predecessor

Kleene's predecessor: iterate `λp. pair (snd p) (succ (snd p))` on the pair
`(0, 0)` and take the first component. -/

@[simp] theorem subst_pairTerm (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N pairTerm = pairTerm := by simp [pairTerm]

@[simp] theorem shift_pairTerm (c : Nat) : SigmaTerm.shift c pairTerm = pairTerm := by
  simp only [pairTerm, SigmaTerm.shift_abs, SigmaTerm.shift_app, SigmaTerm.shift_var]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem subst_fstTerm (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N fstTerm = fstTerm := by simp [fstTerm]

@[simp] theorem shift_fstTerm (c : Nat) : SigmaTerm.shift c fstTerm = fstTerm := by
  simp [fstTerm]

@[simp] theorem subst_sndTerm (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N sndTerm = sndTerm := by simp [sndTerm]

@[simp] theorem shift_sndTerm (c : Nat) : SigmaTerm.shift c sndTerm = sndTerm := by
  simp [sndTerm]

@[simp] theorem subst_succTerm (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N succTerm = succTerm := by simp [succTerm]

@[simp] theorem shift_succTerm (c : Nat) : SigmaTerm.shift c succTerm = succTerm := by
  simp only [succTerm, SigmaTerm.shift_abs, SigmaTerm.shift_app, SigmaTerm.shift_var]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The step function of the predecessor: `λp. pair (snd p) (succ (snd p))`. -/
def predStep : SigmaTerm :=
  abs (app (app pairTerm (app sndTerm (var 0))) (app succTerm (app sndTerm (var 0))))

@[simp] theorem subst_predStep (j : Nat) (N : SigmaTerm) :
    SigmaTerm.subst j N predStep = predStep := by simp [predStep]

@[simp] theorem shift_predStep (c : Nat) : SigmaTerm.shift c predStep = predStep := by
  simp [predStep]

/-- The predecessor `pred = λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))`. -/
def predTerm : SigmaTerm :=
  abs (app fstTerm (app (app (var 0) predStep) (app (app pairTerm (church 0)) (church 0))))

theorem stepS_predStep (Q : SigmaTerm) :
    app predStep Q →βs app (app pairTerm (app sndTerm Q)) (app succTerm (app sndTerm Q)) := by
  have h := StepS.head
    (app (app pairTerm (app sndTerm (var 0))) (app succTerm (app sndTerm (var 0)))) Q
  simpa [predStep] using h

/-- One iteration of the predecessor step on a pair of numerals. -/
theorem predStep_pairS (k n : Nat) :
    app predStep (pairS (church k) (church n)) ⇒βs* pairS (church n) (church (n + 1)) := by
  refine Relation.ReflTransGen.head (stepS_predStep _) ?_
  refine Relation.ReflTransGen.trans
    (betaStarS_app_left _ (betaStarS_app_right pairTerm (snd_pairS (church k) (church n)))) ?_
  refine Relation.ReflTransGen.trans
    (betaStarS_app_right _ (betaStarS_app_right succTerm (snd_pairS (church k) (church n)))) ?_
  refine Relation.ReflTransGen.trans
    (betaStarS_app_right _ (succ_church n)) ?_
  exact pair_app (church n) (church (n + 1))

/-- Iterating the predecessor step `n` times on `(0, 0)` yields `(n-1, n)`. -/
theorem iterApp_predStep (n : Nat) :
    iterApp n predStep (app (app pairTerm (church 0)) (church 0)) ⇒βs*
      pairS (church (n - 1)) (church n) := by
  induction n with
  | zero => exact pair_app (church 0) (church 0)
  | succ n ih =>
    refine Relation.ReflTransGen.trans (betaStarS_app_right predStep ih) ?_
    simpa using predStep_pairS (n - 1) n

/-- **Correctness of the predecessor**: `pred ⌜n⌝ ⇒β* ⌜n-1⌝` (truncated
subtraction, so `pred ⌜0⌝ ⇒β* ⌜0⌝`). -/
theorem pred_church (n : Nat) : app predTerm (church n) ⇒βs* church (n - 1) := by
  have step1 : app predTerm (church n) →βs
      app fstTerm (app (app (church n) predStep)
        (app (app pairTerm (church 0)) (church 0))) := by
    have h := StepS.head
      (app fstTerm (app (app (var 0) predStep) (app (app pairTerm (church 0)) (church 0))))
      (church n)
    simpa [predTerm] using h
  refine Relation.ReflTransGen.head step1 ?_
  refine Relation.ReflTransGen.trans (betaStarS_app_right fstTerm
    (church_app n predStep (app (app pairTerm (church 0)) (church 0)))) ?_
  refine Relation.ReflTransGen.trans
    (betaStarS_app_right fstTerm (iterApp_predStep n)) ?_
  exact fst_pairS (church (n - 1)) (church n)

/-! ### `Ω` is not convertible to any of these values -/

/-- `Ω` is not β-convertible to any Church numeral. -/
theorem omega_not_betaEqS_church (n : Nat) : ¬ (omega ≡βs church n) :=
  omega_not_betaEqS_normal (normalS_church n)

/-- `Ω` is not β-convertible to `true` or to `false`. -/
theorem omega_not_betaEqS_tru : ¬ (omega ≡βs tru) := omega_not_betaEqS_normal normalS_tru

theorem omega_not_betaEqS_fls : ¬ (omega ≡βs fls) := omega_not_betaEqS_normal normalS_fls

end Basic41FinsetNOfFreeIsExact
