module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.NormalForm
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.ChurchRosser.FreeVars

@[expose] public section

/-!
# Church numerals and their arithmetic

Church numerals `⌜n⌝ = λf. λx. fⁿ x` are defined on packaged terms, together
with the combinators for successor, addition and multiplication, and their
correctness is proved as a reduction:

* `Basic41Finset.church_app` — the defining property of the numerals:
  `⌜n⌝ F X ⇒βs* Fⁿ X`;
* `Basic41Finset.succ_church` — `succ ⌜n⌝ ⇒βs* ⌜n+1⌝`;
* `Basic41Finset.plus_church` — `plus ⌜m⌝ ⌜n⌝ ⇒βs* ⌜m+n⌝`;
* `Basic41Finset.mult_church` — `mult ⌜m⌝ ⌜n⌝ ⇒βs* ⌜m*n⌝`;
* `Basic41Finset.normalS_church`, `Basic41Finset.church_inj` — each numeral is
  a normal form and distinct numbers give distinct numerals, hence
  `Basic41Finset.church_betaEqS_iff` : `⌜m⌝ ≡βs ⌜n⌝ ↔ m = n`, i.e. **distinct
  numerals are never β-convertible** (so the arithmetic above is meaningful).
-/

namespace Basic41FinsetNOfFreeIsExact

open SigmaTerm

/-! ### Iterated application -/

/-- `iterApp n F X` is the `n`-fold application `F (F (… (F X)))`. -/
def iterApp : Nat → SigmaTerm → SigmaTerm → SigmaTerm
  | 0, _, X => X
  | n + 1, F, X => app F (iterApp n F X)

@[simp] theorem iterApp_zero (F X : SigmaTerm) : iterApp 0 F X = X := rfl

@[simp] theorem iterApp_succ (n : Nat) (F X : SigmaTerm) :
    iterApp (n + 1) F X = app F (iterApp n F X) := rfl

theorem iterApp_add (m n : Nat) (F X : SigmaTerm) :
    iterApp (m + n) F X = iterApp m F (iterApp n F X) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega, iterApp_succ, ih, iterApp_succ]

@[simp] theorem shift_iterApp (c n : Nat) (F X : SigmaTerm) :
    SigmaTerm.shift c (iterApp n F X)
      = iterApp n (SigmaTerm.shift c F) (SigmaTerm.shift c X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterApp_succ, shift_app, ih, iterApp_succ]

@[simp] theorem subst_iterApp (j n : Nat) (N F X : SigmaTerm) :
    SigmaTerm.subst j N (iterApp n F X)
      = iterApp n (SigmaTerm.subst j N F) (SigmaTerm.subst j N X) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterApp_succ, subst_app, ih, iterApp_succ]

/-- Iterated application is a congruence for reduction in its argument. -/
theorem betaStarS_iterApp_right (n : Nat) (F : SigmaTerm) {X X' : SigmaTerm}
    (h : X ⇒βs* X') : iterApp n F X ⇒βs* iterApp n F X' := by
  induction n with
  | zero => exact h
  | succ n ih => exact betaStarS_app_right F ih

/-! ### The numerals -/

/-- The Church numeral `⌜n⌝ = λf. λx. fⁿ x`. -/
def church (n : Nat) : SigmaTerm := abs (abs (iterApp n (var 1) (var 0)))

@[simp] theorem shift_church (c n : Nat) : SigmaTerm.shift c (church n) = church n := by
  have h1 : ¬ (1 ≥ c + 1 + 1) := by omega
  have h0 : ¬ (0 ≥ c + 1 + 1) := by omega
  simp [church, h1, h0]

@[simp] theorem subst_church (j : Nat) (N : SigmaTerm) (n : Nat) :
    SigmaTerm.subst j N (church n) = church n := by
  have h1' : ¬ (1 > j + 1 + 1) := by omega
  have h0' : ¬ (0 > j + 1 + 1) := by omega
  simp [church, h1', h0']

/-- One β-step applies a numeral to its first argument. -/
theorem stepS_church_app (n : Nat) (F : SigmaTerm) :
    app (church n) F →βs abs (iterApp n (SigmaTerm.shift 0 F) (var 0)) := by
  have h := StepS.head (abs (iterApp n (var 1) (var 0))) F
  simpa [church] using h

/-! ### The defining property of the Church numerals: `⌜n⌝ F X` reduces to the
`n`-fold application `Fⁿ X`. -/
theorem church_app (n : Nat) (F X : SigmaTerm) :
    app (app (church n) F) X ⇒βs* iterApp n F X := by
  refine Relation.ReflTransGen.head
    (StepS.app_left (stepS_church_app n F) X) (Relation.ReflTransGen.single ?_)
  have h := StepS.head (iterApp n (SigmaTerm.shift 0 F) (var 0)) X
  simpa [SigmaTerm.subst_shift] using h

/-! ### Successor -/

/-- The successor combinator `succ = λn. λf. λx. f (n f x)`. -/
def succTerm : SigmaTerm :=
  abs (abs (abs (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- **Correctness of the successor combinator**: `succ ⌜n⌝ ⇒βs* ⌜n+1⌝`. -/
theorem succ_church (n : Nat) : app succTerm (church n) ⇒βs* church (n + 1) := by
  refine Relation.ReflTransGen.head (b := abs (abs (app (var 1)
      (app (app (church n) (var 1)) (var 0))))) ?_ ?_
  · have h := StepS.head (abs (abs (app (var 1) (app (app (var 2) (var 1)) (var 0)))))
      (church n)
    simpa [succTerm] using h
  · exact betaStarS_abs (betaStarS_abs
      (betaStarS_app_right (var 1) (church_app n (var 1) (var 0))))

/-! ### Addition -/

/-- The addition combinator `plus = λm. λn. λf. λx. m f (n f x)`. -/
def plusTerm : SigmaTerm :=
  abs (abs (abs (abs (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))

/-- **Correctness of the addition combinator**: `plus ⌜m⌝ ⌜n⌝ ⇒βs* ⌜m+n⌝`. -/
theorem plus_church (m n : Nat) :
    app (app plusTerm (church m)) (church n) ⇒βs* church (m + n) := by
  have step1 : app plusTerm (church m) →βs
      abs (abs (abs (app (app (church m) (var 1)) (app (app (var 2) (var 1)) (var 0))))) := by
    have h := StepS.head
      (abs (abs (abs (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))
      (church m)
    simpa [plusTerm] using h
  have step2 : app (abs (abs (abs (app (app (church m) (var 1))
        (app (app (var 2) (var 1)) (var 0)))))) (church n) →βs
      abs (abs (app (app (church m) (var 1)) (app (app (church n) (var 1)) (var 0)))) := by
    have h := StepS.head
      (abs (abs (app (app (church m) (var 1)) (app (app (var 2) (var 1)) (var 0)))))
      (church n)
    simpa using h
  refine Relation.ReflTransGen.head (StepS.app_left step1 (church n))
    (Relation.ReflTransGen.head step2 ?_)
  refine betaStarS_abs (betaStarS_abs ?_)
  refine Relation.ReflTransGen.trans
    (betaStarS_app_right _ (church_app n (var 1) (var 0))) ?_
  rw [iterApp_add]
  exact church_app m (var 1) (iterApp n (var 1) (var 0))

/-! ### Multiplication -/

/-- The multiplication combinator `mult = λm. λn. λf. m (n f)`. -/
def multTerm : SigmaTerm := abs (abs (abs (app (var 2) (app (var 1) (var 0)))))

/-- Iterating "apply the numeral `⌜n⌝` to `F`" `m` times is the same, up to
reduction, as iterating `F` itself `n*m` times. -/
theorem betaStarS_iterApp_church (m n : Nat) (F X : SigmaTerm) :
    iterApp m (app (church n) F) X ⇒βs* iterApp (n * m) F X := by
  induction m with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ m ih =>
    refine Relation.ReflTransGen.trans (betaStarS_app_right _ ih) ?_
    refine Relation.ReflTransGen.trans (church_app n F (iterApp (n * m) F X)) ?_
    rw [show n * (m + 1) = n + n * m by ring, iterApp_add]

/-- **Correctness of the multiplication combinator**: `mult ⌜m⌝ ⌜n⌝ ⇒βs* ⌜m*n⌝`. -/
theorem mult_church (m n : Nat) :
    app (app multTerm (church m)) (church n) ⇒βs* church (m * n) := by
  have step1 : app multTerm (church m) →βs
      abs (abs (app (church m) (app (var 1) (var 0)))) := by
    have h := StepS.head (abs (abs (app (var 2) (app (var 1) (var 0))))) (church m)
    simpa [multTerm] using h
  have step2 : app (abs (abs (app (church m) (app (var 1) (var 0))))) (church n) →βs
      abs (app (church m) (app (church n) (var 0))) := by
    have h := StepS.head (abs (app (church m) (app (var 1) (var 0)))) (church n)
    simpa using h
  refine Relation.ReflTransGen.head (StepS.app_left step1 (church n))
    (Relation.ReflTransGen.head step2 ?_)
  refine betaStarS_abs ?_
  refine Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (stepS_church_app m (app (church n) (var 0)))) ?_
  rw [shift_app, shift_church, shift_var, if_pos (Nat.zero_le 0)]
  refine betaStarS_abs ?_
  refine Relation.ReflTransGen.trans (betaStarS_iterApp_church m n (var 1) (var 0)) ?_
  rw [Nat.mul_comm n m]

/-! ### Numerals are distinct normal forms -/

theorem normalS_iterApp_var (n : Nat) : NormalS (iterApp n (var 1) (var 0)) := by
  induction n with
  | zero => exact normalS_var 0
  | succ n ih => exact NormalS.app (normalS_var 1) ih (fun t0 => by simp)

/-- Every Church numeral is a normal form. -/
theorem normalS_church (n : Nat) : NormalS (church n) :=
  ((normalS_iterApp_var n).abs).abs

theorem iterApp_var_inj {m n : Nat}
    (h : iterApp m (var 1) (var 0) = iterApp n (var 1) (var 0)) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact absurd h (by simp [iterApp])
  | succ m ih =>
    cases n with
    | zero => exact absurd h (by simp [iterApp])
    | succ n =>
      rw [iterApp_succ, iterApp_succ, app_inj] at h
      exact congrArg Nat.succ (ih h.2)

/-- Distinct numbers have distinct Church numerals. -/
theorem church_inj {m n : Nat} (h : church m = church n) : m = n :=
  iterApp_var_inj (abs_inj.mp (abs_inj.mp h))

/-- **Distinct Church numerals are not β-convertible.**  Together with the
correctness theorems above, this is what makes Church-numeral arithmetic
meaningful. -/
theorem church_betaEqS_iff {m n : Nat} : church m ≡βs church n ↔ m = n :=
  ⟨fun h => church_inj (betaEqS_eq_of_normal h (normalS_church m) (normalS_church n)),
    fun h => h ▸ Relation.EqvGen.refl _⟩

/-! ### The numerals are closed -/

theorem newFreeIndexes_iterApp_var (n : Nat) :
    (iterApp n (var 1) (var 0)).newFreeIndexes ⊆ {0, 1} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterApp_succ, newFreeIndexes_app]
    exact Finset.union_subset (by simp) ih

/-- Church numerals are closed: they have no free variables. -/
theorem church_closed (n : Nat) : (church n).newFreeIndexes = ∅ := by
  refine Finset.subset_empty.mp ?_
  have h := unbind_subset (unbind_subset (newFreeIndexes_iterApp_var n))
  have h2 : unbind (unbind ({0, 1} : Finset Nat)) = ∅ := by decide
  rw [h2] at h
  exact h

/-! ### The numerals of the source file

The Church numerals and the successor combinator defined in
`Basic41FinsetNOfFreeIsExact.lean` are exactly the ones above. -/

theorem pack_Term_zero : pack Term.zero = church 0 := by
  unfold Term.zero; rw [pack_castTerm]; rfl

theorem pack_Term_one : pack Term.one = church 1 := by
  unfold Term.one; rw [pack_castTerm]; rfl

theorem pack_Term_two : pack Term.two = church 2 := by
  unfold Term.two; rw [pack_castTerm]; rfl

theorem pack_Term_succ : pack Term.succ = succTerm := by
  unfold Term.succ; rw [pack_castTerm]; rfl

/-- `succ ⌜0⌝` β-reduces to `⌜1⌝`, for the very terms of the source file. -/
theorem Term_succ_zero : Term.app Term.succ Term.zero ⇒β* Term.one := by
  show app (pack Term.succ) (pack Term.zero) ⇒βs* pack Term.one
  rw [pack_Term_succ, pack_Term_zero, pack_Term_one]
  exact succ_church 0

/-- `succ ⌜1⌝` β-reduces to `⌜2⌝`, for the very terms of the source file. -/
theorem Term_succ_one : Term.app Term.succ Term.one ⇒β* Term.two := by
  show app (pack Term.succ) (pack Term.one) ⇒βs* pack Term.two
  rw [pack_Term_succ, pack_Term_one, pack_Term_two]
  exact succ_church 1

end Basic41FinsetNOfFreeIsExact
