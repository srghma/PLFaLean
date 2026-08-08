module
public import Plfl.ReallyUntypedLambda.Basic41FinsetNOfFreeIsExact.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Terms packaged with their (existentially quantified) free-variable index

`Basic41Finset.Term s` is indexed by the *exact* set `s` of its free variables,
so an operation such as shifting, substitution or β-reduction changes the index.
Rather than erasing the index (which would amount to reintroducing an untyped
syntax), we package a term together with the index it lives at:

```
structure SigmaTerm where
  newFreeIndexes : Finset Nat
  betaReducedTermTree : Term newFreeIndexes
```

so every operation *returns an existential*: the new free-variable index set
together with the resulting term tree.  Equations between packaged terms are
ordinary (homogeneous) equalities, which makes the substitution calculus
provable by plain `induction`/`rw`, without any heterogeneous-equality
bookkeeping and without any auxiliary untyped syntax.
-/

namespace Basic41FinsetNOfFreeIsExact

/-- A λ-term together with the exact set of free variables it uses.

The two fields are the *existential witness* (`newFreeIndexes`, the free-variable
index set the term lives at) and the term itself (`betaReducedTermTree`). -/
structure SigmaTerm where
  /-- The exact set of free variables of the packaged term. -/
  newFreeIndexes : Finset Nat
  /-- The term itself, indexed by `newFreeIndexes`. -/
  betaReducedTermTree : Term newFreeIndexes

/-- Package an indexed term into a `SigmaTerm`. -/
def pack {s : Finset Nat} (M : Term s) : SigmaTerm := ⟨s, M⟩

@[simp] theorem pack_fst {s : Finset Nat} (M : Term s) : (pack M).newFreeIndexes = s := rfl
@[simp] theorem pack_snd {s : Finset Nat} (M : Term s) : (pack M).betaReducedTermTree = M := rfl
theorem pack_eta (t : SigmaTerm) : pack t.betaReducedTermTree = t := rfl

@[simp] theorem pack_castTerm {s s' : Finset Nat} (M : Term s) (h : s = s') :
    pack (castTerm M h) = pack M := by
  subst h; rfl

/-- Two packaged terms are equal exactly when the indices agree and the terms are
heterogeneously equal. -/
theorem pack_eq_iff {s s' : Finset Nat} {M : Term s} {N : Term s'} :
    pack M = pack N ↔ s = s' ∧ HEq M N := by
  simp [pack, SigmaTerm.mk.injEq]

theorem eq_of_pack_eq {s : Finset Nat} {M N : Term s} (h : pack M = pack N) : M = N :=
  eq_of_heq ((pack_eq_iff.mp h).2)

namespace SigmaTerm

/-- The packaged variable term. -/
def var (i : Nat) : SigmaTerm := pack (Term.var i)

/-- Packaged λ-abstraction. -/
def abs (t : SigmaTerm) : SigmaTerm := pack (Term.abs t.betaReducedTermTree)

/-- Packaged application. -/
def app (t u : SigmaTerm) : SigmaTerm :=
  pack (Term.app t.betaReducedTermTree u.betaReducedTermTree)

/-- Packaged shifting. -/
def shift (c : Nat) (t : SigmaTerm) : SigmaTerm :=
  pack (Basic41FinsetNOfFreeIsExact.shift c t.betaReducedTermTree)

/-- Packaged substitution. -/
def subst (j : Nat) (N t : SigmaTerm) : SigmaTerm :=
  pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree t.betaReducedTermTree)

@[simp] theorem pack_var (i : Nat) : pack (Term.var i) = var i := rfl
@[simp] theorem pack_abs {s : Finset Nat} (P : Term s) : pack (Term.abs P) = abs (pack P) := rfl
@[simp] theorem pack_app {s1 s2 : Finset Nat} (P : Term s1) (Q : Term s2) :
    pack (Term.app P Q) = app (pack P) (pack Q) := rfl
@[simp] theorem pack_shift {s : Finset Nat} (c : Nat) (M : Term s) :
    pack (Basic41FinsetNOfFreeIsExact.shift c M) = shift c (pack M) := rfl
@[simp] theorem pack_subst {s sN : Finset Nat} (j : Nat) (N : Term sN) (M : Term s) :
    pack (Basic41FinsetNOfFreeIsExact.subst j N M) = subst j (pack N) (pack M) := rfl

@[simp] theorem pack_betaSubst {s sN : Finset Nat} (M : Term s) (N : Term sN) :
    pack (Term.betaSubst M N) = subst 0 (pack N) (pack M) := rfl

/-- Induction principle: every packaged term is a variable, an abstraction or an
application of packaged terms. -/
@[elab_as_elim]
theorem induction {P : SigmaTerm → Prop} (hvar : ∀ i, P (var i))
    (habs : ∀ t, P t → P (abs t)) (happ : ∀ t u, P t → P u → P (app t u)) :
    ∀ t, P t := by
  rintro ⟨s, M⟩
  show P (pack M)
  induction M with
  | var i => exact hvar i
  | abs P ih => exact habs _ ih
  | app P Q ihP ihQ => exact happ _ _ ihP ihQ

/-! ### Computation rules for `shift` and `subst` -/

@[simp] theorem shift_var (c i : Nat) : shift c (var i) = var (if i ≥ c then i + 1 else i) := by
  by_cases h : i ≥ c
  · rw [if_pos h]
    show pack (Basic41FinsetNOfFreeIsExact.shift c (Term.var i)) = pack (Term.var (i + 1))
    rw [Basic41FinsetNOfFreeIsExact.shift, dif_pos h, pack_castTerm]
  · rw [if_neg h]
    show pack (Basic41FinsetNOfFreeIsExact.shift c (Term.var i)) = pack (Term.var i)
    rw [Basic41FinsetNOfFreeIsExact.shift, dif_neg h, pack_castTerm]

@[simp] theorem shift_abs (c : Nat) (t : SigmaTerm) : shift c (abs t) = abs (shift (c + 1) t) := by
  show pack (Basic41FinsetNOfFreeIsExact.shift c (Term.abs t.betaReducedTermTree))
      = pack (Term.abs (Basic41FinsetNOfFreeIsExact.shift (c + 1) t.betaReducedTermTree))
  rw [Basic41FinsetNOfFreeIsExact.shift, pack_castTerm]

@[simp] theorem shift_app (c : Nat) (t u : SigmaTerm) :
    shift c (app t u) = app (shift c t) (shift c u) := by
  show pack (Basic41FinsetNOfFreeIsExact.shift c (Term.app t.betaReducedTermTree u.betaReducedTermTree))
      = pack (Term.app (Basic41FinsetNOfFreeIsExact.shift c t.betaReducedTermTree)
          (Basic41FinsetNOfFreeIsExact.shift c u.betaReducedTermTree))
  rw [Basic41FinsetNOfFreeIsExact.shift, pack_castTerm]

@[simp] theorem subst_var (j : Nat) (N : SigmaTerm) (i : Nat) :
    subst j N (var i) = if i = j then N else if i > j then var (i - 1) else var i := by
  by_cases h1 : i = j
  · rw [if_pos h1]
    show pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree (Term.var i)) = N
    rw [Basic41FinsetNOfFreeIsExact.subst, dif_pos h1, pack_castTerm, pack_eta]
  · rw [if_neg h1]
    by_cases h2 : i > j
    · rw [if_pos h2]
      show pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree (Term.var i))
          = pack (Term.var (i - 1))
      rw [Basic41FinsetNOfFreeIsExact.subst, dif_neg h1, dif_pos h2, pack_castTerm]
    · rw [if_neg h2]
      show pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree (Term.var i)) = pack (Term.var i)
      rw [Basic41FinsetNOfFreeIsExact.subst, dif_neg h1, dif_neg h2, pack_castTerm]

@[simp] theorem subst_abs (j : Nat) (N t : SigmaTerm) :
    subst j N (abs t) = abs (subst (j + 1) (shift 0 N) t) := by
  show pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree (Term.abs t.betaReducedTermTree))
      = pack (Term.abs (Basic41FinsetNOfFreeIsExact.subst (j + 1) (Basic41FinsetNOfFreeIsExact.shift 0 N.betaReducedTermTree)
          t.betaReducedTermTree))
  rw [Basic41FinsetNOfFreeIsExact.subst, pack_castTerm]

@[simp] theorem subst_app (j : Nat) (N t u : SigmaTerm) :
    subst j N (app t u) = app (subst j N t) (subst j N u) := by
  show pack (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree
        (Term.app t.betaReducedTermTree u.betaReducedTermTree))
      = pack (Term.app (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree t.betaReducedTermTree)
          (Basic41FinsetNOfFreeIsExact.subst j N.betaReducedTermTree u.betaReducedTermTree))
  rw [Basic41FinsetNOfFreeIsExact.subst, pack_castTerm]

/-! ### Injectivity and disjointness of the constructors -/

/-- Which constructor the packaged term is built from. -/
def shape : SigmaTerm → Nat
  | ⟨_, Term.var _⟩ => 0
  | ⟨_, Term.abs _⟩ => 1
  | ⟨_, Term.app _ _⟩ => 2

@[simp] theorem shape_var (i : Nat) : shape (var i) = 0 := rfl
@[simp] theorem shape_abs (t : SigmaTerm) : shape (abs t) = 1 := rfl
@[simp] theorem shape_app (t u : SigmaTerm) : shape (app t u) = 2 := rfl

/-- The body of an abstraction (the identity on non-abstractions). -/
def unabs : SigmaTerm → SigmaTerm
  | ⟨_, Term.abs P⟩ => pack P
  | t => t

/-- The function part of an application (the identity on non-applications). -/
def fnPart : SigmaTerm → SigmaTerm
  | ⟨_, Term.app P _⟩ => pack P
  | t => t

/-- The argument part of an application (the identity on non-applications). -/
def argPart : SigmaTerm → SigmaTerm
  | ⟨_, Term.app _ Q⟩ => pack Q
  | t => t

@[simp] theorem unabs_abs (t : SigmaTerm) : unabs (abs t) = t := rfl
@[simp] theorem fnPart_app (t u : SigmaTerm) : fnPart (app t u) = t := rfl
@[simp] theorem argPart_app (t u : SigmaTerm) : argPart (app t u) = u := rfl

@[simp] theorem abs_inj {t u : SigmaTerm} : abs t = abs u ↔ t = u :=
  ⟨fun h => by simpa using congrArg unabs h, fun h => h ▸ rfl⟩

@[simp] theorem app_inj {t u t' u' : SigmaTerm} : app t u = app t' u' ↔ t = t' ∧ u = u' :=
  ⟨fun h => ⟨by simpa using congrArg fnPart h, by simpa using congrArg argPart h⟩,
    fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩

@[simp] theorem abs_ne_var (t : SigmaTerm) (i : Nat) : abs t ≠ var i := by
  intro h; simpa using congrArg shape h

@[simp] theorem abs_ne_app (t u v : SigmaTerm) : abs t ≠ app u v := by
  intro h; simpa using congrArg shape h

@[simp] theorem var_ne_abs (i : Nat) (t : SigmaTerm) : var i ≠ abs t := by
  intro h; simpa using congrArg shape h

@[simp] theorem var_ne_app (i : Nat) (u v : SigmaTerm) : var i ≠ app u v := by
  intro h; simpa using congrArg shape h

@[simp] theorem app_ne_var (u v : SigmaTerm) (i : Nat) : app u v ≠ var i := by
  intro h; simpa using congrArg shape h

@[simp] theorem app_ne_abs (u v t : SigmaTerm) : app u v ≠ abs t := by
  intro h; simpa using congrArg shape h

/-! ### The substitution calculus -/

/-- Two shifts commute (with the appropriate index bookkeeping). -/
theorem shift_shift (t : SigmaTerm) : ∀ (j c : Nat), j ≤ c →
    shift (c + 1) (shift j t) = shift j (shift c t) := by
  induction t using SigmaTerm.induction with
  | hvar i =>
    intro j c h
    simp only [shift_var]
    split_ifs <;> first | rfl | (congr 1; omega)
  | habs t ih =>
    intro j c h
    simp only [shift_abs]
    exact congrArg abs (ih (j + 1) (c + 1) (by omega))
  | happ t u iht ihu =>
    intro j c h
    simp only [shift_app]
    exact congrArg₂ app (iht j c h) (ihu j c h)

/-- Substituting at `c` immediately after shifting at `c` is the identity. -/
theorem subst_shift (t : SigmaTerm) : ∀ (c : Nat) (X : SigmaTerm), subst c X (shift c t) = t := by
  induction t using SigmaTerm.induction with
  | hvar i =>
    intro c X
    simp only [shift_var, subst_var]
    split_ifs <;> first | rfl | (congr 1; omega)
  | habs t ih => intro c X; simp only [shift_abs, subst_abs, ih]
  | happ t u iht ihu => intro c X; simp only [shift_app, subst_app, iht, ihu]

/-- Commutation of a shift below the substituted variable. -/
theorem shift_subst_le (A : SigmaTerm) : ∀ (c j : Nat) (N : SigmaTerm), c ≤ j →
    shift c (subst j N A) = subst (j + 1) (shift c N) (shift c A) := by
  induction A using SigmaTerm.induction with
  | hvar i =>
    intro c j N h
    simp only [subst_var, shift_var]
    by_cases h1 : i = j
    · subst h1
      have hic : i ≥ c := h
      simp [hic]
    · by_cases h2 : i > j
      · have hic : i ≥ c := by omega
        have h3 : i - 1 ≥ c := by omega
        have h4 : ¬ (i + 1 = j + 1) := by omega
        have h5 : i + 1 > j + 1 := by omega
        simp only [h1, h2, if_false, if_true, if_pos hic, shift_var, if_pos h3, h4, h5]
        congr 1
        omega
      · have hij : i < j := by omega
        simp only [h1, h2, if_false, shift_var]
        split
        · have h5 : ¬ (i + 1 > j + 1) := by omega
          simp [h1, h5]
        · have h4 : ¬ (i = j + 1) := by omega
          have h5 : ¬ (i > j + 1) := by omega
          simp [h4, h5]
  | habs A ih =>
    intro c j N h
    simp only [subst_abs, shift_abs]
    rw [ih (c + 1) (j + 1) (shift 0 N) (by omega)]
    rw [shift_shift N 0 c (Nat.zero_le c)]
  | happ A B ihA ihB =>
    intro c j N h
    simp only [subst_app, shift_app, ihA c j N h, ihB c j N h]

/-- Commutation of a shift above the substituted variable. -/
theorem shift_subst_ge (A : SigmaTerm) : ∀ (c j : Nat) (N : SigmaTerm), j ≤ c →
    shift c (subst j N A) = subst j (shift c N) (shift (c + 1) A) := by
  induction A using SigmaTerm.induction with
  | hvar i =>
    intro c j N h
    simp only [subst_var, shift_var]
    by_cases h1 : i = j
    · subst h1
      have h2 : ¬ (i ≥ c + 1) := by omega
      simp [h2]
    · by_cases h2 : i > j
      · simp only [h1, h2, if_false, if_true]
        by_cases h3 : i ≥ c + 1
        · have h4 : i - 1 ≥ c := by omega
          have h5 : ¬ (i + 1 = j) := by omega
          have h6 : i + 1 > j := by omega
          simp only [shift_var, if_pos h3, if_pos h4, h5, h6, if_false, if_true]
          congr 1
          omega
        · have h4 : ¬ (i - 1 ≥ c) := by omega
          have h6 : i > j := by omega
          simp only [shift_var, h3, h4, if_false, h1, h6, if_true]
      · have hij : i < j := by omega
        have h3 : ¬ (i ≥ c + 1) := by omega
        have h4 : ¬ (i ≥ c) := by omega
        simp [h1, h2, h3, h4]
  | habs A ih =>
    intro c j N h
    simp only [subst_abs, shift_abs]
    rw [ih (c + 1) (j + 1) (shift 0 N) (by omega)]
    rw [shift_shift N 0 c (Nat.zero_le c)]
  | happ A B ihA ihB =>
    intro c j N h
    simp only [subst_app, shift_app, ihA c j N h, ihB c j N h]

/-- The substitution lemma. -/
theorem subst_subst (A : SigmaTerm) : ∀ (i j : Nat) (B N : SigmaTerm), i ≤ j →
    subst j N (subst i B A) = subst i (subst j N B) (subst (j + 1) (shift i N) A) := by
  induction A using SigmaTerm.induction with
  | hvar k =>
    intro i j B N h
    by_cases h1 : k = i
    · subst h1
      have h2 : ¬ (k = j + 1) := by omega
      have h3 : ¬ (k > j + 1) := by omega
      simp [h2, h3]
    · by_cases h2 : k > i
      · simp only [subst_var, h1, h2, if_false, if_true]
        by_cases h3 : k - 1 = j
        · have h4 : k = j + 1 := by omega
          subst h4
          simp only [Nat.add_sub_cancel]
          exact (subst_shift N i (subst j N B)).symm
        · by_cases h4 : k - 1 > j
          · have h5 : ¬ (k = j + 1) := by omega
            have h6 : k > j + 1 := by omega
            have h7 : ¬ (k - 1 = i) := by omega
            have h8 : k - 1 > i := by omega
            simp [h3, h4, h5, h6, h7, h8]
          · have h5 : ¬ (k = j + 1) := by omega
            have h6 : ¬ (k > j + 1) := by omega
            have h7 : ¬ (k = i) := by omega
            have h8 : k > i := by omega
            simp [h3, h4, h5, h6, h7, h8]
      · have hki : k < i := by omega
        have h3 : ¬ (k = j + 1) := by omega
        have h4 : ¬ (k > j + 1) := by omega
        have h5 : ¬ (k = j) := by omega
        have h6 : ¬ (k > j) := by omega
        simp [h1, h2, h3, h4, h5, h6]
  | habs A ih =>
    intro i j B N h
    simp only [subst_abs]
    rw [ih (i + 1) (j + 1) (shift 0 B) (shift 0 N) (by omega)]
    rw [← shift_subst_le B 0 j N (Nat.zero_le j)]
    rw [shift_shift N 0 i (Nat.zero_le i)]
  | happ A B' ihA ihB =>
    intro i j B N h
    simp only [subst_app, ihA i j B N h, ihB i j B N h]

/-- The instance of `subst_subst` used for the parallel-reduction substitution lemma. -/
theorem subst_subst_zero (A B N : SigmaTerm) (j : Nat) :
    subst j N (subst 0 B A) = subst 0 (subst j N B) (subst (j + 1) (shift 0 N) A) :=
  subst_subst A 0 j B N (Nat.zero_le j)

end SigmaTerm

end Basic41FinsetNOfFreeIsExact
