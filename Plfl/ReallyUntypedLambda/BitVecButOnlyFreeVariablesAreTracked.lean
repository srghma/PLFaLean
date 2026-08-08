module
public import Mathlib.Logic.Relation
public import Aesop

@[expose] public section

namespace Basic43BitVec

attribute [-instance] Fin.instOfNat
attribute [-instance] Lean.Grind.Semiring.ofNat

/-! ## Helper functions, extracted from the constructors -/

/-- A width-`n` mask with only bit `i` set. Used by `Term.var`. -/
abbrev singletonMask (n : Nat) (i : Fin n) : BitVec n :=
  (0b1#n) <<< i.val

/-- Drop the innermost scope slot (bit 0) and narrow the scope by one.
Used by `Term.abs` to update the free-variable scope mask. -/
abbrev popScope {n : Nat} (s : BitVec (n + 1)) : BitVec n :=
  (s >>> 1).truncate n

/-- Union two scope masks of the same width. Used by `Term.app`. -/
abbrev mergeScope {n : Nat} (s1 s2 : BitVec n) : BitVec n :=
  s1 ||| s2

-- #guard demonstrations: bit i=2 set in a width-4 mask
#guard singletonMask 4 ⟨2, by decide⟩ = 0b0100#4

-- popScope: drop bit 0 of 0b101 (width 3) -> 0b10 (width 2)
#guard popScope (0b101#3) = 0b10#2
#guard popScope (0b100#3) = 0b10#2

-- mergeScope: bitwise-or of two width-4 masks
#guard mergeScope (0b1010#4) (0b0110#4) = 0b1110#4

/-! ## The inductive family, with n auto-bound (inferred from the BitVec width) -/
/--
`Term s`:
  the scope size `n` is inferred automatically from the width of `s : BitVec n` (used free variables).
-/
inductive Term : BitVec n → Type
  | var : {n : Nat} → (i : Fin n) → Term (singletonMask n i)
  | abs : {n : Nat} → {s : BitVec (n + 1)} →
      Term s →
      Term (popScope s)
  | app : {n : Nat} → {s1 s2 : BitVec n} →
      Term s1 → Term s2 →
      Term (mergeScope s1 s2)
deriving Repr

/-- Cast a term when its bitvec index is propositionally, but not
definitionally, equal. `n` here is pinned to be literally the
same on both sides (only the mask *value* differs), so `castTerm` never
needs to change the scope size itself. -/
def castTerm {n : Nat} {s : BitVec n} (t : Term s)
    {s' : BitVec n} (hs : s = s') : Term s' := by
  subst hs; exact t

/-- Helper lemma: $c < 2^k \implies c < 2^{n+k}$ for any $n$. -/
theorem lt_two_pow_add (n : Nat) {k c : Nat} (hc : c < 2 ^ k) : c < 2 ^ (n + k) := by
  induction n with
  | zero => simp_all only [Nat.zero_add]
  | succ n ih =>
    have hpow : 2 ^ (n + 1 + k) = 2 ^ (n + k) * 2 := by grind only
    rw [hpow]
    omega

/-- Helper lemma: $c < 2^k \implies c \pmod{2^{n+k}} = c$. -/
theorem mod_two_pow_add_eq (n : Nat) {k c : Nat} (hc : c < 2 ^ k) :
    c % 2 ^ (n + k) = c :=
  Nat.mod_eq_of_lt (lt_two_pow_add n hc)

syntax "bv_auto" : tactic
macro_rules
  | `(tactic| bv_auto) => `(tactic| (
      try (intros; subst_vars);
      first
      | -- concrete goals: simp and then decide
        (simp [singletonMask, popScope, mergeScope]; decide)
      | -- "scope"-shaped goals: symbolic n, work in toNat-land.
        (unfold singletonMask popScope mergeScope;
         apply BitVec.eq_of_toNat_eq;
         simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               BitVec.toNat_ushiftRight, BitVec.toNat_zero,
               BitVec.toNat_or, BitVec.toNat_ushiftLeft];
         repeat rw [Nat.shiftRight_eq_div_pow];
         repeat (first | rw [mod_two_pow_add_eq _ (by decide)] | simp);
         omega)
      | decide
  ))

macro "⟦" t:term "⟧" : term => `(castTerm $t (by bv_auto))

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term => `(Term.var (n := $n) (Fin.mk $i (by try omega; try decide)))

namespace TermsConcrete

def id : Term (0#0) := ⟦ƛ (# 0)⟧
def const : Term (0b0#0) := ⟦ƛ (ƛ (##[2] 1))⟧
def zero  : Term (0b0#0) := ⟦ƛ (ƛ (##[2] 0))⟧
def one   : Term (0b0#0) := ⟦ƛ (ƛ (##[2] 1 ⬝ # 0))⟧
def two   : Term (0b0#0) := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0)))⟧
def three : Term (0b0#0) := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0))))⟧
def succ  : Term (0b0#0) := ⟦ƛ (ƛ (ƛ (##[3] 1 ⬝ ((##[3] 2 ⬝ ##[3] 1) ⬝ # 0))))⟧

def freeTerm : Term (0b11#2) := ⟦##[2] 0 ⬝ ##[2] 1⟧
def boundAndFree : Term (0b1#1) := ⟦ƛ (# 0 ⬝ ##[2] 1)⟧

end TermsConcrete

namespace TermWithCustomProofs

def id {n : Nat} : Term (0#n) :=
  castTerm (ƛ (# 0))
    (show popScope (singletonMask (n + 1) 0) = 0#n by
      unfold popScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    )

def const {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ (##[n+2] 1))
    (by
      unfold popScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have h1 : 2 < 2 ^ (n + 2) := by
        have : 2 ^ (n + 2) = 2 ^ n * 4 := by grind only
        rw [this]
        have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        omega
      have h2 : 1 < 2 ^ (n + 1) := by
        have : 2 ^ (n + 1) = 2 ^ n * 2 := by grind only
        rw [this]
        have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        omega
      rw [Nat.mod_eq_of_lt h1]
      simp
    )

def zero {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ (##[n+2] 0))
    (by
      unfold popScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight])

def one {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ (##[n+2] 1 ⬝ # 0))
    (by
      unfold popScope mergeScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_or]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have h2 : 2 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      have h1 : 1 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      rw [Nat.mod_eq_of_lt h2]
      simp only [Nat.reduceOr, Nat.pow_one, Nat.reduceDiv, Nat.zero_lt_succ, Nat.one_mod_two_pow, Nat.zero_mod]
      )

def two {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ # 0)))
    (by
      unfold popScope mergeScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_or]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have h2 : 2 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      have h1 : 1 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      rw [Nat.mod_eq_of_lt h2]
      simp only [Nat.reduceOr, Nat.pow_one, Nat.reduceDiv, Nat.zero_lt_succ, Nat.one_mod_two_pow, Nat.zero_mod]
    )

def three {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ # 0))))
    (by
      unfold popScope mergeScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp only [Fin.val_zero, BitVec.shiftLeft_zero, BitVec.truncate_eq_setWidth,
        BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft,
        BitVec.toNat_ofNat, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, Nat.one_mod_two_pow,
        Nat.reduceShiftLeft, Nat.zero_mod]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have h2 : 2 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      have h1 : 1 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      rw [Nat.mod_eq_of_lt h2]
      simp only [Nat.reduceOr, Nat.pow_one, Nat.reduceDiv, Nat.zero_lt_succ, Nat.one_mod_two_pow, Nat.zero_mod]
    )

def succ {n : Nat} : Term (0#n) :=
  castTerm (ƛ ƛ ƛ (##[n+3] 1 ⬝ ((##[n+3] 2 ⬝ ##[n+3] 1) ⬝ # 0)))
    (by
      unfold popScope mergeScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp only [Fin.val_zero, BitVec.shiftLeft_zero, BitVec.truncate_eq_setWidth,
        BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft,
        BitVec.toNat_ofNat, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, Nat.one_mod_two_pow,
        Nat.reduceShiftLeft, Nat.zero_mod]
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have h4 : 4 < 2 ^ (n + 3) := lt_two_pow_add n (by decide)
      have h2 : 2 < 2 ^ (n + 3) := lt_two_pow_add n (by decide)
      have h1 : 1 < 2 ^ (n + 3) := lt_two_pow_add n (by decide)
      rw [Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h2]
      simp only [Nat.reduceOr, Nat.pow_one, Nat.reduceDiv]
      have h3 : 3 < 2 ^ (n + 2) := lt_two_pow_add n (by decide)
      rw [Nat.mod_eq_of_lt h3]
      simp only [Nat.reduceDiv, Nat.zero_lt_succ, Nat.one_mod_two_pow, Nat.zero_mod]
    )

end TermWithCustomProofs

-- namespace Term
--
-- def id {n : Nat} : Term (0#n) := ⟦ƛ (# 0)⟧
-- def const {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (##[n+2] 1))⟧
-- def zero  {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (##[n+2] 0))⟧
-- def one   {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ # 0))⟧
-- def two   {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ # 0)))⟧
-- def three {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ two))⟧
-- def succ  {n : Nat} : Term (0#n) := ⟦ƛ (ƛ (ƛ (##[n+3] 1 ⬝ ((##[n+3] 2 ⬝ ##[n+3] 1) ⬝ # 0))))⟧
--
-- end Term

def Term.beq : ∀ {n1 : Nat} {s1 : BitVec n1}
                {n2 : Nat} {s2 : BitVec n2},
    Term s1 → Term s2 → Bool
  | _, _, _, _, Term.var i, t2 =>
      match t2 with
      | Term.var targetIndex => i.val == targetIndex.val
      | _ => false
  | _, _, _, _, Term.abs P, t2 =>
      match t2 with
      | Term.abs Q => Term.beq P Q
      | _ => false
  | _, _, _, _, Term.app P1 P2, t2 =>
      match t2 with
      | Term.app Q1 Q2 => Term.beq P1 Q1 && Term.beq P2 Q2
      | _ => false

instance {n : Nat} {s : BitVec n} : BEq (Term s) where
  beq := Term.beq

theorem termBEq_refl {n : Nat} {s : BitVec n} (t : Term s) :
    Term.beq t t = true := by
  induction t with
  | var i =>
    change (i.val == i.val) = true
    simp_all only [BEq.rfl]
  | abs P ih =>
    change Term.beq P P = true
    exact ih
  | app P Q ihP ihQ =>
    change (Term.beq P P && Term.beq Q Q) = true
    rw [ihP, ihQ]; rfl

instance {n : Nat} {s : BitVec n} : ReflBEq (Term s) where
  rfl {t} := termBEq_refl t

theorem termBEq_heq : ∀ {n : Nat} {s1 : BitVec n} (t1 : Term s1)
    {s2 : BitVec n} (t2 : Term s2),
    Term.beq t1 t2 = true → s1 = s2 ∧ HEq t1 t2 := by
  intro n s1 t1
  induction t1 with
  | var i =>
    intro s2 t2 h
    cases t2 with
    | var targetIndex =>
      change (i.val == targetIndex.val) = true at h
      have hij : i = targetIndex := Fin.ext (eq_of_beq h)
      subst hij
      exact ⟨rfl, HEq.rfl⟩
    | abs Q => exact Bool.noConfusion h
    | app Q1 Q2 => exact Bool.noConfusion h
  | abs P ih =>
    intro s2 t2 h
    cases t2 with
    | var targetIndex => exact Bool.noConfusion h
    | abs Q =>
      change Term.beq P Q = true at h
      obtain ⟨hs, hheq⟩ := ih Q h
      subst hs
      have e : P = Q := eq_of_heq hheq
      subst e
      exact ⟨rfl, HEq.rfl⟩
    | app Q1 Q2 => exact Bool.noConfusion h
  | app P1 P2 ih1 ih2 =>
    intro s2 t2 h
    cases t2 with
    | var targetIndex => exact Bool.noConfusion h
    | abs Q => exact Bool.noConfusion h
    | app Q1 Q2 =>
      change (Term.beq P1 Q1 && Term.beq P2 Q2) = true at h
      have h1 : Term.beq P1 Q1 = true := by
        cases hb : Term.beq P1 Q1
        · simp [hb] at h
        · rfl
      have h2 : Term.beq P2 Q2 = true := by
        cases hb : Term.beq P2 Q2
        · simp [hb] at h
        · rfl
      obtain ⟨hs1, hheq1⟩ := ih1 Q1 h1
      obtain ⟨hs2, hheq2⟩ := ih2 Q2 h2
      subst hs1
      subst hs2
      have e1 : P1 = Q1 := eq_of_heq hheq1
      have e2 : P2 = Q2 := eq_of_heq hheq2
      subst e1; subst e2
      exact ⟨rfl, HEq.rfl⟩

instance {n : Nat} {s : BitVec n} : LawfulBEq (Term s) where
  eq_of_beq {t1 t2} h := eq_of_heq (termBEq_heq t1 t2 h).2

instance {n : Nat} {s : BitVec n} : DecidableEq (Term s) :=
  fun t1 t2 =>
    match h : Term.beq t1 t2 with
    | true  => isTrue (eq_of_heq (termBEq_heq t1 t2 h).2)
    | false => isFalse (by
        intro heq; subst heq
        rw [termBEq_refl t1] at h
        exact absurd h (by decide))

abbrev insertBitAt (c : Nat) {n : Nat} (s : BitVec n) (h : c ≤ n) : BitVec (n + 1) :=
  ((s.extractLsb' c (n - c)) ++ (0#1) ++ (s.extractLsb' 0 c)).cast (by omega)

abbrev removeBitAt (targetIndex : Nat) {n : Nat} (s : BitVec (n + 1)) (h : targetIndex ≤ n) : BitVec n :=
  ((s.extractLsb' (targetIndex + 1) (n - targetIndex)) ++ (s.extractLsb' 0 targetIndex)).cast (by omega)

abbrev shiftMask (c : Nat) {n : Nat} (s : BitVec n) (h : c ≤ n) : BitVec (n + 1) :=
  insertBitAt c s h

abbrev substMask (targetIndex : Nat) {n : Nat} (newPartBitVec : BitVec n) (beforeBitVec : BitVec (n + 1)) (h : targetIndex ≤ n) : BitVec n :=
  removeBitAt targetIndex beforeBitVec h ||| (if beforeBitVec.getLsb ⟨targetIndex, by omega⟩ then newPartBitVec else 0#n)

#guard (substMask 0 0b100#3 0b001#4 (by decide) = 0b100#3) -- [λ] λ λ | #2
#guard (substMask 1 0b100#3 0b001#4 (by decide) = 0b1#3) -- [λ] λ λ | #2
#guard (substMask 2 0b100#3 0b001#4 (by decide) = 0b1#3) -- [λ] λ λ | #2

theorem popScope_eq_removeBitAt {n : Nat} (s : BitVec (n + 1)) :
    popScope s = removeBitAt 0 s (by omega) := by
  simp_all only [BitVec.truncate_eq_setWidth]
  grind only [= BitVec.cast_eq, = BitVec.getElem_append, = BitVec.getElem_setWidth, = BitVec.getElem_extractLsb', = BitVec.getLsbD_ushiftRight]

theorem shiftMask_singleton_ge {n : Nat} (c : Nat) (i : Fin n) (h : i.val ≥ c) (hc : c ≤ n) :
    shiftMask c (singletonMask n i) hc = singletonMask (n+1) ⟨i.val + 1, by omega⟩ := by
  ext targetIndex hj
  unfold shiftMask insertBitAt singletonMask
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one]
  simp_all only [ge_iff_le, Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, Nat.lt_one_iff,
    BitVec.getElem_zero, dite_eq_ite, Bool.if_false_left]
  split
  next h_1 => grind only
  next h_1 =>
    simp_all only [Nat.not_lt]
    grind only [= Lean.Grind.toInt_fin]

theorem shiftMask_singleton_lt {n : Nat} (c : Nat) (i : Fin n) (h : ¬ i.val ≥ c) (hc : c ≤ n) :
    shiftMask c (singletonMask n i) hc = singletonMask (n+1) ⟨i.val, by omega⟩ := by
  ext targetIndex hj
  unfold shiftMask insertBitAt singletonMask
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one]
  simp_all only [ge_iff_le, Nat.not_le, Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, Nat.lt_one_iff,
    BitVec.getElem_zero, dite_eq_ite, Bool.if_false_left]
  split
  next h_1 => grind only [= Lean.Grind.toInt_fin]
  next h_1 =>
    simp_all only [Nat.not_lt]
    grind only [= Lean.Grind.toInt_fin]

theorem shiftMask_mergeScope {n : Nat} (c : Nat) (s1 s2 : BitVec n) (hc : c ≤ n) :
    shiftMask c (mergeScope s1 s2) hc = mergeScope (shiftMask c s1 hc) (shiftMask c s2 hc) := by
  ext targetIndex hj
  unfold shiftMask insertBitAt mergeScope
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_or]
  simp_all only [Nat.zero_add, BitVec.getLsbD_or, Nat.lt_one_iff, BitVec.getElem_zero, dite_eq_ite,
    Bool.if_false_left]
  split
  next h => simp_all only
  next h =>
    simp_all only [Nat.not_lt]
    grind only

theorem substMask_singleton_eq {n : Nat} (targetIndex : Nat) (hj : targetIndex ≤ n) (newPartBitVec : BitVec n) :
    substMask targetIndex newPartBitVec (singletonMask (n + 1) ⟨targetIndex, by omega⟩) hj = newPartBitVec := by
  ext k hk
  unfold substMask removeBitAt singletonMask
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, dite_eq_ite]
  simp_all [↓reduceIte]
  intro a a_1 a_2 a_3
  grind only

theorem substMask_singleton_gt {n : Nat} (targetIndex : Nat) (i : Fin (n + 1)) (h : i.val > targetIndex) (hj : targetIndex ≤ n) (newPartBitVec : BitVec n) :
    substMask targetIndex newPartBitVec (singletonMask (n + 1) i) hj = singletonMask n ⟨i.val - 1, by omega⟩ := by
  ext k hk
  unfold substMask removeBitAt singletonMask
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, dite_eq_ite]
  simp_all only [Nat.zero_lt_succ, decide_true, Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_zero, Bool.or_false]
  simp_all only [gt_iff_lt]
  split
  next h_1 => grind only [= Lean.Grind.toInt_fin]
  next h_1 =>
    simp_all only [Nat.not_lt]
    grind only [= Lean.Grind.toInt_fin]

theorem substMask_singleton_lt {n : Nat} (targetIndex : Nat) (i : Fin (n + 1)) (h : i.val < targetIndex) (hj : targetIndex ≤ n) (newPartBitVec : BitVec n) :
    substMask targetIndex newPartBitVec (singletonMask (n + 1) i) hj = singletonMask n ⟨i.val, by omega⟩ := by
  ext k hk
  unfold substMask removeBitAt singletonMask
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, dite_eq_ite]
  simp_all
  split
  next h_1 =>
    split
    next h_2 =>
      obtain ⟨left, right⟩ := h_2
      grind only [= Lean.Grind.toInt_fin]
    next h_2 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [not_and]
      grind only [= Lean.Grind.toInt_fin]
  next h_1 =>
    simp_all only [Nat.not_lt]
    split
    next h_2 =>
      obtain ⟨left, right⟩ := h_2
      grind only [= Lean.Grind.toInt_fin]
    next h_2 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [not_and]
      grind only [= Lean.Grind.toInt_fin]

theorem substMask_mergeScope {n : Nat} (targetIndex : Nat) (newPartBitVec : BitVec n) (s1 s2 : BitVec (n + 1)) (hj : targetIndex ≤ n) :
    substMask targetIndex newPartBitVec (mergeScope s1 s2) hj = mergeScope (substMask targetIndex newPartBitVec s1 hj) (substMask targetIndex newPartBitVec s2 hj) := by
  ext k hk
  unfold substMask removeBitAt mergeScope
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, BitVec.getLsbD_or, dite_eq_ite]
  simp_all only [Bool.or_eq_true]
  split
  next h =>
    split
    next h_1 =>
      cases h_1 with
      | inl h_2 =>
        simp_all only [↓reduceIte]
        split
        next h_1 => grind only
        next h_1 =>
          simp_all only [BitVec.getElem_zero, Bool.or_false]
          simp_all only [Bool.not_eq_true]
          grind only
      | inr h_3 =>
        simp_all only [↓reduceIte]
        split
        next h_1 => grind only
        next h_1 =>
          simp_all only [BitVec.getElem_zero, Bool.or_false]
          simp_all only [Bool.not_eq_true]
          grind only
    next h_1 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [not_or, Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_zero, Bool.or_false]
  next h =>
    simp_all only [Nat.not_lt]
    split
    next h_1 =>
      cases h_1 with
      | inl h_2 =>
        simp_all only [↓reduceIte]
        split
        next h_1 => grind only
        next h_1 =>
          simp_all only [BitVec.getElem_zero, Bool.or_false]
          simp_all only [Bool.not_eq_true]
          grind only
      | inr h_3 =>
        simp_all only [↓reduceIte]
        split
        next h_1 => grind only
        next h_1 =>
          simp_all only [BitVec.getElem_zero, Bool.or_false]
          simp_all only [Bool.not_eq_true]
          grind only
    next h_1 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [not_or, Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_zero, Bool.or_false]

theorem popScope_getElem {n : Nat} (s : BitVec (n + 1)) (k : Nat) (hk : k < n) :
    (popScope s)[k] = s[k + 1] := by
  unfold popScope
  simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
  simp_all only [BitVec.getLsbD_ushiftRight]
  simp +arith only [Nat.add_lt_add_iff_right, BitVec.getLsbD_eq_getElem, hk]

theorem removeBitAt_getElem {n : Nat} (targetIndex : Nat) (s : BitVec (n + 1)) (hj : targetIndex ≤ n) (k : Nat) (hk : k < n) :
    (removeBitAt targetIndex s hj)[k] = if k < targetIndex then s[k] else s[k + 1] := by
  unfold removeBitAt
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp_all only [Nat.zero_add, dite_eq_ite]
  split
  next h => rfl
  next h =>
    simp_all only [Nat.not_lt]
    simp +arith only [Nat.add_sub_cancel', Nat.add_lt_add_iff_right, BitVec.getLsbD_eq_getElem, h, hk]

theorem shiftMask_zero_getElem_succ {n : Nat} (newPartBitVec : BitVec n) (k : Nat) (hk : k < n) :
    (shiftMask 0 newPartBitVec (by omega))[k + 1] = newPartBitVec[k] := by
  unfold shiftMask insertBitAt
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp_all only [Nat.not_lt_zero, ↓reduceDIte, Nat.sub_zero, Nat.lt_one_iff, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, Nat.add_one_sub_one, Nat.zero_add, BitVec.getLsbD_eq_getElem]

theorem popScope_shiftMask {n : Nat} (c : Nat) (s : BitVec (n + 1)) (hc : c ≤ n) :
    popScope (shiftMask (c + 1) s (by omega)) = shiftMask c (popScope s) (by omega) := by
  ext targetIndex hj
  unfold popScope shiftMask insertBitAt
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp_all only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_cast, Nat.zero_add, BitVec.getLsbD_setWidth, BitVec.getLsbD_eq_getElem, BitVec.getElem_ushiftRight,
    Nat.lt_one_iff, BitVec.getElem_zero, dite_eq_ite, Bool.if_false_left]
  split
  next h => grind only [= BitVec.getLsbD_append, = BitVec.getLsbD_eq_getElem, = BitVec.getElem_extractLsb']
  next h =>
    simp_all only [Nat.not_lt]
    grind only [= BitVec.getLsbD_of_ge, = BitVec.getLsbD_eq_getElem, = BitVec.append_assoc, = BitVec.cast_eq, = BitVec.getLsbD_append, = BitVec.getLsbD_extractLsb', = BitVec.getLsbD_zero]

theorem popScope_substMask {n : Nat} (targetIndex : Nat) (newPartBitVec : BitVec n) (s : BitVec (n + 1 + 1)) (hj : targetIndex ≤ n) :
    popScope (substMask (targetIndex + 1) (shiftMask 0 newPartBitVec (by omega)) s (by omega))
      = substMask targetIndex newPartBitVec (popScope s) hj := by
  ext k hk
  rw [popScope_getElem _ k hk]
  unfold substMask removeBitAt shiftMask insertBitAt
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append,
    BitVec.getElem_extractLsb', BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, dite_eq_ite]
  split <;> split
  · simp_all only [Nat.add_lt_add_iff_right, Nat.sub_zero, Nat.add_zero, BitVec.extractLsb'_eq_self,
      BitVec.extractLsb'_eq_zero, BitVec.append_zero_width, BitVec.cast_eq, ↓reduceIte, BitVec.truncate_eq_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_setWidth]
    split
    next h_2 =>
      have h_k_ge : ¬(k + 1 < 1) := by omega
      have h_k_eq : k + 1 - 1 = k := by omega
      simp_all only [BitVec.getElem_append, ↓reduceDIte]
      grind only [= BitVec.getLsbD_eq_getElem]
    next h_2 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [Bool.not_eq_true]
      grind only [= BitVec.getLsbD_eq_getElem]
  · simp_all only [Nat.add_lt_add_iff_right, BitVec.getElem_zero, Bool.or_false, ↓reduceIte,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_setWidth]
    simp_all only [Bool.not_eq_true]
    split
    next h_2 => grind only [= BitVec.getLsbD_eq_getElem]
    next h_2 =>
      simp_all only [BitVec.getElem_zero, Bool.or_false]
      simp_all only [Bool.not_eq_true]
      grind only
  · simp_all only [Nat.add_lt_add_iff_right, Nat.not_lt, Nat.reduceSubDiff, Nat.sub_zero, Nat.add_zero,
      BitVec.extractLsb'_eq_self, BitVec.extractLsb'_eq_zero, BitVec.append_zero_width, BitVec.cast_eq,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_setWidth]
    split
    next h_2 =>
      split
      next h_3 => grind only
      next h_3 =>
        simp_all only [BitVec.getElem_zero, Bool.or_false]
        simp_all only [Bool.not_eq_true]
        grind only
    next h_2 =>
      simp_all only [Nat.not_lt]
      split
      next h_2 =>
        have h_k_ge : ¬(k + 1 < 1) := by omega
        have h_k_eq : k + 1 - 1 = k := by omega
        simp_all only [BitVec.getElem_append, ↓reduceDIte]
        grind only [= BitVec.getLsbD_eq_getElem]
      next h_2 =>
        simp_all only [BitVec.getElem_zero, Bool.or_false]
        simp_all only [Bool.not_eq_true]
        grind only [= BitVec.getLsbD_eq_getElem]
  · simp_all only [Nat.add_lt_add_iff_right, Nat.not_lt, Nat.reduceSubDiff, BitVec.getElem_zero, Bool.or_false,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_setWidth]
    simp_all only [Bool.not_eq_true]
    split
    next h_2 =>
      split
      next h_3 => grind only
      next h_3 =>
        simp_all only [BitVec.getElem_zero, Bool.or_false]
        simp_all only [Bool.not_eq_true]
        grind only
    next h_2 =>
      simp_all only [Nat.not_lt]
      split
      next h_2 => grind only [= BitVec.getLsbD_eq_getElem]
      next h_2 =>
        simp_all only [BitVec.getElem_zero, Bool.or_false]
        simp_all only [Bool.not_eq_true]
        grind only [= BitVec.getLsbD_of_ge]

def Term.shift (c : Nat) {n : Nat} (hc : c ≤ n) {s : BitVec n}
    (M : Term s) : Term (shiftMask c s hc) :=
  match s, M with
  | _, Term.var i =>
      if h : i.val ≥ c then
        castTerm (Term.var ⟨i.val + 1, by omega⟩)
          (shiftMask_singleton_ge c i h hc).symm
      else
        castTerm (Term.var ⟨i.val, by omega⟩)
          (shiftMask_singleton_lt c i h hc).symm
  | _, @Term.abs _ s_abs P =>
      let P' := Term.shift (c + 1) (by omega) P
      castTerm (Term.abs P')
        (popScope_shiftMask c s_abs hc)
  | _, @Term.app _ s1 s2 P Q =>
      let P' := Term.shift c hc P
      let Q' := Term.shift c hc Q
      castTerm (Term.app P' Q')
        (shiftMask_mergeScope c s1 s2 hc).symm

def Term.size : Term s → Nat
  | Term.var _ => 1
  | Term.abs P => 1 + P.size
  | Term.app P Q => 1 + P.size + Q.size

def Term.subst (targetIndex : Nat) {n : Nat} {newPartBitVec : BitVec n}
    (N : Term newPartBitVec) (hj : targetIndex ≤ n)
    {beforeBitVec : BitVec (n + 1)}
    (M : Term beforeBitVec) :
    Term (substMask targetIndex newPartBitVec beforeBitVec hj) :=
  match beforeBitVec, M with
  | _, Term.var i =>
      if h_eq : i.val = targetIndex then
        castTerm N (by
          have h_i : i = ⟨targetIndex, by omega⟩ := Fin.ext h_eq
          rw [h_i]; exact (substMask_singleton_eq targetIndex hj newPartBitVec).symm)
      else if h_gt : i.val > targetIndex then
        castTerm (Term.var ⟨i.val - 1, by omega⟩)
          (substMask_singleton_gt targetIndex i h_gt hj newPartBitVec).symm
      else
        castTerm (Term.var ⟨i.val, by omega⟩)
          (substMask_singleton_lt targetIndex i (by omega) hj newPartBitVec).symm
  | _, @Term.app _ s1 s2 P Q =>
      let P' := Term.subst targetIndex N hj P
      let Q' := Term.subst targetIndex N hj Q
      castTerm (Term.app P' Q') (substMask_mergeScope targetIndex newPartBitVec s1 s2 hj).symm
  | _, @Term.abs _ s_abs P =>
      let N' := Term.shift (n := n) 0 (Nat.zero_le n) N
      let P' := Term.subst (targetIndex + 1) N' (Nat.succ_le_succ hj) P
      castTerm (Term.abs P') (popScope_substMask targetIndex newPartBitVec s_abs hj)
termination_by M.size
decreasing_by (all_goals (simp [Term.size]; try omega))

-- 1. Simple substitution: x_0[0 := N] ⟹ N
#guard
  let N : Term (0b100#3) := ##[3] 2 -- [λ] λ λ | #2
  let P : Term (0b0001#4) := ##[4] 0 -- λ λ λ [λ] | #0
  -- it substituted #0 with #2 -> gave λ [λ] λ λ | #2
  -- and then peeled off 1 top lambda and scope contracted 4->3 -> [λ] λ λ | #2
  Term.beq (Term.subst 0 N (by omega) P) N

-- 2. Inner variable remains unchanged: x_0[1 := N] ⟹ x_0
#guard
  let N : Term (0b100#3) := ##[3] 2  -- [λ] λ λ | #2
  let P : Term (0b0001#4) := ##[4] 0 -- λ λ λ [λ] | #0
  -- it didn't substitute #1 with #2 bc there is no #1 in P -> so it remained λ λ λ [λ] | #0
  -- then it peeled off 1 top lambda and scope contracted 4->3 -> [λ] λ λ | #0
  Term.beq (Term.subst 1 N (by omega) P) (##[3] 0)

-- 3. Free variable decrement: x_2[0 := N] ⟹ x_1
#guard
  let N : Term (0b100#3) := ##[3] 2  -- [λ] λ λ | #2
  let P : Term (0b0100#4) := ##[4] 2 -- λ [λ] λ λ | #2
  -- it didn't substitute #0 with #2 bc there is no #0 in P -> so it remained λ [λ] λ λ | #2
  -- then it peeled off 1 top lambda and scope contracted 4->3 -> [λ] λ λ | #2
  Term.beq (Term.subst 0 N (by omega) P) (##[3] 1)

-- 4. Substitution under λ-abstraction: (λ. x_1)[0 := N] ⟹ λ. N_shifted
#guard
  let N : Term (0b100#3) := ##[3] 2  -- [λ] λ λ | #2
  let P : Term (0b0001#4) := ⟦ ƛ (##[5] 1) ⟧ -- λ λ λ [λ] | ƛ #1 (inside ƛ: λ λ λ [λ] λ_b | #1)
  let expected : Term (0b0100#3) := ⟦ ƛ (##[4] 3) ⟧ -- λ [λ] λ | ƛ #3 (inside ƛ: [λ] λ λ λ_b | #3)
  Term.beq (Term.subst 0 N (by omega) P) expected

-- 5. Shadowing inside λ: (λ. x_0)[0 := N] ⟹ λ. x_0
#guard
  let N : Term (0b100#3) := ##[3] 2  -- [λ] λ λ | #2
  let P : Term (0b0000#4) := ⟦ ƛ (##[5] 0) ⟧ -- λ λ λ λ | ƛ [λ_b] #0 (inside ƛ: #0 points to bound λ_b)
  let expected : Term (0b0000#3) := ⟦ ƛ (##[4] 0) ⟧ -- λ λ λ | ƛ [λ_b] #0 (shadowed, untouched)
  Term.beq (Term.subst 0 N (by omega) P) expected

-- 6. Real β-step substitution: (x_0 x_1)[0 := var 2] ⟹ var 2 var 0
#guard
  let N : Term (0b100#3) := ##[3] 2  -- [λ] λ λ | #2
  let body : Term (0b0011#4) := ⟦ ##[4] 0 ⬝ ##[4] 1 ⟧ -- λ λ [λ] [λ] | #0 #1
  let expected : Term (0b101#3) := ⟦ ##[3] 2 ⬝ ##[3] 0 ⟧ -- [λ] λ [λ] | #2 #0
  Term.beq (Term.subst 0 N (by omega) body) expected

def Term.betaSubst {n : Nat} {beforeBitVec : BitVec (n + 1)}
    (M : Term beforeBitVec) {newPartBitVec : BitVec n} (N : Term newPartBitVec) :
    Term (substMask 0 newPartBitVec beforeBitVec (by omega)) :=
  Term.subst 0 N (by omega) M

notation:70 M " [" N "]" => Term.betaSubst M N

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 " →β " => BetaStep

inductive BetaStep : ∀ {n1 : Nat} {s1 : BitVec n1}
                       {n2 : Nat} {s2 : BitVec n2},
    Term s1 → Term s2 → Prop where
  | head {n : Nat} {beforeBitVec : BitVec (n+1)}
      {newPartBitVec : BitVec n}
      (P : Term beforeBitVec) (N : Term newPartBitVec) :
      ((ƛ P) ⬝ N) →β P [N]
  | app_left {P P' : _} (Q : Term _) : (P →β P') → (P ⬝ Q) →β (P' ⬝ Q)
  | app_right (P : Term _) {Q Q' : _} : (Q →β Q') → (P ⬝ Q) →β (P ⬝ Q')
  | abs_body {P P' : _} : (P →β P') → (ƛ P) →β (ƛ P')

notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen BetaStep N₁ N₂

-- BetaStep.head test 1: (ƛ #0) · #0  →β  #0 [= #0 itself]
example : ((ƛ (##[1] 0)) ⬝ (Term.abs (##[1] 0))) →β ((##[1] 0) [ Term.abs (##[1] 0) ]) :=
  BetaStep.head _ _

-- BetaStep.head test 2: (ƛ (ƛ #0)) · anything  →β  ƛ #0
example :
    let M : Term (0b0#1) := ⟦ ƛ (##[2] 0) ⟧  -- | ƛ [λ_b] #0
    let N : Term (0b0#0) := ⟦ ƛ (##[1] 0) ⟧  -- | ƛ [λ_b] #0 (in scope 0)
    (ƛ M ⬝ N) →β M [ N ] := BetaStep.head _ _

-- BetaStep.head test 3: (ƛ #0) · (ƛ #0)  →β  (ƛ #0)
example :
    ((ƛ (##[1] 0)) ⬝ (⟦ ƛ (##[1] 0) ⟧ : Term (0b0#0)))
    →β ((##[1] 0) [ (⟦ ƛ (##[1] 0) ⟧ : Term (0b0#0)) ]) :=
  BetaStep.head _ _

-- BetaStep.app_left: ((ƛ #0) · (ƛ #0)) · (ƛ #0)  →β  ((#0 [ ƛ #0 ]) · (ƛ #0))
example :
    (((ƛ (##[1] 0)) ⬝ (Term.abs (##[1] 0))) ⬝ (Term.abs (##[1] 0)))
    →β (((##[1] 0) [ Term.abs (##[1] 0) ]) ⬝ (Term.abs (##[1] 0))) :=
  BetaStep.app_left _ (BetaStep.head _ _)

-- -- BetaStep.app_right: P · ((ƛ Q) · N) →β P · (Q [N])
-- example : BetaStep
--     (Term.abs (Term.abs (##[2] 0)) ⬝ ((Term.abs (##[1] 0)) ⬝ (Term.abs (##[1] 0))))
--     _ :=
--   BetaStep.app_right (Term.abs (Term.abs (##[2] 0))) (BetaStep.head _ _)

-- -- BetaStep.abs_body: ƛ ((ƛ P) · N) →β ƛ (P [N])
-- example : BetaStep
--     (Term.abs ((Term.abs (##[2] 0)) ⬝ (Term.abs (##[2] 0))))
--     _ :=
--   BetaStep.abs_body (BetaStep.head _ _)

end Basic43BitVec
