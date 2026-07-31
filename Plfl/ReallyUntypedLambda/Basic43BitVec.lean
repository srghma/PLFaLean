import Mathlib.Logic.Relation
import Aesop

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

/-- Record, at binder-depth `d`, whether the binder we just closed over was
actually referenced (`usedBit0`), merged into the existing depth-mask `u`.
Used by `Term.abs` to update the binder-usage mask. -/
abbrev recordBinderUsage {d : Nat} (usedBit0 : Bool) (u : BitVec d) : BitVec (d + 1) :=
  ((if usedBit0 then 0b1#(d + 1) else 0b0#(d + 1)) <<< d) ||| u.zeroExtend (d + 1)

/-- Union two scope masks of the same width. Used by `Term.app`. -/
abbrev mergeScope {n : Nat} (s1 s2 : BitVec n) : BitVec n :=
  s1 ||| s2

/-- Union two usage masks of possibly different depth, widening to the max.
Used by `Term.app`. -/
abbrev mergeUsage {d1 d2 : Nat} (u1 : BitVec d1) (u2 : BitVec d2) : BitVec (max d1 d2) :=
  u1.zeroExtend (max d1 d2) ||| u2.zeroExtend (max d1 d2)

-- #guard demonstrations: bit i=2 set in a width-4 mask
#guard singletonMask 4 ⟨2, by decide⟩ = 0b0100#4

-- popScope: drop bit 0 of 0b101 (width 3) -> 0b10 (width 2)
#guard popScope (0b101#3) = 0b10#2
#guard popScope (0b100#3) = 0b10#2

-- recordBinderUsage: binder was used, place its bit at position d=2, keep old usage 0b10
#guard recordBinderUsage (d := 2) true  (0b10#2) = 0b110#3
-- recordBinderUsage: binder was NOT used
#guard recordBinderUsage (d := 2) false (0b10#2) = 0b010#3

-- mergeScope: bitwise-or of two width-4 masks
#guard mergeScope (0b1010#4) (0b0110#4) = 0b1110#4

-- mergeUsage: widen a depth-1 mask into a depth-2 mask and or them together
#guard mergeUsage (0b11#2) (0b1#1) = 0b11#2

/-! ## The inductive family, with n and d auto-bound (inferred from the BitVec widths) -/

/--
`Term s u`:
  the scope size `n` and abstraction depth `d` are inferred automatically
  from the widths of `s : BitVec n` (used free variables) and
  `u : BitVec d` (used binders).
-/
inductive Term : BitVec n → BitVec d → Type
  | var : {n : Nat} → (i : Fin n) → Term (singletonMask n i) (0b0#0)
  | abs : {n d : Nat} → {s : BitVec (n + 1)} → {u : BitVec d} →
      Term s u →
      Term (popScope s) (recordBinderUsage (s.getLsb 0) u)
  | app : {n d1 d2 : Nat} → {s1 s2 : BitVec n} → {u1 : BitVec d1} → {u2 : BitVec d2} →
      Term s1 u1 → Term s2 u2 →
      Term (mergeScope s1 s2) (mergeUsage u1 u2)
deriving Repr

/-- Cast a term when its bitvec indices are propositionally, but not
definitionally, equal. `n` and `d` here are pinned to be literally the
same on both sides (only the mask *values* differ), so `castTerm` never
needs to change the scope size or depth themselves. -/
def castTerm {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} (t : Term s u)
    {s' : BitVec n} {u' : BitVec d}
    (hs : s = s') (hu : u = u') : Term s' u' := by
  subst hs; subst hu; exact t

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

/--
  Updated Tactic:
  Added lemmas to handle symbolic 'n'.
  Specifically:
  - BitVec.getLsb_ofNat_zero/one: handles (1#n).getLsb 0
  - BitVec.ushiftRight_self/one: handles (1#n >>> 1) = 0
  - BitVec.truncate_zero: handles (0).truncate n = 0
-/
syntax "bv_auto" : tactic
macro_rules
  | `(tactic| bv_auto) => `(tactic| (
      try (intros; subst_vars);
      first
      | -- "usage"-shaped goals: fully concrete once combinators unfold.
        (simp [singletonMask, popScope, recordBinderUsage, mergeScope, mergeUsage];
         decide)
      | -- already closed by simp alone (decide errors if no goals left)
        (simp [singletonMask, popScope, recordBinderUsage, mergeScope, mergeUsage])
      | -- "scope"-shaped goals: symbolic n, work in toNat-land.
        (unfold singletonMask popScope recordBinderUsage mergeScope mergeUsage;
         apply BitVec.eq_of_toNat_eq;
         simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
               BitVec.toNat_ushiftRight, BitVec.toNat_zero,
               BitVec.toNat_or, BitVec.toNat_ushiftLeft];
         repeat rw [Nat.shiftRight_eq_div_pow];
         repeat (first | rw [mod_two_pow_add_eq _ (by decide)] | simp);
         omega)
      | decide
  ))

macro "⟦" t:term "⟧" : term => `(castTerm $t (by bv_auto) (by bv_auto))

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term => `(Term.var (n := $n) (Fin.mk $i (by try omega; try decide)))

namespace TermsConcrete

def id : Term (0#0) (0b1#1) := ⟦ƛ (# 0)⟧
def const : Term (0b0#0) (0b10#2) := ⟦ƛ (ƛ (##[2] 1))⟧
def zero  : Term (0b0#0) (0b01#2) := ⟦ƛ (ƛ (##[2] 0))⟧
def one   : Term (0b0#0) (0b11#2) := ⟦ƛ (ƛ (##[2] 1 ⬝ # 0))⟧
def two   : Term (0b0#0) (0b11#2) := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0)))⟧
def three : Term (0b0#0) (0b11#2) := ⟦ƛ (ƛ (##[2] 1 ⬝ (##[2] 1 ⬝ (##[2] 1 ⬝ # 0))))⟧
def succ  : Term (0b0#0) (0b111#3) := ⟦ƛ (ƛ (ƛ (##[3] 1 ⬝ ((##[3] 2 ⬝ ##[3] 1) ⬝ # 0))))⟧

def freeTerm : Term (0b11#2) (0b0#0) := ⟦##[2] 0 ⬝ ##[2] 1⟧
def boundAndFree : Term (0b1#1) (0b1#1) := ⟦ƛ (# 0 ⬝ ##[2] 1)⟧

end TermsConcrete

namespace TermWithCustomProofs

def id : Term (0#n) (0b1#1) :=
  castTerm (ƛ (# 0))
    (show popScope (singletonMask (n + 1) 0) = 0#n by
      unfold popScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    )
    (show recordBinderUsage ((singletonMask (n + 1) 0).getLsb 0) (0#0) = 0b1#1 by
      unfold recordBinderUsage singletonMask
      have hlsb : (1#(n+1) <<< 0).getLsb 0 = true := by
        simp only [BitVec.shiftLeft_zero, BitVec.getLsb_eq_getElem, Fin.getElem_fin, Fin.val_zero,
          BitVec.getElem_one, decide_true]
      apply BitVec.eq_of_toNat_eq
      simp only [Nat.reduceAdd, Fin.val_zero, BitVec.shiftLeft_zero, BitVec.getLsb_eq_getElem,
        Fin.getElem_fin, BitVec.getElem_one, decide_true, ↓reduceIte, BitVec.truncate_eq_setWidth,
        Nat.zero_le, Nat.pow_zero, Nat.lt_add_one, BitVec.setWidth_ofNat_of_le_of_lt,
        BitVec.or_zero, BitVec.toNat_ofNat, Nat.pow_one, Nat.mod_succ]
    )

def const {n : Nat} : Term (0#n) (0b10#2) :=
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
    (by
      simp [recordBinderUsage, popScope, singletonMask]
    )

def zero {n : Nat} : Term (0#n) (0b01#2) :=
  castTerm (ƛ ƛ (##[n+2] 0))
    (by
      unfold popScope singletonMask
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight])
    (by
      simp [recordBinderUsage, popScope, singletonMask]
    )

def one {n : Nat} : Term (0#n) (0b11#2) :=
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
    (by
      simp [recordBinderUsage, popScope, mergeScope, singletonMask]
      decide)

def two {n : Nat} : Term (0#n) (0b11#2) :=
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
    (by
      simp [recordBinderUsage, popScope, mergeScope, singletonMask]
      decide)

def three {n : Nat} : Term (0#n) (0b11#2) :=
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
    (by
      simp [recordBinderUsage, popScope, mergeScope, singletonMask]
      decide)

def succ {n : Nat} : Term (0#n) (0b111#3) :=
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
    (by
      simp [recordBinderUsage, popScope, mergeScope, singletonMask]
      decide)

end TermWithCustomProofs

-- namespace Term
--
-- def id : Term (0#n) (0b1#1) := ⟦ƛ (# 0)⟧
-- def const : Term (0#n) (0b10#2) := ⟦ƛ (ƛ (##[n+2] 1))⟧
-- def zero  : Term (0#n) (0b01#2) := ⟦ƛ (ƛ (##[n+2] 0))⟧
-- def one   : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ # 0))⟧
-- def two   : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ # 0)))⟧
-- def three : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ two))⟧
-- def succ  : Term (0#n) (0b111#3) := ⟦ƛ (ƛ (ƛ (##[n+3] 1 ⬝ ((##[n+3] 2 ⬝ ##[n+3] 1) ⬝ # 0))))⟧
--
-- end Term

def Term.beq : ∀ {n1 : Nat} {s1 : BitVec n1} {d1 : Nat} {u1 : BitVec d1}
                {n2 : Nat} {s2 : BitVec n2} {d2 : Nat} {u2 : BitVec d2},
    Term s1 u1 → Term s2 u2 → Bool
  | _, _, _, _, _, _, _, _, Term.var i, t2 =>
      match t2 with
      | Term.var j => i.val == j.val
      | _ => false
  | _, _, _, _, _, _, _, _, Term.abs P, t2 =>
      match t2 with
      | Term.abs Q => Term.beq P Q
      | _ => false
  | _, _, _, _, _, _, _, _, Term.app P1 P2, t2 =>
      match t2 with
      | Term.app Q1 Q2 => Term.beq P1 Q1 && Term.beq P2 Q2
      | _ => false

instance {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} : BEq (Term s u) where
  beq := Term.beq

theorem termBEq_refl {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} (t : Term s u) :
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

instance {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} : ReflBEq (Term s u) where
  rfl {t} := termBEq_refl t

theorem termBEq_heq : ∀ {n : Nat} {s1 : BitVec n} {d1 : Nat} {u1 : BitVec d1} (t1 : Term s1 u1)
    {s2 : BitVec n} {d2 : Nat} {u2 : BitVec d2} (t2 : Term s2 u2),
    Term.beq t1 t2 = true → s1 = s2 ∧ d1 = d2 ∧ HEq u1 u2 ∧ HEq t1 t2 := by
  intro n s1 d1 u1 t1
  induction t1 with
  | var i =>
    intro s2 d2 u2 t2 h
    cases t2 with
    | var j =>
      change (i.val == j.val) = true at h
      have hij : i = j := Fin.ext (eq_of_beq h)
      subst hij
      exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩
    | abs Q => exact Bool.noConfusion h
    | app Q1 Q2 => exact Bool.noConfusion h
  | abs P ih =>
    intro s2 d2 u2 t2 h
    cases t2 with
    | var j => exact Bool.noConfusion h
    | abs Q =>
      change Term.beq P Q = true at h
      obtain ⟨hs, hd, hu, hheq⟩ := ih Q h
      subst hs
      subst hd
      simp_all only [heq_eq_eq, BitVec.truncate_eq_setWidth, BitVec.getLsb_eq_getElem, Fin.getElem_fin, Fin.val_zero, true_and]
      subst hu
      grind only
    | app Q1 Q2 => exact Bool.noConfusion h
  | app P1 P2 ih1 ih2 =>
    intro s2 d2 u2 t2 h
    cases t2 with
    | var j => exact Bool.noConfusion h
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
      obtain ⟨hs1, hd1, hu1, hheq1⟩ := ih1 Q1 h1
      obtain ⟨hs2, hd2, hu2, hheq2⟩ := ih2 Q2 h2
      subst hs1; subst hd1
      have hu1' : _ = _ := eq_of_heq hu1
      subst hu1'
      subst hs2; subst hd2
      have hu2' : _ = _ := eq_of_heq hu2
      subst hu2'
      have e1 : P1 = Q1 := eq_of_heq hheq1
      have e2 : P2 = Q2 := eq_of_heq hheq2
      subst e1; subst e2
      exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩

instance {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} : LawfulBEq (Term s u) where
  eq_of_beq {t1 t2} h := eq_of_heq (termBEq_heq t1 t2 h).2.2.2

instance {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} : DecidableEq (Term s u) :=
  fun t1 t2 =>
    match h : Term.beq t1 t2 with
    | true  => isTrue (eq_of_heq (termBEq_heq t1 t2 h).2.2.2)
    | false => isFalse (by
        intro heq; subst heq
        rw [termBEq_refl t1] at h
        exact absurd h (by decide))

abbrev insertBitAt (c : Nat) {n : Nat} (s : BitVec n) (h : c ≤ n) : BitVec (n + 1) :=
  ((s.extractLsb' c (n - c)) ++ (0#1) ++ (s.extractLsb' 0 c)).cast (by omega)

abbrev removeBitAt (j : Nat) {n : Nat} (s : BitVec (n + 1)) (h : j ≤ n) : BitVec n :=
  ((s.extractLsb' (j + 1) (n - j)) ++ (s.extractLsb' 0 j)).cast (by omega)

abbrev shiftMask (c : Nat) {n : Nat} (s : BitVec n) (h : c ≤ n) : BitVec (n + 1) :=
  insertBitAt c s h

abbrev substMask (j : Nat) {n : Nat} (sN : BitVec n) (sP : BitVec (n + 1)) (h : j ≤ n) : BitVec n :=
  removeBitAt j sP h ||| (if sP.getLsb ⟨j, by omega⟩ then sN else 0#n)

theorem popScope_eq_removeBitAt {n : Nat} (s : BitVec (n + 1)) :
    popScope s = removeBitAt 0 s (by omega) := by
  simp_all only [BitVec.truncate_eq_setWidth]
  grind only [= BitVec.cast_eq, = BitVec.getElem_append, = BitVec.getElem_setWidth, = BitVec.getElem_extractLsb', = BitVec.getLsbD_ushiftRight]

theorem shiftMask_singleton_ge {n : Nat} (c : Nat) (i : Fin n) (h : i.val ≥ c) (hc : c ≤ n) :
    shiftMask c (singletonMask n i) hc = singletonMask (n+1) ⟨i.val + 1, by omega⟩ := by
  ext j hj
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
  ext j hj
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
  ext j hj
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

theorem substMask_singleton_eq {n : Nat} (j : Nat) (hj : j ≤ n) (sN : BitVec n) :
    substMask j sN (singletonMask (n + 1) ⟨j, by omega⟩) hj = sN := by
  ext k hk
  unfold substMask removeBitAt singletonMask
  simp only [BitVec.getElem_or, BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getElem_shiftLeft, BitVec.getElem_one, BitVec.getLsb_eq_getElem, Fin.getElem_fin]
  simp_all only [Nat.zero_add, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, dite_eq_ite]
  simp_all [↓reduceIte]
  intro a a_1 a_2 a_3
  grind only

theorem substMask_singleton_gt {n : Nat} (j : Nat) (i : Fin (n + 1)) (h : i.val > j) (hj : j ≤ n) (sN : BitVec n) :
    substMask j sN (singletonMask (n + 1) i) hj = singletonMask n ⟨i.val - 1, by omega⟩ := by
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

theorem substMask_singleton_lt {n : Nat} (j : Nat) (i : Fin (n + 1)) (h : i.val < j) (hj : j ≤ n) (sN : BitVec n) :
    substMask j sN (singletonMask (n + 1) i) hj = singletonMask n ⟨i.val, by omega⟩ := by
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

theorem substMask_mergeScope {n : Nat} (j : Nat) (sN : BitVec n) (s1 s2 : BitVec (n + 1)) (hj : j ≤ n) :
    substMask j sN (mergeScope s1 s2) hj = mergeScope (substMask j sN s1 hj) (substMask j sN s2 hj) := by
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

theorem getLsb_zero_shiftMask {n : Nat} (c : Nat) (s : BitVec (n + 1)) (hc : c ≤ n) :
    (shiftMask (c + 1) s (by omega)).getLsb 0 = s.getLsb 0 := by
  unfold shiftMask insertBitAt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_cast,
    BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp only [Nat.zero_add, Fin.val_zero]
  simp_all only [Nat.zero_lt_succ, ↓reduceDIte, BitVec.getLsbD_eq_getElem]

theorem popScope_getElem {n : Nat} (s : BitVec (n + 1)) (k : Nat) (hk : k < n) :
    (popScope s)[k] = s[k + 1] := by
  unfold popScope
  simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
  simp_all only [BitVec.getLsbD_ushiftRight]
  simp +arith only [Nat.add_lt_add_iff_right, BitVec.getLsbD_eq_getElem, hk]

theorem removeBitAt_getElem {n : Nat} (j : Nat) (s : BitVec (n + 1)) (hj : j ≤ n) (k : Nat) (hk : k < n) :
    (removeBitAt j s hj)[k] = if k < j then s[k] else s[k + 1] := by
  unfold removeBitAt
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp_all only [Nat.zero_add, dite_eq_ite]
  split
  next h => rfl
  next h =>
    simp_all only [Nat.not_lt]
    simp +arith only [Nat.add_sub_cancel', Nat.add_lt_add_iff_right, BitVec.getLsbD_eq_getElem, h, hk]

theorem shiftMask_zero_getElem_succ {n : Nat} (sN : BitVec n) (k : Nat) (hk : k < n) :
    (shiftMask 0 sN (by omega))[k + 1] = sN[k] := by
  unfold shiftMask insertBitAt
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp_all only [Nat.not_lt_zero, ↓reduceDIte, Nat.sub_zero, Nat.lt_one_iff, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, Nat.add_one_sub_one, Nat.zero_add, BitVec.getLsbD_eq_getElem]

theorem popScope_shiftMask {n : Nat} (c : Nat) (s : BitVec (n + 1)) (hc : c ≤ n) :
    popScope (shiftMask (c + 1) s (by omega)) = shiftMask c (popScope s) (by omega) := by
  ext j hj
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

theorem getLsb_zero_substMask {n : Nat} (j : Nat) (sN : BitVec n) (sP : BitVec (n + 1 + 1)) (hj : j ≤ n) :
    (substMask (j + 1) (shiftMask 0 sN (by omega)) sP (by omega)).getLsb 0 = sP.getLsb 0 := by
  unfold substMask removeBitAt shiftMask insertBitAt
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_or, BitVec.getElem_cast,
    BitVec.getElem_append, BitVec.getElem_extractLsb']
  simp only [Nat.zero_add, Fin.val_zero]
  simp_all [↓reduceDIte]
  intro a
  split at a
  next h =>
    simp [BitVec.getElem_append, BitVec.getElem_zero] at a
  next h => simp_all only [BitVec.getElem_zero, Bool.false_eq_true]

theorem popScope_substMask {n : Nat} (j : Nat) (sN : BitVec n) (s : BitVec (n + 1 + 1)) (hj : j ≤ n) :
    popScope (substMask (j + 1) (shiftMask 0 sN (by omega)) s (by omega))
      = substMask j sN (popScope s) hj := by
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


def Term.shift (c : Nat) {n : Nat} (hc : c ≤ n) {s : BitVec n} {d : Nat} {u : BitVec d}
    (M : Term s u) : Term (shiftMask c s hc) u :=
  match s, d, u, M with
  | _, _, _, Term.var i =>
      if h : i.val ≥ c then
        castTerm (Term.var ⟨i.val + 1, by omega⟩)
          (shiftMask_singleton_ge c i h hc).symm
          rfl
      else
        castTerm (Term.var ⟨i.val, by omega⟩)
          (shiftMask_singleton_lt c i h hc).symm
          rfl
  | _, _, _, @Term.abs _ _ s_abs u_abs P =>
      let P' := Term.shift (c + 1) (by omega) P
      castTerm (Term.abs P')
        (popScope_shiftMask c s_abs hc)
        (by rw [getLsb_zero_shiftMask c s_abs hc])
  | _, _, _, @Term.app _ _ _ s1 s2 _ _ P Q =>
      let P' := Term.shift c hc P
      let Q' := Term.shift c hc Q
      castTerm (Term.app P' Q')
        (shiftMask_mergeScope c s1 s2 hc).symm
        rfl

-- bc autogenerated sizeOf is ugly when is generated for indexed inductive family
def Term.size : Term s u → Nat
  | Term.var _ => 1
  | Term.abs P => 1 + P.size
  | Term.app P Q => 1 + P.size + Q.size

def Term.subst (j : Nat) {n : Nat} {sN : BitVec n} {dN : Nat} {uN : BitVec dN}
    (N : Term sN uN) (hj : j ≤ n)
    {sP : BitVec (n + 1)} {dP : Nat} {uP : BitVec dP}
    (M : Term sP uP) :
    (d' : Nat) × (u' : BitVec d') × Term (substMask j sN sP hj) u' :=
  match sP, dP, uP, M with
  | _, _, _, Term.var i =>
      if h_eq : i.val = j then
        ⟨dN, uN, castTerm N (by
          have h_i : i = ⟨j, by omega⟩ := Fin.ext h_eq
          rw [h_i]; exact (substMask_singleton_eq j hj sN).symm) rfl⟩
      else if h_gt : i.val > j then
        ⟨0, 0b0#0, castTerm (Term.var ⟨i.val - 1, by omega⟩)
          (substMask_singleton_gt j i h_gt hj sN).symm rfl⟩
      else
        ⟨0, 0b0#0, castTerm (Term.var ⟨i.val, by omega⟩)
          (substMask_singleton_lt j i (by omega) hj sN).symm rfl⟩
  | _, _, _, @Term.app _ _ _ s1 s2 _ _ P Q =>
      let ⟨dP', uP', P'⟩ := Term.subst j N hj P
      let ⟨dQ', uQ', Q'⟩ := Term.subst j N hj Q
      ⟨max dP' dQ', mergeUsage uP' uQ',
        castTerm (Term.app P' Q') (substMask_mergeScope j sN s1 s2 hj).symm rfl⟩
  | _, _, _, @Term.abs _ _ s_abs u_abs P =>
      let N' := Term.shift 0 (by omega) N
      let ⟨dP', uP', P'⟩ := Term.subst (j + 1) N' (by omega) P
      ⟨dP' + 1, recordBinderUsage (s_abs.getLsb 0) uP',
        castTerm (Term.abs P') (popScope_substMask j sN s_abs hj)
          (by rw [getLsb_zero_substMask j sN s_abs hj])⟩
termination_by M.size
decreasing_by (all_goals (simp [Term.size]; try omega))

-- 1. Simple substitution: x_0[0 := N] ⟹ N
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let P : Term (0b0001#4) (0#0) := ##[4] 0
  Term.beq (Term.subst 0 N (by omega) P).2.2 N

-- 2. Inner variable remains unchanged: x_0[1 := N] ⟹ x_0
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let P : Term (0b0001#4) (0#0) := ##[4] 0
  Term.beq (Term.subst 1 N (by omega) P).2.2 (##[3] 0)

-- 3. Free variable decrement: x_2[0 := N] ⟹ x_1
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let P : Term (0b0100#4) (0#0) := ##[4] 2
  Term.beq (Term.subst 0 N (by omega) P).2.2 (##[3] 1)

-- 4. Substitution under λ-abstraction: (λ. x_1)[0 := N] ⟹ λ. N_shifted
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let P : Term (0b0001#4) (0b0#1) := ⟦ ƛ (##[5] 1) ⟧
  let expected : Term (0b0100#3) (0b0#1) := ⟦ ƛ (##[4] 3) ⟧
  Term.beq (Term.subst 0 N (by omega) P).2.2 expected

-- 5. Shadowing inside λ: (λ. x_0)[0 := N] ⟹ λ. x_0
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let P : Term (0b0000#4) (0b1#1) := ⟦ ƛ (##[5] 0) ⟧
  let expected : Term (0b0000#3) (0b1#1) := ⟦ ƛ (##[4] 0) ⟧
  Term.beq (Term.subst 0 N (by omega) P).2.2 expected

-- 6. Real β-step substitution: (x_0 x_1)[0 := var 2] ⟹ var 2 var 0
#guard
  let N : Term (0b100#3) (0#0) := ##[3] 2
  let body : Term (0b0011#4) (0#0) := ⟦ ##[4] 0 ⬝ ##[4] 1 ⟧
  let expected : Term (0b101#3) (0#0) := ⟦ ##[3] 2 ⬝ ##[3] 0 ⟧
  Term.beq (Term.subst 0 N (by omega) body).2.2 expected


def Term.betaSubst {n : Nat} {sP : BitVec (n + 1)} {dP : Nat} {uP : BitVec dP}
    (M : Term sP uP) {sN : BitVec n} {dN : Nat} {uN : BitVec dN} (N : Term sN uN) :
    Term (substMask 0 sN sP (by omega)) (Term.subst 0 N (by omega) M).2.1 :=
  (Term.subst 0 N (by omega) M).2.2

notation:70 M " [" N "]" => Term.betaSubst M N

set_option hygiene false in
set_option quotPrecheck false in
infixl:65 " →β " => BetaStep

inductive BetaStep : ∀ {n1 : Nat} {s1 : BitVec n1} {d1 : Nat} {u1 : BitVec d1}
                       {n2 : Nat} {s2 : BitVec n2} {d2 : Nat} {u2 : BitVec d2},
    Term s1 u1 → Term s2 u2 → Prop where
  | head {n : Nat} {sP : BitVec (n+1)} {dP : Nat} {uP : BitVec dP}
      {sN : BitVec n} {dN : Nat} {uN : BitVec dN}
      (P : Term sP uP) (N : Term sN uN) :
      ((ƛ P) ⬝ N) →β P [N]
  | app_left {P P' : _} (Q : Term _ _) : (P →β P') → (P ⬝ Q) →β (P' ⬝ Q)
  | app_right (P : Term _ _) {Q Q' : _} : (Q →β Q') → (P ⬝ Q) →β (P ⬝ Q')
  | abs_body {P P' : _} : (P →β P') → (ƛ P) →β (ƛ P')

notation:65 N₁ " ⇒β " N₂ => Relation.ReflTransGen BetaStep N₁ N₂
