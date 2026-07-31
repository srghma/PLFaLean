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

/-- Cast a term when its bitvec indices are propositionally, but not
definitionally, equal. `n` and `d` here are pinned to be literally the
same on both sides (only the mask *values* differ), so `castTerm` never
needs to change the scope size or depth themselves. -/
def castTerm {n : Nat} {s : BitVec n} {d : Nat} {u : BitVec d} (t : Term s u)
    {s' : BitVec n} {u' : BitVec d}
    (hs : s = s') (hu : u = u') : Term s' u' := by
  subst hs; subst hu; exact t

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
      simp (config := { decide := true }) [
        singletonMask, popScope, recordBinderUsage, mergeScope, mergeUsage,
        BitVec.ofNat, BitVec.truncate, BitVec.or,
        BitVec.getLsb, BitVec.zeroExtend,
        Nat.max, Fin.val_mk, if_pos, if_neg
      ];
      -- Symbolic Hammer: Convert BitVec equality to Nat equality
      try (
        apply BitVec.eq_of_toNat_eq;
        simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
              BitVec.toNat_ushiftRight, BitVec.toNat_zero,
              BitVec.toNat_or, BitVec.toNat_ushiftLeft];
        omega
      );
      try (rw [BitVec.eq_refl]);
      try decide
  ))

macro "⟦" t:term "⟧" : term => `(castTerm $t (by bv_auto) (by bv_auto))

prefix:100 "ƛ " => Term.abs
infixl:70 " ⬝ " => Term.app
prefix:100 "# " => Term.var
macro:100 "##[" n:term "]" i:term:max : term => `(Term.var (n := $n) (Fin.mk $i (by decide)))

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

namespace Term

def id_ : Term (0#n) (0b1#1) :=
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

def const_ {n : Nat} : Term (0#n) (0b10#2) :=
  castTerm (ƛ ƛ (##[n+2] 1))
    (by
      simp [popScope, recordBinderUsage, singletonMask]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    )
    (by -- Prove final usage is 10#2 (which is 2 in decimal)
      simp [recordBinderUsage, popScope, singletonMask]
      -- Prove bit 0 of 1#n+1 is true
      have h1 : (BitVec.truncate (n + 1) (BitVec.ofNat (n + 2) 2 >>> 1)).getLsb 0 = true := by
        apply BitVec.eq_of_toNat_eq -- Technically we just need the LSB logic here
        simp [BitVec.getLsb_entry, BitVec.toNat_truncate, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      rw [h1]; simp
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_or, BitVec.toNat_ushiftLeft, BitVec.toNat_ofNat, BitVec.toNat_zeroExtend]
    )

def id : Term (0#n) (0b1#1) := ⟦ƛ (# 0)⟧
def const : Term (0#n) (0b10#2) := ⟦ƛ (ƛ (##[n+2] 1))⟧
def zero  : Term (0#n) (0b01#2) := ⟦ƛ (ƛ (##[n+2] 0))⟧
def one   : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ # 0))⟧
def two   : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ (##[n+2] 1 ⬝ # 0)))⟧
def three : Term (0#n) (0b11#2) := ⟦ƛ (ƛ (##[n+2] 1 ⬝ two))⟧
def succ  : Term (0#n) (0b111#3) := ⟦ƛ (ƛ (ƛ (##[n+3] 1 ⬝ ((##[n+3] 2 ⬝ ##[n+3] 1) ⬝ # 0))))⟧

end Term
