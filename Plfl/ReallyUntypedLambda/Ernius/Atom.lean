module
public import Aesop
@[expose] public section
abbrev Atom := Nat

def swap_atom (a b c : Atom) : Atom :=
  if c = a then b
  else if c = b then a
  else c

notation "(" a " ∙ " b ")ₐ " c => swap_atom a b c

namespace Atom

-- theorem «lemma∙ₐ» (a b c : Atom) :
--     (c = a ∧ ((a ∙ b)ₐ c) = b) ∨
--     (c = b ∧ c ≠ a ∧ ((a ∙ b)ₐ c) = a) ∨
--     (c ≠ a ∧ c ≠ b ∧ ((a ∙ b)ₐ c) = c) := by
--   grind only [swap_atom, #ff44, #9143, #cc3c, #3278, #b572, #2722, #717b]
--
-- theorem «lemma∙ₐc≡a» (a b c : Atom) (h : c = a) : ((a ∙ b)ₐ c) = b := by
--   grind [= swap_atom]
--
-- theorem «lemma∙ₐc≡b» (a b c : Atom) (h : c = b) : ((a ∙ b)ₐ c) = a := by
--   grind [= swap_atom]
--
-- theorem «lemma∙ₐc≢a∧c≢b» {a b c : Atom} (h1 : c ≠ a) (h2 : c ≠ b) : ((a ∙ b)ₐ c) = c := by
--   grind [= swap_atom]
--
-- theorem «lemma∙ₐa≢b∧a≢c∧a≢d→a≢（bc）d» {a b c d : Atom}
--     (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) : a ≠ (b ∙ c)ₐ d := by
--   grind [= swap_atom]
--
-- theorem «lemma（aa）b≡b» {a b : Atom} : ((a ∙ a)ₐ b) = b := by
--   grind [= swap_atom]
--
-- theorem «lemma（ab）（ab）c≡c» {a b c : Atom} : ((a ∙ b)ₐ ((a ∙ b)ₐ c)) = c := by
--   grind [= swap_atom]
--
-- theorem «lemma∙ₐinj» {a b c d : Atom} (h : c ≠ d) : ((a ∙ b)ₐ c) ≠ (a ∙ b)ₐ d := by
--   grind [= swap_atom]
--
-- theorem «lemma∙ₐcomm» {a b c : Atom} : (a ∙ b)ₐ c = (b ∙ a)ₐ c := by
--   unfold swap_atom; split_ifs <;> subst_vars <;> try rfl
--   · contradiction
--
-- theorem «lemma∙ₐ（aa）a≡a» {a : Atom} : (a ∙ a)ₐ a = a := by
--   unfold swap_atom; split_ifs <;> rfl
--
-- theorem «lemma∙ₐ（ab）a≡b» {a b : Atom} : (a ∙ b)ₐ a = b := by
--   unfold swap_atom; split_ifs <;> rfl
--
-- theorem «lemma∙ₐ（ab）b≡a» {a b : Atom} : (a ∙ b)ₐ b = a := by
--   unfold swap_atom; split_ifs with h1 <;> [exact h1.symm; rfl; rfl]
--
-- theorem «lemma∙ₐdistributive» (a b c d e : Atom) :
--     (a ∙ b)ₐ ((c ∙ d)ₐ e) = ((a ∙ b)ₐ c ∙ (a ∙ b)ₐ d)ₐ ((a ∙ b)ₐ e) := by
--   unfold swap_atom; split_ifs <;> subst_vars <;> try rfl
--   · contradiction
--
-- theorem «lemma∙ₐcancel» {a b c d : Atom} (hdb : d ≠ b) (hdc : d ≠ c) :
--     (c ∙ b)ₐ ((a ∙ c)ₐ d) = (a ∙ b)ₐ d := by
--   unfold swap_atom; split_ifs <;> subst_vars <;> try rfl
--   · contradiction
--   · contradiction

end Atom
