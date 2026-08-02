module
public import Mathlib.Data.List.Basic
@[expose] public section

abbrev V := Nat

def χ_aux (xs : List V) (n : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n ∈ xs then χ_aux xs (n + 1) fuel else n

/-- Generates the smallest natural number not present in `xs`. -/
def χ' (xs : List V) : V :=
  χ_aux xs 0 (xs.length + 1)

namespace Chi

private theorem erase_mem_of_mem_of_ne {a b : Nat} {xs : List Nat} (ha : a ∈ xs) (hne : a ≠ b) : a ∈ xs.erase b := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rw [List.erase_cons]
    split_ifs with h
    · simp_all only [ne_eq, not_false_eq_true, List.mem_erase_of_ne, implies_true, List.mem_cons, beq_iff_eq, false_or]
    · cases ha with
      | head => left
      | tail _ hmem => right; exact ih hmem

-- private theorem forall_lt_mem_imp_length_ge (k : Nat) : ∀ (xs : List Nat), (∀ i < k, i ∈ xs) → xs.length ≥ k := by
--   induction k with
--   | zero => intros; exact Nat.zero_le _
--   | succ k ih =>
--     intro xs h
--     have hk : k ∈ xs := h k (Nat.lt_succ_self k)
--     have h_sub : ∀ i < k, i ∈ xs.erase k := by
--       intro i hi
--       apply erase_mem_of_mem_of_ne (h i (Nat.lt_succ_of_lt hi)) (ne_of_lt hi)
--     have ih' := ih (xs.erase k) h_sub
--     have h_len : (xs.erase k).length = xs.length - 1 := List.length_erase_of_mem hk
--     omega
--
-- private theorem χ_aux_spec (xs : List V) (n fuel : Nat) :
--     χ_aux xs n fuel ∉ xs ∨ (∀ i, n ≤ i ∧ i < n + fuel → i ∈ xs) := by
--   induction fuel generalizing n with
--   | zero =>
--     right
--     intro i h; omega
--   | succ fuel ih =>
--     simp [χ_aux]
--     split_ifs with hn
--     · cases ih (n + 1) with
--       | inl h_not => left; exact h_not
--       | inr h_all =>
--         right
--         intro i hi
--         if h_eq : i = n then
--           subst h_eq; exact hn
--         else
--           apply h_all i
--           constructor <;> omega
--     · left; exact hn
--
-- private theorem χ_aux_lt (xs : List V) (n fuel : Nat) (j : Nat) (hj1 : j ≥ n) (hj2 : j < χ_aux xs n fuel) : j ∈ xs := by
--   induction fuel generalizing n with
--   | zero =>
--     simp [χ_aux] at hj2; omega
--   | succ fuel ih =>
--     simp [χ_aux] at hj2
--     split_ifs at hj2 with hn
--     · if h_eq : j = n then
--         subst h_eq; exact hn
--       else
--         apply ih (n + 1) (by omega) hj2
--     · omega
--
-- theorem lemmaχ∉ (xs : List V) : χ' xs ∉ xs := by
--   unfold χ'
--   have spec := χ_aux_spec xs 0 (xs.length + 1)
--   cases spec with
--   | inl h_not => exact h_not
--   | inr h_all =>
--     have h_ge := forall_lt_mem_imp_length_ge (xs.length + 1) xs (fun i hi => h_all i ⟨Nat.zero_le i, hi⟩)
--     omega
--
-- theorem lemmaχaux⊆ (xs ys : List V) (h1 : ∀ z, z ∈ xs → z ∈ ys) (h2 : ∀ z, z ∈ ys → z ∈ xs) :
--     χ' xs = χ' ys := by
--   have hx_not : χ' xs ∉ xs := lemmaχ∉ xs
--   have hy_not : χ' ys ∉ ys := lemmaχ∉ ys
--   have hx_not_y : χ' xs ∉ ys := fun h => hx_not (h2 _ h)
--   have hy_not_x : χ' ys ∉ xs := fun h => hy_not (h1 _ h)
--   have hx_lt : ∀ j < χ' xs, j ∈ ys := fun j hj => h1 _ (χ_aux_lt xs 0 (xs.length + 1) j (Nat.zero_le j) hj)
--   have hy_lt : ∀ j < χ' ys, j ∈ xs := fun j hj => h2 _ (χ_aux_lt ys 0 (ys.length + 1) j (Nat.zero_le j) hj)
--   rcases Nat.lt_trichotomy (χ' xs) (χ' ys) with hlt | heq | hgt
--   · exfalso; exact hx_not_y (hy_lt _ hlt)
--   · exact heq
--   · exfalso; exact hy_not_x (hx_lt _ hgt)
--
-- end Chi
