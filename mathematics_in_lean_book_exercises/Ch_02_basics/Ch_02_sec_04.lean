import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

example : max a b = max b a := by
  apply le_antisymm
  apply max_le
  apply le_max_right
  apply le_max_left
  apply max_le
  apply le_max_right
  apply le_max_left
  
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left

    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right

    apply min_le_right
  
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left

  apply le_trans
  apply min_le_right
  apply min_le_right

-- This is the first time I used · and indententation in a proof,
-- it took some time to get the hang of it.

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

end

section
variable (w x y z : ℕ)

-- theorems with dvd in their names refer to divisibility

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

end

section
variable (m n : ℕ)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat'
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left  
end

