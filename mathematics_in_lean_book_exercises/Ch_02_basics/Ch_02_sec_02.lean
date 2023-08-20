import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left a c]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← neg_add_cancel_right a b, add_assoc, add_comm _ b, ← add_assoc]
  rw [h, add_neg_cancel_right]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel_right a b, add_assoc, add_comm, add_assoc]
  rw [add_comm] at h
  rw [h, add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [add_left_neg]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a, add_right_neg]

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

section
variable {G : Type _} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h: (a*a⁻¹)⁻¹ * (a*a⁻¹*(a*a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a a⁻¹, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹*a⁻¹), ← mul_left_inv (a*b), mul_assoc]
  rw [mul_assoc a b _, ← mul_assoc b b⁻¹, mul_right_inv b]
  rw [one_mul, mul_right_inv, mul_one]

end MyGroup

end
