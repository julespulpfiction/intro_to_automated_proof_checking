import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  apply lt_of_le_of_lt h₂
  apply h₃

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have h: exp (a+d) ≤ exp (a+e) := by
    apply exp_le_exp.2
    apply add_le_add_left
    apply h₀   
  apply add_le_add_left
  apply h

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos
    norm_num
    apply exp_pos
  
  have h₁ : 0 < 1 + exp b := by
    apply add_pos
    norm_num
    apply exp_pos

  apply (log_le_log h₀ h₁).mpr
  apply add_le_add_left
  apply exp_le_exp.2
  apply h

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h1: - exp b ≤ - exp a := by apply neg_le_neg; apply exp_le_exp.2; apply h
  linarith [h1]

theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h1: (0: ℝ) < 2:= by norm_num
  apply abs_le'.2
  constructor
  · rw [le_div_iff]
    apply fact1
    exact h1

  · rw [le_div_iff]
    apply fact2
    apply h1  
