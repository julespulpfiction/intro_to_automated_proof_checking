import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  rcases a with ⟨xa, ya, za⟩ 
  rcases b with ⟨xb, yb, zb⟩
  rcases c with ⟨xc, yc, zc⟩ -- This splits the goal into the goals for each component separately

  simp [add, add_assoc] -- This simplifies the goal using the definition of add

def smul (r : ℝ) (a : Point) : Point := ⟨r*a.x, r*a.y, r*a.z⟩

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  -- To prove that scalar multiplication distributes over addition,
  -- it suffices to prove that it distributes over each component
  rcases a with ⟨xa, ya, za⟩
  rcases b with ⟨xb, yb, zb⟩
  simp [smul, add, mul_add] -- This simplifies the goal using the definition of smul

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

noncomputable section

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex
  -- We define the weighted average of a and b as the point
  -- lambda * a + (1 - lambda) * b
  where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z

  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)

  -- I am stuck here
end

end StandardTwoSimplex