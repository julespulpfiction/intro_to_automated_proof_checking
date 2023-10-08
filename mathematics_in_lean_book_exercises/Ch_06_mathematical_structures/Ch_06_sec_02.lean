section

structure AddGroup₁ (α : Type _) where -- We define an additive group
  (add : α → α → α)
  zero: α
  neg : α → α
  inv : α → α
  addAssoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_left_neg : ∀ a : α, add (neg a) a = zero

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  sorry

def neg (a : Point) : Point :=
  sorry

def zero : Point :=
  sorry

def addGroupPoint : AddGroup₁ Point := sorry

end Point