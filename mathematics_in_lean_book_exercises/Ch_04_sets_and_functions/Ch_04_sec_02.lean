import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this

  intro h y y_in_fs
  rcases y_in_fs with ⟨x, xs, fx_eq_y⟩
  rw [← fx_eq_y]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x x_fifs
  rcases x_fifs with ⟨y, ys, fx_eq_fy⟩
  rw [← h fx_eq_fy]
  -- basically changed the goal from x ∈ s to y ∈ s using injectivity
  exact ys 

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  rcases h with ⟨y, y_in_f_inv_u, fy_eq_x⟩
  rw [← fy_eq_x]
  exact y_in_f_inv_u

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fx_eq_y⟩
  use x
  constructor
  · show f x ∈ u -- Changed the goal from x ∈ f ⁻¹' u to f x ∈ u
    rw [fx_eq_y]
    exact yu
  rw [fx_eq_y]
  
example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y y_in_fs
  rcases y_in_fs with ⟨x, xs, fx_eq_y⟩
  use x
  constructor
  exact h xs -- x is an element of s, which is a subset of t
  rw [fx_eq_y]

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x x_in_finv_u
  show f x ∈ v -- Changed the goal from x ∈ f ⁻¹' v to f x ∈ v
  have : f x ∈ u := x_in_finv_u
  exact h this

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  rfl

-- There are many more set theoretic identities which I can easily do,
-- But I am skipping for the interest of time.

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x xs_or_x_in_finv_u
  rcases xs_or_x_in_finv_u with (xs | x_in_finv_u)

  left
  use x
  constructor
  exact xs
  rfl

  show f x ∈ f '' s ∪ u
  right
  exact x_in_finv_u


end

section

open Set Real

example : InjOn sqrt { x | x ≥ 0 } := by
  -- Proving that the sqrt function is injective
  intro x x_nonneg y y_nonneg
  intro sqrtx_eq_sqrty
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt x_nonneg]
    _ = sqrt y ^ 2 := by rw [sqrtx_eq_sqrty]
    _ = y := by rw [sq_sqrt y_nonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  -- Proving that the function x ↦ x ^ 2 is injective for non-negative reals
  intro x x_nonneg y y_nonneg
  intro x2_eq_y2
  dsimp at * -- This is a nice trick to unfold the definition of our function
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq x_nonneg]
    _ = sqrt (y ^ 2) := by rw [x2_eq_y2]
    _ = y := by rw [sqrt_sq y_nonneg]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  -- Proving that the range of the function is all the non-neg reals
  ext y
  constructor
  · intro y_in_range
    rcases y_in_range with ⟨x, x2_eq_y⟩
    rw [← x2_eq_y]
    dsimp
    exact sq_nonneg x -- sq_nonneg is a tactic that x ^ 2 is always non-negative
  
  intro y_non_neg
  use sqrt y
  dsimp
  rw [sq_sqrt y_non_neg]

end

section
variable {α β : Type _} [Inhabited α]
variable (P : α → Prop) (h : ∃ x, P x)

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h
                      else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]
  dsimp
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  -- Proving that f is injective iff the left inverse of f is (inverse f)
  -- as defined above
  constructor
  · intro f_is_inj x
    apply f_is_inj
    apply inverse_spec
    use x
  
  intro left_inv -- left_inv means inverse f (f y) = y
  intro x y
  intro fx_eq_fy
  calc
    x = (inverse f (f x)) := by rw [left_inv]
    _ = (inverse f (f y)) := by rw [fx_eq_fy]
    _ = y := by rw [left_inv]
  
example : Surjective f ↔ RightInverse (inverse f) f := by
  -- Proving that f is surjective iff the right inverse of f is (inverse f)
  -- as defined above
  constructor

  · intro h y
    apply inverse_spec
    apply h
  
  intro right_inv -- right_inv means f (inverse f y) = y
  intro y
  use inverse f y
  rw [right_inv]

end

section
variable {α : Type _}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  -- Proving the Cantor Theorem:
  -- there is no surjective map from a set to it's power set

  intro f surjf
  -- We have assumed that such a surjective map exists
  -- And we will now arrive at a contradiction.
  let S := { i | i ∉ f i }

  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction

  have h₂ : j ∈ S := h₁ -- because j ∉ f j, j ∈ S
  
  have h₃ : j ∉ S := by rwa [h] at h₁ -- from h1, j ∉ f j, and from h, f j = S,
  -- we get j ∉ S, which contradicts h2

  contradiction
end