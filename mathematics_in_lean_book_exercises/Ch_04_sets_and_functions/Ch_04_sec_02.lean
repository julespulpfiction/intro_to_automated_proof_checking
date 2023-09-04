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
    have k: f x ∈ f '' s := mem_image_of_mem _ xs
    use h k

  intro h y y_in_fs
  rcases y_in_fs with ⟨x, xs, fx_eq_y⟩
  rw [← fx_eq_y]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x x_fifs
  rcases x_fifs with ⟨y, ys, fx_eq_fy⟩
  rw [← h fx_eq_fy]
  -- basically changed the goal from x ∈ s to y ∈ s using injectivity
  use ys
