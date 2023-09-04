import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

example : f ¹' (u ∩ v) = f ¹' u ∩ f ¹' v := by
  ext
  rfl
