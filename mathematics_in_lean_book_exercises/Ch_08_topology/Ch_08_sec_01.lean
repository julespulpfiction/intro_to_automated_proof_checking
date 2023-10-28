import Mathlib.Tactic
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type _} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  -- We must show three properties of a filter:
  -- 1. The set of all elements of α belongs to the filter
  -- 2. If A is in the filter and A ⊆ B, then B is in the filter.
  -- 3. If A and B are in the filter, then so is A ∩ B.
  univ_sets := subset_univ s
  sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
  inter_sets := fun hU hV ↦ subset_inter hU hV

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use
      simp

    sets_of_superset := by
      rintro U V ⟨N, hN⟩ hUV
      use N
      tauto

    inter_sets := by
      rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
      use max N N'
      intro b hb
      rw [max_le_iff] at hb
      constructor <;> tauto }

def Tendsto₁ {X Y : Type _} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

example {X Y Z : Type _} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg

example {X Y Z : Type _} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  -- Composition of limits
  intro V hV
  rw [preimage_comp]
  apply hf
  apply hg
  exact hV
