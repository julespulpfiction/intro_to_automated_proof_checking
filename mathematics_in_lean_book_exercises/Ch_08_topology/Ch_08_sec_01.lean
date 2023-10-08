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
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry