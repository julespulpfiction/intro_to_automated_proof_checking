import Mathlib.Tactic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type _} [MetricSpace X] (a b c : X)

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  continuity

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  hf.comp ((continuous_pow 2).add continuous_id)

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
  -- Given seq u → a and u_n ∈ s ∀ n, we want to show a ∈ closure s.

  rw [Metric.tendsto_atTop] at hu -- writes ε defn of seq u tends to a
  rw [Metric.mem_closure_iff]     -- writes ε defn of a in closure s

  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, u_tendsto_a_after_N⟩
  refine' ⟨u N, hs N, _⟩

  have N_geq_N: N ≥ N := by linarith
  have dist_comm_uN_a: dist (u N) a = dist a (u N) := by apply dist_comm
  have p: dist (u N) a < ε := u_tendsto_a_after_N N N_geq_N

  rw [dist_comm_uN_a] at p
  exact p

example {X : Type _} [MetricSpace X] [CompactSpace X]
      {Y : Type _} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  -- Given f : X → Y, we want to show f is uniformly continuous.
  
