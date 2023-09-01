import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

section
variable {α : Type _}
variable (s t u : Set α)
open Set

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x x_stu
  have xs : x ∈ s := x_stu.1
  have xtu : x ∈ t ∪ u := x_stu.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩

  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  -- This is known as definitional reduction, a trick to reduce the number of lines in the proof.
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩) -- definitional reduction
  · use xs
    left
    use xt

  · use xs
    right
    use xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  -- xstu: x ∈ (s \ t) \ u. So xstu.1.1 means x ∈ s, etc.

  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2

  constructor
  · use xs
  
  intro xtu
  
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu)
  contradiction
  contradiction
  -- We can also write rintro (xt | xu) <;> contradiction
  -- tactic <;> tactic' runs tactic on the main goal
  -- and tactic' on each produced goal, concatenating all goals produced by tactic'.

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  rw [mem_diff]
  constructor
  use xs

  have h1: ¬ x ∈ t := by
    rw [union_def, mem_setOf, not_or] at xntu
    rcases xntu with ⟨nxt, _⟩
    use nxt
  use h1

  have h2: ¬ x ∈ u := by
    rw [union_def, mem_setOf, not_or] at xntu
    rcases xntu with ⟨_, nxu⟩
    use nxu
  use h2

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm

  show s ∩ (s ∪ t) ⊆ s
  intro x xsst
  rcases xsst with ⟨xs, xst⟩
  use xs

  show s ⊆ s ∩ (s ∪ t)
  intro x xs
  constructor
  use xs
  left
  use xs
  
example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, _⟩) <;> use xs
  · intro xs; left; use xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, _⟩ | xt)
    · left; use xs
    · right; use xt
  
  show x ∈ s ∪ t → x ∈ s \ t ∪ t
  by_cases h : x ∈ t
  intro
  right
  use h

  show x ∈ s ∪ t → x ∈ s \ t ∪ t
  rintro (xs | xt)
  · left
    use xs
  
  show x ∈ s \ t ∪ t
  right
  use xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left; use xs
      rintro ⟨_, xt⟩
      contradiction
    
    · constructor
      right; use xt
      rintro ⟨xs, _⟩
      contradiction

  · rintro ⟨ xs | xt, nxst⟩
    · left
      use xs
      intro xt
      apply nxst
      constructor
      use xs
      use xt

    · right
      use xt
      intro xs
      apply nxst
      constructor
      use xs
      use xt

end

section

variable (s t : Set ℕ)

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, oddx, primex⟩
  use x
  constructor
  apply ssubt xs
  show Prime x
  apply primex

end

end

section
variable {α I : Type _}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  
  constructor
  · rintro (xs | xI)
    · intro i
      right
      use xs

    intro i
    left
    exact xI i
  
  show (∀ (i : I), x ∈ A i ∨ x ∈ s) → x ∈ s ∨ ∀ (i : I), x ∈ A i
  intro h
  by_cases xs : x ∈ s
  · left
    use xs
  
  show x ∈ s ∨ ∀ (i : I), x ∈ A i
  right
  intro i
  cases h i
  · assumption
  contradiction

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, xgep, primep⟩
  use p, primep

end
