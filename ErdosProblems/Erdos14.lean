/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
-/

/- Modified by OpenMath contributors, 2026.
   Reorganized for public theorem registry.
-/

import Mathlib
namespace Erdos14
open Asymptotics Filter

abbrev allUniqueSums (A : Set ℕ) : Set ℕ :=
  { n | ∃! (a : ℕ × ℕ), a.1 ≤ a.2 ∧ a.1 ∈ A ∧ a.2 ∈ A ∧ a.1 + a.2 = n }

/--
The number of integers in $\{1,\ldots,N\}$ which are not representable in exactly one way
as the sum of two elements from $A$ (either because they are not representable at all, or
because they are representable in more than one way).
-/
noncomputable def nonUniqueSumCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ (allUniqueSums A)).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1/2 - ε)

noncomputable def squareRoot (N : ℕ) : ℝ :=
  Real.sqrt N

/--
Let $A ⊆ \mathbb{N}$. Let $B ⊆ \mathbb{N}$ be the set of integers which are representable
in exactly one way as the sum of two elements from $A$. Is it true that for all
$\epsilon > 0$ and large $N$, $|\{1,\ldots,N\} \setminus B| \gg_\epsilon N^{1/2 - \epsilon}$?
-/
theorem erdos_14a : ∀ A, ∀ ε > 0, nonUniqueSumCount A ≫ almostSquareRoot ε := by sorry

/--
Is it possible that $|\{1,\ldots,N\} \setminus B| = o(N^\frac{1}{2})$?
-/
theorem erdos_14b : ∃ (A : Set ℕ), IsLittleO atTop (nonUniqueSumCount A) squareRoot := by sorry

end Erdos14
