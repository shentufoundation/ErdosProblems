/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
-/
/- Erdős Problem #12 (Part 2) Modified by OpenMath contributors, 2026.
   Reorganized for public theorem registry.
-/
import Mathlib
namespace Erdos12
/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

/--
Let $A$ be an infinite set such that there are no distinct $a,b,c \in A$
such that $a \mid (b+c)$ and $b,c > a$. Does there exist some absolute constant $c > 0$
such that there are always infinitely many $N$
with $|A \cap \{1, \dotsc, N\}| < N^{1−c}$?
-/
theorem erdos_12.parts.ii : ∃ c > (0 : ℝ), ∀ (A : Set ℕ), IsGood A →
  {N : ℕ| (A ∩ Set.Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite := by sorry

end Erdos12
