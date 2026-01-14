/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
-/

/- Erdős Problem #12 (Part 1) Modified by OpenMath contributors, 2026.
   Reorganized for public theorem registry.
-/

import Mathlib
/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

/--
Let $A$ be an infinite set such that there are no distinct $a,b,c \in A$
such that $a \mid (b+c)$ and $b,c > a$. Is there such an $A$ with
$\liminf \frac{|A \cap \{1, \dotsc, N\}|}{N^{1/2}} > 0$ ?
-/
theorem erdos_12.parts.i : ∃ (A : Set ℕ), IsGood A ∧
    (0 : ℝ) < Filter.atTop.liminf
      (fun N => (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by sorry
