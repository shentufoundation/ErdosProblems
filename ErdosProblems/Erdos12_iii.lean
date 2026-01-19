/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
-/

/- Modified by OpenMath contributors, 2026.
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
such that $a \mid (b+c)$ and $b,c > a$. Is it true that $∑_{n \in A} \frac{1}{n} < \infty$?
-/
theorem erdos_12.parts.iii : ∀ (A : Set ℕ), IsGood A → Summable (fun (n : A) ↦ (1 / n : ℝ)) := by
sorry

end Erdos12
