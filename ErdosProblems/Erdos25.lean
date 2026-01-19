/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
Modified by OpenMath contributors, 2026.
   Reorganized for public theorem registry.
-/

import Mathlib
open Filter Real Nat Set
open scoped Topology
namespace Erdos25
/--
The logarithmic density of a set `s : Set ℕ` exists and equals `d`
if and only if
  lim_{x → ∞} (1 / log x) * ∑_{n ∈ s ∩ Iio x} (1 / n) = d.
-/
abbrev HasLogDensity (s : Set ℕ) (d : ℝ) : Prop := Tendsto (fun x : ℝ =>
   (1 / Real.log x) * ∑' n : ℕ, Set.indicator s
      (fun n => if (n : ℝ) ≤ x then (1 : ℝ) / (n + 1) else 0) n) atTop (𝓝 d)

/--
Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class
$a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either $n < n_i$ or
$n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?
-/
theorem erdos_25 : ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
      ∃ d, HasLogDensity
        { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) } d := by sorry

end Erdos25
