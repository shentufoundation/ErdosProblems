/-
Copyright 2025 The Formal Conjectures Authors (Google DeepMind).
Licensed under the Apache License, Version 2.0
-/

/- Modified by OpenMath contributors, 2026.
   Reorganized for public theorem registry.
-/

import Mathlib

namespace Erdos10
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

theorem erdos_10.variants.granville_soundararajan_odd :
    {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3 ∧
      {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4 := by sorry

end Erdos10
