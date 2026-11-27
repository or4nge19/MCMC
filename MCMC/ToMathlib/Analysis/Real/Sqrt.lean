/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# A power below a product of powers of the square root

Staged for `Mathlib/Analysis/Real/Sqrt.lean`: for `0 ≤ ρ ≤ 1`, a bound `ρ ^ max k l` splits as
`√ρ ^ k * √ρ ^ l`, a product of a function of `k` and a function of `l`.

## Search

At Mathlib `d13f23b`: `grep -rn "pow_le_sqrt\|sqrt_pow_mul\|min_pow_le" Mathlib` finds nothing.
-/

@[expose] public section

/-- **A power below a product of square roots**: for `0 ≤ ρ ≤ 1` and `k ≤ l`,
`ρ ^ l ≤ √ρ ^ k * √ρ ^ l`. -/
theorem Real.pow_le_sqrt_pow_mul_sqrt_pow {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {k l : ℕ}
    (hkl : k ≤ l) : ρ ^ l ≤ √ρ ^ k * √ρ ^ l :=
  calc ρ ^ l = √ρ ^ l * √ρ ^ l := by rw [← mul_pow, Real.mul_self_sqrt h0]
    _ ≤ √ρ ^ k * √ρ ^ l := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 h1) hkl)
        (pow_nonneg (Real.sqrt_nonneg _) _)
