/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Second moments of finite sums of square integrable functions

Staged for `Mathlib/MeasureTheory/Function/L2Space.lean`.

* `MeasureTheory.integral_sq_sum_range_eq`: the second moment of `∑_{k < n} Y k`, by lags.
* `MeasureTheory.integral_sq_sum_abs_le_card_mul_sum_integral_sq`: the Cauchy–Schwarz inequality
  `∫ (∑_{i ∈ s} |Y i|)² ≤ #s ∑_{i ∈ s} ∫ (Y i)²`.

## Search

At Mathlib `d13f23b`: `grep -rn "integral_sq_sum\|integral_sum_sq\|variance_sum" Mathlib` finds
`ProbabilityTheory.variance_sum'` (`Probability/Moments/Variance.lean`: the variance of a sum as
the double sum of covariances, centered at the means, for a finite measure) and
`ProbabilityTheory.IndepFun.variance_sum`; neither expands the second moment of a sum that is not
centered at its mean, and neither orders the pairs by lag.
`grep -rn "sq_sum_le_card_mul_sum_sq" Mathlib` finds the inequality for finite sums of numbers
(`Algebra/Order/Chebyshev.lean`), with no integrated form.
-/

@[expose] public section

open Finset

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The second moment of a sum, by lags**: for square integrable `Y k`,
`∫ (∑_{k < n} Y k)² = ∑_{k < n} (2 ∑_{l < n - k} ∫ Y k Y (k + l) - ∫ (Y k)²)`. -/
theorem integral_sq_sum_range_eq {Y : ℕ → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 μ) (n : ℕ) :
    ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂μ = ∑ k ∈ range n,
      (2 * ∑ l ∈ range (n - k), ∫ ω, Y k ω * Y (k + l) ω ∂μ - ∫ ω, Y k ω ^ 2 ∂μ) := by
  have hi2 (k l : ℕ) : Integrable (fun ω ↦ Y k ω * Y (k + l) ω) μ :=
    (hY k).integrable_mul (hY (k + l))
  have hi (k : ℕ) : Integrable (fun ω ↦ ∑ l ∈ range (n - k), Y k ω * Y (k + l) ω) μ :=
    integrable_finsetSum _ fun l _ ↦ hi2 k l
  simp_rw [Finset.sq_sum_range_eq_sum_range_sum_range]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [integral_sub ((hi k).const_mul 2) (hY k).integrable_sq, integral_const_mul,
      integral_finsetSum _ fun l _ ↦ hi2 k l]
  · exact fun k _ ↦ ((hi k).const_mul 2).sub (hY k).integrable_sq

/-- **Cauchy–Schwarz for a finite sum of square integrable functions**:
`∫ (∑_{i ∈ s} |Y i|)² ≤ #s ∑_{i ∈ s} ∫ (Y i)²`. -/
theorem integral_sq_sum_abs_le_card_mul_sum_integral_sq {ι : Type*} (s : Finset ι)
    {Y : ι → Ω → ℝ} (hY : ∀ i ∈ s, MemLp (Y i) 2 μ) :
    ∫ ω, (∑ i ∈ s, |Y i ω|) ^ 2 ∂μ ≤ #s * ∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ := by
  rw [← integral_finsetSum _ fun i hi ↦ (hY i hi).integrable_sq, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
    ((integrable_finsetSum _ fun i hi ↦ (hY i hi).integrable_sq).const_mul _)
    (ae_of_all _ fun ω ↦ ?_)
  simpa only [sq_abs] using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ |Y i ω|)

end MeasureTheory
