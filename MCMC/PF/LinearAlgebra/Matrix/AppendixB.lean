import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Seneta Appendix B

This file packages the matrix-analysis input from Seneta's Appendix B by specializing mathlib's
geometric-series and exponential API to finite matrices.

## Main statements

* `isUnit_one_sub_and_tsum_pow_eq_inv_of_tendsto_zero`: a Neumann-series inversion principle from
  the vanishing of powers.
* `isUnit_one_sub_smul_and_tsum_pow_eq_inv_of_tendsto_zero`: a resolvent expansion obtained from the
  vanishing of the powers of `z • A`.
* `summable_matrixExpSeries`: summability of the matrix exponential series.

## Implementation notes

The additive law for matrix exponentials is already available in mathlib as
`Matrix.exp_add_of_commute`, so this file only adds the Seneta-specific resolvent packaging that is
not already present in the imported API.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Tags

matrix, resolvent, Neumann series, matrix exponential
-/

namespace MCMC.PF

open Filter Topology
open scoped BigOperators

section AppendixB

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
If the powers of a finite matrix tend to `0`, then the geometric series of powers inverts `1 - A`.
-/
theorem isUnit_one_sub_and_tsum_pow_eq_inv_of_tendsto_zero
    {A : Matrix n n ℝ} (h_tendsto : Tendsto (fun k : ℕ => A ^ k) atTop (nhds 0)) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k := by
  sorry

/--
If the powers of `z • A` tend to `0`, then the resolvent of `A` at `z` is given by the convergent
power series.
-/
theorem isUnit_one_sub_smul_and_tsum_pow_eq_inv_of_tendsto_zero
    {A : Matrix n n ℂ} {z : ℂ}
    (h_tendsto : Tendsto (fun k : ℕ => (z • A) ^ k) atTop (nhds 0)) :
    IsUnit (1 - z • A) ∧ (1 - z • A)⁻¹ = ∑' k : ℕ, z ^ k • A ^ k := by
  sorry

/--
The matrix exponential series is summable termwise.
-/
theorem summable_matrixExpSeries {A : Matrix n n ℂ} (t : ℂ) :
    Summable (fun k : ℕ => (t ^ k / (Nat.factorial k : ℂ)) • A ^ k) := by
  sorry

end AppendixB

end MCMC.PF
