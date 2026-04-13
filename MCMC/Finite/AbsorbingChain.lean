import MCMC.Finite.Core
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Absorbing chains and the fundamental matrix

This file contains the Chapter 4 absorbing-chain scaffold.

The transient regime is encoded structurally through summability of the geometric series
`∑ Q^k`, so the Green-kernel objects `expectedVisitsMatrix` and `expectedAbsorptionTime` are only
defined after providing a transient witness.
-/

namespace MCMC.Finite

open Filter Matrix Topology
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite matrix is substochastic if it is entrywise nonnegative and every row sum is at most `1`. -/
def IsSubstochastic (Q : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j ≤ 1

/--
Transience of the transient block is encoded by summability of the geometric series
`∑ Q^k`.
-/
def IsTransient (Q : Matrix n n ℝ) : Prop :=
  Summable fun k : ℕ => Q ^ k

/-- A transient substochastic matrix. -/
def IsTransientSubstochastic (Q : Matrix n n ℝ) : Prop :=
  IsSubstochastic Q ∧ IsTransient Q

/-- The finite geometric partial sums attached to `Q`. -/
def geometricPartialSums (Q : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  Finset.sum (Finset.range N) fun k => Q ^ k

@[simp]
theorem geometricPartialSums_zero (Q : Matrix n n ℝ) :
    geometricPartialSums Q 0 = 0 := by
  simp [geometricPartialSums]

/-- The classical fundamental matrix `(I - Q)⁻¹`. -/
noncomputable def fundamentalMatrix (Q : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - Q)⁻¹

/--
The Green kernel attached to `Q`, defined only in the transient regime.
-/
noncomputable def expectedVisitsMatrix (Q : Matrix n n ℝ) (_hQ : IsTransient Q) : Matrix n n ℝ :=
  ∑' k : ℕ, Q ^ k

/--
Expected absorption times as the Green kernel applied to the all-ones vector.
-/
noncomputable def expectedAbsorptionTime (Q : Matrix n n ℝ) (_hQ : IsTransient Q) : n → ℝ :=
  expectedVisitsMatrix Q _hQ *ᵥ (1 : n → ℝ)

/-- Summability of the powers implies their convergence to zero. -/
theorem IsTransient.tendsto_pow_zero
    {Q : Matrix n n ℝ} (hQ : IsTransient Q) :
    Tendsto (fun k : ℕ => Q ^ k) atTop (nhds (0 : Matrix n n ℝ)) := by
  sorry

/-- Transient substochastic matrices have powers converging to zero. -/
theorem transient_tendsto_zero
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    Tendsto (fun k : ℕ => Q ^ k) atTop (nhds (0 : Matrix n n ℝ)) := by
  exact hQ.2.tendsto_pow_zero

/--
Finite geometric-sum identity for matrices.
-/
theorem one_sub_mul_geometricPartialSums
    {Q : Matrix n n ℝ} (N : ℕ) :
    (1 - Q) * geometricPartialSums Q N = 1 - Q ^ N := by
  sorry

/--
The geometric partial sums converge to the Green kernel in the transient regime.
-/
theorem geometricPartialSums_tendsto_expectedVisitsMatrix
    {Q : Matrix n n ℝ} (hQ : IsTransient Q) :
    Tendsto (fun N : ℕ => geometricPartialSums Q N) atTop
      (nhds (expectedVisitsMatrix Q hQ)) := by
  sorry

/--
The geometric partial sums converge to the fundamental matrix in the transient substochastic
regime.
-/
theorem geometricPartialSums_tendsto_fundamentalMatrix
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    Tendsto (fun N : ℕ => geometricPartialSums Q N) atTop
      (nhds (fundamentalMatrix Q)) := by
  sorry

/--
Existence and entrywise nonnegativity of the fundamental matrix.
-/
theorem fundamentalMatrix_isUnit_and_nonneg
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    IsUnit (1 - Q) ∧ ∀ i j, 0 ≤ fundamentalMatrix Q i j := by
  sorry

/--
The Green-kernel series agrees with the fundamental matrix.
-/
theorem expectedVisitsMatrix_eq_fundamentalMatrix
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    expectedVisitsMatrix Q hQ.2 = fundamentalMatrix Q := by
  sorry

/--
Expected absorption times are obtained by summing the expected visits.
-/
@[simp] theorem expectedAbsorptionTime_eq_expectedVisitsMatrix_mulVec_one
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    expectedAbsorptionTime Q hQ.2 = expectedVisitsMatrix Q hQ.2 *ᵥ (1 : n → ℝ) := by
  rfl

/--
Expected absorption times are given by the fundamental matrix applied to the all-ones vector.
-/
theorem expectedAbsorptionTime_eq_fundamentalMatrix_mulVec_one
    {Q : Matrix n n ℝ} (hQ : IsTransientSubstochastic Q) :
    expectedAbsorptionTime Q hQ.2 = fundamentalMatrix Q *ᵥ (1 : n → ℝ) := by
  sorry

end MCMC.Finite
