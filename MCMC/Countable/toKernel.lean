import MCMC.Countable.CountableStochastic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Irreducible

/-!
# Countable matrices as kernels

This file bridges the countable-state matrix interface in
`MCMC.Countable.CountableStochastic` with mathlib's `Kernel` API on discrete measurable spaces.

## Main definitions

* `weightsToMeasure`: the atomic measure attached to a nonnegative weight function.
* `matrixToKernel`: the kernel attached to a nonnegative infinite matrix.

## Main statements

* `isStochastic_iff_isMarkovKernel`: a nonnegative matrix is stochastic iff the associated kernel is
  Markov.
* `isInvariantMeasure_iff_invariant`: pointwise invariant measures agree with kernel invariance.
* `kernel_isIrreducible_of_isIrreducible`: countable irreducibility implies kernel irreducibility
  with respect to counting measure.

## Implementation notes

The elementary Chapter 5 definitions are kept in pointwise form in
`MCMC.Countable.CountableStochastic`. This file provides the measure-theoretic bridge needed to
reuse mathlib's kernel API without hard-coding measurable-space assumptions into the core file.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Tags

kernel, invariant measure, stochastic matrix, countable state space
-/

namespace MCMC.Countable

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

section KernelBridge

variable {α : Type*} [Countable α] [DecidableEq α]
variable [MeasurableSpace α] [MeasurableSingletonClass α]

/--
Turn a nonnegative weight function on a countable discrete space into the corresponding atomic
measure.
-/
noncomputable def weightsToMeasure (w : α → ℝ) (_hw : ∀ i, 0 ≤ w i) : Measure α :=
  Measure.sum fun i : α => ENNReal.ofReal (w i) • Measure.dirac i

@[simp] theorem weightsToMeasure_apply_singleton
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) (i : α) :
    weightsToMeasure w hw {i} = ENNReal.ofReal (w i) := by
  sorry

/--
Interpret a nonnegative countable-state matrix as a kernel on the associated discrete measurable
space.
-/
noncomputable def matrixToKernel (P : InfMatrix α) (hP_nonneg : ∀ i j, 0 ≤ P i j) : Kernel α α :=
  Kernel.ofFunOfCountable fun i => weightsToMeasure (P i) (hP_nonneg i)

omit [DecidableEq α] in
@[simp] theorem matrixToKernel_apply (P : InfMatrix α) (hP_nonneg : ∀ i j, 0 ≤ P i j) (i : α) :
    matrixToKernel P hP_nonneg i = weightsToMeasure (P i) (hP_nonneg i) := by
  rfl

/-- The matrix-induced kernel evaluates on singletons by reading off the corresponding entry. -/
@[simp] theorem matrixToKernel_apply_singleton
    (P : InfMatrix α) (hP_nonneg : ∀ i j, 0 ≤ P i j) (i j : α) :
    matrixToKernel P hP_nonneg i {j} = ENNReal.ofReal (P i j) := by
  rw [matrixToKernel_apply]
  simp

/--
For a nonnegative matrix, stochasticity is equivalent to the associated discrete kernel being
Markov.
-/
theorem isStochastic_iff_isMarkovKernel
    {P : InfMatrix α} (hP_nonneg : ∀ i j, 0 ≤ P i j) :
    IsStochastic P ↔ IsMarkovKernel (matrixToKernel P hP_nonneg) := by
  sorry

/--
Pointwise invariant measures coincide with invariant measures for the associated discrete kernel.
-/
theorem isInvariantMeasure_iff_invariant
    {P : InfMatrix α} (hP_nonneg : ∀ i j, 0 ≤ P i j)
    {v : α → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) :
    IsInvariantMeasure P v ↔
      v ≠ 0 ∧ Kernel.Invariant (matrixToKernel P hP_nonneg) (weightsToMeasure v hv_nonneg) := by
  sorry

/--
Countable irreducibility implies irreducibility of the associated discrete kernel with respect to
counting measure.
-/
theorem kernel_isIrreducible_of_isIrreducible
    {P : InfMatrix α} (hP_irred : IsIrreducible P) :
    ProbabilityTheory.Kernel.IsIrreducible Measure.count (matrixToKernel P hP_irred.nonneg) := by
  sorry

end KernelBridge

end MCMC.Countable
