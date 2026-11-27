import MCMC.Finite.MetropolisHastings
import MCMC.ToMathlib.Probability.Kernel.Invariance

namespace MCMC.Finite

open ProbabilityTheory MeasureTheory Matrix Kernel Mathlib
open scoped Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n]

/-- The kernel `i ↦ ∑ j, P i j • δ_j` of a nonnegative matrix on a finite type; it is a Markov
kernel for a stochastic matrix (`matrixToKernel_isMarkov`). -/
noncomputable def matrixToKernel (P : Matrix n n ℝ) (_ : ∀ i j, 0 ≤ P i j) :
    Kernel n n :=
  -- Build kernel rows as sums of (nonnegative) weights times Dirac measures.
  let rowMeasure : n → Measure n :=
    fun i => ∑ j : n, (ENNReal.ofReal (P i j)) • Measure.dirac j
  ProbabilityTheory.Kernel.ofFunOfCountable rowMeasure

/-- Convert a probability vector to a probability measure on finite types -/
noncomputable def vecToMeasure (π : stdSimplex ℝ n) : Measure n :=
  ∑ i : n, (ENNReal.ofReal (π.val i)) • Measure.dirac i

omit [DecidableEq n] in
/-- The kernel of a matrix on a measurable set: the sum of the entries of the row in the set. -/
theorem matrixToKernel_apply {P : Matrix n n ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : n) {B : Set n}
    (hB : MeasurableSet B) :
    matrixToKernel P hP i B = ∑ j : n, ENNReal.ofReal (P i j) * B.indicator 1 j := by
  change ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) B = _
  simp [hB, Measure.dirac_apply']

omit [DecidableEq n] in
/-- The kernel of a matrix on a singleton is the entry. -/
theorem matrixToKernel_singleton {P : Matrix n n ℝ} (hP : ∀ i j, 0 ≤ P i j) (i j : n) :
    matrixToKernel P hP i {j} = ENNReal.ofReal (P i j) := by
  classical
  change ((∑ k : n, ENNReal.ofReal (P i k) • Measure.dirac k) : Measure n) {j} = _
  simp [Measure.dirac_apply', Pi.single_apply]

open scoped ENNReal

instance isProbabilityMeasure_vecToMeasure (π : stdSimplex ℝ n) :
    IsProbabilityMeasure (vecToMeasure π) :=
  ⟨by rw [← ENNReal.ofReal_one, ← π.property.2,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ π.property.1 i]; simp [vecToMeasure]⟩

/-- The measure of a probability vector on a singleton is the entry. -/
theorem vecToMeasure_singleton (π : stdSimplex ℝ n) (i : n) :
    vecToMeasure π {i} = ENNReal.ofReal (π.val i) := by
  simp [vecToMeasure, Measure.dirac_apply', Pi.single_apply]

/-- The kernel of a nonnegative matrix on a finite type is finite. -/
instance isFiniteKernel_matrixToKernel (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    IsFiniteKernel (matrixToKernel P hP) :=
  ⟨⟨∑ i, ∑ j, ENNReal.ofReal (P i j), ENNReal.sum_lt_top.2 fun _ _ ↦
    ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top, fun i ↦ by
      change ((∑ k : n, ENNReal.ofReal (P i k) • Measure.dirac k) : Measure n) Set.univ ≤ _
      simpa using Finset.single_le_sum (f := fun i ↦ ∑ j, ENNReal.ofReal (P i j))
        (fun _ _ ↦ zero_le) (Finset.mem_univ i)⟩⟩

/-- Matrix stationarity is equivalent to kernel invariance -/
theorem isStationary_iff_invariant (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (hP : ∀ i j, 0 ≤ P i j) :
    IsStationary P π ↔ Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) := by
  rw [Kernel.Invariant, Measure.ext_iff_singleton, IsStationary, funext_iff]
  refine forall_congr' fun j ↦ ?_
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _), lintegral_fintype,
    vecToMeasure_singleton]
  simp_rw [matrixToKernel_singleton, vecToMeasure_singleton, ← ENNReal.ofReal_mul (hP _ _)]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (hP i j) (π.property.1 i),
    ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hP i j)
      (π.property.1 i)) (π.property.1 j)]
  rfl

/-- Matrix reversibility is equivalent to kernel reversibility -/
theorem isReversible_iff_kernel_reversible (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (hP : ∀ i j, 0 ≤ P i j) :
    IsReversible P π ↔ Kernel.IsReversible (matrixToKernel P hP) (vecToMeasure π) := by
  rw [Kernel.isReversible_iff_map_swap_compProd, Measure.ext_iff_singleton, Prod.forall]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rw [Measure.map_apply measurable_swap (measurableSet_singleton _),
    show Prod.swap ⁻¹' {(i, j)} = {(j, i)} from Set.ext fun p ↦ by simp [Prod.ext_iff, and_comm],
    Measure.compProd_apply_singleton, Measure.compProd_apply_singleton, vecToMeasure_singleton,
    vecToMeasure_singleton, matrixToKernel_singleton, matrixToKernel_singleton,
    ← ENNReal.ofReal_mul (π.property.1 _), ← ENNReal.ofReal_mul (π.property.1 _),
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (π.property.1 _) (hP _ _))
      (mul_nonneg (π.property.1 _) (hP _ _))]
  exact eq_comm

/-- The kernel of a stochastic matrix is a Markov kernel. -/
instance matrixToKernel_isMarkov (P : Matrix n n ℝ) (hP : IsStochastic P) :
    IsMarkovKernel (matrixToKernel P hP.1) :=
  ⟨fun i ↦ ⟨by
    change ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) Set.univ = 1
    simp [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hP.1 i j, hP.2 i]⟩⟩

theorem IsReversible.is_stationary' {P : Matrix n n ℝ} {π : stdSimplex ℝ n}
    (hP : IsStochastic P) (h_rev : IsReversible P π) :
    IsStationary P π := by
  rw [isStationary_iff_invariant P π hP.1]
  rw [isReversible_iff_kernel_reversible P π hP.1] at h_rev
  have := matrixToKernel_isMarkov P hP
  exact h_rev.invariant

end MCMC.Finite
