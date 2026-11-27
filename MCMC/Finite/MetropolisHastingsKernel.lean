/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.Finite.toKernel
import MCMC.ToMathlib.Probability.Kernel.AcceptReject

/-!
# The finite Metropolis–Hastings matrix is the general Metropolis–Hastings kernel

On a finite state space, `matrixToKernel` sends a nonnegative matrix `Q` to the kernel
`i ↦ ∑ j, Q i j • δ_j`. The matrix acceptance `mh_acceptance_prob π Q` is the measure-theoretic
Metropolis–Hastings acceptance almost everywhere for `vecToMeasure π ⊗ₘ matrixToKernel Q`
(`ae_eq_mhAcceptance`): the two can differ only where the proposed flow `π x * Q x y` vanishes,
where the matrix convention takes the value `1`. Detailed balance of the Metropolis–Hastings
matrix is then a corollary of the reversibility of the general kernel, for every nonnegative
proposal (`isReversible_metropolisHastingsKernel`): the diagonal does not matter
(`isReversible_metropolisHastingsKernel_iff`), and the kernel of the off-diagonal part is the
accepted part `(matrixToKernel Q).withDensity a` of the accept–reject kernel
(`matrixToKernel_mul`). For a stochastic `Q`, `matrixToKernel` sends the whole matrix to the
accept–reject kernel (`matrixToKernel_metropolisHastingsKernel`). The arithmetic proof of the
detailed balance is `metropolisHastings_is_reversible`.
-/

namespace MCMC.Finite

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n]
  {π : stdSimplex ℝ n} {Q : Matrix n n ℝ}

/-- `matrixToKernel` sends the Metropolis–Hastings matrix to the accept–reject kernel of the
proposal with the acceptance `mh_acceptance_prob`. -/
theorem matrixToKernel_metropolisHastingsKernel (hQ : IsStochastic Q)
    (hP : IsStochastic (metropolisHastingsKernel π Q)) :
    matrixToKernel (metropolisHastingsKernel π Q) hP.1 =
      Kernel.acceptReject (matrixToKernel Q hQ.1)
        fun x y ↦ ENNReal.ofReal (mh_acceptance_prob π Q x y) := by
  have hA := fun x y ↦ mh_acceptance_prob_bounds (π := π) hQ.1 x y
  have hsum : ∀ x, ∑ z, Q x z * mh_acceptance_prob π Q x z ≤ 1 := fun x ↦
    (Finset.sum_le_sum fun z _ ↦ mul_le_of_le_one_right (hQ.1 x z) (hA x z).2).trans_eq (hQ.2 x)
  have hint : ∀ x, ∫⁻ z, ENNReal.ofReal (mh_acceptance_prob π Q x z) ∂(matrixToKernel Q hQ.1 x) =
      ENNReal.ofReal (∑ z, Q x z * mh_acceptance_prob π Q x z) := fun x ↦ by
    rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun z _ ↦ mul_nonneg (hQ.1 x z) (hA x z).1]
    simp_rw [matrixToKernel_singleton, ← ENNReal.ofReal_mul (hA x _).1, mul_comm]
  refine Kernel.ext fun x ↦ Measure.ext_iff_singleton.2 fun y ↦ ?_
  rw [matrixToKernel_singleton, Kernel.acceptReject_apply (measurable_of_countable _),
    Measure.add_apply, withDensity_apply _ (measurableSet_singleton y), lintegral_singleton,
    matrixToKernel_singleton, Measure.smul_apply, hint, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (Finset.sum_nonneg fun z _ ↦ mul_nonneg (hQ.1 x z) (hA x z).1),
    ← ENNReal.ofReal_mul (hA x y).1, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton y)]
  simp only [metropolisHastingsKernel]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    rw [indicator_of_mem (mem_singleton x), Pi.one_apply, mul_one,
      ENNReal.ofReal_add (mul_nonneg (hQ.1 x x) (hA x x).1) (sub_nonneg.2 (hsum x)), mul_comm]
  · simp only [hxy, ↓reduceIte, add_zero]
    rw [indicator_of_notMem (mem_singleton_iff.not.2 hxy), mul_zero, add_zero, mul_comm]

/-- The acceptance of the finite Metropolis–Hastings matrix is the Metropolis–Hastings acceptance,
almost everywhere for the proposed flow. -/
theorem ae_eq_mhAcceptance (hQ : ∀ i j, 0 ≤ Q i j) :
    (Function.uncurry fun x y ↦ ENNReal.ofReal (mh_acceptance_prob π Q x y))
      =ᵐ[vecToMeasure π ⊗ₘ matrixToKernel Q hQ]
        Function.uncurry ((vecToMeasure π).mhAcceptance (matrixToKernel Q hQ)) := by
  refine ae_iff_of_countable.2 fun ⟨x, y⟩ hxy ↦ ?_
  rw [Measure.compProd_apply_singleton, vecToMeasure_singleton, matrixToKernel_singleton] at hxy
  have hpos : 0 < π.val x * Q x y := lt_of_le_of_ne (mul_nonneg (π.property.1 x) (hQ x y))
    (fun h ↦ hxy (by rw [← ENNReal.ofReal_mul (π.property.1 x), ← h, ENNReal.ofReal_zero]))
  have h0 : vecToMeasure π {x} * matrixToKernel Q hQ x {y} ≠ 0 := by
    rwa [vecToMeasure_singleton, matrixToKernel_singleton]
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair,
    Kernel.mhAcceptance_eq_min_one_div h0, vecToMeasure_singleton, vecToMeasure_singleton,
    matrixToKernel_singleton, matrixToKernel_singleton]
  simp only [mh_acceptance_prob, hpos.ne', ↓reduceIte]
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_mul (π.property.1 y), ENNReal.ofReal_mul (π.property.1 x)]

omit [MeasurableSpace n] [MeasurableSingletonClass n] in
/-- The Metropolis–Hastings matrix and its proposed-and-accepted part `Q x y * A x y` agree off
the diagonal, so one satisfies detailed balance iff the other does. -/
theorem isReversible_metropolisHastingsKernel_iff :
    IsReversible (metropolisHastingsKernel π Q) π ↔
      IsReversible (fun x y ↦ Q x y * mh_acceptance_prob π Q x y) π := by
  refine forall_congr' fun x ↦ forall_congr' fun y ↦ ?_
  rcases eq_or_ne x y with rfl | hxy
  · exact iff_of_true rfl rfl
  · simp only [metropolisHastingsKernel, hxy, hxy.symm, ↓reduceIte, add_zero]

omit [DecidableEq n] in
/-- The kernel of the entrywise product of two nonnegative matrices is the kernel of the first
with the second as density. -/
theorem matrixToKernel_mul (hQ : ∀ i j, 0 ≤ Q i j) {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    matrixToKernel (fun x y ↦ Q x y * A x y) (fun i j ↦ mul_nonneg (hQ i j) (hA i j)) =
      (matrixToKernel Q hQ).withDensity fun x y ↦ ENNReal.ofReal (A x y) := by
  refine Kernel.ext fun x ↦ Measure.ext_iff_singleton.2 fun y ↦
    (matrixToKernel_singleton _ x y).trans ((ENNReal.ofReal_mul (hQ x y)).trans ?_)
  rw [Kernel.withDensity_apply _ (measurable_of_countable _),
    withDensity_apply _ (measurableSet_singleton y), lintegral_singleton, matrixToKernel_singleton,
    mul_comm]

/-- **Detailed balance of the finite Metropolis–Hastings matrix**, for every nonnegative
proposal, as a corollary of the reversibility of the general Metropolis–Hastings kernel. -/
theorem isReversible_metropolisHastingsKernel (hQ : ∀ i j, 0 ≤ Q i j) :
    IsReversible (metropolisHastingsKernel π Q) π := by
  have hA : ∀ x y, 0 ≤ mh_acceptance_prob π Q x y := fun x y ↦
    (mh_acceptance_prob_bounds hQ x y).1
  rw [isReversible_metropolisHastingsKernel_iff,
    isReversible_iff_kernel_reversible _ π fun x y ↦ mul_nonneg (hQ x y) (hA x y),
    matrixToKernel_mul hQ hA]
  exact Kernel.isReversible_acceptReject_iff.1
    (Kernel.isReversible_acceptReject_of_ae_eq_mhAcceptance (measurable_of_countable _)
      (ae_eq_mhAcceptance hQ))

end MCMC.Finite
