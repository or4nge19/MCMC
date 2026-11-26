/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.Finite.toKernel
import MCMC.ToMathlib.Probability.Kernel.AcceptReject

/-!
# The finite Metropolis–Hastings matrix is the general Metropolis–Hastings kernel

On a finite state space, `matrixToKernel` sends the Metropolis–Hastings matrix
`metropolisHastingsKernel π Q` to the accept–reject kernel of `matrixToKernel Q` with the acceptance
`mh_acceptance_prob π Q` (`matrixToKernel_metropolisHastingsKernel`), and this acceptance is the
measure-theoretic Metropolis–Hastings acceptance almost everywhere for
`vecToMeasure π ⊗ₘ matrixToKernel Q` (`ae_eq_mhAcceptance`): the two can differ only where the
proposed flow `π x * Q x y` vanishes, where the matrix convention takes the value `1`. Detailed
balance of the matrix is then a corollary of the reversibility of the general kernel
(`isReversible_metropolisHastingsKernel_of_isStochastic`); the arithmetic proof of the same
statement, `metropolisHastings_is_reversible`, assumes only a nonnegative `Q`, while
`matrixToKernel` needs a stochastic one.
-/

namespace MCMC.Finite

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n]
  {π : stdSimplex ℝ n} {Q : Matrix n n ℝ}

instance isProbabilityMeasure_vecToMeasure (π : stdSimplex ℝ n) :
    IsProbabilityMeasure (vecToMeasure π) :=
  ⟨by rw [← ENNReal.ofReal_one, ← π.property.2,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ π.property.1 i]; simp [vecToMeasure]⟩

theorem vecToMeasure_singleton (π : stdSimplex ℝ n) (i : n) :
    vecToMeasure π {i} = ENNReal.ofReal (π.val i) := by
  simp [vecToMeasure, Measure.dirac_apply', Pi.single_apply]

theorem matrixToKernel_singleton (hQ : IsStochastic Q) (i j : n) :
    matrixToKernel Q hQ i {j} = ENNReal.ofReal (Q i j) := by
  change ((∑ k : n, ENNReal.ofReal (Q i k) • Measure.dirac k) : Measure n) {j} = _
  simp [Measure.dirac_apply', Pi.single_apply]

/-- `matrixToKernel` sends the Metropolis–Hastings matrix to the accept–reject kernel of the
proposal with the acceptance `mh_acceptance_prob`. -/
theorem matrixToKernel_metropolisHastingsKernel (hQ : IsStochastic Q)
    (hP : IsStochastic (metropolisHastingsKernel π Q)) :
    matrixToKernel (metropolisHastingsKernel π Q) hP =
      Kernel.acceptReject (matrixToKernel Q hQ)
        fun x y ↦ ENNReal.ofReal (mh_acceptance_prob π Q x y) := by
  have hA := fun x y ↦ mh_acceptance_prob_bounds (π := π) hQ.1 x y
  have hsum : ∀ x, ∑ z, Q x z * mh_acceptance_prob π Q x z ≤ 1 := fun x ↦
    (Finset.sum_le_sum fun z _ ↦ mul_le_of_le_one_right (hQ.1 x z) (hA x z).2).trans_eq (hQ.2 x)
  have hint : ∀ x, ∫⁻ z, ENNReal.ofReal (mh_acceptance_prob π Q x z) ∂(matrixToKernel Q hQ x) =
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
theorem ae_eq_mhAcceptance (hQ : IsStochastic Q) :
    (Function.uncurry fun x y ↦ ENNReal.ofReal (mh_acceptance_prob π Q x y))
      =ᵐ[vecToMeasure π ⊗ₘ matrixToKernel Q hQ]
        Function.uncurry ((vecToMeasure π).mhAcceptance (matrixToKernel Q hQ)) := by
  refine ae_iff_of_countable.2 fun ⟨x, y⟩ hxy ↦ ?_
  rw [Measure.compProd_apply_singleton, vecToMeasure_singleton, matrixToKernel_singleton] at hxy
  have hpos : 0 < π.val x * Q x y := lt_of_le_of_ne (mul_nonneg (π.property.1 x) (hQ.1 x y))
    (fun h ↦ hxy (by rw [← ENNReal.ofReal_mul (π.property.1 x), ← h, ENNReal.ofReal_zero]))
  have h0 : vecToMeasure π {x} * matrixToKernel Q hQ x {y} ≠ 0 := by
    rwa [vecToMeasure_singleton, matrixToKernel_singleton]
  have htop : vecToMeasure π {x} * matrixToKernel Q hQ x {y} ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair,
    Kernel.mhAcceptance_eq_min_one_div h0 htop, vecToMeasure_singleton, vecToMeasure_singleton,
    matrixToKernel_singleton, matrixToKernel_singleton]
  simp only [mh_acceptance_prob, hpos.ne', ↓reduceIte]
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_mul (π.property.1 y), ENNReal.ofReal_mul (π.property.1 x)]

/-- **Detailed balance of the finite Metropolis–Hastings matrix**, as a corollary of the
reversibility of the general Metropolis–Hastings kernel. -/
theorem isReversible_metropolisHastingsKernel_of_isStochastic (hQ : IsStochastic Q) :
    IsReversible (metropolisHastingsKernel π Q) π := by
  have hP := metropolisHastings_is_stochastic (π := π) hQ
  rw [isReversible_iff_kernel_reversible _ π hP, matrixToKernel_metropolisHastingsKernel hQ hP]
  exact Kernel.isReversible_acceptReject_of_ae_eq_mhAcceptance (measurable_of_countable _)
    (ae_eq_mhAcceptance hQ)

end MCMC.Finite
