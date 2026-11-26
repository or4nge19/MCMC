/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import MCMC.ToMathlib.Probability.Kernel.Reversible

/-!
# The Gaussian autoregressive kernel is reversible

For a centered Gaussian measure `μ` on a separable Banach space and an angle `θ`, the kernel
`x ↦ law of cos θ • x + sin θ • W`, `W ∼ μ`, is `μ`-reversible. This is the proposal of the
preconditioned Crank–Nicolson algorithm. The proof is Mathlib's rotation invariance of `μ.prod μ`
(`ProbabilityTheory.IsGaussian.map_rotation_eq_self`): the swap of `(X, cos θ • X + sin θ • W)` is
its image under the reflection `(x, w) ↦ (cos θ • x + sin θ • w, sin θ • x - cos θ • w)`, a rotation
followed by `w ↦ -w`.

## Main statements

* `isReversible_map_cos_smul_add_sin_smul`.
* `isReversible_gaussianReal_ar`: the Gaussian AR(1) kernel `x ↦ N(a x, v)` is reversible for its
  stationary law `N(0, v / (1 - a ^ 2))`, `|a| < 1`.
* `not_isReversible_map_cos_smul_add_sin_smul_gaussianReal_one`: the centering is needed;
  `not_isReversible_gaussianReal_ar_one`: so is `|a| < 1`.

Staged for `Mathlib/Probability/Distributions/Gaussian/Reversible.lean` (new file). Searched on
2026-11-26 in the pinned Mathlib: `grep -rn "IsReversible" Mathlib` finds only
`Probability/Kernel/Invariance.lean`; `grep -rln "map_rotation_eq_self" Mathlib` finds only
`Probability/Distributions/Gaussian/Fernique.lean` (its proof and the moment bounds).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The preconditioned Crank–Nicolson proposal is reversible.** For a centered Gaussian measure
`μ` on a separable Banach space, the kernel `x ↦ law of cos θ • x + sin θ • W`, `W ∼ μ`, is
`μ`-reversible. -/
theorem isReversible_map_cos_smul_add_sin_smul [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure E} [IsGaussian μ] (hμ : μ[id] = 0) (θ : ℝ) :
    ((Kernel.id ×ₖ Kernel.const E μ).map
      fun p : E × E ↦ Real.cos θ • p.1 + Real.sin θ • p.2).IsReversible μ := by
  have hL : Measurable fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2) := by fun_prop
  have hneg : μ.map Neg.neg = μ := calc
    μ.map Neg.neg = ((μ.prod μ).map Prod.fst).map Neg.neg := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = ((μ.prod μ).map (ContinuousLinearMap.rotation Real.pi)).map Prod.fst := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext p
        simp [ContinuousLinearMap.rotation_apply]
    _ = μ := by
        rw [IsGaussian.map_rotation_eq_self hμ, Measure.map_fst_prod, measure_univ, one_smul]
  have hMμ : (μ.prod μ).map (Prod.map id Neg.neg ∘ ContinuousLinearMap.rotation θ) = μ.prod μ := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), IsGaussian.map_rotation_eq_self hμ,
      ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id, hneg]
  have hLM : (Prod.swap ∘ fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2)) =
      (fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2)) ∘
        (Prod.map id Neg.neg ∘ ContinuousLinearMap.rotation θ) := by
    funext p
    refine Prod.ext ?_ ?_
    · simp [ContinuousLinearMap.rotation_apply]
    · simp only [Function.comp_apply, Prod.swap_prod_mk, Prod.map_apply, id_eq,
        ContinuousLinearMap.rotation_apply]
      linear_combination (norm := module) -(Real.cos_sq_add_sin_sq θ) • p.1
  refine Kernel.IsReversible.of_map_swap_compProd ?_
  rw [Measure.compProd_map_id_prod_const (by fun_prop), Measure.map_map measurable_swap hL]
  calc (μ.prod μ).map (Prod.swap ∘ fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2))
      = ((μ.prod μ).map (Prod.map id Neg.neg ∘ ContinuousLinearMap.rotation θ)).map
          fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2) := by
        rw [hLM, Measure.map_map hL (by fun_prop)]
    _ = (μ.prod μ).map fun p : E × E ↦ (p.1, Real.cos θ • p.1 + Real.sin θ • p.2) := by
        rw [hMμ]

/-- The centering is needed in `isReversible_map_cos_smul_add_sin_smul`: for `μ = N(1, 1)` and
`θ = π` the kernel is `x ↦ δ_{-x}`, which sends `μ` to `N(-1, 1)`. -/
theorem not_isReversible_map_cos_smul_add_sin_smul_gaussianReal_one :
    ¬ ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 1 1)).map
      fun p : ℝ × ℝ ↦ Real.cos Real.pi • p.1 + Real.sin Real.pi • p.2).IsReversible
        (gaussianReal 1 1) := by
  intro h
  have := Kernel.IsMarkovKernel.map (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 1 1))
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦ Real.cos Real.pi • p.1 + Real.sin Real.pi • p.2)
  have hinv := h.invariant.def
  rw [← Measure.snd_compProd, Measure.compProd_map_id_prod_const (by fun_prop),
    Measure.snd_map_prodMk measurable_fst (by fun_prop),
    show (fun p : ℝ × ℝ ↦ Real.cos Real.pi • p.1 + Real.sin Real.pi • p.2) =
      (fun x ↦ -x) ∘ Prod.fst by funext p; simp,
    ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul,
    gaussianReal_map_neg] at hinv
  have := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ) hinv
  simp only [integral_id_gaussianReal] at this
  norm_num at this

/-- **The Gaussian AR(1) kernel is reversible.** For `|a| < 1`, the kernel `x ↦ N(a x, v)` is
reversible for its stationary law `N(0, v / (1 - a ^ 2))`. It is the kernel of
`isReversible_map_cos_smul_add_sin_smul` on `ℝ` with `cos θ = a`. -/
theorem isReversible_gaussianReal_ar {a : ℝ} (ha : |a| < 1) (v : ℝ≥0) :
    ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2).IsReversible (gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2))) := by
  have h1 : -1 ≤ a := by linarith [neg_abs_le a]
  have h2 : a ≤ 1 := by linarith [le_abs_self a]
  have ha2 : a ^ 2 < 1 := by nlinarith [abs_lt.1 ha]
  have hsin : Real.sin (Real.arccos a) ^ 2 = 1 - a ^ 2 := by
    rw [Real.sin_arccos, Real.sq_sqrt (by linarith)]
  have hnorm : ‖a‖₊ ^ 2 ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    simpa [sq_abs] using ha2.le
  have hne : (1 : ℝ) - a ^ 2 ≠ 0 := by linarith
  have hK : (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      (fun p : ℝ × ℝ ↦ a * p.1 + p.2) = (Kernel.id ×ₖ Kernel.const ℝ
        (gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2)))).map fun p : ℝ × ℝ ↦
          Real.cos (Real.arccos a) • p.1 + Real.sin (Real.arccos a) • p.2 := by
    ext x : 1
    rw [Kernel.map_apply _ (by fun_prop), Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
      Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left,
      Measure.map_map (by fun_prop) measurable_prodMk_left,
      show (fun p : ℝ × ℝ ↦ a * p.1 + p.2) ∘ Prod.mk x = (a * x + ·) from rfl,
      show (fun p : ℝ × ℝ ↦ Real.cos (Real.arccos a) • p.1 + Real.sin (Real.arccos a) • p.2) ∘
        Prod.mk x = (Real.cos (Real.arccos a) * x + ·) ∘ (Real.sin (Real.arccos a) * ·) by
          funext w; simp [smul_eq_mul],
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add, gaussianReal_map_const_add, Real.cos_arccos h1 h2]
    congr 1
    · simp
    · apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_sub hnorm, NNReal.coe_mk, hsin]
      simp only [NNReal.coe_one, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
      field_simp
  rw [hK]
  exact isReversible_map_cos_smul_add_sin_smul (by simp [integral_id_gaussianReal]) _

/-- The bound `|a| < 1` is needed in `isReversible_gaussianReal_ar`: for `a = 1` the claimed law
is `N(0, 0) = δ_0` and the random walk `x ↦ N(x, 1)` leaves `δ_0`. -/
theorem not_isReversible_gaussianReal_ar_one :
    ¬ ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 1)).map
      fun p : ℝ × ℝ ↦ (1 : ℝ) * p.1 + p.2).IsReversible
        (gaussianReal 0 (1 / (1 - ‖(1 : ℝ)‖₊ ^ 2))) := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  have hF : Measurable fun p : ℝ × ℝ ↦ (1 : ℝ) * p.1 + p.2 := by fun_prop
  have hK : ∀ x, ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 1)).map
      fun p : ℝ × ℝ ↦ (1 : ℝ) * p.1 + p.2) x = (gaussianReal 0 1).map (fun w ↦ x + w) := by
    intro x
    rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
    congr 1
    funext w
    simp
  intro h
  have h1 := h (measurableSet_singleton 0) MeasurableSet.univ
  rw [show (1 : ℝ≥0) / (1 - ‖(1 : ℝ)‖₊ ^ 2) = 0 by simp, gaussianReal_zero_var, lintegral_singleton,
    Measure.restrict_univ, lintegral_dirac, hK,
    Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at h1
  simp at h1

end ProbabilityTheory
