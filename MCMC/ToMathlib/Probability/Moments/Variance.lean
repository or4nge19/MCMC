/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Probability.Moments.Variance

/-!
# Jensen's inequality for the square, under a dominating function

Staged for `Mathlib/Probability/Moments/Variance.lean`: for a probability measure, if `f² ≤ g`
almost everywhere with `g` integrable, then `(∫ f)² ≤ ∫ g`. No measurability of `f` is asked: the
integral of a function that is not almost everywhere strongly measurable is `0`.

## Search

At Mathlib `d13f23b`:
`grep -rn "sq_integral_le\|integral_sq_ge\|pow_integral_le\|map_integral_le" Mathlib` finds
`ConvexOn.map_integral_le` (`Analysis/Convex/Integral.lean`: Jensen's inequality for a convex
function continuous on a closed convex set, with `f` and `g ∘ f` integrable), and no statement
for the square with a dominating function; `ProbabilityTheory.variance_nonneg` and
`ProbabilityTheory.variance_eq_sub` give `(∫ f)² ≤ ∫ f²` for `f` in `L²`, used here.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **Jensen's inequality for the square, under a dominating function**: for a probability
measure `μ`, if `f² ≤ g` almost everywhere and `g` is integrable, then `(∫ f ∂μ)² ≤ ∫ g ∂μ`. -/
theorem sq_integral_le_integral_of_sq_le [IsProbabilityMeasure μ] {f g : α → ℝ}
    (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, f x ^ 2 ≤ g x) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, g x ∂μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · have hf2 : Integrable (fun x ↦ f x ^ 2) μ := hg.mono' (hf.pow 2) (h.mono fun x hx ↦
      (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (sq_nonneg _)).trans_le hx))
    have hvar := variance_nonneg f μ
    rw [variance_eq_sub ((memLp_two_iff_integrable_sq hf).2 hf2)] at hvar
    exact (sub_nonneg.1 hvar).trans (integral_mono_ae hf2 hg h)
  · rw [integral_non_aestronglyMeasurable hf, zero_pow two_ne_zero]
    exact integral_nonneg_of_ae (h.mono fun x hx ↦ (sq_nonneg _).trans hx)

end ProbabilityTheory
