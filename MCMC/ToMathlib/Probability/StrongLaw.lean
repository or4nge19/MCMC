/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Analysis.SpecificLimits.FloorPow
public import MCMC.ToMathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.PSeries

/-!
# A strong law of large numbers from second moments

Rajchman's argument without independence, for functions `Y k` into a real normed space: if the
partial sums `S n = ∑_{k < n} Y k` of square integrable functions have `∫ ‖S n‖² ≤ B n`, and every
`Y k` has `∫ ‖Y k‖² ≤ B`, then `S n / n → 0` almost everywhere
(`ae_tendsto_inv_smul_sum_of_integral_sq_norm_le`; for real functions,
`ae_tendsto_inv_mul_sum_of_integral_sq_le`). Along the squares,
`∑_q ∫ ‖S (q²) / q²‖² ≤ ∑_q B / q² < ∞`; on the block `[q², (q + 1)²)`,
`(∑ ‖Y k‖)² ≤ (2 q + 1) ∑ ‖Y k‖²` gives `∫ (∑ ‖Y k‖ / q²)² ≤ 9 B / q²`; a sequence of functions
with summable second moments tends to zero almost everywhere
(`ae_tendsto_zero_of_summable_integral_norm_sq`, the case `p = 2` of
`ae_tendsto_zero_of_tsum_lintegral_enorm_rpow_ne_top` for every `p > 0`), and the squares and
blocks control `S n / n` (`tendsto_inv_smul_sum_of_tendsto_inv_sq_smul`, in
`MCMC/ToMathlib/Analysis/SpecificLimits/FloorPow.lean`). No independence, no identical
distribution and no measure-preserving map is used: the bound on the second moments of the
partial sums is the only interaction between the `Y k`.

## Search

At Mathlib `d13f23b`: `grep -rn "Rajchman\|rajchman" Mathlib` finds nothing;
`Probability/StrongLaw.lean` proves Etemadi's law for pairwise independent identically
distributed functions through truncations, and none of its lemmas assumes a bound on the second
moments of the partial sums. `grep -rn "tsum_eLpNorm\|tendsto_atTop_zero_of_tsum_ne_top" Mathlib`
finds `MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top` (`MeasureTheory/Function/LpSpace/
InfiniteSum.lean`: for `1 ≤ p`, summable `Lᵖ` norms give pointwise summable norms almost
everywhere), whose hypothesis is the summability of `(∫ ‖f n‖ᵖ)^(1/p)`, while
`ae_tendsto_zero_of_tsum_lintegral_enorm_rpow_ne_top` asks for that of `∫ ‖f n‖ᵖ`, for every
`p > 0`, and concludes `f n → 0`; and `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`, used here; no
statement with second moments of partial sums.
-/

@[expose] public section

open Filter MeasureTheory Finset
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {E : Type*} [NormedAddCommGroup E]

/-- **Summable `p`-th moments give convergence to zero almost everywhere**: for `p > 0`, if every
`f n` is almost everywhere strongly measurable and `∑ₙ ∫⁻ ‖f n‖ₑ ^ p` is finite, then `f n → 0`
almost everywhere. -/
theorem ae_tendsto_zero_of_tsum_lintegral_enorm_rpow_ne_top {f : ℕ → Ω → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp : 0 < p)
    (hs : ∑' n, ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEMeasurable (fun ω ↦ ‖f n ω‖ₑ ^ p) μ := (hf n).enorm.pow_const p
  rw [← lintegral_tsum hm] at hs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hs] with ω hω
  have h1 := ((ENNReal.continuous_rpow_const (y := p⁻¹)).tendsto 0).comp
    (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne)
  rw [ENNReal.zero_rpow_of_pos (inv_pos.2 hp)] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  simpa [Function.comp_def, ← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne'] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1

/-- **Summable second moments give convergence to zero almost everywhere**: if every `f n` is
square integrable and `∑ₙ ∫ ‖f n‖²` converges, then `f n → 0` almost everywhere. -/
theorem ae_tendsto_zero_of_summable_integral_norm_sq {f : ℕ → Ω → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hs : Summable fun n ↦ ∫ ω, ‖f n ω‖ ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (fun ω ↦ ‖f n ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hf n).aestronglyMeasurable).1 (hf n)
  have he (n : ℕ) : ∫⁻ ω, ‖f n ω‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ ω, ‖f n ω‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ fun _ ↦ sq_nonneg _)]
    refine lintegral_congr fun ω ↦ ?_
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  refine ae_tendsto_zero_of_tsum_lintegral_enorm_rpow_ne_top
    (fun n ↦ (hf n).aestronglyMeasurable) two_pos ?_
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun _ ↦ sq_nonneg _) hs]
  exact ENNReal.ofReal_ne_top

/-- **A strong law of large numbers from second moments** (Rajchman's argument), in a real
normed space: if every `Y k` is square integrable, `∫ ‖∑_{k < n} Y k‖² ≤ B n` for every `n` and
`∫ ‖Y k‖² ≤ B` for every `k`, then `n⁻¹ • ∑_{k < n} Y k → 0` almost everywhere. -/
theorem ae_tendsto_inv_smul_sum_of_integral_sq_norm_le [NormedSpace ℝ E] {Y : ℕ → Ω → E}
    (hY : ∀ k, MemLp (Y k) 2 μ) {B : ℝ}
    (hS : ∀ n, ∫ ω, ‖∑ k ∈ range n, Y k ω‖ ^ 2 ∂μ ≤ B * n)
    (hY2 : ∀ k, ∫ ω, ‖Y k ω‖ ^ 2 ∂μ ≤ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, Y k ω) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (integral_nonneg fun _ ↦ sq_nonneg _).trans (hY2 0)
  have hsq : Summable fun q : ℕ ↦ B * ((q : ℝ) ^ 2)⁻¹ :=
    (Real.summable_nat_pow_inv.2 one_lt_two).mul_left B
  have hc (q : ℕ) : #(Ico (q ^ 2) ((q + 1) ^ 2)) = 2 * q + 1 := by
    rw [Nat.card_Ico]
    exact Nat.sub_eq_of_eq_add (by ring)
  have h1 (q : ℕ) : ∫ ω, ‖((q : ℝ) ^ 2)⁻¹ • ∑ k ∈ range (q ^ 2), Y k ω‖ ^ 2 ∂μ ≤
      B * ((q : ℝ) ^ 2)⁻¹ := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    simp_rw [norm_smul, mul_pow, norm_inv, norm_pow, Real.norm_natCast]
    rw [integral_const_mul]
    calc _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * (B * ((q ^ 2 : ℕ) : ℝ)) := by gcongr; exact hS _
      _ = B * ((q : ℝ) ^ 2)⁻¹ := by field_simp; push_cast; ring
  have h2 (q : ℕ) : ∫ ω, ‖((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ Ico (q ^ 2) ((q + 1) ^ 2), ‖Y k ω‖‖ ^ 2 ∂μ ≤
      9 * (B * ((q : ℝ) ^ 2)⁻¹) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    simp_rw [Real.norm_eq_abs, sq_abs, mul_pow]
    rw [integral_const_mul]
    calc _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * (#(Ico (q ^ 2) ((q + 1) ^ 2)) *
          (#(Ico (q ^ 2) ((q + 1) ^ 2)) * B)) := by
          gcongr
          refine (integral_sq_sum_norm_le_card_mul_sum_integral_sq_norm _ fun k _ ↦ hY k).trans ?_
          gcongr
          exact (sum_le_sum fun k _ ↦ hY2 k).trans_eq (by simp)
      _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * ((3 * q) * ((3 * q) * B)) := by
          rw [hc]
          gcongr <;> push_cast <;> linarith [(by exact_mod_cast hq : (1 : ℝ) ≤ q)]
      _ = 9 * (B * ((q : ℝ) ^ 2)⁻¹) := by field_simp; ring
  have ha := ae_tendsto_zero_of_summable_integral_norm_sq
    (f := fun q ω ↦ ((q : ℝ) ^ 2)⁻¹ • ∑ k ∈ range (q ^ 2), Y k ω)
    (fun q ↦ (memLp_finsetSum _ fun k _ ↦ hY k).const_smul _)
    (hsq.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) h1)
  have hd := ae_tendsto_zero_of_summable_integral_norm_sq
    (f := fun q ω ↦ ((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ Ico (q ^ 2) ((q + 1) ^ 2), ‖Y k ω‖)
    (fun q ↦ (memLp_finsetSum _ fun k _ ↦ (hY k).norm).const_mul _)
    ((hsq.mul_left 9).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) h2)
  filter_upwards [ha, hd] with ω h1 h2
  exact tendsto_inv_smul_sum_of_tendsto_inv_sq_smul h1 h2

/-- **A strong law of large numbers from second moments**, for real functions: if every `Y k`
is square integrable, `∫ (∑_{k < n} Y k)² ≤ B n` for every `n` and `∫ (Y k)² ≤ B` for every `k`,
then `n⁻¹ ∑_{k < n} Y k → 0` almost everywhere. -/
theorem ae_tendsto_inv_mul_sum_of_integral_sq_le {Y : ℕ → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 μ)
    {B : ℝ} (hS : ∀ n, ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂μ ≤ B * n)
    (hY2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂μ ≤ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω) atTop (𝓝 0) :=
  ae_tendsto_inv_smul_sum_of_integral_sq_norm_le hY
    (by simpa only [Real.norm_eq_abs, sq_abs] using hS)
    (by simpa only [Real.norm_eq_abs, sq_abs] using hY2)

end ProbabilityTheory
