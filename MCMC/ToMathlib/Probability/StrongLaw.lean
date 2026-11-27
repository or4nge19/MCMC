/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Analysis.SpecificLimits.FloorPow
public import MCMC.ToMathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# A strong law of large numbers from second moments

Rajchman's argument without independence: if the partial sums `S n = ∑_{k < n} Y k` of real
functions with finite second moments have `∫ (S n)² ≤ B n`, and every `Y k` has `∫ (Y k)² ≤ B`,
then `S n / n → 0` almost everywhere (`ae_tendsto_inv_mul_sum_of_integral_sq_le`). Along the
squares, `∑_q ∫ (S (q²) / q²)² ≤ ∑_q B / q² < ∞`; on the block `[q², (q + 1)²)`,
`(∑ |Y k|)² ≤ (2 q + 1) ∑ (Y k)²` gives `∫ (∑ |Y k| / q²)² ≤ 9 B / q²`; a sequence of functions
with summable second moments tends to zero almost everywhere
(`ae_tendsto_zero_of_summable_integral_sq`), and the squares and blocks control `S n / n`
(`tendsto_inv_mul_sum_of_tendsto_inv_sq_mul`, in
`MCMC/ToMathlib/Analysis/SpecificLimits/FloorPow.lean`). No independence, no identical
distribution and no measure-preserving map is used: the bound on the second moments of the
partial sums is the only interaction between the `Y k`.

## Search

At Mathlib `d13f23b`: `grep -rn "Rajchman\|rajchman" Mathlib` finds nothing;
`Probability/StrongLaw.lean` proves Etemadi's law for pairwise independent identically
distributed functions through truncations, and none of its lemmas assumes a bound on the second
moments of the partial sums. `grep -rn "tsum_eLpNorm\|tendsto_atTop_zero_of_tsum_ne_top" Mathlib`
finds `MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top` (`MeasureTheory/Function/LpSpace/
InfiniteSum.lean`: summable `Lᵖ` norms give pointwise summable norms almost everywhere), which
proves `ae_tendsto_zero_of_summable_integral_sq` at `p = 1` for the squares, and the uses of the
series lemma in `MeasureTheory/Function/LpSpace/Complete.lean`; no statement with second
moments of partial sums.
-/

@[expose] public section

open Filter MeasureTheory Finset
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Summable second moments give convergence to zero almost everywhere**: if every `f n` is
square integrable and `∑ₙ ∫ (f n)²` converges, then `f n → 0` almost everywhere. -/
theorem ae_tendsto_zero_of_summable_integral_sq {f : ℕ → Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (hs : Summable fun n ↦ ∫ ω, f n ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 0) := by
  have he (n : ℕ) : eLpNorm (fun ω ↦ f n ω ^ 2) 1 μ = ENNReal.ofReal (∫ ω, f n ω ^ 2 ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hf n).integrable_sq]
    · simp
    · exact (hf n).integrable_sq.1
  have h1 : ∑' n, eLpNorm (fun ω ↦ f n ω ^ 2) 1 μ ≠ ∞ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun _ ↦ sq_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl h1] with ω hω
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  simpa [Real.sqrt_sq_eq_abs] using hω.tendsto_atTop_zero.sqrt

/-- **A strong law of large numbers from second moments** (Rajchman's argument): if every `Y k`
is square integrable, `∫ (∑_{k < n} Y k)² ≤ B n` for every `n` and `∫ (Y k)² ≤ B` for every `k`,
then `n⁻¹ ∑_{k < n} Y k → 0` almost everywhere. -/
theorem ae_tendsto_inv_mul_sum_of_integral_sq_le {Y : ℕ → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 μ)
    {B : ℝ} (hS : ∀ n, ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂μ ≤ B * n)
    (hY2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂μ ≤ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, Y k ω) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (integral_nonneg fun _ ↦ sq_nonneg _).trans (hY2 0)
  have hsq : Summable fun q : ℕ ↦ B * ((q : ℝ) ^ 2)⁻¹ :=
    (Real.summable_nat_pow_inv.2 one_lt_two).mul_left B
  have hc (q : ℕ) : #(Ico (q ^ 2) ((q + 1) ^ 2)) = 2 * q + 1 := by
    rw [Nat.card_Ico]
    exact Nat.sub_eq_of_eq_add (by ring)
  have h1 (q : ℕ) : ∫ ω, (((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ range (q ^ 2), Y k ω) ^ 2 ∂μ ≤
      B * ((q : ℝ) ^ 2)⁻¹ := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * (B * ((q ^ 2 : ℕ) : ℝ)) := by gcongr; exact hS _
      _ = B * ((q : ℝ) ^ 2)⁻¹ := by field_simp; push_cast; ring
  have h2 (q : ℕ) : ∫ ω, (((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ Ico (q ^ 2) ((q + 1) ^ 2), |Y k ω|) ^ 2 ∂μ ≤
      9 * (B * ((q : ℝ) ^ 2)⁻¹) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * (#(Ico (q ^ 2) ((q + 1) ^ 2)) *
          (#(Ico (q ^ 2) ((q + 1) ^ 2)) * B)) := by
          gcongr
          refine (integral_sq_sum_abs_le_card_mul_sum_integral_sq _ fun k _ ↦ hY k).trans ?_
          gcongr
          exact (sum_le_sum fun k _ ↦ hY2 k).trans_eq (by simp)
      _ ≤ ((q : ℝ) ^ 2)⁻¹ ^ 2 * ((3 * q) * ((3 * q) * B)) := by
          rw [hc]
          gcongr <;> push_cast <;> linarith [(by exact_mod_cast hq : (1 : ℝ) ≤ q)]
      _ = 9 * (B * ((q : ℝ) ^ 2)⁻¹) := by field_simp; ring
  have ha := ae_tendsto_zero_of_summable_integral_sq
    (f := fun q ω ↦ ((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ range (q ^ 2), Y k ω)
    (fun q ↦ (memLp_finsetSum _ fun k _ ↦ hY k).const_mul _)
    (hsq.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) h1)
  have hd := ae_tendsto_zero_of_summable_integral_sq
    (f := fun q ω ↦ ((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ Ico (q ^ 2) ((q + 1) ^ 2), |Y k ω|)
    (fun q ↦ (memLp_finsetSum _ fun k _ ↦ (hY k).abs).const_mul _)
    ((hsq.mul_left 9).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) h2)
  filter_upwards [ha, hd] with ω h1 h2
  exact tendsto_inv_mul_sum_of_tendsto_inv_sq_mul h1 h2

end ProbabilityTheory
