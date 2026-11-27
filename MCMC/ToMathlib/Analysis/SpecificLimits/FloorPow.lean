/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.SpecificLimits.FloorPow

/-!
# Cesàro means from the squares and the blocks between them

Staged for `Mathlib/Analysis/SpecificLimits/FloorPow.lean`, next to
`tendsto_div_of_monotone_of_tendsto_div_floor_pow`, the subsequence lemma of Etemadi's strong law
(monotone sequences along `⌊c ^ n⌋`). Here the subsequence is the squares and the sequence need not
be monotone: the blocks between consecutive squares are controlled in absolute value.

## Search

At Mathlib `d13f23b`:
`grep -rn "tendsto_div_of_monotone_of_tendsto_div_floor_pow\|tendsto.*Nat.sqrt" Mathlib` finds the
lemma above and its use in `Probability/StrongLaw.lean`, and no statement along the squares.
-/

@[expose] public section

open Filter Finset
open scoped Topology

/-- **Squares and blocks**: a real sequence whose partial sums along the squares are `o(q²)`,
and whose absolute sums over the blocks `[q², (q + 1)²)` are `o(q²)`, has Cesàro means tending
to zero. -/
theorem tendsto_inv_mul_sum_of_tendsto_inv_sq_mul {y : ℕ → ℝ}
    (ha : Tendsto (fun q : ℕ ↦ ((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ range (q ^ 2), y k) atTop (𝓝 0))
    (hd : Tendsto (fun q : ℕ ↦ ((q : ℝ) ^ 2)⁻¹ * ∑ k ∈ Ico (q ^ 2) ((q + 1) ^ 2), |y k|) atTop
      (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, y k) atTop (𝓝 0) := by
  have hq : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨b * b, fun n hn ↦ Nat.le_sqrt.2 hn⟩
  have h0 := (ha.abs.add hd).comp hq
  rw [abs_zero, add_zero] at h0
  refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩) h0
  have hq1 := Nat.sqrt_le' n
  have hpos : (0 : ℝ) < (Nat.sqrt n : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.sqrt_pos.2 hn)) 2
  have hle : (n : ℝ)⁻¹ ≤ ((Nat.sqrt n : ℝ) ^ 2)⁻¹ := inv_anti₀ hpos (by exact_mod_cast hq1)
  have hblock : |∑ k ∈ Ico (Nat.sqrt n ^ 2) n, y k| ≤
      ∑ k ∈ Ico (Nat.sqrt n ^ 2) ((Nat.sqrt n + 1) ^ 2), |y k| :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg
      (Ico_subset_Ico_right (Nat.lt_succ_sqrt' n).le) fun _ _ _ ↦ abs_nonneg _)
  rw [← sum_range_add_sum_Ico _ hq1, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast,
    Function.comp_apply, abs_mul, abs_inv, abs_of_pos hpos, ← mul_add]
  exact mul_le_mul hle ((abs_add_le _ _).trans (add_le_add le_rfl hblock)) (abs_nonneg _)
    (inv_nonneg.2 hpos.le)
