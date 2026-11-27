/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Cesàro means of triangular sums

Staged for `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`, after `Filter.Tendsto.cesaro`
and `Filter.Tendsto.cesaro_smul`, which it uses (so it cannot sit in `Analysis/SpecificLimits`,
which that file imports).

* `Filter.tendsto_inv_smul_sum_range_sum_range_of_norm_sub_le`: if `‖a k l - b l‖ ≤ c k * d l`
  with `c k → 0`, `d` summable and the partial sums of `b` converging to `s`, then
  `n⁻¹ • ∑_{k < n} ∑_{l < n - k} a k l → s`.
* `Filter.tendsto_inv_mul_sum_two_mul_sum_sub_of_abs_sub_le`: for real `a`, `b`, the same
  hypotheses give `n⁻¹ ∑_{k < n} (2 ∑_{l < n - k} a k l - a k 0) → 2 s - b 0`, the form in
  which the second moment of a sum is expanded by lags
  (`MeasureTheory.integral_sq_sum_range_eq`); the column `l = 0` is `Filter.Tendsto.cesaro`.

For a summable `b` the limit is `s = ∑' l, b l` (`Summable.hasSum`, `HasSum.tendsto_sum_nat`);
`b` need not be summable, only its partial sums in the order of `ℕ` need converge.

## Search

At Mathlib `d13f23b`: `grep -rln "cesaro" Mathlib` finds only
`Analysis/Asymptotics/SpecificAsymptotics.lean` (`Filter.Tendsto.cesaro_smul`,
`Filter.Tendsto.cesaro`), with no Cesàro mean of a sum over a triangle.
-/

@[expose] public section

open Filter Finset
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Cesàro means of triangular sums**: if `‖a k l - b l‖ ≤ c k * d l` with `c k → 0`, `d`
summable and the partial sums `∑_{l < N} b l` converging to `s`, then
`n⁻¹ • ∑_{k < n} ∑_{l < n - k} a k l → s`. For a summable `b`, `s = ∑' l, b l`
(`HasSum.tendsto_sum_nat`).

The hypotheses `hc` and `hd` are forced, on paper (not compiled), with `b = 0` and `s = 0` in both
cases. Without `c k → 0`: for `c = 1`, `d` the indicator of `0` and `a k l` the indicator of
`l = 0`, the means are `1` for `n ≥ 1`. Without the summability of `d`: for `c k = 1 / (k + 1)`,
`d = 1` and `a k l = 1 / (k + 1)`, the means are `n⁻¹ ∑_{k < n} (n - k) / (k + 1)`, which is at
least `∑_{k < n} 1 / (k + 1) - 1` and tends to infinity. -/
theorem Filter.tendsto_inv_smul_sum_range_sum_range_of_norm_sub_le {a : ℕ → ℕ → E} {b : ℕ → E}
    {c d : ℕ → ℝ} {s : E} (hab : ∀ k l, ‖a k l - b l‖ ≤ c k * d l) (hc : Tendsto c atTop (𝓝 0))
    (hd : Summable d) (hb : Tendsto (fun N ↦ ∑ l ∈ range N, b l) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, ∑ l ∈ range (n - k), a k l) atTop
      (𝓝 s) := by
  have hk (N k : ℕ) : ‖∑ l ∈ range N, (a k l - b l)‖ ≤ |c k| * ∑' l, |d l| :=
    (norm_sum_le _ _).trans ((sum_le_sum fun l _ ↦ (hab k l).trans
      ((le_abs_self _).trans_eq (abs_mul _ _))).trans (by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (hd.abs.sum_le_tsum _ fun _ _ ↦ abs_nonneg _)
          (abs_nonneg _)))
  have hU (n : ℕ) : ∑ k ∈ range n, ∑ l ∈ range (n - k), b l =
      ∑ j ∈ range n, ∑ l ∈ range (j + 1), b l := by
    rw [← Finset.sum_range_reflect]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [mem_range] at hj; rw [show n - (n - 1 - j) = j + 1 by omega]
  have hc' : Tendsto (fun k ↦ |c k| * ∑' l, |d l|) atTop (𝓝 0) := by
    simpa using hc.abs.mul_const (∑' l, |d l|)
  have h0 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, ∑ l ∈ range (n - k),
      (a k l - b l)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ by
      rw [norm_smul, norm_inv, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (sum_le_sum fun k _ ↦ hk (n - k) k)) (by positivity)) hc'.cesaro
  have h := ((hb.comp (tendsto_add_atTop_nat 1)).cesaro_smul).add h0
  rw [add_zero] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  rw [← hU n, ← smul_add, ← sum_add_distrib]
  simp only [← sum_add_distrib, add_sub_cancel]

/-- **Cesàro means of lag sums**: for real `a`, `b`, if `|a k l - b l| ≤ c k * d l` with
`c k → 0`, `d` summable and the partial sums `∑_{l < N} b l` converging to `s`, then
`n⁻¹ ∑_{k < n} (2 ∑_{l < n - k} a k l - a k 0) → 2 s - b 0`. For a summable `b`, `s = ∑' l, b l`
(`HasSum.tendsto_sum_nat`).

The hypotheses `hc` and `hd` are forced, on paper (not compiled), by the two examples of
`Filter.tendsto_inv_smul_sum_range_sum_range_of_norm_sub_le`, where `2 s - b 0 = 0`: in the first
the means are `1` for `n ≥ 1`, in the second they are at least `∑_{k < n} 1 / (k + 1) - 2`. -/
theorem Filter.tendsto_inv_mul_sum_two_mul_sum_sub_of_abs_sub_le {a : ℕ → ℕ → ℝ} {b c d : ℕ → ℝ}
    {s : ℝ} (hab : ∀ k l, |a k l - b l| ≤ c k * d l) (hc : Tendsto c atTop (𝓝 0))
    (hd : Summable d) (hb : Tendsto (fun N ↦ ∑ l ∈ range N, b l) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), a k l - a k 0))
      atTop (𝓝 (2 * s - b 0)) := by
  have h0 : Tendsto (fun k ↦ a k 0) atTop (𝓝 (b 0)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ hab k 0)
      (by simpa using hc.mul_const (d 0)))
  refine (((Filter.tendsto_inv_smul_sum_range_sum_range_of_norm_sub_le hab hc hd
    hb).const_mul 2).sub h0.cesaro).congr fun n ↦ ?_
  rw [sum_sub_distrib, ← mul_sum, smul_eq_mul]
  ring
