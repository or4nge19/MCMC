/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed
import MCMC.ToMathlib.Analysis.Normed.Algebra.GelfandRadius

/-!
# The resolvent beyond the Gelfand radius

In a complete normed algebra over a normed field `𝕜`, the Neumann series `∑ₙ k⁻ⁿ⁻¹ • aⁿ`
inverts `k - a` as soon as `gelfandRadius a < ‖k‖`. So every spectral value has norm at most
`gelfandRadius a`, over any `𝕜`. Over `ℂ` this is half of Gelfand's formula; over `ℝ` it is strict
for a rotation of `ℝ²` (empty real spectrum, Gelfand radius `1`). This is why the spectral radius of
a real operator is `gelfandRadius`, not `spectralRadius ℝ`.

## Main statements

* `gelfandRadius_lt_one_iff_tendsto_pow_atTop_nhds_zero`: `gelfandRadius a < 1` iff `aⁿ → 0`.
* `summable_pow_of_gelfandRadius_lt_one`: the geometric series of `a` converges below Gelfand
  radius `1`.
* `exists_unit_hasSum_of_gelfandRadius_lt`, `hasSum_resolvent_of_gelfandRadius_lt`: the
  Neumann series of the resolvent beyond the Gelfand radius.
* `spectralRadius_le_gelfandRadius`, `le_gelfandRadius_of_mul_pow_le_norm_pow`.

Staged as additions to `Mathlib/Analysis/Normed/Algebra/GelfandRadius.lean`. Searched on
2026-10-17: that file on mathlib master (after #42607) has no resolvent or summability statement;
the Neumann series in mathlib is stated below norm `1` (`NormedRing.inverse_one_sub`,
`geom_series_mul_neg`); no open PR mentions `gelfandRadius` and `resolvent`.
-/

open Filter Topology

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The powers of `a` tend to `0` iff the Gelfand radius of `a` is `< 1`. -/
theorem gelfandRadius_lt_one_iff_tendsto_pow_atTop_nhds_zero {a : A} :
    gelfandRadius a < 1 ↔ Tendsto (a ^ ·) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨s, hs, hs1⟩ := exists_between h
    obtain ⟨C, -, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a hs
    refine squeeze_zero_norm hb ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      ((gelfandRadius_nonneg a).trans hs.le) hs1).const_mul C
  · obtain ⟨n, hn, hn0⟩ := ((h.norm.eventually (gt_mem_nhds (by simp : ‖(0 : A)‖ < 1))).and
      (eventually_ne_atTop 0)).exists
    exact (gelfandRadius_le_norm_pow a hn0).trans_lt
      (Real.rpow_lt_one (norm_nonneg _) hn (by positivity))

/-- Lower bound for the Gelfand radius: `K * cⁿ ≤ ‖aⁿ‖` for all `n`, with `K > 0`, gives
`c ≤ gelfandRadius a`. -/
theorem le_gelfandRadius_of_mul_pow_le_norm_pow {a : A} {c K : ℝ} (hc : 0 ≤ c) (hK : 0 < K)
    (h : ∀ n, K * c ^ n ≤ ‖a ^ n‖) : c ≤ gelfandRadius a := by
  have hlim : Tendsto (fun n : ℕ ↦ K ^ (n : ℝ)⁻¹ * c) atTop (𝓝 c) := by
    simpa using (((Real.continuous_const_rpow hK.ne').tendsto' 0 1 (Real.rpow_zero _)).comp
      tendsto_inv_atTop_nhds_zero_nat).mul_const c
  refine le_of_tendsto_of_tendsto hlim (tendsto_gelfandRadius a) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  calc K ^ (n : ℝ)⁻¹ * c = (K * c ^ n) ^ (n : ℝ)⁻¹ := by
        rw [Real.mul_rpow hK.le (by positivity), Real.pow_rpow_inv_natCast hc hn]
    _ ≤ ‖a ^ n‖ ^ (n : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) (h n) (by positivity)

/-- Lower bound for the Gelfand radius: `cⁿ ≤ ‖aⁿ‖` for all `n` gives `c ≤ gelfandRadius a`. -/
theorem le_gelfandRadius_of_pow_le_norm_pow {a : A} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, c ^ n ≤ ‖a ^ n‖) : c ≤ gelfandRadius a :=
  le_gelfandRadius_of_mul_pow_le_norm_pow hc one_pos fun n ↦ (one_mul (c ^ n)).trans_le (h n)

variable [CompleteSpace A]

/-- Below Gelfand radius `1` the geometric series converges. -/
theorem summable_pow_of_gelfandRadius_lt_one {a : A} (h : gelfandRadius a < 1) :
    Summable (a ^ ·) := by
  obtain ⟨s, hs, hs1⟩ := exists_between h
  obtain ⟨C, -, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a hs
  exact .of_norm_bounded ((summable_geometric_of_lt_one
    ((gelfandRadius_nonneg a).trans hs.le) hs1).mul_left C) hb

/-- **Neumann series beyond the Gelfand radius**: `k - a` is a unit whose inverse is
`∑ₙ k⁻ⁿ⁻¹ • aⁿ`. -/
theorem exists_unit_hasSum_of_gelfandRadius_lt {a : A} {k : 𝕜} (hk : gelfandRadius a < ‖k‖) :
    ∃ u : Aˣ, (u : A) = algebraMap 𝕜 A k - a ∧
      HasSum (fun n : ℕ ↦ (k ^ (n + 1))⁻¹ • a ^ n) ↑u⁻¹ := by
  have hk0 : k ≠ 0 := norm_pos_iff.1 ((gelfandRadius_nonneg a).trans_lt hk)
  have hu : gelfandRadius (k⁻¹ • a) < 1 := by
    rwa [gelfandRadius_smul, norm_inv, inv_mul_lt_one₀ (norm_pos_iff.2 hk0)]
  have hs := summable_pow_of_gelfandRadius_lt_one hu
  have hsub : algebraMap 𝕜 A k - a = k • (1 - k⁻¹ • a) := by
    simp [smul_sub, smul_smul, hk0, Algebra.algebraMap_eq_smul_one]
  refine ⟨⟨_, k⁻¹ • ∑' n, (k⁻¹ • a) ^ n, ?_, ?_⟩, rfl, ?_⟩
  · simp [hsub, hk0, hs.one_sub_mul_tsum_pow]
  · simp [hsub, hk0, hs.tsum_pow_mul_one_sub]
  · convert hs.hasSum.const_smul k⁻¹ using 2 with n
    simp [smul_pow, smul_smul, pow_succ, mul_comm]

theorem mem_resolventSet_of_gelfandRadius_lt {a : A} {k : 𝕜} (hk : gelfandRadius a < ‖k‖) :
    k ∈ resolventSet 𝕜 a := by
  obtain ⟨u, hu, -⟩ := exists_unit_hasSum_of_gelfandRadius_lt hk
  exact ⟨u, hu⟩

theorem hasSum_resolvent_of_gelfandRadius_lt {a : A} {k : 𝕜} (hk : gelfandRadius a < ‖k‖) :
    HasSum (fun n : ℕ ↦ (k ^ (n + 1))⁻¹ • a ^ n) (resolvent a k) := by
  obtain ⟨u, hu, hsum⟩ := exists_unit_hasSum_of_gelfandRadius_lt hk
  rwa [resolvent, ← hu, Ring.inverse_unit]

theorem resolvent_eq_tsum_of_gelfandRadius_lt {a : A} {k : 𝕜} (hk : gelfandRadius a < ‖k‖) :
    resolvent a k = ∑' n : ℕ, (k ^ (n + 1))⁻¹ • a ^ n :=
  (hasSum_resolvent_of_gelfandRadius_lt hk).tsum_eq.symm

/-- Beyond the Gelfand radius, the resolvent is a right inverse of `k - a`. -/
theorem algebraMap_sub_mul_resolvent_of_gelfandRadius_lt {a : A} {k : 𝕜}
    (hk : gelfandRadius a < ‖k‖) : (algebraMap 𝕜 A k - a) * resolvent a k = 1 := by
  obtain ⟨u, hu, -⟩ := exists_unit_hasSum_of_gelfandRadius_lt hk
  rw [resolvent, ← hu, Ring.inverse_unit, Units.mul_inv]

/-- Beyond the Gelfand radius, the resolvent is a left inverse of `k - a`. -/
theorem resolvent_mul_algebraMap_sub_of_gelfandRadius_lt {a : A} {k : 𝕜}
    (hk : gelfandRadius a < ‖k‖) : resolvent a k * (algebraMap 𝕜 A k - a) = 1 := by
  obtain ⟨u, hu, -⟩ := exists_unit_hasSum_of_gelfandRadius_lt hk
  rw [resolvent, ← hu, Ring.inverse_unit, Units.inv_mul]

/-- Every spectral value has norm at most the Gelfand radius, over any normed field. Over `ℂ`
this is an equality (`spectrum.spectralRadius_eq_gelfandRadius`). -/
theorem spectralRadius_le_gelfandRadius (a : A) :
    spectralRadius 𝕜 a ≤ ENNReal.ofReal (gelfandRadius a) := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun k hk ↦ ?_
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal <| not_lt.1 fun h ↦ hk (mem_resolventSet_of_gelfandRadius_lt h)
