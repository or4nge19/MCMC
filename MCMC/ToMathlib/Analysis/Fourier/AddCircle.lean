/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coefficients on sliding windows

As `s → ∞`, the Fourier coefficients of a signal on the windows `[s, s + T]` recover those of
the `T`-periodic profile the signal approaches: the harmonics of a steady state.

* `fourierCoeff_fourier_smul`: the profile `fourier m • c` has the single harmonic `c`, at `m`;
  a constant has the single harmonic at `0` (`fourierCoeff_const`).
* `norm_fourierCoeffOn_le`: a window coefficient is bounded by any bound of the signal there.
* `tendsto_fourierCoeffOn_of_tendsto_zero`: the window coefficients of a signal tending to `0`
  tend to `0`; no measurability is needed.
* `tendsto_fourierCoeffOn_of_tendsto_sub`: for a signal locally integrable near `+∞` and
  asymptotic to an integrable profile `p` on `AddCircle T`, they tend to `fourierCoeff p`.

Staged for `Mathlib/Analysis/Fourier/AddCircle.lean`. Searched on 2026-11-12 (pinned `d13f23b`):
`octo` ("Fourier coefficient on a sliding window [s, s+T] of a function asymptotic to a periodic
function converges", "Fourier coefficient of fourier m times a constant vector") and `rg` for
`fourierCoeffOn` next to `Tendsto`, for `fourier m x •` and for `norm_fourierCoeff`: the tree has
`fourierCoeff_fourier` (scalar profile only), no norm bound and no window limit. A translated form, `Filter.Tendsto.fourierCoeffOn_comp_add`, exists at another pin as the
third item.
-/

open Set Filter Topology MeasureTheory AddCircle
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The profile `fourier m • c` has the single harmonic `c`, at `m`. -/
theorem fourierCoeff_fourier_smul [CompleteSpace E] {T : ℝ} [Fact (0 < T)] (m : ℤ) (c : E) :
    fourierCoeff (fun x : AddCircle T => fourier m x • c) = Pi.single m c := by
  ext n
  have h := congrFun (fourierCoeff_fourier (T := T) m) n
  simp only [fourierCoeff, smul_smul, smul_eq_mul] at h ⊢
  rw [integral_smul_const, h]
  rcases eq_or_ne n m with rfl | hnm <;> simp [*]

/-- A constant has the single harmonic `c`, at `0`. -/
theorem fourierCoeff_const [CompleteSpace E] {T : ℝ} [Fact (0 < T)] (c : E) :
    fourierCoeff (fun _ : AddCircle T => c) = Pi.single 0 c := by
  simpa using fourierCoeff_fourier_smul (T := T) 0 c

/-- A Fourier coefficient on `[a, b]` is bounded by any bound of the signal on `(a, b]`. -/
theorem norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {f : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Ioc a b, ‖f x‖ ≤ C) (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral, norm_smul, norm_div, norm_one, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 hab), div_mul_eq_mul_div, one_mul, div_le_iff₀ (sub_pos.2 hab),
    ← abs_of_pos (sub_pos.2 hab)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [uIoc_of_le hab.le] at hx
  rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  exact hf x hx

/-- On the windows `[s, s + T]`, the coefficients of a signal tending to `0` tend to `0`. -/
theorem tendsto_fourierCoeffOn_of_tendsto_zero {T : ℝ} (hT : 0 < T) {f : ℝ → E}
    (hf : Tendsto f atTop (𝓝 0)) (n : ℤ) :
    Tendsto (fun s => fourierCoeffOn (lt_add_of_pos_right s hT) f n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf (ε / 2) (half_pos hε)
  refine ⟨N, fun s hs => ?_⟩
  rw [dist_zero_right]
  refine (norm_fourierCoeffOn_le _ (fun x hx => ?_) n).trans_lt (half_lt_self hε)
  simpa using (hN x (hs.trans hx.1.le)).le

/-- On the windows `[s, s + T]`, the Fourier coefficients of a signal asymptotic to an integrable
profile `p` on `AddCircle T` tend to those of `p`. Local integrability near `+∞` is forced: on a
window where the signal is not integrable its coefficients are `0`. -/
theorem tendsto_fourierCoeffOn_of_tendsto_sub {T : ℝ} [hT : Fact (0 < T)] {f : ℝ → E}
    {p : AddCircle T → E} {a : ℝ} (hf : LocallyIntegrableOn f (Ici a))
    (hp : Integrable p haarAddCircle) (h : Tendsto (fun t : ℝ => f t - p t) atTop (𝓝 0))
    (n : ℤ) :
    Tendsto (fun s => fourierCoeffOn (lt_add_of_pos_right s hT.out) f n) atTop
      (𝓝 (fourierCoeff p n)) := by
  refine (zero_add (fourierCoeff p n) ▸
    (tendsto_fourierCoeffOn_of_tendsto_zero hT.out h n).add_const (fourierCoeff p n)).congr' ?_
  filter_upwards [eventually_ge_atTop a] with s hs
  have hle : s ≤ s + T := le_add_of_nonneg_right hT.out.le
  have hcont : ContinuousOn (fun x : ℝ => (fourier (-n) (x : AddCircle T) : ℂ)) [[s, s + T]] :=
    ((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' T)).continuousOn
  have hfi : IntervalIntegrable f volume s (s + T) :=
    (hf.integrableOn_compact_subset (by rw [uIcc_of_le hle]; exact Icc_subset_Ici_iff hle |>.2 hs)
      isCompact_uIcc).intervalIntegrable
  have hpi : IntervalIntegrable (fun x : ℝ => p x) volume s (s + T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2
      ((AddCircle.measurePreserving_mk T s).integrable_comp_of_integrable
        (hp.smul_measure ENNReal.ofReal_ne_top))
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeff_eq_intervalIntegral _ _ s, add_sub_cancel_left, ← smul_add,
    ← intervalIntegral.integral_add ((hfi.sub hpi).continuousOn_smul hcont)
      (hpi.continuousOn_smul hcont)]
  simp_rw [← smul_add, sub_add_cancel]
