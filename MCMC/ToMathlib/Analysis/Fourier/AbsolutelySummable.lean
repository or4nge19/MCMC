/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolutely summable Fourier series

An absolutely summable sequence `c : ℤ → E` is the sequence of Fourier coefficients of the
continuous function `t ↦ ∑' k, fourier k t • c k` on `AddCircle T`
(`fourierCoeff_tsum_fourier_smul`, `continuous_tsum_fourier_smul`): the converse of Mathlib's
`hasSum_fourier_series_of_summable`. For a summable real sequence with `r (-k) = r k` that sum is
real: `r` is the sequence of Fourier coefficients of a continuous real function
(`exists_continuous_fourierCoeff_eq_of_summable`), the form in which a summable autocovariance has
a continuous spectral density. For `r k = a^|k| v / (1 - a²)`, `|a| < 1` (the autocovariance of
the Gaussian autoregression), the series sums to `v / |1 - a e_1 t|²`
(`hasSum_fourier_smul_pow_natAbs_mul`, `fourierCoeff_div_normSq_one_sub_mul_fourier`).

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -n "theorem\|lemma"
Analysis/Fourier/AddCircle.lean` finds `fourierCoeff_fourier`, `hasSum_fourier_series_of_summable`
and `has_pointwise_sum_fourier_series_of_summable` (from coefficients of a given continuous
function to its series), and no statement computing the coefficients of a given series;
`grep -rn "fourierCoeff (fun" Mathlib` finds no `tsum`.
-/

@[expose] public section

open MeasureTheory AddCircle ComplexConjugate

variable {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- The profile `fourier m • c` has the single harmonic `c`, at `m`. -/
theorem fourierCoeff_fourier_smul (m : ℤ) (c : E) :
    fourierCoeff (fun x : AddCircle T => fourier m x • c) = Pi.single m c := by
  ext n
  have h := congrFun (fourierCoeff_fourier (T := T) m) n
  simp only [fourierCoeff, smul_smul, smul_eq_mul] at h ⊢
  rw [integral_smul_const, h]
  rcases eq_or_ne n m with rfl | hnm <;> simp [*]


omit [Fact (0 < T)] [CompleteSpace E] in
/-- The terms `fourier k t • c` have norm `‖c‖`. -/
theorem norm_fourier_smul (k : ℤ) (t : AddCircle T) (c : E) : ‖fourier k t • c‖ = ‖c‖ := by
  rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

omit [Fact (0 < T)] in
/-- An absolutely summable trigonometric series has a continuous sum. -/
theorem continuous_tsum_fourier_smul {c : ℤ → E} (hc : Summable fun k ↦ ‖c k‖) :
    Continuous fun t : AddCircle T ↦ ∑' k, fourier k t • c k :=
  continuous_tsum (fun k ↦ (map_continuous (fourier k)).smul continuous_const) hc
    fun k t ↦ (norm_fourier_smul k t (c k)).le

/-- **An absolutely summable trigonometric series is the Fourier series of its sum**: for
`∑ ‖c k‖ < ∞`, the Fourier coefficients of `t ↦ ∑' k, fourier k t • c k` are `c`. -/
theorem fourierCoeff_tsum_fourier_smul {c : ℤ → E} (hc : Summable fun k ↦ ‖c k‖) :
    fourierCoeff (fun t : AddCircle T ↦ ∑' k, fourier k t • c k) = c := by
  ext n
  have hint (k : ℤ) : Integrable (fun t : AddCircle T ↦ fourier (-n) t • fourier k t • c k)
      haarAddCircle := ((integrable_const (c k)).fourier_smul k).fourier_smul (-n)
  have hnorm (k : ℤ) : ∫ t : AddCircle T, ‖fourier (-n) t • fourier k t • c k‖ ∂haarAddCircle =
      ‖c k‖ := by
    simp_rw [norm_fourier_smul]
    simp
  rw [fourierCoeff]
  simp_rw [← (Summable.of_norm (hc.congr fun k ↦
    (norm_fourier_smul k _ (c k)).symm)).tsum_const_smul]
  rw [← integral_tsum_of_summable_integral_norm hint (by simpa only [hnorm] using hc),
    tsum_eq_single n fun k hk ↦ ?_]
  · simpa [fourierCoeff] using congrFun (fourierCoeff_fourier_smul (T := T) n (c n)) n
  · simpa [fourierCoeff, Pi.single_apply, Ne.symm hk] using
      congrFun (fourierCoeff_fourier_smul (T := T) k (c k)) n

/-- **A summable symmetric real sequence is the sequence of Fourier coefficients of a continuous
real function**: for summable `r : ℤ → ℝ` with `r (-k) = r k`, there is a continuous
`F : AddCircle T → ℝ` with `(r k : ℂ) = fourierCoeff F k` for every `k`. -/
theorem exists_continuous_fourierCoeff_eq_of_summable {r : ℤ → ℝ} (hr : Summable r)
    (hsymm : ∀ k, r (-k) = r k) :
    ∃ F : AddCircle T → ℝ, Continuous F ∧
      ∀ k, (r k : ℂ) = fourierCoeff (fun t ↦ (F t : ℂ)) k := by
  have hc : Summable fun k ↦ ‖(r k : ℂ)‖ := by simpa using hr.abs
  have hreal (t : AddCircle T) :
      (((∑' k, fourier k t • (r k : ℂ)).re : ℝ) : ℂ) = ∑' k, fourier k t • (r k : ℂ) := by
    rw [← Complex.conj_eq_iff_re, Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun k ↦ ?_
    rw [Equiv.neg_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, ← fourier_neg, neg_neg,
      hsymm, smul_eq_mul]
  refine ⟨fun t ↦ (∑' k, fourier k t • (r k : ℂ)).re,
    Complex.continuous_re.comp (continuous_tsum_fourier_smul hc), fun k ↦ ?_⟩
  simp_rw [hreal]
  exact (congrFun (fourierCoeff_tsum_fourier_smul hc) k).symm

omit [Fact (0 < T)] in
/-- **The Fourier series of `v / |1 - a e₁|²`**, `v / (1 - a²)` times the Poisson kernel: for
real `|a| < 1`, `∑ₖ e_k t · a^|k| v / (1 - a²) = v / |1 - a e_1 t|²`, the geometric series
`∑_{n ≥ 0} (a z)ⁿ` and `∑_{n ≥ 1} (a z̄)ⁿ`, `z = e_1 t`, `z z̄ = 1`. -/
theorem hasSum_fourier_smul_pow_natAbs_mul {a : ℝ} (ha : |a| < 1) (v : ℝ) (t : AddCircle T) :
    HasSum (fun k : ℤ ↦ fourier k t • ((a ^ k.natAbs * (v / (1 - a ^ 2)) : ℝ) : ℂ))
      ((v / Complex.normSq (1 - a * fourier 1 t) : ℝ) : ℂ) := by
  set z : ℂ := fourier 1 t with hzdef
  have hz : ‖z‖ = 1 := by simp [hzdef]
  have hk (k : ℤ) : fourier k t = z ^ k := by
    rw [fourier_apply, toCircle_zsmul, Circle.coe_zpow, hzdef, fourier_one]
  have hzc : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow, Complex.ofReal_one]
  have hzi : z⁻¹ = conj z := inv_eq_of_mul_eq_one_right hzc
  have h1 : ‖(a : ℂ) * z‖ < 1 := by rwa [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(a : ℂ) * conj z‖ < 1 := by
    rwa [norm_mul, Complex.norm_conj, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have ha2 : (1 : ℂ) - a ^ 2 ≠ 0 := by
    exact_mod_cast (sub_pos.2 ((sq_lt_one_iff_abs_lt_one a).2 ha)).ne'
  have hn1 : (1 : ℂ) - a * z ≠ 0 := fun h ↦ by
    rw [sub_eq_zero] at h; rw [← h, norm_one] at h1; exact lt_irrefl _ h1
  have hn2 : (1 : ℂ) - a * conj z ≠ 0 := fun h ↦ by
    rw [sub_eq_zero] at h; rw [← h, norm_one] at h2; exact lt_irrefl _ h2
  have hA := (hasSum_geometric_of_norm_lt_one h1).mul_right ((v / (1 - a ^ 2) : ℝ) : ℂ)
  have hB := ((hasSum_geometric_of_norm_lt_one h2).mul_left ((a : ℂ) * conj z)).mul_right
    ((v / (1 - a ^ 2) : ℝ) : ℂ)
  have hS := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ ↦ fourier k t •
    ((a ^ k.natAbs * (v / (1 - a ^ 2)) : ℝ) : ℂ)) (hA.congr_fun fun n ↦ by
      rw [hk, smul_eq_mul, zpow_natCast, Int.natAbs_natCast]; push_cast; ring)
    (hB.congr_fun fun n ↦ by
      rw [hk, smul_eq_mul, zpow_neg, ← Nat.cast_succ, zpow_natCast, ← inv_pow, hzi,
        Int.natAbs_neg, Int.natAbs_natCast, Nat.succ_eq_add_one]
      push_cast
      ring)
  convert hS using 1
  rw [Complex.ofReal_div, ← Complex.mul_conj, map_sub, map_one, map_mul, Complex.conj_ofReal]
  push_cast
  field_simp
  linear_combination (a ^ 2 * v) * hzc

/-- **The spectral density `v / |1 - a e₁|²` of the autocovariance `a^|k| v / (1 - a²)`**: for
real `|a| < 1`, the Fourier coefficients of `t ↦ v / |1 - a e_1 t|²` are `a^|k| v / (1 - a²)`, the
stationary autocovariance of the Gaussian autoregression
(`ProbabilityTheory.tendsto_covariance_gaussian_ar`). -/
theorem fourierCoeff_div_normSq_one_sub_mul_fourier {a : ℝ} (ha : |a| < 1) (v : ℝ) :
    fourierCoeff (fun t : AddCircle T ↦ ((v / Complex.normSq (1 - a * fourier 1 t) : ℝ) : ℂ)) =
      fun k ↦ ((a ^ k.natAbs * (v / (1 - a ^ 2)) : ℝ) : ℂ) := by
  have hg : Summable fun n : ℕ ↦ |a| ^ n * |v / (1 - a ^ 2)| :=
    (summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right _
  have hs : Summable fun k : ℤ ↦ ‖((a ^ k.natAbs * (v / (1 - a ^ 2)) : ℝ) : ℂ)‖ := by
    refine Summable.of_nat_of_neg_add_one (hg.congr fun n ↦ ?_)
      (((summable_nat_add_iff 1).2 hg).congr fun n ↦ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, Int.natAbs_natCast]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, ← Nat.cast_succ, Int.natAbs_neg,
        Int.natAbs_natCast]
  rw [← fourierCoeff_tsum_fourier_smul (T := T) hs]
  exact congrArg fourierCoeff
    (funext fun t ↦ (hasSum_fourier_smul_pow_natAbs_mul ha v t).tsum_eq.symm)
