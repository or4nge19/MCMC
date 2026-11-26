/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Fourier.AbsolutelySummable
import MCMC.ToMathlib.Probability.Kernel.RandomMap
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Moments.Variance

/-!
# Mixing of Harris chains: correlations along the chain and decay of covariances

For a Markov kernel `P` with a drift `∫⁻ V ∂(P x) ≤ γ V x + K` and a minorization
`α • ν ≤ (P ^ m) x` on `{V ≤ R}`, `K + γ R < R`, and test functions with
`φ², ψ² ≤ M (1 + V)`:

* `√V` has the drift `∫⁻ √V ∂(P x) ≤ √γ √(V x) + √K` (`lintegral_sqrt_le_of_drift`: Jensen's
  inequality, then `√(a + b) ≤ √a + √b`), and every sublevel set of `V` is small for a power of
  `P` (`exists_smul_le_pow_add_of_drift_of_minorization_pow`), so Harris' theorem applies to
  `√V`: `|∫ φ ∂(Pⁿ x) - ∫ φ ∂π| ≤ C ρⁿ √M (1 + √(V x))`
  (`exists_abs_integral_pow_sub_integral_le_sqrt_of_drift_of_minorization_pow`).
* **The stationary covariances decay geometrically**:
  `|∫ ψ · Pⁿφ ∂π - ∫ ψ ∂π ∫ φ ∂π| ≤ C ρⁿ M`
  (`exists_abs_integral_mul_integral_pow_sub_le_of_drift_of_minorization_pow`).
* **Correlations along the chain converge**: from every law `μ` integrating `V`,
  `|∫ ψ · Pˡφ ∂(Pᵏ ∘ₘ μ) - ∫ ψ · Pˡφ ∂π| ≤ C ρᵏ M (1 + ∫ V ∂μ)`
  (`exists_abs_integral_mul_integral_comp_pow_sub_le_of_drift_of_minorization_pow`).
* **For a process with the chain's law**, started at a law integrating `V`, the covariances
  converge, `cov[φ (ζ (k + l)), ψ (ζ k)] → ∫ ψ · Pˡφ ∂π - ∫ φ ∂π ∫ ψ ∂π`
  (`tendsto_covariance_of_drift_of_minorization_pow`), to a limit `L l` with `|L l| ≤ C ρˡ`
  (`exists_tendsto_covariance_of_drift_of_minorization_pow`), and for one observable `h` the limit
  is the sequence of Fourier coefficients of a continuous function on the circle
  (`exists_tendsto_covariance_fourierCoeff_of_drift_of_minorization_pow`, through
  `exists_continuous_fourierCoeff_eq_of_summable`): a spectral density.

The weight `√V` is what makes `ψ · (Pⁿφ - ∫ φ ∂π)` integrable against `π` with only
`∫ V ∂π < ∞` known: with the weight `V` one would need `∫ V^{3/2} ∂π < ∞`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "sqrt" MeasureTheory/Integral/Lebesgue
Probability/Kernel` finds no Jensen inequality for the square root of a lintegral; Mathlib's
`ENNReal.lintegral_mul_norm_pow_le` (Hölder with exponents summing to one) gives it;
`grep -rn "tendsto_covariance" Probability` finds no covariance limit. Searched on 2026-11-26:
Mathlib has `variance_congr` but no `covariance_congr` (`grep -rn "covariance_congr"` finds
nothing; `grep -n congr Probability/Moments/Covariance.lean` finds only the `congr` tactic and
`Finset.sum_congr`).
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X} {V : X → ℝ≥0} {γ K : ℝ≥0}

/-- **The square root of a Lyapunov function is one**: if `∫⁻ V ∂(P x) ≤ γ V x + K`, then
`∫⁻ √V ∂(P x) ≤ √γ √(V x) + √K`. -/
theorem lintegral_sqrt_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (x : X) :
    ∫⁻ y, NNReal.sqrt (V y) ∂(P x) ≤ NNReal.sqrt γ * NNReal.sqrt (V x) + NNReal.sqrt K := by
  have hs (a : ℝ≥0) : ((NNReal.sqrt a : ℝ≥0) : ℝ≥0∞) = (a : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
    rw [NNReal.sqrt_eq_rpow, ENNReal.coe_rpow_of_nonneg _ (by norm_num), one_div]
  have hH := ENNReal.lintegral_mul_norm_pow_le (μ := P x) (f := fun y ↦ (V y : ℝ≥0∞)) (g := 1)
    hV.coe_nnreal_ennreal.aemeasurable aemeasurable_const (p := 2⁻¹) (q := 2⁻¹) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [Pi.one_apply, lintegral_one, measure_univ, ENNReal.one_rpow, mul_one] at hH
  calc ∫⁻ y, NNReal.sqrt (V y) ∂(P x) = ∫⁻ y, (V y : ℝ≥0∞) ^ (2⁻¹ : ℝ) ∂(P x) := by
        simp_rw [hs]
    _ ≤ (∫⁻ y, V y ∂(P x)) ^ (2⁻¹ : ℝ) := hH
    _ ≤ ((γ : ℝ≥0∞) * V x + K) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow (hdrift x) (by norm_num)
    _ ≤ ((γ : ℝ≥0∞) * V x) ^ (2⁻¹ : ℝ) + (K : ℝ≥0∞) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← hs, ← hs, ← hs]

/-- A real `a` with `a ^ 2 ≤ M (1 + v)`, `v ≥ 0`, has `|a| ≤ √M (1 + √v)`. -/
theorem _root_.Real.abs_le_sqrt_mul_one_add_sqrt {a M v : ℝ} (hv : 0 ≤ v)
    (h : a ^ 2 ≤ M * (1 + v)) : |a| ≤ √M * (1 + √v) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg a).trans h) (by linarith)
  rw [← Real.sqrt_sq_eq_abs]
  calc √(a ^ 2) ≤ √(M * (1 + v)) := Real.sqrt_le_sqrt h
    _ = √M * √(1 + v) := Real.sqrt_mul hM _
    _ ≤ √M * (1 + √v) := by
        gcongr
        exact (Real.sqrt_le_sqrt (by nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v])).trans_eq
          (Real.sqrt_sq (by positivity))

/-- A real `a` with `a ^ 2 ≤ M (1 + v)`, `v ≥ 0`, has `|a| ≤ (1 + M) (1 + v)`. -/
theorem _root_.Real.abs_le_one_add_mul_one_add {a M v : ℝ} (hv : 0 ≤ v)
    (h : a ^ 2 ≤ M * (1 + v)) : |a| ≤ (1 + M) * (1 + v) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg a).trans h) (by linarith)
  nlinarith [sq_abs a, sq_nonneg (|a| - 1), mul_nonneg hM hv]

/-- **Harris' theorem in the weight `√V`**: under the drift and the minorization of `P ^ m` on
`{V ≤ R}`, `α > 0`, `K + γ R < R`, there are `C ≥ 0` and `0 ≤ ρ < 1` with
`|∫ φ ∂(Pⁿ x) - ∫ φ ∂π| ≤ C ρⁿ √M (1 + √(V x))` for every invariant law `π` and every
measurable `φ` with `φ² ≤ M (1 + V)`. -/
theorem exists_abs_integral_pow_sub_integral_le_sqrt_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ φ : X → ℝ, Measurable φ → ∀ M : ℝ, (∀ x, φ x ^ 2 ≤ M * (1 + V x)) → ∀ (n : ℕ) (x : X),
        |∫ y, φ y ∂((P ^ n) x) - ∫ y, φ y ∂π| ≤ C * ρ ^ n * √M * (1 + √(V x : ℝ)) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hsγ : NNReal.sqrt γ < 1 := (NNReal.sqrt_lt_sqrt.2 hγ).trans_eq NNReal.sqrt_one
  have hLR := NNReal.div_one_sub_lt_of_add_mul_lt hR
  have hR0 : (0 : ℝ≥0) < R := NNReal.coe_pos.1 ((NNReal.coe_nonneg _).trans_lt hLR)
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ≥0, NNReal.sqrt K + NNReal.sqrt γ * R' < R' := by
    obtain ⟨n, hn⟩ := Archimedean.arch (NNReal.sqrt K) (tsub_pos_of_lt hsγ)
    refine ⟨n + 1, ?_⟩
    have hn' : (NNReal.sqrt K : ℝ) ≤ n * (1 - NNReal.sqrt γ) := by
      simpa [NNReal.coe_sub hsγ.le] using NNReal.coe_le_coe.2 hn
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one]
    nlinarith [(NNReal.sqrt γ).coe_nonneg, (by exact_mod_cast hsγ : (NNReal.sqrt γ : ℝ) < 1)]
  obtain ⟨j, hj⟩ := exists_smul_le_pow_add_of_drift_of_minorization_pow hV hdrift hR hmin (R' ^ 2)
  have hW : Measurable fun x ↦ NNReal.sqrt (V x) := NNReal.continuous_sqrt.measurable.comp hV
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow
      (V := fun x ↦ NNReal.sqrt (V x)) hW
      (lintegral_sqrt_le_of_drift hV hdrift) (m := m + j)
      (mul_pos (div_pos (tsub_pos_of_lt hLR) (mul_pos two_pos hR0)) hα) hR'
      fun x hx ↦ hj x (NNReal.sqrt_le_iff_le_sq.1 hx)
  refine ⟨C, ρ, hC, hρ0, hρ, fun π hπ hinv φ hφ M hφM n x ↦ ?_⟩
  have hb := h π hπ hinv (Measure.dirac x) inferInstance
    (by rw [lintegral_dirac' _ hW.coe_nnreal_ennreal]
        exact ENNReal.coe_ne_top) φ hφ √M
    (fun y ↦ by simpa [Real.coe_sqrt] using
      Real.abs_le_sqrt_mul_one_add_sqrt (V y).coe_nonneg (hφM y)) n
  rw [Measure.dirac_bind (Kernel.measurable _),
    integral_dirac' _ _ hW.coe_nnreal_real.stronglyMeasurable] at hb
  simpa [Real.coe_sqrt] using hb

/-- A function whose square is dominated by an integrable function is square integrable. -/
theorem _root_.MeasureTheory.memLp_two_of_sq_le {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (h : ∀ x, f x ^ 2 ≤ g x) : MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf).2 (hg.mono' (hf.pow 2) (ae_of_all _ fun x ↦
    (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (sq_nonneg _)).trans_le (h x))))

/-- Under a drift with `γ < 1`, every invariant probability measure integrates `V`. -/
theorem integrable_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) : Integrable (fun x ↦ (V x : ℝ)) π := by
  simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
    (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top (tsub_pos_of_lt
      (by exact_mod_cast hγ)).ne') (lintegral_le_of_invariant_of_drift hV hdrift hγ hπ))

/-- **From convergence in the weight `1 + √V` to covariances**: for a probability measure `π`
integrating `V`, measurable `φ`, `ψ` with `ψ² ≤ M (1 + V)`, and an s-finite kernel `Q` with
`|∫ φ ∂(Q x) - ∫ φ ∂π| ≤ D (1 + √(V x))` for every `x`,
`|∫ ψ · Qφ ∂π - ∫ ψ ∂π ∫ φ ∂π| ≤ 2 D √M (1 + ∫ V ∂π)`. -/
theorem abs_integral_mul_integral_sub_le_of_forall_abs_integral_sub_le {Q : Kernel X X}
    [IsSFiniteKernel Q] {π : Measure X} [IsProbabilityMeasure π]
    (hVi : Integrable (fun x ↦ (V x : ℝ)) π) {φ ψ : X → ℝ} (hφ : Measurable φ)
    (hψ : Measurable ψ) {M D : ℝ} (hψM : ∀ x, ψ x ^ 2 ≤ M * (1 + V x))
    (hQ : ∀ x, |∫ y, φ y ∂(Q x) - ∫ y, φ y ∂π| ≤ D * (1 + √(V x : ℝ))) :
    |∫ x, ψ x * ∫ y, φ y ∂(Q x) ∂π - (∫ x, ψ x ∂π) * ∫ x, φ x ∂π| ≤
      2 * D * √M * (1 + ∫ x, (V x : ℝ) ∂π) := by
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure π
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hQ x₀)) (by positivity)
  have hb (x : X) : |ψ x * (∫ y, φ y ∂(Q x) - ∫ y, φ y ∂π)| ≤ 2 * D * √M * (1 + V x) := by
    rw [abs_mul]
    calc |ψ x| * |∫ y, φ y ∂(Q x) - ∫ y, φ y ∂π|
        ≤ (√M * (1 + √(V x : ℝ))) * (D * (1 + √(V x : ℝ))) :=
          mul_le_mul (Real.abs_le_sqrt_mul_one_add_sqrt (V x).coe_nonneg (hψM x)) (hQ x)
            (abs_nonneg _) (by positivity)
      _ = D * √M * (1 + √(V x : ℝ)) ^ 2 := by ring
      _ ≤ D * √M * (2 * (1 + V x)) := by
          gcongr
          nlinarith [Real.sq_sqrt (V x).coe_nonneg, sq_nonneg (√(V x : ℝ) - 1)]
      _ = 2 * D * √M * (1 + V x) := by ring
  have hψi : Integrable ψ π := (memLp_two_of_sq_le hψ.aestronglyMeasurable
    (((integrable_const 1).add hVi).const_mul M) hψM).integrable one_le_two
  have hd : Integrable (fun x ↦ ψ x * (∫ y, φ y ∂(Q x) - ∫ y, φ y ∂π)) π :=
    (((integrable_const 1).add hVi).const_mul (2 * D * √M)).mono'
      (hψ.mul ((hφ.stronglyMeasurable.integral_kernel (κ := Q)).measurable.sub_const
        _)).aestronglyMeasurable (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hb x))
  rw [← integral_mul_const, ← integral_sub ((hd.add (hψi.mul_const (∫ y, φ y ∂π))).congr
    (ae_of_all _ fun x ↦ by simp only [Pi.add_apply]; ring)) (hψi.mul_const _)]
  calc |∫ x, (ψ x * ∫ y, φ y ∂(Q x) - ψ x * ∫ y, φ y ∂π) ∂π|
      ≤ ∫ x, 2 * D * √M * (1 + V x) ∂π := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (ae_of_all _ fun _ ↦ abs_nonneg _) (((integrable_const 1).add hVi).const_mul _)
          (ae_of_all _ fun x ↦ (le_of_eq (by ring_nf)).trans (hb x)))
    _ = 2 * D * √M * (1 + ∫ x, (V x : ℝ) ∂π) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hVi]
        simp

/-- **The stationary covariances decay geometrically**: under the drift and the minorization of
`P ^ m` on `{V ≤ R}`, `α > 0`, `K + γ R < R`, there are `C ≥ 0` and `0 ≤ ρ < 1` with
`|∫ ψ · Pⁿφ ∂π - ∫ ψ ∂π ∫ φ ∂π| ≤ C ρⁿ M` for every invariant law `π` and all measurable `φ`,
`ψ` with `φ², ψ² ≤ M (1 + V)`. -/
theorem exists_abs_integral_mul_integral_pow_sub_le_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ φ ψ : X → ℝ, Measurable φ → Measurable ψ → ∀ M : ℝ, (∀ x, φ x ^ 2 ≤ M * (1 + V x)) →
        (∀ x, ψ x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
          |∫ x, ψ x * ∫ y, φ y ∂((P ^ n) x) ∂π - (∫ x, ψ x ∂π) * ∫ x, φ x ∂π| ≤
            C * ρ ^ n * M := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_pow_sub_integral_le_sqrt_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  refine ⟨2 * C * (1 + K / (1 - γ)), ρ, by positivity, hρ0, hρ,
    fun π hπ hinv φ ψ hφ hψ M hφM hψM n ↦ ?_⟩
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure π
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hψM x₀)) (by positivity)
  have hA : 0 ≤ C * ρ ^ n * M := by positivity
  refine (abs_integral_mul_integral_sub_le_of_forall_abs_integral_sub_le
    (integrable_of_invariant_of_drift hV hdrift hγ hinv) hφ hψ hψM
    (D := C * ρ ^ n * √M) fun x ↦ h π hπ hinv φ hφ M hφM n x).trans ?_
  rw [mul_assoc 2, mul_assoc (C * ρ ^ n), Real.mul_self_sqrt hM]
  nlinarith [mul_le_mul_of_nonneg_left (integral_le_of_invariant_of_drift hV hdrift hγ hinv) hA]

/-- Under the drift with `γ < 1`, a function with `φ² ≤ M (1 + V)` has
`(∫ φ ∂(Pⁿ x))² ≤ M (1 + K / (1 - γ)) (1 + V x)`: Jensen's inequality and the iterated drift. -/
theorem sq_integral_pow_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {φ : X → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hφM : ∀ x, φ x ^ 2 ≤ M * (1 + V x)) (n : ℕ) (x : X) :
    (∫ y, φ y ∂((P ^ n) x)) ^ 2 ≤ M * (1 + K / (1 - γ)) * (1 + V x) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hφM x)) (by positivity)
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  have hVi : Integrable (fun y ↦ (V y : ℝ)) ((P ^ n) x) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_pow_ne_top_of_drift hV hdrift n x)
  have hD : Integrable (fun y ↦ M * (1 + (V y : ℝ))) ((P ^ n) x) :=
    ((integrable_const 1).add hVi).const_mul M
  have hφ2 : Integrable (fun y ↦ φ y ^ 2) ((P ^ n) x) :=
    hD.mono' (hφ.pow_const 2).aestronglyMeasurable (ae_of_all _ fun y ↦
      (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (sq_nonneg _)).trans_le (hφM y)))
  have hvar := variance_nonneg φ ((P ^ n) x)
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).2 hφ2)] at hvar
  have hI : ∫ y, φ y ^ 2 ∂((P ^ n) x) ≤ ∫ y, M * (1 + (V y : ℝ)) ∂((P ^ n) x) :=
    integral_mono hφ2 hD hφM
  rw [integral_const_mul, integral_add (integrable_const 1) hVi] at hI
  have hpow := integral_pow_le_of_drift hV hdrift hγ n x
  have hγn : (γ : ℝ) ^ n ≤ 1 := pow_le_one₀ γ.coe_nonneg (by exact_mod_cast hγ.le)
  simp only [Pi.pow_apply, MeasureTheory.integral_const, probReal_univ, smul_eq_mul,
    mul_one] at hvar hI
  nlinarith [mul_le_mul_of_nonneg_left hpow hM, mul_nonneg hM (mul_nonneg hL (V x).coe_nonneg),
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (V x).coe_nonneg hγn) hM]

/-- **Correlations along the chain converge**: under the drift and the minorization of `P ^ m`
on `{V ≤ R}`, `α > 0`, `K + γ R < R`, there are `C ≥ 0` and `0 ≤ ρ < 1` with
`|∫ ψ · Pˡφ ∂(Pᵏ ∘ₘ μ) - ∫ ψ · Pˡφ ∂π| ≤ C ρᵏ M (1 + ∫ V ∂μ)` for every invariant law `π`, every
initial law `μ` integrating `V`, all `l` and all measurable `φ`, `ψ` with `φ², ψ² ≤ M (1 + V)`. -/
theorem exists_abs_integral_mul_integral_comp_pow_sub_le_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ φ ψ : X → ℝ, Measurable φ → Measurable ψ → ∀ M : ℝ, (∀ x, φ x ^ 2 ≤ M * (1 + V x)) →
        (∀ x, ψ x ^ 2 ≤ M * (1 + V x)) → ∀ k l : ℕ,
          |∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂((P ^ k) ∘ₘ μ) -
            ∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂π| ≤ C * ρ ^ k * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  refine ⟨C * (1 + K / (1 - γ)), ρ, by positivity, hρ0, hρ,
    fun π hπ hinv μ hμ hμV φ ψ hφ hψ M hφM hψM k l ↦ (h π hπ hinv μ hμ hμV _
      (hψ.mul (hφ.stronglyMeasurable.integral_kernel (κ := P ^ l)).measurable)
      (M * (1 + K / (1 - γ))) (fun x ↦ ?_) k).trans_eq (by ring)⟩
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hψM x)) (by positivity)
  have hJ := sq_integral_pow_le_of_drift hV hdrift hγ hφ hφM l x
  have hv := (V x).coe_nonneg
  rw [Pi.mul_apply, abs_mul]
  nlinarith [two_mul_le_add_sq |ψ x| |∫ y, φ y ∂((P ^ l) x)|, sq_abs (ψ x),
    sq_abs (∫ y, φ y ∂((P ^ l) x)), hψM x, mul_nonneg hM (mul_nonneg hL hv), mul_nonneg hM hL]

open Finset Preorder in
/-- If the trajectory of `ζ` has the law of the chain of `P` started at `μ.map (ζ 0)`, then `ζ j`
has law `(P ^ j) ∘ₘ μ.map (ζ 0)`. -/
theorem map_eq_comp_pow_of_map_eq_trajMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [IsMarkovKernel P] {ζ : ℕ → Ω → X}
    (hζ : ∀ k, Measurable (ζ k))
    (hlaw : μ.map (fun ω n ↦ ζ n ω) = trajMeasure (X := fun _ ↦ X) (μ.map (ζ 0)) fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)) (j : ℕ) :
    μ.map (ζ j) = (P ^ j) ∘ₘ μ.map (ζ 0) := by
  rw [← trajMeasure_map_eval (P := P) (μ := μ.map (ζ 0)) j, ← hlaw,
    Measure.map_map (measurable_pi_apply j) (measurable_pi_iff.2 hζ)]
  rfl

open Finset Preorder in
/-- **Correlations of a chain from its kernel**: if the trajectory of `ζ` has the law of the chain
of `P` started at `μ.map (ζ 0)`, then `E[φ (ζ (k + l)) ψ (ζ k)] = ∫ ψ · Pˡφ ∂(Pᵏ ∘ₘ μ.map (ζ 0))`
whenever `φ (ζ (k + l)) ψ (ζ k)` is integrable. -/
theorem integral_comp_mul_comp_eq_of_map_eq_trajMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [IsMarkovKernel P] {ζ : ℕ → Ω → X}
    (hζ : ∀ k, Measurable (ζ k))
    (hlaw : μ.map (fun ω n ↦ ζ n ω) = trajMeasure (X := fun _ ↦ X) (μ.map (ζ 0)) fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
    {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) (k l : ℕ)
    (hint : Integrable (fun ω ↦ φ (ζ (k + l) ω) * ψ (ζ k ω)) μ) :
    ∫ ω, φ (ζ (k + l) ω) * ψ (ζ k ω) ∂μ =
      ∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂((P ^ k) ∘ₘ μ.map (ζ 0)) := by
  have hpath : Measurable fun ω n ↦ ζ n ω := measurable_pi_iff.2 hζ
  have hpair : μ.map (fun ω ↦ (ζ k ω, ζ (k + l) ω)) = ((P ^ k) ∘ₘ μ.map (ζ 0)) ⊗ₘ (P ^ l) := by
    rw [← trajMeasure_map_eval_eval_add (P := P) (μ := μ.map (ζ 0)) k l, ← hlaw,
      Measure.map_map (by fun_prop) hpath]
    rfl
  have hg : Measurable fun p : X × X ↦ ψ p.1 * φ p.2 :=
    (hψ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have h1 : ∫ ω, φ (ζ (k + l) ω) * ψ (ζ k ω) ∂μ =
      ∫ p, ψ p.1 * φ p.2 ∂(μ.map fun ω ↦ (ζ k ω, ζ (k + l) ω)) := by
    rw [integral_map ((hζ k).prodMk (hζ (k + l))).aemeasurable hg.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)
  have hint' : Integrable (fun p : X × X ↦ ψ p.1 * φ p.2)
      (((P ^ k : Kernel X X) ∘ₘ μ.map (ζ 0)) ⊗ₘ (P ^ l)) := by
    rw [← hpair, integrable_map_measure hg.aestronglyMeasurable
      ((hζ k).prodMk (hζ (k + l))).aemeasurable]
    exact hint.congr (ae_of_all _ fun ω ↦ mul_comm _ _)
  rw [h1, hpair, Measure.integral_compProd hint']
  simp_rw [integral_const_mul]

open Finset Preorder in
/-- **The covariances of a Harris chain converge**: if the trajectory of `ζ` has the law of the
chain of `P` started at a law integrating `V`, under the drift and the minorization of `P ^ m` on
`{V ≤ R}` (`α > 0`, `K + γ R < R`), then for measurable `φ`, `ψ` with
`φ², ψ² ≤ M (1 + V)` and every lag `l`,
`cov[φ (ζ (k + l)), ψ (ζ k)] → ∫ ψ · Pˡφ ∂π - ∫ φ ∂π ∫ ψ ∂π` as `k → ∞`, for the invariant law
`π`. -/
theorem tendsto_covariance_of_drift_of_minorization_pow {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} [IsProbabilityMeasure ν]
    {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {ζ : ℕ → Ω → X} (hζ : ∀ k, Measurable (ζ k))
    (hlaw : μ.map (fun ω n ↦ ζ n ω) = trajMeasure (X := fun _ ↦ X) (μ.map (ζ 0)) fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
    (hμV : ∫⁻ x, V x ∂(μ.map (ζ 0)) ≠ ∞) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {M : ℝ}
    (hφM : ∀ x, φ x ^ 2 ≤ M * (1 + V x)) (hψM : ∀ x, ψ x ^ 2 ≤ M * (1 + V x)) (l : ℕ) :
    Tendsto (fun k ↦ cov[fun ω ↦ φ (ζ (k + l) ω), fun ω ↦ ψ (ζ k ω); μ]) atTop
      (𝓝 (∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂π - (∫ x, φ x ∂π) * ∫ x, ψ x ∂π)) := by
  have hlawk := map_eq_comp_pow_of_map_eq_trajMeasure hζ hlaw
  have hVj (j : ℕ) : Integrable (fun ω ↦ (V (ζ j ω) : ℝ)) μ := by
    simpa only [Function.comp_def, ENNReal.coe_toReal] using (integrable_map_measure
      hV.coe_nnreal_ennreal.ennreal_toReal.aestronglyMeasurable (hζ j).aemeasurable).1
      ((hlawk j).symm ▸ integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
        (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV j))
  have hmem (f : X → ℝ) (hf : Measurable f) (hfM : ∀ x, f x ^ 2 ≤ M * (1 + V x)) (j : ℕ) :
      MemLp (fun ω ↦ f (ζ j ω)) 2 μ := memLp_two_of_sq_le (hf.comp (hζ j)).aestronglyMeasurable
    (((integrable_const 1).add (hVj j)).const_mul M) fun ω ↦ hfM _
  have hE (f : X → ℝ) (hf : Measurable f) (j : ℕ) :
      ∫ ω, f (ζ j ω) ∂μ = ∫ x, f x ∂((P ^ j) ∘ₘ μ.map (ζ 0)) := by
    rw [← hlawk, integral_map (hζ j).aemeasurable hf.aestronglyMeasurable]
  have hlim (a : ℕ → ℝ) (L C ρ A B : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
      (h : ∀ k, |a k - L| ≤ C * ρ ^ k * A * B) : Tendsto a atTop (𝓝 L) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun k ↦ (Real.norm_eq_abs _).trans_le (h k)) (by simpa using
        (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).const_mul C).mul_const A).mul_const B))
  obtain ⟨C₁, ρ₁, -, hρ₁0, hρ₁, h₁⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  obtain ⟨C₂, ρ₂, -, hρ₂0, hρ₂, h₂⟩ :=
    exists_abs_integral_mul_integral_comp_pow_sub_le_of_drift_of_minorization_pow hV hdrift hα
      hR hmin
  refine Tendsto.congr (fun k ↦ ?_) ((hlim _ _ _ _ _ _ hρ₂0 hρ₂ fun k ↦
    h₂ π inferInstance hπ _ inferInstance hμV φ ψ hφ hψ M hφM hψM k l).sub
    (((hlim _ _ _ _ _ _ hρ₁0 hρ₁ fun k ↦ h₁ π inferInstance hπ _ inferInstance hμV φ hφ (1 + M)
      (fun x ↦ Real.abs_le_one_add_mul_one_add (V x).coe_nonneg (hφM x)) k).comp
        (tendsto_add_atTop_nat l)).mul
    (hlim _ _ _ _ _ _ hρ₁0 hρ₁ fun k ↦ h₁ π inferInstance hπ _ inferInstance hμV ψ hψ (1 + M)
      (fun x ↦ Real.abs_le_one_add_mul_one_add (V x).coe_nonneg (hψM x)) k)))
  rw [covariance_eq_sub (hmem φ hφ hφM (k + l)) (hmem ψ hψ hψM k), Function.comp_apply,
    hE φ hφ (k + l), hE ψ hψ k, ← integral_comp_mul_comp_eq_of_map_eq_trajMeasure hζ hlaw hφ hψ k l
      ((hmem φ hφ hφM (k + l)).integrable_mul (hmem ψ hψ hψM k))]
  rfl

open Finset Preorder in
/-- **The covariances of a Harris chain converge to a geometrically decaying limit**: if the
trajectory of `ζ` has the law of the chain of `P` started at a law integrating `V`, under the drift
and the minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), then for measurable
`φ`, `ψ` with `φ², ψ² ≤ M (1 + V)` there are `L l` with `cov[φ (ζ (k + l)), ψ (ζ k)] → L l` as
`k → ∞` and `|L l| ≤ C ρ^l`, `ρ < 1`. -/
theorem exists_tendsto_covariance_of_drift_of_minorization_pow {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Kernel X X}
    [IsMarkovKernel P] {V : X → ℝ≥0} {γ K : ℝ≥0} (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} [IsProbabilityMeasure ν]
    {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {ζ : ℕ → Ω → X} (hζ : ∀ k, Measurable (ζ k))
    (hlaw : μ.map (fun ω n ↦ ζ n ω) = trajMeasure (X := fun _ ↦ X) (μ.map (ζ 0)) fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
    (hμV : ∫⁻ x, V x ∂(μ.map (ζ 0)) ≠ ∞) {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {M : ℝ} (hφM : ∀ x, φ x ^ 2 ≤ M * (1 + V x)) (hψM : ∀ x, ψ x ^ 2 ≤ M * (1 + V x)) :
    ∃ L : ℕ → ℝ, (∀ l, Tendsto (fun k ↦ cov[fun ω ↦ φ (ζ (k + l) ω), fun ω ↦ ψ (ζ k ω); μ])
      atTop (𝓝 (L l))) ∧ ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ l, |L l| ≤ C * ρ ^ l := by
  obtain ⟨m, hm, α, hα, hmin⟩ : ∃ m, 0 < m ∧ ∃ α : ℝ≥0, 0 < α ∧ ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x :=
    ⟨m + 1, m.succ_pos, _, mul_pos (tsub_pos_of_lt ((div_lt_one (hR.trans_le' zero_le)).2 hR)) hα,
      smul_le_pow_add_one_of_drift_of_minorization_pow hV hdrift hR hmin⟩
  obtain ⟨π, ⟨hπ1, hπ⟩, -⟩ := existsUnique_invariant_of_drift_of_minorization_pow hV
    (m := m) (γ := γ ^ m) (K := K * ∑ k ∈ Finset.range m, γ ^ k)
    (fun x ↦ by simpa using lintegral_pow_le_of_drift hV hdrift m x) hα
    (NNReal.mul_sum_pow_add_pow_mul_lt hR hm) hmin
  obtain ⟨C, ρ, -, hρ0, hρ, hb⟩ :=
    exists_abs_integral_mul_integral_pow_sub_le_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  refine ⟨fun l ↦ ∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂π - (∫ x, φ x ∂π) * ∫ x, ψ x ∂π,
    fun l ↦ tendsto_covariance_of_drift_of_minorization_pow hV hdrift hα hR hmin hζ hlaw hμV
      hπ hφ hψ hφM hψM l, C * M, ρ, hρ0, hρ, fun l ↦ ?_⟩
  rw [mul_comm (∫ x, φ x ∂π)]
  exact (hb π hπ1 hπ φ ψ hφ hψ M hφM hψM l).trans_eq (by ring)

open Finset Preorder in
/-- **The covariances of a Harris chain have a continuous spectral density**: if the trajectory
of `ζ` has the law of the chain of `P` started at a law integrating `V`, under the drift and the
minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), then for a measurable `h` with
`h² ≤ M (1 + V)` every `h (ζ k)` is square-integrable, and there are `r : ℤ → ℝ` and a continuous
`F` on `AddCircle τ` with `cov[h (ζ (k + l)), h (ζ k)] → r l` as `k → ∞`, `|r k| ≤ C ρ^|k|`,
`ρ < 1`, and `r k` the Fourier coefficients of `F`. -/
theorem exists_tendsto_covariance_fourierCoeff_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ζ : ℕ → Ω → X} (hζ : ∀ k, Measurable (ζ k))
    (hlaw : μ.map (fun ω n ↦ ζ n ω) = trajMeasure (X := fun _ ↦ X) (μ.map (ζ 0)) fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
    (hμV : ∫⁻ x, V x ∂(μ.map (ζ 0)) ≠ ∞) {h : X → ℝ} (hh : Measurable h) {M : ℝ}
    (hhM : ∀ x, h x ^ 2 ≤ M * (1 + V x)) (τ : ℝ) [Fact (0 < τ)] :
    (∀ k, MemLp (fun ω ↦ h (ζ k ω)) 2 μ) ∧
      ∃ (r : ℤ → ℝ) (F : AddCircle τ → ℝ), Continuous F ∧
        (∀ l : ℕ, Tendsto (fun k ↦ cov[fun ω ↦ h (ζ (k + l) ω), fun ω ↦ h (ζ k ω); μ]) atTop
          (𝓝 (r l))) ∧
        (∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : ℤ, |r k| ≤ C * ρ ^ k.natAbs) ∧
        ∀ k, (r k : ℂ) = fourierCoeff (fun t ↦ (F t : ℂ)) k := by
  have hlawk := map_eq_comp_pow_of_map_eq_trajMeasure hζ hlaw
  refine ⟨fun j ↦ ?_, ?_⟩
  · have hVj : Integrable (fun ω ↦ (V (ζ j ω) : ℝ)) μ := by
      simpa only [Function.comp_def, ENNReal.coe_toReal] using (integrable_map_measure
        hV.coe_nnreal_ennreal.ennreal_toReal.aestronglyMeasurable (hζ j).aemeasurable).1
        ((hlawk j).symm ▸ integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
          (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV j))
    exact memLp_two_of_sq_le (hh.comp (hζ j)).aestronglyMeasurable
      (((integrable_const 1).add hVj).const_mul M) fun ω ↦ hhM _
  obtain ⟨L, hL, C, ρ, hρ0, hρ, hdecay⟩ := exists_tendsto_covariance_of_drift_of_minorization_pow
    hV hdrift hα hR hmin hζ hlaw hμV hh hh hhM hhM
  have hLs : Summable L := Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left C) fun n ↦ (Real.norm_eq_abs _).trans_le
      (hdecay n)
  obtain ⟨F, hF, hr⟩ := exists_continuous_fourierCoeff_eq_of_summable (T := τ)
    (r := fun k ↦ L k.natAbs) (Summable.of_nat_of_neg_add_one (by simpa using hLs)
      (((summable_nat_add_iff 1).2 hLs).congr fun n ↦ congrArg L (by
        rw [Int.natAbs_neg]; exact_mod_cast (Int.natAbs_natCast (n + 1)).symm))) fun k ↦ by simp
  exact ⟨fun k ↦ L k.natAbs, F, hF, fun l ↦ by simpa using hL l,
    ⟨C, ρ, hρ0, hρ, fun k ↦ hdecay _⟩, hr⟩

end Kernel

/-- Covariance respects almost-everywhere equality, as `variance_congr` does. -/
theorem covariance_congr {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  rw [covariance, covariance, integral_congr_ae hX, integral_congr_ae hY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h₁ h₂; rw [h₁, h₂])

/-! ### The Gaussian autoregression as a process -/

/-- **The noise-free autoregression**: if `ξ (k + 1) = a ξ k + w k` with `w k = 0` a.e., then
`ξ k = aᵏ ξ 0` a.e. and `cov[ξ (k + l), ξ k] = a^{2k+l} Var ξ₀`. -/
theorem covariance_ar_of_ae_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {a : ℝ} {ξ w : ℕ → Ω → ℝ} (hξ₀ : AEMeasurable (ξ 0) μ)
    (hξ : ∀ k ω, ξ (k + 1) ω = a * ξ k ω + w k ω) (hw : ∀ k, w k =ᵐ[μ] 0) (k l : ℕ) :
    cov[ξ (k + l), ξ k; μ] = a ^ (2 * k + l) * Var[ξ 0; μ] := by
  have hξk (j : ℕ) : ξ j =ᵐ[μ] fun ω ↦ a ^ j * ξ 0 ω := by
    induction j with
    | zero => exact .of_forall fun ω ↦ by simp
    | succ j ih =>
      filter_upwards [ih, hw j] with ω h₁ h₂
      rw [hξ, h₁, h₂, Pi.zero_apply, add_zero, pow_succ]
      ring
  rw [covariance_congr (hξk (k + l)) (hξk k), covariance_const_mul_left,
    covariance_const_mul_right, covariance_self hξ₀]
  ring

/-- **The covariances of the Gaussian autoregression converge to `aˡ v / (1 - a²)`**: for
`ξ (k + 1) = a ξ k + w k` with `|a| < 1`, the `w k` independent with law `N(0, v)`, independent
of `ξ 0`, and `E ξ₀² < ∞`, `cov[ξ (k + l), ξ k] → aˡ v / (1 - a²)` as `k → ∞`: for `v ≠ 0` the
limit `∫ x · ∫ y ∂(Pˡ x) ∂π` of `tendsto_covariance_of_drift_of_minorization_pow`, with
`Pˡ x = N(aˡ x, ·)` (`Kernel.pow_apply_gaussianReal_ar`) and `π = N(0, v / (1 - a²))` (the
hypotheses of that theorem and of `ProbabilityTheory.map_eq_trajMeasure_of_iIndepFun` hold
together here); at `v = 0`, `ξ k = aᵏ ξ 0` a.s. and the limit is `0`
(`covariance_ar_of_ae_eq_zero`). Its spectral density is `v / |1 - a e₁|²`
(`fourierCoeff_div_normSq_one_sub_mul_fourier`). -/
theorem tendsto_covariance_gaussian_ar {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} (ha : |a| < 1) {v : ℝ≥0} {ξ w : ℕ → Ω → ℝ}
    (hξ₀ : Measurable (ξ 0)) (hw : ∀ k, Measurable (w k))
    (hξ : ∀ k ω, ξ (k + 1) ω = a * ξ k ω + w k ω) (hind : IndepFun (ξ 0) (fun ω k ↦ w k ω) μ)
    (hiid : iIndepFun w μ) (hlaw : ∀ k, μ.map (w k) = gaussianReal 0 v)
    (hξ₀2 : ∫⁻ ω, ((‖ξ 0 ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂μ ≠ ∞) (l : ℕ) :
    Tendsto (fun k ↦ cov[ξ (k + l), ξ k; μ]) atTop (𝓝 (a ^ l * (v / (1 - a ^ 2)))) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp_rw [covariance_ar_of_ae_eq_zero hξ₀.aemeasurable hξ (fun k ↦ HasLaw.ae_eq_of_dirac
      (x := (0 : ℝ)) ⟨(hw k).aemeasurable, by rw [hlaw, gaussianReal_zero_var]⟩),
      NNReal.coe_zero, zero_div, mul_zero]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha).comp
      (tendsto_atTop_mono (fun k ↦ by omega : ∀ k : ℕ, k ≤ 2 * k + l) tendsto_id)).mul_const
        Var[ξ 0; μ]
  have hF : Measurable (Function.uncurry fun (x y : ℝ) ↦ a * x + y) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  have : IsMarkovKernel ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) := Kernel.IsMarkovKernel.map _ hF
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hξm (k : ℕ) : Measurable (ξ k) := by
    induction k with
    | zero => exact hξ₀
    | succ k ih => rw [funext (hξ k)]; exact (measurable_const.mul ih).add (hw k)
  obtain ⟨R, α, hα, hR, hdrift, hmin⟩ := Kernel.exists_drift_minorization_gaussian_ar ha hv
  have h := Kernel.tendsto_covariance_of_drift_of_minorization_pow (V := fun y ↦ ‖y‖₊ ^ 2)
    (by fun_prop) hdrift (m := 1) hα
    (lt_of_le_of_lt (by rw [two_mul, add_assoc]; exact le_add_self) hR)
    (fun x hx ↦ by rw [pow_one]; exact hmin x hx) hξm
    (map_eq_trajMeasure_of_iIndepFun (Q := (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) hF (Kernel.map_prod_const_apply hF _) hξ₀ hw hξ hind hiid
      hlaw)
    (by rwa [lintegral_map (by fun_prop) hξ₀]) (Kernel.invariant_gaussianReal_ar ha v)
    (φ := fun y ↦ y) (ψ := fun y ↦ y) measurable_id measurable_id (M := 1)
    (fun y ↦ by simp [sq_abs]) (fun y ↦ by simp [sq_abs]) l
  have hc : ‖a‖₊ ^ 2 ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one, sq_abs]
    exact ((sq_lt_one_iff_abs_lt_one a).2 ha).le
  have hπ : ∫ x, x * (a ^ l * x) ∂(gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2))) =
      a ^ l * (v / (1 - a ^ 2)) := by
    simp_rw [mul_left_comm _ (a ^ l), ← sq]
    rw [integral_const_mul, integral_sq_gaussianReal, NNReal.coe_div, NNReal.coe_sub hc,
      NNReal.coe_one, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
    ring
  simpa [integral_id_gaussianReal, Kernel.pow_apply_gaussianReal_ar, hπ] using h

end ProbabilityTheory
