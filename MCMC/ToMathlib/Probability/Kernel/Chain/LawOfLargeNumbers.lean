/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Chain.Basic
public import MCMC.ToMathlib.Probability.Kernel.Mixing
public import MCMC.ToMathlib.Probability.StrongLaw
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The law of large numbers for Harris chains

For a Markov kernel `P` with a drift `∫⁻ V ∂(P x) ≤ γ V x + K`, a minorization
`α • ν ≤ (P ^ m) x` on `{V ≤ R}` with `α > 0` and `K + γ R < R`, an invariant law `π`, and a
measurable `g` with `g² ≤ M (1 + V)`, write `ḡ = g - ∫ g ∂π`:

* **Variance growth**: `∫ (∑_{k < n} ḡ (ω k))² ∂(P.chain ∘ₘ μ) ≤ C M n (1 + ∫ V ∂μ)` for every
  initial law `μ` integrating `V`, with `C` independent of `π`, `μ`, `g`, `M` and `n`
  (`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow`), and in `ℝ≥0∞`, with
  `μ univ + ∫⁻ V ∂μ` on the right, for every measure `μ`
  (`exists_lintegral_sq_sum_sub_le_of_drift_of_minorization_pow`). The correlations
  `∫ ψ (ω k) φ (ω (k + l))` with `∫ φ ∂π = 0` are `O(ρˡ)` uniformly in `k`
  (`exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow`), through the bound
  `|Pˡφ| ≤ C ρˡ √M (1 + √V)` of `Mixing.lean`.
* **The strong law**: `n⁻¹ ∑_{k < n} g (ω k) → ∫ g ∂π` for `P.chain x`-almost every `ω`, from every
  point `x` (`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow`), hence from every
  initial measure, with no moment
  (`ae_tendsto_inv_mul_sum_chain_comp_of_drift_of_minorization_pow`): the variance growth and
  Rajchman's argument (`ProbabilityTheory.ae_tendsto_inv_mul_sum_of_integral_sq_le`).
* **The asymptotic variance**: `n⁻¹ ∫ (∑_{k < n} ḡ (ω k))² ∂(P.chain ∘ₘ μ) → σ²` for every initial
  law `μ` integrating `V` (`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow`),
  where `σ² = Var[g (ω 0)] + 2 ∑_{l ≥ 1} cov[g (ω 0), g (ω l)]` is the series of the covariances
  of the stationary chain `P.chain ∘ₘ π`. The series converges absolutely
  (`summable_covariance_comp_chain_comp_of_drift_of_minorization_pow`), `σ² ≥ 0`
  (`variance_add_two_mul_tsum_covariance_comp_chain_comp_nonneg_of_drift_of_minorization_pow`),
  its first term is `Var[g; π]` (`variance_comp_chain_comp_of_invariant`) and the covariance at
  lag `l` is `∫ ḡ · Pˡḡ ∂π` (`covariance_comp_chain_comp_of_invariant`). The correlations from `μ`
  approach the stationary ones at the rate `ρᵏ ρˡ`
  (`exists_abs_integral_comp_mul_comp_chain_sub_le_of_drift_of_minorization_pow`).

The class `g² ≤ M (1 + V)` is the class of the variance growth: at `n = 1` from a point `x` its
left side is `(g x - ∫ g ∂π)²`. For the strong law it is the class this second-moment argument
reaches, and it is not claimed optimal there.

## The hypotheses are forced, and they hold together

The hypotheses on the kernel are those of Harris' theorem with the minorization of a power
(`exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow`).

* The identity kernel of `Bool` has every Dirac mass as invariant law, its averages converge to
  `g x` from `x` (`ae_tendsto_inv_mul_sum_chain_id`,
  `not_forall_ae_tendsto_inv_mul_sum_chain_id_bool`) and its centered sums have second moment `n²`
  (`integral_sq_sum_sub_chain_id_bool`). Each of the drift, the threshold `K + γ R < R`, the
  minorization and `α > 0`, left out of the statement of the strong law, of the variance growth
  or of the asymptotic variance at `X = Bool`, gives a statement that this kernel refutes (the
  twelve `example`s after `not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool`).
* The moment `∫⁻ V ∂μ ≠ ∞` of the initial law is forced in the variance growth and in the
  asymptotic variance, and is not needed in the strong law: for the descent `x ↦ x - 1` on `ℕ`
  with `V x = 2ˣ` (`drift_and_minorization_descent`), started at `∑ⱼ 2⁻⁽ʲ⁺¹⁾ δ_{4ʲ}`, the second
  moment at `n = 4ᴶ` is at least `n 2ᴶ / 2` (`le_integral_sq_sum_sub_chain_descent_comp`,
  `not_exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow_nat`,
  `not_tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow_nat`).
* The hypotheses hold together on the halving chain of `Harris.lean` (the strong law and the
  asymptotic variance, with the invariant law of `invariant_of_halving`) and on the Gaussian
  autoregression of `RandomMap.lean` (the last three `example`s).

## Search

At Mathlib `d13f23b`: `grep -rln "strong_law" Mathlib` finds `Probability/StrongLaw.lean`
(independent identically distributed sequences) and its uses, none for a Markov chain;
`grep -rn "variance_sum" Mathlib` finds `ProbabilityTheory.variance_sum'`
(`Probability/Moments/Variance.lean`: the variance of a sum as the double sum of covariances,
centered at the means), while the sums here are centered at `∫ g ∂π`, so their second moment is
expanded by lags (`MeasureTheory.integral_sq_sum_range_eq`);
`grep -rn "sq_sum_le_card_mul_sum_sq" Mathlib` finds the Cauchy–Schwarz inequality for finite
sums (`Algebra/Order/Chebyshev.lean`) and no expansion of `(∑_{k < n} a k)²` by lags.
`grep -rn "asymptotic variance\|asymptoticVariance" Mathlib` finds nothing;
`grep -rln "cesaro" Mathlib` finds only `Analysis/Asymptotics/SpecificAsymptotics.lean`
(`Filter.Tendsto.cesaro`, used here), with no Cesàro mean of lag sums;
`grep -rn "pow_le_sqrt\|sqrt_pow_mul\|min_pow_le" Mathlib` finds nothing.
-/

@[expose] public section

open Filter MeasureTheory Finset
open scoped ENNReal NNReal Topology

/-- **The square of a sum, by lags**:
`(∑_{k < n} a k)² = ∑_{k < n} (2 ∑_{l < n - k} a k a (k + l) - (a k)²)`. -/
theorem Finset.sq_sum_range_eq_sum_range_sum_range {R : Type*} [CommRing R] (a : ℕ → R)
    (n : ℕ) : (∑ k ∈ range n, a k) ^ 2 =
      ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), a k * a (k + l) - a k ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h (k : ℕ) (hk : k ∈ range n) : 2 * ∑ l ∈ range (n + 1 - k), a k * a (k + l) - a k ^ 2 =
        (2 * ∑ l ∈ range (n - k), a k * a (k + l) - a k ^ 2) + 2 * (a k * a n) := by
      rw [Nat.sub_add_comm (mem_range.1 hk).le, sum_range_succ,
        Nat.add_sub_of_le (mem_range.1 hk).le]
      ring
    rw [sum_range_succ, add_sq, ih, sum_range_succ, sum_congr rfl h, sum_add_distrib,
      Nat.add_sub_cancel_left, sum_range_one, add_zero, ← mul_sum, ← sum_mul]
    ring

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The second moment of a sum, by lags**: for square integrable `Y k`,
`∫ (∑_{k < n} Y k)² = ∑_{k < n} (2 ∑_{l < n - k} ∫ Y k Y (k + l) - ∫ (Y k)²)`. -/
theorem integral_sq_sum_range_eq {Y : ℕ → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 μ) (n : ℕ) :
    ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂μ = ∑ k ∈ range n,
      (2 * ∑ l ∈ range (n - k), ∫ ω, Y k ω * Y (k + l) ω ∂μ - ∫ ω, Y k ω ^ 2 ∂μ) := by
  have hi2 (k l : ℕ) : Integrable (fun ω ↦ Y k ω * Y (k + l) ω) μ :=
    (hY k).integrable_mul (hY (k + l))
  have hi (k : ℕ) : Integrable (fun ω ↦ ∑ l ∈ range (n - k), Y k ω * Y (k + l) ω) μ :=
    integrable_finsetSum _ fun l _ ↦ hi2 k l
  simp_rw [Finset.sq_sum_range_eq_sum_range_sum_range]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [integral_sub ((hi k).const_mul 2) (hY k).integrable_sq, integral_const_mul,
      integral_finsetSum _ fun l _ ↦ hi2 k l]
  · exact fun k _ ↦ ((hi k).const_mul 2).sub (hY k).integrable_sq

end MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X} {V : X → ℝ≥0} {γ K : ℝ≥0}

/-- **Second moments along the chain**: under a drift, from a finite initial measure integrating
`V`, a measurable `φ` with `φ² ≤ M (1 + V)` is square integrable at every time of the chain. -/
theorem memLp_comp_chain_comp_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : ∫⁻ x, V x ∂μ ≠ ∞) {φ : X → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ x, φ x ^ 2 ≤ M * (1 + V x)) (j : ℕ) :
    MemLp (fun ω ↦ φ (ω j)) 2 (P.chain ∘ₘ μ) := by
  have hVj : Integrable (fun x ↦ (V x : ℝ)) ((P.chain ∘ₘ μ).map fun ω ↦ ω j) := by
    rw [Measure.map_comp _ _ (measurable_pi_apply j), chain_map_eval]
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_comp_pow_ne_top_of_drift hV hdrift hμ j)
  exact memLp_two_of_sq_le (hφ.comp (measurable_pi_apply j)).aestronglyMeasurable
    (((integrable_const 1).add ((integrable_map_measure hV.coe_nnreal_real.aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 hVj)).const_mul M) fun ω ↦ hφM (ω j)

/-- **Moments of invariant laws, for a square**: under a drift with `γ < 1`, every invariant
probability measure `π` has `(∫ φ ∂π)² ≤ M (1 + K / (1 - γ))` for measurable `φ` with
`φ² ≤ M (1 + V)`. -/
theorem sq_integral_le_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) {φ : X → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ x, φ x ^ 2 ≤ M * (1 + V x)) : (∫ x, φ x ∂π) ^ 2 ≤ M * (1 + K / (1 - γ)) := by
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure π
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hφM x₀)) (by positivity)
  have hVi := integrable_of_invariant_of_drift hV hdrift hγ hπ
  have hmem := memLp_two_of_sq_le hφ.aestronglyMeasurable
    (((integrable_const 1).add hVi).const_mul M) hφM
  have hvar := variance_nonneg φ π
  rw [variance_eq_sub hmem] at hvar
  have hI : ∫ x, φ x ^ 2 ∂π ≤ ∫ x, M * (1 + (V x : ℝ)) ∂π :=
    integral_mono hmem.integrable_sq (((integrable_const 1).add hVi).const_mul M) hφM
  rw [integral_const_mul, integral_add (integrable_const 1) hVi] at hI
  simp only [Pi.pow_apply, MeasureTheory.integral_const, probReal_univ, smul_eq_mul,
    mul_one] at hvar hI
  nlinarith [mul_le_mul_of_nonneg_left (integral_le_of_invariant_of_drift hV hdrift hγ hπ) hM]

/-- **Centering at an invariant law**: under a drift with `γ < 1`, for an invariant probability
measure `π` and measurable `g` with `g² ≤ M (1 + V)`,
`(g - ∫ g ∂π)² ≤ 2 (2 + K / (1 - γ)) M (1 + V)`. -/
theorem sq_sub_integral_le_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) (x : X) :
    (g x - ∫ y, g y ∂π) ^ 2 ≤ 2 * (2 + K / (1 - γ)) * M * (1 + V x) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hgM x)) (by positivity)
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  have hc := sq_integral_le_of_invariant_of_drift hV hdrift hγ hπ hg hgM
  nlinarith [sq_nonneg (g x + ∫ y, g y ∂π), hgM x, (V x).coe_nonneg,
    mul_nonneg (mul_nonneg hM (by positivity : (0 : ℝ) ≤ 1 + K / (1 - γ))) (V x).coe_nonneg]

/-- **The correlations along a Harris chain decay geometrically in the lag**: under the drift and
the minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), there are `C ≥ 0` and
`0 ≤ ρ < 1` with `|∫ ψ (ω k) φ (ω (k + l)) ∂(P.chain ∘ₘ μ)| ≤ C ρˡ M (1 + ∫ V ∂μ)` for every
invariant law `π`, every initial law `μ` integrating `V`, all times `k`, `l` and all measurable
`φ`, `ψ` with `φ², ψ² ≤ M (1 + V)` and `∫ φ ∂π = 0`. -/
theorem exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ φ ψ : X → ℝ, Measurable φ → Measurable ψ → ∫ x, φ x ∂π = 0 → ∀ M : ℝ,
      (∀ x, φ x ^ 2 ≤ M * (1 + V x)) → (∀ x, ψ x ^ 2 ≤ M * (1 + V x)) → ∀ k l : ℕ,
        |∫ ω, ψ (ω k) * φ (ω (k + l)) ∂(P.chain ∘ₘ μ)| ≤
          C * ρ ^ l * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_pow_sub_integral_le_sqrt_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  refine ⟨2 * C * (1 + K / (1 - γ)), ρ, by positivity, hρ0, hρ,
    fun π hπ hinv μ hμ hμV φ ψ hφ hψ hφ0 M hφM hψM k l ↦ ?_⟩
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans
    (hψM (nonempty_of_isProbabilityMeasure μ).some)) (by positivity)
  have hA : 0 ≤ 2 * C * ρ ^ l * M := by positivity
  have hI : 0 ≤ ∫ x, (V x : ℝ) ∂μ := integral_nonneg fun _ ↦ (V _).coe_nonneg
  have hb (x : X) : |ψ x * ∫ y, φ y ∂((P ^ l) x)| ≤ 2 * C * ρ ^ l * M * (1 + V x) := by
    rw [abs_mul]
    calc |ψ x| * |∫ y, φ y ∂((P ^ l) x)|
        ≤ (√M * (1 + √(V x : ℝ))) * (C * ρ ^ l * √M * (1 + √(V x : ℝ))) :=
          mul_le_mul (Real.abs_le_sqrt_mul_one_add_sqrt (V x).coe_nonneg (hψM x))
            (by simpa [hφ0] using h π hπ hinv φ hφ M hφM l x) (abs_nonneg _) (by positivity)
      _ = C * ρ ^ l * M * (1 + √(V x : ℝ)) ^ 2 := by
          linear_combination (C * ρ ^ l * (1 + √(V x : ℝ)) ^ 2) * Real.mul_self_sqrt hM
      _ ≤ C * ρ ^ l * M * (2 * (1 + V x)) := by
          gcongr; nlinarith [Real.sq_sqrt (V x).coe_nonneg, sq_nonneg (√(V x : ℝ) - 1)]
      _ = 2 * C * ρ ^ l * M * (1 + V x) := by ring
  have hVk : Integrable (fun x ↦ (V x : ℝ)) ((P ^ k : Kernel X X) ∘ₘ μ) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV k)
  rw [integral_comp_mul_comp_chain_comp P μ k l hφ.aemeasurable hψ.aemeasurable
    ((memLp_comp_chain_comp_of_drift hV hdrift hμV hψ hψM k).integrable_mul
      (memLp_comp_chain_comp_of_drift hV hdrift hμV hφ hφM (k + l)))]
  calc |∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂((P ^ k) ∘ₘ μ)|
      ≤ ∫ x, 2 * C * ρ ^ l * M * (1 + V x) ∂((P ^ k) ∘ₘ μ) :=
        abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (ae_of_all _ fun _ ↦ abs_nonneg _) (((integrable_const 1).add hVk).const_mul _)
          (ae_of_all _ hb))
    _ = 2 * C * ρ ^ l * M * (1 + ∫ x, (V x : ℝ) ∂((P ^ k) ∘ₘ μ)) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hVk]
        simp
    _ ≤ 2 * C * (1 + K / (1 - γ)) * ρ ^ l * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
        nlinarith [mul_le_mul_of_nonneg_left
          (integral_comp_pow_le_of_drift hV hdrift hγ hμV k) hA, mul_nonneg hA (mul_nonneg hL hI)]

/-- **Variance growth of the sums of a Harris chain**: under the drift and the minorization of
`P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), there is `C ≥ 0` with
`∫ (∑_{k < n} (g (ω k) - ∫ g ∂π))² ∂(P.chain ∘ₘ μ) ≤ C M n (1 + ∫ V ∂μ)` for every invariant law
`π`, every initial law `μ` integrating `V`, every measurable `g` with `g² ≤ M (1 + V)` and every
`n`. -/
theorem exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : X → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  have hρ1 : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (sub_nonneg.2 hρ.le)
  refine ⟨C * (2 * (2 + K / (1 - γ))) * (2 * (1 - ρ)⁻¹), by positivity,
    fun π hπ hinv μ hμ hμV g hg M hgM n ↦ ?_⟩
  have hc0 : ∫ x, (g x - ∫ y, g y ∂π) ∂π = 0 := by
    simpa [average_eq_integral] using integral_sub_average π g
  have hgM' := sq_sub_integral_le_of_invariant_of_drift hV hdrift hγ hinv hg hgM
  set c := ∫ x, g x ∂π
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hgM x₀)) (by positivity)
  set B := C * (2 * (2 + K / (1 - γ)) * M) * (1 + ∫ x, (V x : ℝ) ∂μ) with hBdef
  have hB : 0 ≤ B := by positivity
  have hsum (k : ℕ) : ∑ l ∈ range (n - k),
      ∫ ω, (g (ω k) - c) * (g (ω (k + l)) - c) ∂(P.chain ∘ₘ μ) ≤ B * (1 - ρ)⁻¹ := by
    calc _ ≤ ∑ l ∈ range (n - k), B * ρ ^ l := Finset.sum_le_sum fun l _ ↦ (le_abs_self _).trans
          ((h π hπ hinv μ hμ hμV _ _ (hg.sub_const c) (hg.sub_const c) hc0 _ hgM' hgM' k
            l).trans_eq (by rw [hBdef]; ring))
      _ = B * ∑ l ∈ range (n - k), ρ ^ l := (Finset.mul_sum _ _ _).symm
      _ ≤ B * (1 - ρ)⁻¹ := mul_le_mul_of_nonneg_left (((summable_geometric_of_lt_one hρ0
          hρ).sum_le_tsum _ fun _ _ ↦ pow_nonneg hρ0 _).trans_eq
            (tsum_geometric_of_lt_one hρ0 hρ)) hB
  rw [integral_sq_sum_range_eq (fun k ↦ memLp_comp_chain_comp_of_drift hV hdrift hμV
    (hg.sub_const c) hgM' k) n]
  calc _ ≤ ∑ k ∈ range n, 2 * (B * (1 - ρ)⁻¹) := Finset.sum_le_sum fun k _ ↦
        (sub_le_self _ (integral_nonneg fun _ ↦ sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hsum k) zero_le_two)
    _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul, hBdef]; ring

/-- **Variance growth with no moment of the initial measure**: under the drift and the
minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), there is `C` with
`∫⁻ (∑_{k < n} (g (ω k) - ∫ g ∂π))² ∂(P.chain ∘ₘ μ) ≤ C M n (μ univ + ∫⁻ V ∂μ)` in `ℝ≥0∞`, for
every invariant law `π`, every measure `μ`, every measurable `g` with `g² ≤ M (1 + V)` and every
`n`. -/
theorem exists_lintegral_sq_sum_sub_le_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C : ℝ≥0, ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π → ∀ μ : Measure X,
      ∀ g : X → ℝ, Measurable g → ∀ M : ℝ≥0, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2) ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (μ Set.univ + ∫⁻ x, V x ∂μ) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  obtain ⟨C, hC, h⟩ :=
    exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  lift C to ℝ≥0 using hC
  refine ⟨C, fun π hπ hinv μ g hg M hgM n ↦ ?_⟩
  have hF : Measurable fun ω : ℕ → X ↦
      ENNReal.ofReal ((∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2) :=
    ((Finset.measurable_sum _ fun k _ ↦
      (hg.comp (measurable_pi_apply k)).sub_const _).pow_const 2).ennreal_ofReal
  have hd (x : X) : ∫⁻ y, V y ∂(Measure.dirac x) ≠ ∞ := by
    rw [lintegral_dirac' _ hV.coe_nnreal_ennreal]
    exact ENNReal.coe_ne_top
  have hint (x : X) : Integrable (fun ω : ℕ → X ↦
      (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2) (P.chain ∘ₘ Measure.dirac x) :=
    (memLp_finsetSum (range n) fun k _ ↦ memLp_comp_chain_comp_of_drift hV hdrift (hd x)
      (hg.sub_const _) (sq_sub_integral_le_of_invariant_of_drift hV hdrift hγ hinv hg hgM)
      k).integrable_sq
  have hb (x : X) := h π hπ hinv (Measure.dirac x) inferInstance (hd x) g hg M hgM n
  simp only [Measure.dirac_bind P.chain.measurable,
    integral_dirac' _ _ hV.coe_nnreal_real.stronglyMeasurable] at hint hb
  have hx (x : X) : ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2)
      ∂(P.chain x) ≤ ((C * M * n * (1 + V x) : ℝ≥0) : ℝ≥0∞) :=
    calc _ = ENNReal.ofReal (∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain x)) :=
        (ofReal_integral_eq_lintegral_ofReal (hint x) (ae_of_all _ fun _ ↦ sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal ((C * M * n * (1 + V x) : ℝ≥0) : ℝ) :=
        ENNReal.ofReal_le_ofReal ((hb x).trans_eq (by push_cast; rfl))
      _ = _ := ENNReal.ofReal_coe_nnreal
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]
  refine (lintegral_mono hx).trans_eq ?_
  simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_natCast]
  have hm : Measurable fun a : X ↦ (1 : ℝ≥0∞) + V a :=
    measurable_const.add hV.coe_nnreal_ennreal
  rw [lintegral_const_mul _ hm, lintegral_add_left measurable_const, lintegral_one]

/-- **The strong law of large numbers for Harris chains, from every point**: under the drift and
the minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), for an invariant law `π` and a
measurable `g` with `g² ≤ M (1 + V)`, from every point `x`,
`n⁻¹ ∑_{k < n} g (ω k) → ∫ g ∂π` for `P.chain x`-almost every trajectory `ω`. -/
theorem ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) (x : X) :
    ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨C, hC, h⟩ :=
    exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  obtain ⟨C₁, ρ₁, hC₁, -, -, h₁⟩ :=
    exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  have hc0 : ∫ x, (g x - ∫ y, g y ∂π) ∂π = 0 := by
    simpa [average_eq_integral] using integral_sub_average π g
  have hgM' := sq_sub_integral_le_of_invariant_of_drift hV hdrift hγ hπ hg hgM
  set c := ∫ y, g y ∂π
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hgM x)) (by positivity)
  have hx : ∫⁻ y, V y ∂(Measure.dirac x) ≠ ∞ := by
    rw [lintegral_dirac' _ hV.coe_nnreal_ennreal]
    exact ENNReal.coe_ne_top
  set A := 1 + ∫ y, (V y : ℝ) ∂Measure.dirac x
  have hA : 0 ≤ A := by positivity
  have hmem (k : ℕ) := memLp_comp_chain_comp_of_drift hV hdrift hx (hg.sub_const c) hgM' k
  have hS (n : ℕ) := h π inferInstance hπ _ inferInstance hx g hg M hgM n
  have hY2 (k : ℕ) := h₁ π inferInstance hπ _ inferInstance hx _ _ (hg.sub_const c)
    (hg.sub_const c) hc0 _ hgM' hgM' k 0
  rw [Measure.dirac_bind P.chain.measurable] at hmem hS hY2
  refine (ProbabilityTheory.ae_tendsto_inv_mul_sum_of_integral_sq_le hmem
    (B := (C + C₁ * (2 * (2 + K / (1 - γ)))) * M * A) (fun n ↦ (hS n).trans ?_)
    fun k ↦ ?_).mono fun ω hω ↦ ?_
  · nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by positivity :
      (0 : ℝ) ≤ 2 * (2 + K / (1 - γ)))) hM) (mul_nonneg hA (Nat.cast_nonneg (α := ℝ) n))]
  · refine ((le_abs_self _).trans_eq' ?_).trans ((hY2 k).trans ?_)
    · simp [sq]
    · rw [pow_zero, mul_one]
      nlinarith [mul_nonneg (mul_nonneg hC hM) hA]
  · have h0 := hω.add_const c
    rw [zero_add] at h0
    refine h0.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
    beta_reduce
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul, mul_sub,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (by omega)), sub_add_cancel]

/-- **The strong law of large numbers for Harris chains, from every initial measure**: under the
drift and the minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), for an invariant law
`π` and a measurable `g` with `g² ≤ M (1 + V)`, from every initial measure `μ` (no moment and no
finiteness), `n⁻¹ ∑_{k < n} g (ω k) → ∫ g ∂π` for `P.chain ∘ₘ μ`-almost every `ω`. -/
theorem ae_tendsto_inv_mul_sum_chain_comp_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) (μ : Measure X) :
    ∀ᵐ ω ∂(P.chain ∘ₘ μ), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) :=
  Measure.ae_comp_of_ae_ae (measurableSet_tendsto _ fun _ ↦ measurable_const.mul
    (Finset.measurable_sum _ fun k _ ↦ hg.comp (measurable_pi_apply k)))
    (ae_of_all _ (ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow hV hdrift hα hR hmin
      hπ hg hgM))

/-! ### The asymptotic variance -/

/-- **A power below a product of square roots**: for `0 ≤ ρ ≤ 1` and `k ≤ l`,
`ρ ^ l ≤ √ρ ^ k * √ρ ^ l`. -/
theorem _root_.Real.pow_le_sqrt_pow_mul_sqrt_pow {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {k l : ℕ}
    (hkl : k ≤ l) : ρ ^ l ≤ √ρ ^ k * √ρ ^ l :=
  calc ρ ^ l = √ρ ^ l * √ρ ^ l := by rw [← mul_pow, Real.mul_self_sqrt h0]
    _ ≤ √ρ ^ k * √ρ ^ l := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 h1) hkl)
        (pow_nonneg (Real.sqrt_nonneg _) _)

/-- **Cesàro means of lag sums**: if `|a k l - b l| ≤ E rᵏ rˡ` with `0 ≤ r < 1` and `b` is
summable, then `n⁻¹ ∑_{k < n} (2 ∑_{l < n - k} a k l - a k 0) → 2 ∑' l, b l - b 0`. -/
theorem _root_.Filter.tendsto_inv_mul_sum_two_mul_sum_sub_of_abs_sub_le {a : ℕ → ℕ → ℝ}
    {b : ℕ → ℝ} {E r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hab : ∀ k l, |a k l - b l| ≤ E * r ^ k * r ^ l) (hb : Summable b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), a k l - a k 0))
      atTop (𝓝 (2 * ∑' l, b l - b 0)) := by
  have hE : 0 ≤ E := by simpa using (abs_nonneg _).trans (hab 0 0)
  have hgeom (N : ℕ) : ∑ l ∈ range N, r ^ l ≤ (1 - r)⁻¹ :=
    ((summable_geometric_of_lt_one hr0 hr).sum_le_tsum _ fun _ _ ↦ pow_nonneg hr0 _).trans_eq
      (tsum_geometric_of_lt_one hr0 hr)
  have h1 : (1 : ℝ) ≤ (1 - r)⁻¹ := (one_le_inv₀ (sub_pos.2 hr)).2 (by linarith)
  have hk (N k : ℕ) : |2 * ∑ l ∈ range N, a k l - a k 0 - (2 * ∑ l ∈ range N, b l - b 0)| ≤
      3 * E * (1 - r)⁻¹ * r ^ k := by
    rw [show 2 * ∑ l ∈ range N, a k l - a k 0 - (2 * ∑ l ∈ range N, b l - b 0) =
        2 * ∑ l ∈ range N, (a k l - b l) - (a k 0 - b 0) by rw [Finset.sum_sub_distrib]; ring]
    calc _ ≤ 2 * ∑ l ∈ range N, |a k l - b l| + |a k 0 - b 0| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) zero_le_two
      _ ≤ 2 * (E * r ^ k * ∑ l ∈ range N, r ^ l) + E * r ^ k * (1 - r)⁻¹ := by
          gcongr
          · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun l _ ↦ hab k l
          · exact (hab k 0).trans (by
              rw [pow_zero, mul_one]; exact le_mul_of_one_le_right (by positivity) h1)
      _ ≤ 2 * (E * r ^ k * (1 - r)⁻¹) + E * r ^ k * (1 - r)⁻¹ := by gcongr; exact hgeom N
      _ = 3 * E * (1 - r)⁻¹ * r ^ k := by ring
  have hU (n : ℕ) : ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), b l - b 0) =
      ∑ j ∈ range n, (2 * ∑ l ∈ range (j + 1), b l - b 0) := by
    rw [← Finset.sum_range_reflect]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [mem_range] at hj; rw [show n - (n - 1 - j) = j + 1 by omega]
  have h0 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      (∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), a k l - a k 0) -
        ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), b l - b 0))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) (by
      simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (3 * E * (1 - r)⁻¹ * (1 - r)⁻¹))
    rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun k _ ↦ hk (n - k) k).trans ?_)) (by positivity)
    exact (Finset.mul_sum _ _ _).symm.trans_le (mul_le_mul_of_nonneg_left (hgeom n) (by positivity))
  have h := (((hb.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul 2).sub_const
    (b 0)).cesaro.add h0
  rw [add_zero] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, ← hU n]
  ring

/-- **The correlations of a Harris chain approach the stationary ones**: under the drift and the
minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), there are `C ≥ 0` and `0 ≤ r < 1`
with `|∫ ψ (ω k) φ (ω (k + l)) ∂(P.chain ∘ₘ μ) - ∫ ψ · Pˡφ ∂π| ≤ C rᵏ rˡ M (1 + ∫ V ∂μ)` for
every invariant law `π`, every initial law `μ` integrating `V`, all times `k`, `l` and all
measurable `φ`, `ψ` with `φ², ψ² ≤ M (1 + V)` and `∫ φ ∂π = 0`. -/
theorem exists_abs_integral_comp_mul_comp_chain_sub_le_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ φ ψ : X → ℝ, Measurable φ → Measurable ψ → ∫ x, φ x ∂π = 0 → ∀ M : ℝ,
      (∀ x, φ x ^ 2 ≤ M * (1 + V x)) → (∀ x, ψ x ^ 2 ≤ M * (1 + V x)) → ∀ k l : ℕ,
        |∫ ω, ψ (ω k) * φ (ω (k + l)) ∂(P.chain ∘ₘ μ) -
          ∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂π| ≤
            C * r ^ k * r ^ l * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  obtain ⟨C₁, ρ₁, hC₁, hρ₁0, hρ₁, h₁⟩ :=
    exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  obtain ⟨C₂, ρ₂, hC₂, hρ₂0, hρ₂, h₂⟩ :=
    exists_abs_integral_mul_integral_comp_pow_sub_le_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  obtain ⟨C₃, ρ₃, hC₃, hρ₃0, hρ₃, h₃⟩ :=
    exists_abs_integral_mul_integral_pow_sub_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  have hρ0 : 0 ≤ max ρ₁ (max ρ₂ ρ₃) := le_max_of_le_left hρ₁0
  have hρ1 : max ρ₁ (max ρ₂ ρ₃) < 1 := max_lt hρ₁ (max_lt hρ₂ hρ₃)
  refine ⟨C₁ + C₂ + C₃, √(max ρ₁ (max ρ₂ ρ₃)), by positivity, Real.sqrt_nonneg _,
    (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hρ1),
    fun π hπ hinv μ hμ hμV φ ψ hφ hψ hφ0 M hφM hψM k l ↦ ?_⟩
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans
    (hψM (nonempty_of_isProbabilityMeasure μ).some)) (by positivity)
  have hI : 0 ≤ ∫ x, (V x : ℝ) ∂μ := integral_nonneg fun _ ↦ (V _).coe_nonneg
  have hs0 : 0 ≤ √(max ρ₁ (max ρ₂ ρ₃)) ^ k * √(max ρ₁ (max ρ₂ ρ₃)) ^ l := by positivity
  have hA := h₂ π hπ hinv μ hμ hμV φ ψ hφ hψ M hφM hψM k l
  rw [← integral_comp_mul_comp_chain_comp P μ k l hφ.aemeasurable hψ.aemeasurable
    ((memLp_comp_chain_comp_of_drift hV hdrift hμV hψ hψM k).integrable_mul
      (memLp_comp_chain_comp_of_drift hV hdrift hμV hφ hφM (k + l)))] at hA
  have hb := h₃ π hπ hinv φ ψ hφ hψ M hφM hψM l
  rw [hφ0, mul_zero, sub_zero] at hb
  rcases le_total k l with hkl | hlk
  · have hs := Real.pow_le_sqrt_pow_mul_sqrt_pow hρ0 hρ1.le hkl
    calc _ ≤ C₁ * ρ₁ ^ l * M * (1 + ∫ x, (V x : ℝ) ∂μ) + C₃ * ρ₃ ^ l * M := (abs_sub _ _).trans
          (add_le_add (h₁ π hπ hinv μ hμ hμV φ ψ hφ hψ hφ0 M hφM hψM k l) hb)
      _ ≤ C₁ * (√(max ρ₁ (max ρ₂ ρ₃)) ^ k * √(max ρ₁ (max ρ₂ ρ₃)) ^ l) * M *
          (1 + ∫ x, (V x : ℝ) ∂μ) + C₃ * (√(max ρ₁ (max ρ₂ ρ₃)) ^ k *
            √(max ρ₁ (max ρ₂ ρ₃)) ^ l) * M := by
          gcongr
          · exact (pow_le_pow_left₀ hρ₁0 (le_max_left _ _) l).trans hs
          · exact (pow_le_pow_left₀ hρ₃0 (le_max_of_le_right (le_max_right _ _)) l).trans hs
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC₂ hs0) (mul_nonneg hM
          (add_nonneg zero_le_one hI)), mul_nonneg (mul_nonneg hC₃ hs0) (mul_nonneg hM hI)]
  · refine hA.trans ?_
    gcongr ?_ * M * _
    rw [mul_assoc]
    exact mul_le_mul (by linarith) ((pow_le_pow_left₀ hρ₂0 (le_max_of_le_right
      (le_max_left _ _)) k).trans ((Real.pow_le_sqrt_pow_mul_sqrt_pow hρ0 hρ1.le hlk).trans_eq
        (mul_comm _ _))) (by positivity) (by positivity)

/-- **The covariances of the stationary chain**: for an invariant probability measure `π` and
`g` square integrable under `π`, the covariance of `g (ω 0)` and `g (ω l)` under `P.chain ∘ₘ π` is
`∫ ḡ · (∫ ḡ ∂(P ^ l ·)) ∂π`, where `ḡ = g - ∫ g ∂π`. -/
theorem covariance_comp_chain_comp_of_invariant [IsMarkovKernel P] {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) {g : X → ℝ} (hg : MemLp g 2 π) (l : ℕ) :
    cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω l); P.chain ∘ₘ π] =
      ∫ x, (g x - ∫ y, g y ∂π) * ∫ y, (g y - ∫ z, g z ∂π) ∂((P ^ l) x) ∂π := by
  have hlaw (j : ℕ) : (P.chain ∘ₘ π).map (fun ω ↦ ω j) = π := by
    rw [Measure.map_comp _ _ (measurable_pi_apply j), chain_map_eval, (hπ.pow j).def]
  have hmean (j : ℕ) : ∫ ω, g (ω j) ∂(P.chain ∘ₘ π) = ∫ y, g y ∂π := by
    rw [← integral_map (measurable_pi_apply j).aemeasurable
      (by rw [hlaw j]; exact hg.aestronglyMeasurable), hlaw j]
  have hmem (j : ℕ) : MemLp (fun ω ↦ g (ω j) - ∫ y, g y ∂π) 2 (P.chain ∘ₘ π) :=
    ((memLp_map_measure_iff (by rw [hlaw j]; exact hg.aestronglyMeasurable)
      (measurable_pi_apply j).aemeasurable).1 (by rw [hlaw j]; exact hg)).sub (memLp_const _)
  have hc (j : ℕ) : AEMeasurable (fun x ↦ g x - ∫ y, g y ∂π) ((P ^ j : Kernel X X) ∘ₘ π) := by
    rw [(hπ.pow j).def]
    exact hg.aestronglyMeasurable.aemeasurable.sub_const _
  simp only [covariance, hmean]
  simpa only [zero_add, (hπ.pow 0).def] using integral_comp_mul_comp_chain_comp P π 0 l
    (hc (0 + l)) (hc 0) ((hmem 0).integrable_mul (hmem (0 + l)))

/-- **The variance at a time of the stationary chain**: for an invariant measure `π` and `g`
almost everywhere measurable under `π`, the variance of `g (ω j)` under `P.chain ∘ₘ π` is the
variance of `g` under `π`. -/
theorem variance_comp_chain_comp_of_invariant [IsMarkovKernel P] {π : Measure X}
    (hπ : Invariant P π) {g : X → ℝ} (hg : AEMeasurable g π) (j : ℕ) :
    Var[fun ω ↦ g (ω j); P.chain ∘ₘ π] = Var[g; π] := by
  have hlaw : (P.chain ∘ₘ π).map (fun ω ↦ ω j) = π := by
    rw [Measure.map_comp _ _ (measurable_pi_apply j), chain_map_eval, (hπ.pow j).def]
  exact (variance_map (μ := P.chain ∘ₘ π) (X := g) (Y := fun ω ↦ ω j) (by rwa [hlaw])
    (measurable_pi_apply j).aemeasurable).symm.trans (by rw [hlaw])

/-- **The covariances of the stationary chain are summable**: under the drift and the
minorization of `P ^ m` on `{V ≤ R}` (`α > 0`, `K + γ R < R`), for an invariant law `π` and a
measurable `g` with `g² ≤ M (1 + V)`, the covariances `cov[g (ω 0), g (ω l)]` under
`P.chain ∘ₘ π` are bounded by a geometric sequence. -/
theorem summable_covariance_comp_chain_comp_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) :
    Summable (fun l ↦ cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω l); P.chain ∘ₘ π]) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  obtain ⟨C₃, ρ₃, -, hρ₃0, hρ₃, h₃⟩ :=
    exists_abs_integral_mul_integral_pow_sub_le_of_drift_of_minorization_pow hV hdrift hα hR hmin
  have hc0 : ∫ x, (g x - ∫ y, g y ∂π) ∂π = 0 := by
    simpa [average_eq_integral] using integral_sub_average π g
  have hgM' := sq_sub_integral_le_of_invariant_of_drift hV hdrift hγ hπ hg hgM
  have hcov := covariance_comp_chain_comp_of_invariant (P := P) hπ (memLp_two_of_sq_le
    hg.aestronglyMeasurable (((integrable_const 1).add
      (integrable_of_invariant_of_drift hV hdrift hγ hπ)).const_mul M) hgM)
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ₃0 hρ₃).mul_left
    (C₃ * (2 * (2 + K / (1 - γ)) * M))) fun l ↦ ?_
  rw [hcov, Real.norm_eq_abs]
  refine (Eq.trans_le ?_ (h₃ π inferInstance hπ _ _ (hg.sub_const (∫ y, g y ∂π))
    (hg.sub_const (∫ y, g y ∂π)) _ hgM' hgM' l)).trans_eq (by ring)
  rw [hc0, mul_zero, sub_zero]

/-- **The asymptotic variance of a Harris chain**: under the drift and the minorization of `P ^ m`
on `{V ≤ R}` (`α > 0`, `K + γ R < R`), for an invariant law `π`, an initial law `μ` integrating `V`
and a measurable `g` with `g² ≤ M (1 + V)`,
`n⁻¹ ∫ (∑_{k < n} (g (ω k) - ∫ g ∂π))² ∂(P.chain ∘ₘ μ) → Var[g (ω 0)] + 2 ∑_{l ≥ 1} cov[g (ω 0),
g (ω l)]`, the variance and the covariances under `P.chain ∘ₘ π`. -/
theorem tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {μ : Measure X} [IsProbabilityMeasure μ] (hμ : ∫⁻ x, V x ∂μ ≠ ∞)
    {g : X → ℝ} (hg : Measurable g) {M : ℝ} (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π])) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  obtain ⟨C, r, -, hr0, hr, h⟩ :=
    exists_abs_integral_comp_mul_comp_chain_sub_le_of_drift_of_minorization_pow hV hdrift hα hR
      hmin
  have hc0 : ∫ x, (g x - ∫ y, g y ∂π) ∂π = 0 := by
    simpa [average_eq_integral] using integral_sub_average π g
  have hgM' := sq_sub_integral_le_of_invariant_of_drift hV hdrift hγ hπ hg hgM
  have hcov := covariance_comp_chain_comp_of_invariant (P := P) hπ (memLp_two_of_sq_le
    hg.aestronglyMeasurable (((integrable_const 1).add
      (integrable_of_invariant_of_drift hV hdrift hγ hπ)).const_mul M) hgM)
  have hsum :=
    summable_covariance_comp_chain_comp_of_drift_of_minorization_pow hV hdrift hα hR hmin hπ hg hgM
  set c := ∫ x, g x ∂π
  rw [← covariance_self (X := fun ω : ℕ → X ↦ g (ω 0))
      (hg.comp (measurable_pi_apply 0)).aemeasurable,
    show cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
      2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π] =
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω l); P.chain ∘ₘ π] -
          cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω 0); P.chain ∘ₘ π] by
      rw [hsum.tsum_eq_zero_add]; ring]
  refine (Filter.tendsto_inv_mul_sum_two_mul_sum_sub_of_abs_sub_le hr0 hr
    (a := fun k l ↦ ∫ ω, (g (ω k) - c) * (g (ω (k + l)) - c) ∂(P.chain ∘ₘ μ))
    (E := C * (2 * (2 + K / (1 - γ)) * M) * (1 + ∫ x, (V x : ℝ) ∂μ)) (fun k l ↦ ?_)
    hsum).congr fun n ↦ ?_
  · rw [hcov]
    exact (h π inferInstance hπ μ inferInstance hμ _ _ (hg.sub_const c) (hg.sub_const c) hc0 _
      hgM' hgM' k l).trans_eq (by ring)
  · rw [integral_sq_sum_range_eq (fun k ↦ memLp_comp_chain_comp_of_drift hV hdrift hμ
      (hg.sub_const c) hgM' k) n]
    simp only [add_zero, sq]

/-- **The asymptotic variance is nonnegative**: under the drift and the minorization of `P ^ m`
on `{V ≤ R}` (`α > 0`, `K + γ R < R`), for an invariant law `π` and a measurable `g` with
`g² ≤ M (1 + V)`, `0 ≤ Var[g (ω 0)] + 2 ∑_{l ≥ 1} cov[g (ω 0), g (ω l)]` under `P.chain ∘ₘ π`. -/
theorem variance_add_two_mul_tsum_covariance_comp_chain_comp_nonneg_of_drift_of_minorization_pow
    [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : Invariant P π) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) :
    0 ≤ Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
      2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π] :=
  ge_of_tendsto' (tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow hV hdrift hα
    hR hmin hπ (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top (tsub_pos_of_lt
      (by exact_mod_cast NNReal.lt_one_of_add_mul_lt hR)).ne')
        (lintegral_le_of_invariant_of_drift hV hdrift (NNReal.lt_one_of_add_mul_lt hR) hπ))
    hg hgM) fun n ↦ mul_nonneg (inv_nonneg.2 n.cast_nonneg) (integral_nonneg fun _ ↦ sq_nonneg _)

/-! ### The hypotheses are forced, and they hold together -/

/-- **The class `g² ≤ M (1 + V)` is the class of the variance growth**: at `n = 1` from a point
`x`, the left side of the bound is `(g x - c)²`, so a bound `B (1 + V x)` for it is a bound of
this form for `g - c`. -/
example [IsMarkovKernel P] {g : X → ℝ} (hg : Measurable g) (c : ℝ) (x : X) :
    ∫ ω, (∑ k ∈ range 1, (g (ω k) - c)) ^ 2 ∂(P.chain x) = (g x - c) ^ 2 := by
  have hF : Measurable fun y : X ↦ (g y - c) ^ 2 := (hg.sub_const c).pow_const 2
  have h := integral_map (μ := P.chain x) (measurable_pi_apply 0).aemeasurable
    hF.aestronglyMeasurable
  rw [← map_apply _ (measurable_pi_apply 0), chain_map_eval, pow_zero] at h
  simp only [sum_range_one]
  rw [← h]
  change ∫ y, (g y - c) ^ 2 ∂(Kernel.id x) = _
  rw [Kernel.id_apply]
  exact integral_dirac' _ _ hF.stronglyMeasurable

/-- **The identity chain stays at its start**: with measurable singletons, from every point `x`,
`n⁻¹ ∑_{k < n} g (ω k) → g x` for `Kernel.id.chain x`-almost every `ω`. -/
theorem ae_tendsto_inv_mul_sum_chain_id [MeasurableSingletonClass X] (g : X → ℝ) (x : X) :
    ∀ᵐ ω ∂((Kernel.id : Kernel X X).chain x),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop (𝓝 (g x)) := by
  filter_upwards [ae_forall_eq_iterate_chain_deterministic measurable_id x] with ω hω
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  simp only [hω, Function.iterate_id, id_eq, Finset.sum_const, card_range, nsmul_eq_mul]
  rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (by omega))]

/-- **The strong law fails for the identity kernel of `Bool`**: every Dirac mass is invariant,
and from `false` the fraction of time spent at `true` tends to `0`, not to the mass `1` of `true`
under the invariant law `dirac true`. -/
theorem not_forall_ae_tendsto_inv_mul_sum_chain_id_bool :
    ¬ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant (Kernel.id : Kernel Bool Bool) π →
      ∀ x, ∀ᵐ ω ∂((Kernel.id : Kernel Bool Bool).chain x),
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (if ω k then (1 : ℝ) else 0)) atTop
          (𝓝 (∫ y, (if y then (1 : ℝ) else 0) ∂π)) := fun h ↦ by
  obtain ⟨ω, h1, h2⟩ := ((h (Measure.dirac true) inferInstance Measure.id_comp false).and
    (ae_tendsto_inv_mul_sum_chain_id (fun y : Bool ↦ if y then (1 : ℝ) else 0) false)).exists
  simpa using tendsto_nhds_unique h1 h2

/-- **The centered sums of the identity chain of `Bool` grow linearly**: from `false`, with the
invariant law `dirac true` and `g = 1_{true}`, every centered summand is `-1`, so
`∫ (∑_{k < n} (g (ω k) - ∫ g ∂(dirac true)))² ∂(Kernel.id.chain false) = n²`. -/
theorem integral_sq_sum_sub_chain_id_bool (n : ℕ) :
    ∫ ω, (∑ k ∈ range n, ((if ω k then (1 : ℝ) else 0) -
      ∫ y, (if y then (1 : ℝ) else 0) ∂Measure.dirac true)) ^ 2
        ∂((Kernel.id : Kernel Bool Bool).chain false) = (n : ℝ) ^ 2 := by
  rw [integral_congr_ae (g := fun _ ↦ (n : ℝ) ^ 2)]
  · simp
  filter_upwards [ae_forall_eq_iterate_chain_deterministic measurable_id false] with ω hω
  simp [hω]

/-- **The variance growth fails for the identity kernel of `Bool`**: for every `V` with
`V false = 0` and every `C`, the bound of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` fails for `Kernel.id` (at
`π = dirac true`, `μ = dirac false`, `g = 1_{true}`, `M = 1`, where the second moment is `n²`). -/
theorem not_forall_integral_sq_sum_sub_chain_id_bool_le {V : Bool → ℝ≥0} (hV0 : V false = 0)
    (C : ℝ) :
    ¬ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant (Kernel.id : Kernel Bool Bool) π →
      ∀ μ : Measure Bool, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2
          ∂((Kernel.id : Kernel Bool Bool).chain ∘ₘ μ) ≤
            C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  intro hC
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  have h := hC (Measure.dirac true) inferInstance Measure.id_comp (Measure.dirac false)
    inferInstance (by simp) (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
    (fun y ↦ by cases y <;> simp [hV0]) n
  rw [Measure.dirac_bind (Kernel.measurable _), integral_sq_sum_sub_chain_id_bool,
    integral_dirac, hV0] at h
  nlinarith [le_max_left C 0, le_max_right C 0, (by simpa using h : (n : ℝ) ^ 2 ≤ C * n)]

/-- **The asymptotic variance fails for the identity kernel of `Bool`**: for every `V` with
`V false = 0`, the limit of `tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow`
fails for `Kernel.id` (at `π = dirac true`, `μ = dirac false`, `g = 1_{true}`, `M = 1`, where
`n⁻¹ ∫ (∑_{k < n} (g (ω k) - ∫ g ∂π))² = n` has no limit). -/
theorem not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool {V : Bool → ℝ≥0}
    (hV0 : V false = 0) :
    ¬ ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant (Kernel.id : Kernel Bool Bool) π →
    ∀ (μ : Measure Bool) [IsProbabilityMeasure μ], ∫⁻ x, V x ∂μ ≠ ∞ → ∀ g : Bool → ℝ,
    Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2
          ∂((Kernel.id : Kernel Bool Bool).chain ∘ₘ μ)) atTop
        (𝓝 (Var[fun ω ↦ g (ω 0); (Kernel.id : Kernel Bool Bool).chain ∘ₘ π] +
          2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1));
            (Kernel.id : Kernel Bool Bool).chain ∘ₘ π])) := by
  intro h
  have hσ := h (Measure.dirac true) Measure.id_comp (Measure.dirac false) (by simp)
    (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
    (fun y ↦ by cases y <;> simp [hV0])
  simp only [Measure.dirac_bind (Kernel.measurable _), integral_sq_sum_sub_chain_id_bool] at hσ
  refine not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop _
    (hσ.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩))
  rw [sq, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (by omega))]

/-- **The threshold `K + γ R < R` is forced in the strong law**: the statement of
`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow` at `X = Bool` with
`K + γ * R < R` left out, and nothing else changed, is false, by the identity kernel with
`V = 1_{true}`, `γ = 0`, `K = 1`, `R = 0`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    ∀ x, ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) := fun h ↦
  not_forall_ae_tendsto_inv_mul_sum_chain_id_bool fun π _ hπ x ↦
    h Kernel.id (fun y ↦ if y then 1 else 0) 0 1 (measurable_of_countable _)
      (fun x ↦ by cases x <;> simp [Kernel.id_apply]) (Measure.dirac false) 1 0 1 one_pos
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => simp at hx) π hπ
      (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
      (fun y ↦ by cases y <;> norm_num) x

/-- **The drift is forced in the strong law**: the statement of
`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow` at `X = Bool` with
the drift left out, and nothing else changed, is false, by the identity kernel with
`V = 2 · 1_{true}`, `γ = K = 0`, `R = 1`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α → K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    ∀ x, ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) := fun h ↦
  not_forall_ae_tendsto_inv_mul_sum_chain_id_bool fun π _ hπ x ↦
    h Kernel.id (fun y ↦ if y then 2 else 0) 0 0 (measurable_of_countable _)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num)
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => norm_num at hx) π hπ
      (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
      (fun y ↦ by cases y <;> norm_num) x

/-- **The minorization is forced in the strong law**: the statement of
`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow` at `X = Bool` with
the minorization left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (_ : ℕ), 0 < α → K + γ * R < R →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    ∀ x, ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) := fun h ↦
  not_forall_ae_tendsto_inv_mul_sum_chain_id_bool fun π _ hπ x ↦
    h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num) π hπ
      (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
      (fun y ↦ by cases y <;> norm_num) x

/-- **`α > 0` is forced in the strong law**: the statement of
`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow` at `X = Bool` with
`0 < α` left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 0`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    ∀ x, ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g (ω k)) atTop
      (𝓝 (∫ y, g y ∂π)) := fun h ↦
  not_forall_ae_tendsto_inv_mul_sum_chain_id_bool fun π _ hπ x ↦
    h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 0 1 1 (by norm_num)
      (fun _ _ ↦ by rw [zero_smul]; exact Measure.zero_le _) π hπ
      (fun y ↦ if y then 1 else 0) (measurable_of_countable _) 1
      (fun y ↦ by cases y <;> norm_num) x

/-- **The threshold `K + γ R < R` is forced in the variance growth**: the statement of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` at `X = Bool` with
`K + γ * R < R` left out, and nothing else changed, is false, by the identity kernel with
`V = 1_{true}`, `γ = 0`, `K = 1`, `R = 0`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure Bool, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := fun h ↦ by
  obtain ⟨C, -, hC⟩ :=
    h Kernel.id (fun y ↦ if y then 1 else 0) 0 1 (measurable_of_countable _)
      (fun x ↦ by cases x <;> simp [Kernel.id_apply]) (Measure.dirac false) 1 0 1 one_pos
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => simp at hx)
  exact not_forall_integral_sq_sum_sub_chain_id_bool_le (by simp) C hC

/-- **The drift is forced in the variance growth**: the statement of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` at `X = Bool` with
the drift left out, and nothing else changed, is false, by the identity kernel with
`V = 2 · 1_{true}`, `γ = K = 0`, `R = 1`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α → K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure Bool, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := fun h ↦ by
  obtain ⟨C, -, hC⟩ :=
    h Kernel.id (fun y ↦ if y then 2 else 0) 0 0 (measurable_of_countable _)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num)
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => norm_num at hx)
  exact not_forall_integral_sq_sum_sub_chain_id_bool_le (by simp) C hC

/-- **The minorization is forced in the variance growth**: the statement of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` at `X = Bool` with
the minorization left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (_ : ℕ), 0 < α → K + γ * R < R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure Bool, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := fun h ↦ by
  obtain ⟨C, -, hC⟩ :=
    h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num)
  exact not_forall_integral_sq_sum_sub_chain_id_bool_le rfl C hC

/-- **`α > 0` is forced in the variance growth**: the statement of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` at `X = Bool` with
`0 < α` left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 0`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure Bool, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ g : Bool → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ) := fun h ↦ by
  obtain ⟨C, -, hC⟩ :=
    h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 0 1 1 (by norm_num)
      (fun _ _ ↦ by rw [zero_smul]; exact Measure.zero_le _)
  exact not_forall_integral_sq_sum_sub_chain_id_bool_le rfl C hC

/-- **The threshold `K + γ R < R` is forced in the asymptotic variance**: the statement of
`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow` at `X = Bool` with
`K + γ * R < R` left out, and nothing else changed, is false, by the identity kernel with
`V = 1_{true}`, `γ = 0`, `K = 1`, `R = 0`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ (μ : Measure Bool) [IsProbabilityMeasure μ], ∫⁻ x, V x ∂μ ≠ ∞ → ∀ g : Bool → ℝ,
    Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π])) := fun h ↦
  not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool (by simp)
    fun π _ hπ μ _ hμ g hg M hgM ↦
      h Kernel.id (fun y ↦ if y then 1 else 0) 0 1 (measurable_of_countable _)
      (fun x ↦ by cases x <;> simp [Kernel.id_apply]) (Measure.dirac false) 1 0 1 one_pos
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => simp at hx) π hπ μ hμ g hg M hgM

/-- **The drift is forced in the asymptotic variance**: the statement of
`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow` at `X = Bool` with
the drift left out, and nothing else changed, is false, by the identity kernel with
`V = 2 · 1_{true}`, `γ = K = 0`, `R = 1`, `ν = dirac false`, `α = 1`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), 0 < α → K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ (μ : Measure Bool) [IsProbabilityMeasure μ], ∫⁻ x, V x ∂μ ≠ ∞ → ∀ g : Bool → ℝ,
    Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π])) := fun h ↦
  not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool (by simp)
    fun π _ hπ μ _ hμ g hg M hgM ↦
      h Kernel.id (fun y ↦ if y then 2 else 0) 0 0 (measurable_of_countable _)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num)
      (fun x hx ↦ by
        cases x with
        | false => simp [Kernel.id_apply]
        | true => norm_num at hx) π hπ μ hμ g hg M hgM

/-- **The minorization is forced in the asymptotic variance**: the statement of
`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow` at `X = Bool` with
the minorization left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (_ : ℕ), 0 < α → K + γ * R < R →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ (μ : Measure Bool) [IsProbabilityMeasure μ], ∫⁻ x, V x ∂μ ≠ ∞ → ∀ g : Bool → ℝ,
    Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π])) := fun h ↦
  not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool rfl
    fun π _ hπ μ _ hμ g hg M hgM ↦
      h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 1 1 1 one_pos (by norm_num) π hπ μ hμ g hg M hgM

/-- **`α > 0` is forced in the asymptotic variance**: the statement of
`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow` at `X = Bool` with
`0 < α` left out, and nothing else changed, is false, by the identity kernel with
`V = 0`, `γ = K = 0`, `R = 1`, `α = 0`, `m = 1`. -/
example : ¬ ∀ (P : Kernel Bool Bool) [IsMarkovKernel P] (V : Bool → ℝ≥0) (γ K : ℝ≥0),
    Measurable V → (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) →
    ∀ (ν : Measure Bool) [IsProbabilityMeasure ν] (α R : ℝ≥0) (m : ℕ), K + γ * R < R →
    (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure Bool) [IsProbabilityMeasure π], Invariant P π →
    ∀ (μ : Measure Bool) [IsProbabilityMeasure μ], ∫⁻ x, V x ∂μ ≠ ∞ → ∀ g : Bool → ℝ,
    Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π])) := fun h ↦
  not_forall_tendsto_inv_mul_integral_sq_sum_sub_chain_id_bool rfl
    fun π _ hπ μ _ hμ g hg M hgM ↦
      h Kernel.id (fun _ ↦ 0) 0 0 (measurable_of_countable _) (fun _ ↦ by simp)
      (Measure.dirac false) 0 1 1 (by norm_num)
      (fun _ _ ↦ by rw [zero_smul]; exact Measure.zero_le _) π hπ μ hμ g hg M hgM

/-- **A law with the masses `2⁻⁽ʲ⁺¹⁾`**: `∑ⱼ 2⁻⁽ʲ⁺¹⁾ δ_{x j}` is a probability measure. -/
theorem _root_.MeasureTheory.isProbabilityMeasure_sum_inv_two_pow_smul_dirac {α : Type*}
    [MeasurableSpace α] (x : ℕ → α) :
    IsProbabilityMeasure
      (Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (x j)) := ⟨by
  simp only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one, ENNReal.inv_pow]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

/-- **The descent `x ↦ x - 1` on `ℕ`** with `V x = 2ˣ` has the drift with `γ = 1/2`, `K = 1`,
the minorization `dirac 0 ≤ P x` on `{V ≤ 3}` (`α = 1`, `m = 1`, and `K + γ R = 5/2 < 3 = R`),
and the invariant law `dirac 0`. -/
theorem drift_and_minorization_descent :
    (∀ x : ℕ, ∫⁻ y, (((2 : ℝ≥0) ^ y : ℝ≥0) : ℝ≥0∞)
        ∂(deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _) x) ≤
      (1 / 2 : ℝ≥0) * ((2 : ℝ≥0) ^ x : ℝ≥0) + (1 : ℝ≥0)) ∧
    (∀ x : ℕ, ((2 : ℝ≥0) ^ x : ℝ≥0) ≤ 3 → (1 : ℝ≥0) • Measure.dirac 0 ≤
      (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _) ^ 1) x) ∧
    Invariant (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _))
      (Measure.dirac 0) := by
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have h2 : (2 : ℝ≥0) ^ (x - 1) ≤ 1 / 2 * 2 ^ x + 1 := by
      rcases x with _ | x
      · rw [Nat.zero_sub, pow_zero, mul_one]
        exact le_add_self
      · rw [Nat.add_sub_cancel, pow_succ, mul_comm (1 / 2 : ℝ≥0), mul_assoc,
          mul_one_div_cancel two_ne_zero, mul_one]
        exact le_self_add
    rw [deterministic_apply, lintegral_dirac]
    exact_mod_cast h2
  · have h4 (hc : 1 < x) : (4 : ℝ≥0) ≤ 2 ^ x :=
      (pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt hc)).trans_eq' (by norm_num)
    have hx1 : x ≤ 1 := not_lt.1 fun hc ↦ absurd ((h4 hc).trans hx) (by norm_num)
    rw [pow_one, deterministic_apply, one_smul, (by omega : x - 1 = 0)]
  · simp [Invariant, Measure.dirac_bind (Kernel.measurable _), deterministic_apply]

/-- **A law with no moment**: `V x = 2ˣ` is not integrable under `∑ⱼ 2⁻⁽ʲ⁺¹⁾ δ_{4ʲ}`. -/
theorem lintegral_two_pow_sum_inv_two_pow_smul_dirac :
    ∫⁻ x, (((2 : ℝ≥0) ^ x : ℝ≥0) : ℝ≥0∞)
      ∂(Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)) = ∞ := by
  rw [lintegral_sum_measure]
  refine top_unique ((ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm.trans_le
    (ENNReal.tsum_le_tsum fun j ↦ ?_))
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hj : j + 1 ≤ 4 ^ j := Nat.lt_pow_self (by norm_num)
  have hle : (2 : ℝ≥0∞) ^ (j + 1) ≤ (((2 : ℝ≥0) ^ 4 ^ j : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_pow]
    exact pow_le_pow_right₀ (by norm_num) hj
  calc (1 : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ * (2 : ℝ≥0∞) ^ (j + 1) :=
        (ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).symm
    _ ≤ _ := by gcongr

/-- **The centered sums of the descent grow linearly before it lands**: from `x ≥ n`, with the
invariant law `dirac 0` and `g = 1_{≠ 0}`, every centered summand before time `n` is `1`, so
`∫ (∑_{k < n} (g (ω k) - ∫ g ∂(dirac 0)))² ∂(P.chain x) = n²`. -/
theorem integral_sq_sum_sub_chain_descent {n x : ℕ} (hnx : n ≤ x) :
    ∫ ω, (∑ k ∈ range n, ((if ω k = 0 then (0 : ℝ) else 1) -
      ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0)) ^ 2
        ∂((deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _)).chain x) =
      (n : ℝ) ^ 2 := by
  have h0 : ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0 = 0 := by simp
  have hit (k : ℕ) : (fun y : ℕ ↦ y - 1)^[k] x = x - k := Nat.pred_iterate x k
  have hs : ∑ k ∈ range n, (if x - k = 0 then (0 : ℝ) else 1) = n := by
    rw [sum_congr rfl fun k hk ↦ ite_eq_right
      (Nat.sub_ne_zero_of_lt ((mem_range.1 hk).trans_le hnx))]
    simp
  rw [integral_congr_ae (g := fun _ ↦ (n : ℝ) ^ 2)]
  · simp
  filter_upwards [ae_forall_eq_iterate_chain_deterministic
    (measurable_of_countable (fun x : ℕ ↦ x - 1)) x] with ω hω
  simp only [h0, hω, hit, sub_zero, hs]

/-- **The second moments from a law with no moment**: for the descent on `ℕ` started at
`∑ⱼ 2⁻⁽ʲ⁺¹⁾ δ_{4ʲ}`, with `π = dirac 0` and `g = 1_{≠ 0}`, the second moment of the centered sum
at `n = 4ᴶ` is at least `2⁻⁽ᴶ⁺¹⁾ n² = n 2ᴶ / 2`: the mass at `4ᴶ` has not landed. -/
theorem le_integral_sq_sum_sub_chain_descent_comp (J : ℕ) :
    (4 : ℝ) ^ J * (2 ^ J / 2) ≤
      ∫ ω, (∑ k ∈ range (4 ^ J), ((if ω k = 0 then (0 : ℝ) else 1) -
        ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0)) ^ 2
          ∂((deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _)).chain ∘ₘ
            Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)) := by
  have := isProbabilityMeasure_sum_inv_two_pow_smul_dirac fun j : ℕ ↦ 4 ^ j
  have h0 : ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0 = 0 := by simp
  have hfm : Measurable fun ω : ℕ → ℕ ↦ (∑ k ∈ range (4 ^ J), ((if ω k = 0 then (0 : ℝ) else 1) -
      ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0)) ^ 2 :=
    (Finset.measurable_sum _ fun k _ ↦ ((measurable_of_countable fun y : ℕ ↦
      if y = 0 then (0 : ℝ) else 1).comp (measurable_pi_apply k)).sub measurable_const).pow_const 2
  have hbd (ω : ℕ → ℕ) : ‖(∑ k ∈ range (4 ^ J), ((if ω k = 0 then (0 : ℝ) else 1) -
      ∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0)) ^ 2‖ ≤ ((4 ^ J : ℕ) : ℝ) ^ 2 := by
    rw [h0, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (sum_nonneg fun k _ ↦ by split_ifs <;> norm_num)
      ((sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun k _ ↦ by split_ifs <;> norm_num).trans_eq
        (by simp)) 2
  have hle : (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _)).chain ∘ₘ
      (((2 : ℝ≥0∞) ^ (J + 1))⁻¹ • Measure.dirac (4 ^ J)) ≤
      (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _)).chain ∘ₘ
        Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j) := by
    refine Measure.le_intro fun s hs _ ↦ ?_
    rw [Measure.bind_apply hs (Kernel.aemeasurable _),
      Measure.bind_apply hs (Kernel.aemeasurable _)]
    exact lintegral_mono' (Measure.le_sum
      (fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)) J) le_rfl
  refine le_trans (le_of_eq ?_) (integral_mono_measure hle (ae_of_all _ fun _ ↦ sq_nonneg _)
    ((integrable_const _).mono' hfm.aestronglyMeasurable (ae_of_all _ hbd)))
  rw [Measure.comp_smul, Measure.dirac_bind (Kernel.measurable _), integral_smul_measure,
    integral_sq_sum_sub_chain_descent le_rfl]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [show (4 : ℝ) ^ J = 2 ^ J * 2 ^ J by rw [← mul_pow]; norm_num, pow_succ]
  field_simp

/-- **The moment of the initial law is forced in the variance growth**: the statement of
`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow` at `X = ℕ` with the hypothesis
`∫⁻ x, V x ∂μ ≠ ∞` left out, and nothing else changed, is false. -/
theorem not_exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow_nat :
    ¬ (∀ (P : Kernel ℕ ℕ) [IsMarkovKernel P] (V : ℕ → ℝ≥0) (γ K : ℝ≥0), Measurable V →
    (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) → ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (α R : ℝ≥0) (m : ℕ), 0 < α → K + γ * R < R → (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Measure ℕ, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure ℕ, IsProbabilityMeasure μ →
      ∀ g : ℕ → ℝ, Measurable g → ∀ M : ℝ, (∀ x, g x ^ 2 ≤ M * (1 + V x)) → ∀ n : ℕ,
        ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ) ≤
          C * M * n * (1 + ∫ x, (V x : ℝ) ∂μ)) := by
  intro h
  obtain ⟨hd, hm, hinv⟩ := drift_and_minorization_descent
  obtain ⟨C, -, hC⟩ := h (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _))
    (fun x ↦ 2 ^ x) (1 / 2) 1 (measurable_of_countable _) hd (Measure.dirac 0) 1 3 1 one_pos
    (by norm_num) hm
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * C)
  have hJ2 : 2 * C < (2 : ℝ) ^ J := hJ.trans (by exact_mod_cast Nat.lt_two_pow_self)
  have hV0 : ∫ x, (((2 : ℝ≥0) ^ x : ℝ≥0) : ℝ)
      ∂(Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)) = 0 :=
    integral_undef fun hi ↦ (lt_top_iff_ne_top.1 (by
      simpa only [ENNReal.ofReal_coe_nnreal] using hi.lintegral_lt_top))
        lintegral_two_pow_sum_inv_two_pow_smul_dirac
  have hb := (le_integral_sq_sum_sub_chain_descent_comp J).trans (hC (Measure.dirac 0)
    inferInstance hinv (Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j))
    (isProbabilityMeasure_sum_inv_two_pow_smul_dirac fun j : ℕ ↦ 4 ^ j)
    (fun y ↦ if y = 0 then 0 else 1) (measurable_of_countable _) 1
    (fun x ↦ by by_cases hx : x = 0 <;> simp [hx]) (4 ^ J))
  rw [hV0] at hb
  push_cast at hb
  nlinarith [(by positivity : (0 : ℝ) < 4 ^ J)]

/-- **The moment of the initial law is forced in the asymptotic variance**: the statement of
`tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow` at `X = ℕ` with the hypothesis
`∫⁻ x, V x ∂μ ≠ ∞` left out, and nothing else changed, is false: for the descent on `ℕ` the
normalized second moments are unbounded along `n = 4ᴶ`. -/
theorem not_tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow_nat :
    ¬ (∀ (P : Kernel ℕ ℕ) [IsMarkovKernel P] (V : ℕ → ℝ≥0) (γ K : ℝ≥0), Measurable V →
    (∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) → ∀ (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (α R : ℝ≥0) (m : ℕ), 0 < α → K + γ * R < R → (∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) →
    ∀ (π : Measure ℕ) [IsProbabilityMeasure π], Invariant P π →
    ∀ (μ : Measure ℕ) [IsProbabilityMeasure μ] (g : ℕ → ℝ), Measurable g → ∀ M : ℝ,
    (∀ x, g x ^ 2 ≤ M * (1 + V x)) →
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∫ ω, (∑ k ∈ range n, (g (ω k) - ∫ x, g x ∂π)) ^ 2 ∂(P.chain ∘ₘ μ)) atTop
      (𝓝 (Var[fun ω ↦ g (ω 0); P.chain ∘ₘ π] +
        2 * ∑' l, cov[fun ω ↦ g (ω 0), fun ω ↦ g (ω (l + 1)); P.chain ∘ₘ π]))) := by
  intro h
  have := isProbabilityMeasure_sum_inv_two_pow_smul_dirac fun j : ℕ ↦ 4 ^ j
  obtain ⟨hd, hm, hinv⟩ := drift_and_minorization_descent
  obtain ⟨B, hB⟩ := (h (deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _))
    (fun x ↦ 2 ^ x) (1 / 2) 1 (measurable_of_countable _) hd
    (Measure.dirac 0) 1 3 1 one_pos (by norm_num) hm (Measure.dirac 0) hinv
    (Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j))
    (fun y ↦ if y = 0 then 0 else 1) (measurable_of_countable _) 1
    (fun x ↦ by by_cases hx : x = 0 <;> simp [hx])).bddAbove_range
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * B)
  have hJ2 : 2 * B < (2 : ℝ) ^ J := hJ.trans (by exact_mod_cast Nat.lt_two_pow_self)
  have hb := hB ⟨4 ^ J, rfl⟩
  have h4 : (0 : ℝ) < 4 ^ J := by positivity
  have hl : 2 ^ J / 2 ≤ ((4 ^ J : ℕ) : ℝ)⁻¹ * ∫ ω, (∑ k ∈ range (4 ^ J),
      ((if ω k = 0 then (0 : ℝ) else 1) - ∫ y, (if y = 0 then (0 : ℝ) else 1)
        ∂Measure.dirac 0)) ^ 2 ∂((deterministic (fun x : ℕ ↦ x - 1)
          (measurable_of_countable _)).chain ∘ₘ
            Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)) := by
    push_cast
    rw [le_inv_mul_iff₀ h4]
    exact le_integral_sq_sum_sub_chain_descent_comp J
  simp only at hb
  linarith

/-- **The strong law needs no moment of the initial law**: for the descent on `ℕ` started at
`∑ⱼ 2⁻⁽ʲ⁺¹⁾ δ_{4ʲ}`, the fraction of time spent off `0` tends to `0`. -/
example : ∀ᵐ ω ∂((deterministic (fun x : ℕ ↦ x - 1) (measurable_of_countable _)).chain ∘ₘ
      Measure.sum fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (j + 1))⁻¹ • Measure.dirac (4 ^ j)),
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (if ω k = 0 then (0 : ℝ) else 1)) atTop
      (𝓝 (∫ y, (if y = 0 then (0 : ℝ) else 1) ∂Measure.dirac 0)) :=
  ae_tendsto_inv_mul_sum_chain_comp_of_drift_of_minorization_pow (V := fun x ↦ 2 ^ x)
    (measurable_of_countable _) drift_and_minorization_descent.1 one_pos (by norm_num)
    drift_and_minorization_descent.2.1 drift_and_minorization_descent.2.2
    (measurable_of_countable _) (M := 1) (fun x ↦ by by_cases hx : x = 0 <;> simp [hx]) _

/-- **The invariant law of the halving chain** of `drift_and_minorization_of_halving`:
`P 0 = (1/2) • dirac 0 + (1/2) • dirac 1` is invariant. -/
theorem invariant_of_halving {P : Kernel ℕ ℕ} (hP : ∀ n, P n = if n ≤ 1 then
    (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1 else Measure.dirac (n / 2)) :
    Invariant P (P 0) := by
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), hP 0]
  simp only [zero_le_one, ↓reduceIte]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac, hP, hP]
  simp only [zero_le_one, le_refl, ↓reduceIte]
  rw [← add_smul, add_halves, one_smul]

/-- **The hypotheses hold together: the halving chain** of `drift_and_minorization_of_halving`
(`V n = n`, `γ = K = 1/2`, the minorization `(1/2) • dirac 1 ≤ P x` on `{V ≤ 3}`) has the invariant
law `P 0 = (1/2) • dirac 0 + (1/2) • dirac 1`, and from every start the chain spends half of its
time at `0`. -/
example {P : Kernel ℕ ℕ} [IsMarkovKernel P] (hP : ∀ n, P n = if n ≤ 1 then
    (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1 else Measure.dirac (n / 2))
    (x : ℕ) :
    ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      Set.indicator {0} (1 : ℕ → ℝ) (ω k)) atTop (𝓝 (1 / 2)) := by
  obtain ⟨-, hd, hm⟩ := drift_and_minorization_of_halving hP
  have h := ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow (P := P)
    (V := fun n : ℕ ↦ (n : ℝ≥0)) (γ := 1 / 2) (K := 1 / 2) (ν := Measure.dirac 1) (α := 1 / 2)
    (R := 3) (m := 1) (measurable_of_countable _) hd (by norm_num) (by norm_num)
    (fun y hy ↦ by rw [pow_one]; exact hm y hy) (invariant_of_halving hP)
    (g := Set.indicator ({0} : Set ℕ) 1) (measurable_of_countable _) (M := 1)
    (fun y ↦ by by_cases hy : y = 0 <;> simp [hy]; positivity) x
  rw [integral_indicator_one (measurableSet_singleton 0)] at h
  convert h using 2
  simp [Measure.real, hP 0]

/-- **The hypotheses of the asymptotic variance hold together: the halving chain**, from every
point `x`, for `g = 1_{0}`. -/
example {P : Kernel ℕ ℕ} [IsMarkovKernel P] (hP : ∀ n, P n = if n ≤ 1 then
    (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1 else Measure.dirac (n / 2))
    (x : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∫ ω, (∑ k ∈ range n,
        (Set.indicator {0} (1 : ℕ → ℝ) (ω k) - ∫ y, Set.indicator {0} (1 : ℕ → ℝ) y ∂(P 0))) ^ 2
          ∂(P.chain ∘ₘ Measure.dirac x)) atTop
      (𝓝 (Var[fun ω ↦ Set.indicator {0} (1 : ℕ → ℝ) (ω 0); P.chain ∘ₘ P 0] +
        2 * ∑' l, cov[fun ω ↦ Set.indicator {0} (1 : ℕ → ℝ) (ω 0),
          fun ω ↦ Set.indicator {0} (1 : ℕ → ℝ) (ω (l + 1)); P.chain ∘ₘ P 0])) := by
  obtain ⟨-, hd, hm⟩ := drift_and_minorization_of_halving hP
  exact tendsto_inv_mul_integral_sq_sum_sub_of_drift_of_minorization_pow (P := P)
    (V := fun n : ℕ ↦ (n : ℝ≥0)) (γ := 1 / 2) (K := 1 / 2) (ν := Measure.dirac 1) (α := 1 / 2)
    (R := 3) (m := 1) (measurable_of_countable _) hd (by norm_num) (by norm_num)
    (fun y hy ↦ by rw [pow_one]; exact hm y hy) (invariant_of_halving hP) (μ := Measure.dirac x)
    (by rw [lintegral_dirac' _ (measurable_of_countable _)]; exact ENNReal.coe_ne_top)
    (g := Set.indicator ({0} : Set ℕ) 1) (measurable_of_countable _) (M := 1)
    (fun y ↦ by by_cases hy : y = 0 <;> simp [hy]; positivity)

/-- **The hypotheses hold together: the Gaussian autoregression** `y ↦ a y + w`,
`w ∼ N(0, v)`, `|a| < 1`, `v ≠ 0`, of `exists_drift_minorization_gaussian_ar` (`V y = y²`): from
every start the averages of the chain tend to `0`, the mean of its invariant law
`N(0, v / (1 - a²))`. -/
example {a : ℝ} (ha : |a| < 1) {v : ℝ≥0} (hv : v ≠ 0) {P : Kernel ℝ ℝ} [IsMarkovKernel P]
    (hP : P = (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) (x : ℝ) :
    ∀ᵐ ω ∂(P.chain x), Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ω k) atTop (𝓝 0) := by
  subst hP
  obtain ⟨R, α, hα, hR, hdrift, hmin⟩ := exists_drift_minorization_gaussian_ar ha hv
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  simpa [integral_id_gaussianReal] using ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow
    (V := fun y ↦ ‖y‖₊ ^ 2) (m := 1) (by fun_prop) hdrift hα
    (lt_of_le_of_lt (by rw [two_mul, add_assoc]; exact le_add_self) hR) (by simpa using hmin)
    (invariant_gaussianReal_ar ha v) (g := id) measurable_id (M := 1)
    (fun y ↦ by simp [sq_abs]) x

end ProbabilityTheory.Kernel
