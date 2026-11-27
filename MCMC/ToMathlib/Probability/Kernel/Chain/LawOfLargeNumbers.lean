/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Chain.Basic
public import MCMC.ToMathlib.Probability.Kernel.Mixing
public import MCMC.ToMathlib.Probability.StrongLaw

/-!
# The law of large numbers for Harris chains

For a Markov kernel `P` with a drift `∫⁻ V ∂(P x) ≤ γ V x + K`, a minorization
`α • ν ≤ (P ^ m) x` on `{V ≤ R}` with `α > 0` and `K + γ R < R`, an invariant law `π`, and a
measurable `g` with `g² ≤ M (1 + V)`, write `ḡ = g - ∫ g ∂π`:

* **Variance growth**: `∫ (∑_{k < n} ḡ (ω k))² ∂(P.chain ∘ₘ μ) ≤ C M n (1 + ∫ V ∂μ)` for every
  initial law `μ` integrating `V`, with `C` independent of `π`, `μ`, `g`, `M` and `n`
  (`exists_integral_sq_sum_sub_le_of_drift_of_minorization_pow`). The correlations
  `∫ ψ (ω k) φ (ω (k + l))` with `∫ φ ∂π = 0` are `O(ρˡ)` uniformly in `k`
  (`exists_abs_integral_comp_mul_comp_chain_le_of_drift_of_minorization_pow`), through the bound
  `|Pˡφ| ≤ C ρˡ √M (1 + √V)` of `Mixing.lean`.
* **The strong law**: `n⁻¹ ∑_{k < n} g (ω k) → ∫ g ∂π` for `P.chain x`-almost every `ω`, from every
  point `x` (`ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow`), hence from every
  initial measure, with no moment
  (`ae_tendsto_inv_mul_sum_chain_comp_of_drift_of_minorization_pow`): the variance growth and
  Rajchman's argument (`ProbabilityTheory.ae_tendsto_inv_mul_sum_of_integral_sq_le`).

The class `g² ≤ M (1 + V)` is the class this second-moment argument reaches; it is not claimed
optimal (for a Harris recurrent chain the strong law holds for every `g ∈ L¹(π)`). The
hypotheses on the kernel are those of Harris' theorem with the minorization of a power
(`exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow`), and none is
removable: the identity kernel of `Bool` has every Dirac mass as invariant law and its averages
converge to `g x` from `x` (`ae_tendsto_inv_mul_sum_chain_id`,
`not_forall_ae_tendsto_inv_mul_sum_chain_id_bool`), and with suitable `V`, `γ`, `K`, `R` it
satisfies all the hypotheses but the threshold, all but the drift, and all but the minorization
(the `example`s at the end). The hypotheses hold together on the halving chain of `Harris.lean`
and on the Gaussian autoregression of `RandomMap.lean` (the last two `example`s).

## Search

At Mathlib `d13f23b`: `grep -rln "strong_law" Mathlib` finds `Probability/StrongLaw.lean`
(independent identically distributed sequences) and its uses, none for a Markov chain;
`grep -rn "variance_sum" Mathlib` finds `ProbabilityTheory.variance_sum'`
(`Probability/Moments/Variance.lean`: the variance of a sum as the double sum of covariances,
centered at the means), while the sums here are centered at `∫ g ∂π`, so their second moment is
expanded by lags (`MeasureTheory.integral_sq_sum_range_eq`);
`grep -rn "sq_sum_le_card_mul_sum_sq" Mathlib` finds the Cauchy–Schwarz inequality for finite
sums (`Algebra/Order/Chebyshev.lean`) and no expansion of `(∑_{k < n} a k)²` by lags.
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
measure `π` and measurable `g` with `g² ≤ M (1 + V)`, the function `g - ∫ g ∂π` has integral `0`
under `π` and `(g - ∫ g ∂π)² ≤ 2 (2 + K / (1 - γ)) M (1 + V)`. -/
theorem integral_sub_integral_eq_zero_and_sq_sub_integral_le_of_invariant_of_drift
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    (hγ : γ < 1) {π : Measure X} [IsProbabilityMeasure π] (hπ : Invariant P π) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ} (hgM : ∀ x, g x ^ 2 ≤ M * (1 + V x)) :
    ∫ x, (g x - ∫ y, g y ∂π) ∂π = 0 ∧
      ∀ x, (g x - ∫ y, g y ∂π) ^ 2 ≤ 2 * (2 + K / (1 - γ)) * M * (1 + V x) := by
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure π
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hgM x₀)) (by positivity)
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  have hgi : Integrable g π := (memLp_two_of_sq_le hg.aestronglyMeasurable
    (((integrable_const 1).add (integrable_of_invariant_of_drift hV hdrift hγ hπ)).const_mul M)
      hgM).integrable one_le_two
  have hc := sq_integral_le_of_invariant_of_drift hV hdrift hγ hπ hg hgM
  refine ⟨by rw [integral_sub hgi (integrable_const _)]; simp, fun x ↦ ?_⟩
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
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((sq_nonneg _).trans (hψM x₀)) (by positivity)
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
          gcongr
          nlinarith [Real.sq_sqrt (V x).coe_nonneg, sq_nonneg (√(V x : ℝ) - 1)]
      _ = 2 * C * ρ ^ l * M * (1 + V x) := by ring
  have hVk : Integrable (fun x ↦ (V x : ℝ)) ((P ^ k : Kernel X X) ∘ₘ μ) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV k)
  rw [integral_comp_mul_comp_chain_comp P μ hφ hψ k l
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
  obtain ⟨hc0, hgM'⟩ := integral_sub_integral_eq_zero_and_sq_sub_integral_le_of_invariant_of_drift
    hV hdrift hγ hinv hg hgM
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
  obtain ⟨hc0, hgM'⟩ := integral_sub_integral_eq_zero_and_sq_sub_integral_le_of_invariant_of_drift
    hV hdrift hγ hπ hg hgM
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

/-! ### The hypotheses are forced, and they hold together -/

/-- **The chain of a deterministic map follows the orbit**: with measurable singletons, for
`(deterministic f hf).chain x`-almost every `ω`, `ω k = f^[k] x` for every `k`. -/
theorem ae_forall_eq_iterate_chain_deterministic [MeasurableSingletonClass X] {f : X → X}
    (hf : Measurable f) (x : X) :
    ∀ᵐ ω ∂((deterministic f hf).chain x), ∀ k, ω k = f^[k] x := by
  refine ae_all_iff.2 fun k ↦ ae_of_ae_map (f := fun ω : ℕ → X ↦ ω k)
    (p := fun y ↦ y = f^[k] x) (measurable_pi_apply k).aemeasurable ?_
  rw [← map_apply _ (measurable_pi_apply k), chain_map_eval, deterministic_pow,
    deterministic_apply]
  exact (ae_dirac_iff (measurableSet_singleton _)).2 rfl

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

/-- **The threshold `K + γ R < R` is forced**: the identity kernel of `Bool` with
`V = 1_{true}` has the drift with `γ = 0`, `K = 1` and the minorization `dirac false ≤ P x` on
`{V ≤ 0}` (`α = 1`, `m = 1`), but `K + γ R = 1 > 0 = R`, and the strong law fails for
`g = 1_{true}` (`g² ≤ 1 + V`). -/
example :
    (∀ x, ∫⁻ y, (if y then (1 : ℝ≥0) else 0) ∂((Kernel.id : Kernel Bool Bool) x) ≤
      (0 : ℝ≥0) * (if x then (1 : ℝ≥0) else 0) + (1 : ℝ≥0)) ∧
    (∀ x, (if x then (1 : ℝ≥0) else 0) ≤ 0 →
      (1 : ℝ≥0) • Measure.dirac false ≤ ((Kernel.id : Kernel Bool Bool) ^ 1) x) ∧
    ¬ ((1 : ℝ≥0) + 0 * 0 < 0) ∧
    ¬ ∀ π : Measure Bool, IsProbabilityMeasure π → Invariant (Kernel.id : Kernel Bool Bool) π →
      ∀ x, ∀ᵐ ω ∂((Kernel.id : Kernel Bool Bool).chain x),
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, (if ω k then (1 : ℝ) else 0)) atTop
          (𝓝 (∫ y, (if y then (1 : ℝ) else 0) ∂π)) :=
  ⟨fun x ↦ by cases x <;> simp [Kernel.id_apply], fun x hx ↦ by
    cases x with
    | false => simp [Kernel.id_apply]
    | true => simp at hx, by simp, not_forall_ae_tendsto_inv_mul_sum_chain_id_bool⟩

/-- **The drift is forced**: the identity kernel of `Bool` with `V = 2 · 1_{true}` has the
minorization `dirac false ≤ P x` on `{V ≤ 1}` (`α = 1`, `m = 1`) and `K + γ R < R` for `γ = K = 0`,
`R = 1`, but not the drift, and the strong law fails for `g = 1_{true}`. -/
example :
    (∀ x, (if x then (2 : ℝ≥0) else 0) ≤ 1 →
      (1 : ℝ≥0) • Measure.dirac false ≤ ((Kernel.id : Kernel Bool Bool) ^ 1) x) ∧
    (0 : ℝ≥0) + 0 * 1 < 1 ∧
    ¬ (∀ x, ∫⁻ y, (if y then (2 : ℝ≥0) else 0) ∂((Kernel.id : Kernel Bool Bool) x) ≤
      (0 : ℝ≥0) * (if x then (2 : ℝ≥0) else 0) + (0 : ℝ≥0)) :=
  ⟨fun x hx ↦ by
    cases x with
    | false => simp [Kernel.id_apply]
    | true => norm_num at hx, by norm_num, fun h ↦ by simpa [Kernel.id_apply] using h true⟩

/-- **The minorization is forced, and `α > 0` in it**: the identity kernel of `Bool` with `V = 0`
has the drift with `γ = K = 0` and `K + γ R < R` for `R = 1`, and the minorization of `P ^ 1`
(every power of the identity is the identity) holds with `α = 0` and with no `α > 0`: the strong
law fails (`not_forall_ae_tendsto_inv_mul_sum_chain_id_bool`). -/
example {ν : Measure Bool} [IsProbabilityMeasure ν] {α : ℝ≥0} (hα : 0 < α) :
    (∀ x, ∫⁻ _y, ((0 : ℝ≥0) : ℝ≥0∞) ∂((Kernel.id : Kernel Bool Bool) x) ≤
      (0 : ℝ≥0) * (0 : ℝ≥0) + (0 : ℝ≥0)) ∧
    (0 : ℝ≥0) + 0 * 1 < 1 ∧
    (∀ x, (0 : ℝ≥0) ≤ 1 → (0 : ℝ≥0) • ν ≤ ((Kernel.id : Kernel Bool Bool) ^ 1) x) ∧
    ¬ (∀ x, (0 : ℝ≥0) ≤ 1 → α • ν ≤ ((Kernel.id : Kernel Bool Bool) ^ 1) x) :=
  ⟨fun _ ↦ by simp, by norm_num, fun _ _ ↦ by rw [zero_smul]; exact Measure.zero_le _,
    fun h ↦ not_forall_smul_le_id_bool hα
    fun x ↦ by simpa using h x zero_le_one⟩

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
  have hπ : Invariant P (P 0) := by
    refine Measure.ext fun s hs ↦ ?_
    rw [Measure.bind_apply hs (Kernel.aemeasurable _), hP 0]
    simp only [zero_le_one, ↓reduceIte]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac, hP, hP]
    simp only [zero_le_one, le_refl, ↓reduceIte]
    rw [← add_smul, add_halves, one_smul]
  have h := ae_tendsto_inv_mul_sum_chain_of_drift_of_minorization_pow (P := P)
    (V := fun n : ℕ ↦ (n : ℝ≥0)) (γ := 1 / 2) (K := 1 / 2) (ν := Measure.dirac 1) (α := 1 / 2)
    (R := 3) (m := 1) (measurable_of_countable _) hd (by norm_num) (by norm_num)
    (fun y hy ↦ by rw [pow_one]; exact hm y hy) hπ (g := Set.indicator ({0} : Set ℕ) 1)
    (measurable_of_countable _) (M := 1)
    (fun y ↦ by by_cases hy : y = 0 <;> simp [hy]; positivity) x
  rw [integral_indicator_one (measurableSet_singleton 0)] at h
  convert h using 2
  simp [Measure.real, hP 0]

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
