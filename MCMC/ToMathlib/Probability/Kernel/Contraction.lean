/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.MeasureTheory.Measure.UniformLimit
import MCMC.ToMathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import MCMC.ToMathlib.Probability.Kernel.Invariance

/-!
# Markov kernels that contract a weighted oscillation

For `V : X → ℝ≥0` and `β ≥ 0`, Hairer and Mattingly measure a test function `φ : X → ℝ` by the
least `c` with `|φ x - φ y| ≤ c (2 + β V x + β V y)` for all `x`, `y` (the Lipschitz seminorm for
the metric `2 + β V x + β V y` off the diagonal). A Markov kernel `P` *contracts* it with rate `ρ`
if `|∫ φ ∂(P x) - ∫ φ ∂(P y)| ≤ ρ c (2 + β V x + β V y)` whenever `φ` has seminorm at most `c`.
This file proves what follows from such a contraction together with a drift
`∫⁻ V ∂(P x) ≤ γ V x + K`, `γ < 1`; Doeblin's and Harris' theorems
(`MCMC/ToMathlib/Probability/Kernel/Doeblin.lean`, `…/Harris.lean`) supply the contraction.

* `exists_forall_abs_add_le` (M. Hairer, J. C. Mattingly, *Yet another look at Harris' ergodic
  theorem for Markov chains*, 2011, arXiv:0810.2777, Lemma 2.1): increments bounded by
  `w x + w y` make `|φ + c| ≤ w` for some constant `c`.
* `MeasureTheory.abs_integral_sub_integral_le_of_forall_abs_sub_le`: for probability measures
  `μ₁`, `μ₂` sharing a component `θ`, `|∫ φ ∂μ₁ - ∫ φ ∂μ₂| ≤ c (2 + β E₁ V + β E₂ V - 2 θ(X))`;
  `θ = 0` is the bound by the product coupling, `θ = α ν` the minorization step.
* `ProbabilityTheory.Kernel.lintegral_pow_le_of_drift`: the drift iterated,
  `∫⁻ V ∂(Pⁿ x) ≤ γⁿ V x + K ∑_{k<n} γᵏ`.
* `ProbabilityTheory.Kernel.abs_integral_comp_pow_sub_le`: the iterated contraction bounded
  through the product coupling of two laws,
  `|∫ φ ∂(Pⁿ ∘ₘ μ₁) - ∫ φ ∂(Pⁿ ∘ₘ μ₂)| ≤ ρⁿ c (2 + β E₁ V + β E₂ V)`.
* `ProbabilityTheory.Kernel.lintegral_totalVariation_comp_le` (Hairer–Mattingly, Theorem 1.3 from
  their Theorem 3.1): under a drift, a contraction of the oscillation with rate `ρ` gives
  `ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ ρ ρ_β(μ₁, μ₂)` for all probability measures `μ₁`, `μ₂`, where
  `ρ_β(μ₁, μ₂) = ∫⁻ (1 + β V) ∂|μ₁ - μ₂|` and `|μ₁ - μ₂|` is Mathlib's total variation; no moment
  is assumed. Iterated: `…lintegral_totalVariation_comp_pow_le`; in the unweighted `ρ₁`, some power
  contracts (Hairer–Mattingly's Remark 1.4): `…lintegral_totalVariation_comp_pow_le_max`. In real
  form:
  `…integral_totalVariation_comp_le` (finite measures of equal mass such that `μ₁`, `μ₂`,
  `P ∘ₘ μ₁`, `P ∘ₘ μ₂` integrate `1 + β V`) and
  `…integral_totalVariation_comp_le_of_drift` (laws integrating `V`). Conversely
  (`…forall_abs_integral_sub_le_of_lintegral_totalVariation_le`), the contraction of `ρ_β` between
  the laws `P ∘ₘ dirac x` gives the contraction of the oscillation: the two forms are equivalent.
  A rate `ρ ≤ 0` makes all `P ∘ₘ μ` equal (`…comp_eq_comp_of_contraction_of_nonpos`).
* `MeasureTheory.isGreatest_integral_sub_integral_of_abs_sub_le` (their Lemma 2.1 on measures,
  `d_β = ρ_β`): for finite measures of equal mass, `∫ w ∂|μ₁ - μ₂|` is the greatest
  `∫ g ∂μ₁ - ∫ g ∂μ₂` over measurable `g` with `|g x - g y| ≤ w x + w y`.
* `ProbabilityTheory.Kernel.lintegral_le_of_invariant_of_drift`: under the drift alone, every
  invariant probability measure has `∫⁻ V ≤ K / (1 - γ)`.
* `ProbabilityTheory.Kernel.exists_invariant_of_contraction`: an invariant probability measure,
  the limit of `Pⁿ x₀` uniformly on measurable sets
  (`MeasureTheory.Measure.exists_tendstoUniformlyOn_of_uniformCauchySeqOn`): no topology on `X`.
* `ProbabilityTheory.Kernel.existsUnique_invariant_of_contraction` and
  `…abs_integral_comp_pow_sub_integral_le_of_contraction`: exactly one invariant law, and
  `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ρⁿ M (1 + ∫ V ∂μ)` with `C = max 1 β⁻¹ (2 + β K / (1 - γ) + β)`
  for `|φ| ≤ M (1 + V)`; `pow_div_le_inv_mul_rpow_inv_pow` turns a rate along the multiples of
  `m` into a rate along every `n`.
* `ProbabilityTheory.Kernel.eq_of_invariant_of_contraction`: every invariant probability measure
  equals one with `∫⁻ V ∂π < ∞`; no moment is assumed of the other.

The hypotheses are the ones the proofs use: the drift gives the finiteness of the moments (the
contraction does the rest); `γ < 1` enters the existence (the moments of `Pⁿ x₀` are bounded in
`n`) and the bound `∫⁻ V ∂π ≤ K / (1 - γ)` of invariant laws, hence the constant of
`…abs_integral_comp_pow_sub_integral_le_of_contraction`; the uniqueness
`…eq_of_invariant_of_contraction` and the contraction of `ρ_β`,
`…lintegral_totalVariation_comp_le`, use no `γ < 1`; `ρ < 1` with `0 ≤ ρ` gives the limits.

No search hit: `grep -rln "Doeblin\|Dobrushin\|Harris\|minoriz\|Lyapunov function" Mathlib`
finds only `Combinatorics/SetFamily/HarrisKleitman.lean` (searched 2026-11-24, Mathlib `d13f23b`);
`grep -rli drift Mathlib/Probability` finds nothing.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- **Hairer–Mattingly, Lemma 2.1**: a real function whose increments are bounded by
`w x + w y` lies, after adding a constant, between `-w` and `w`. -/
theorem exists_forall_abs_add_le {X : Type*} {f w : X → ℝ}
    (h : ∀ x y, |f x - f y| ≤ w x + w y) : ∃ c : ℝ, ∀ x, |f x + c| ≤ w x := by
  refine ⟨⨅ y, (w y - f y), fun x ↦ abs_le.2 ⟨?_, ?_⟩⟩
  · have : Nonempty X := ⟨x⟩
    linarith [le_ciInf fun y ↦ (by linarith [(abs_le.1 (h x y)).1] : -w x - f x ≤ w y - f y)]
  · have hb := ciInf_le (f := fun y ↦ w y - f y)
      ⟨-w x - f x, by rintro _ ⟨y, rfl⟩; linarith [(abs_le.1 (h x y)).1]⟩ x
    beta_reduce at hb
    linarith

/-- Real functions `F n` with `|F (n + k) x - F n x| ≤ ρⁿ C` on `s`, `0 ≤ ρ < 1`, are uniformly
Cauchy on `s`. -/
theorem uniformCauchySeqOn_of_abs_add_sub_le {ι : Type*} {F : ℕ → ι → ℝ} {s : Set ι} {ρ C : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (h : ∀ n k, ∀ x ∈ s, |F (n + k) x - F n x| ≤ ρ ^ n * C) :
    UniformCauchySeqOn F atTop s := by
  refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).mul_const C).eventually
    (gt_mem_nhds (by simpa using half_pos hε : 0 * C < ε / 2))).exists
  refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq]
  linarith [abs_sub_le (F (N + k) x) (F N x) (F (N + l) x), abs_sub_comm (F N x) (F (N + l) x),
    h N k x hx, h N l x hx]

/-- A geometric rate along the multiples of `m` is a geometric rate: for `0 ≤ ρ < 1`, `0 < m` and
`r = max ρ (1/2)`, `ρ ^ (n / m) ≤ r⁻¹ (r ^ (1 / m)) ^ n` for every `n`, and `r ^ (1 / m) < 1`. -/
theorem pow_div_le_inv_mul_rpow_inv_pow {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) {m : ℕ}
    (hm : 0 < m) (n : ℕ) :
    ρ ^ (n / m) ≤ (max ρ 2⁻¹)⁻¹ * (max ρ 2⁻¹ ^ (m : ℝ)⁻¹) ^ n ∧ max ρ 2⁻¹ ^ (m : ℝ)⁻¹ < 1 := by
  have hr0 : 0 < max ρ 2⁻¹ := lt_max_of_lt_right (by norm_num)
  have hr1 : max ρ 2⁻¹ < 1 := max_lt hρ (by norm_num)
  have h0 : 0 ≤ max ρ 2⁻¹ ^ (m : ℝ)⁻¹ := Real.rpow_nonneg hr0.le _
  have h1 : max ρ 2⁻¹ ^ (m : ℝ)⁻¹ < 1 := Real.rpow_lt_one hr0.le hr1 (by positivity)
  have hpow : (max ρ 2⁻¹ ^ (m : ℝ)⁻¹) ^ m = max ρ 2⁻¹ := Real.rpow_inv_natCast_pow hr0.le hm.ne'
  have hn : n ≤ m * (n / m) + m := by linarith [Nat.div_add_mod n m, Nat.mod_lt n hm]
  refine ⟨?_, h1⟩
  calc ρ ^ (n / m) ≤ max ρ 2⁻¹ ^ (n / m) := pow_le_pow_left₀ hρ0 (le_max_left _ _) _
    _ = (max ρ 2⁻¹)⁻¹ * (max ρ 2⁻¹ ^ (m : ℝ)⁻¹) ^ (m * (n / m) + m) := by
        rw [pow_add, pow_mul, hpow, ← mul_assoc, mul_comm _ (max ρ 2⁻¹ ^ (n / m)), mul_assoc,
          inv_mul_cancel₀ hr0.ne', mul_one]
    _ ≤ (max ρ 2⁻¹)⁻¹ * (max ρ 2⁻¹ ^ (m : ℝ)⁻¹) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1.le hn) (inv_nonneg.2 hr0.le)

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- Two finite measures with a common component `θ`: the integrals of `g` with `|g| ≤ w` differ
by at most `∫ w ∂μ₁ + ∫ w ∂μ₂ - 2 ∫ w ∂θ`. -/
theorem abs_integral_sub_integral_le_of_le_of_le {μ₁ μ₂ θ : Measure α} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (h₁ : θ ≤ μ₁) (h₂ : θ ≤ μ₂) {g w : α → ℝ} (hg : Measurable g)
    (hgw : ∀ x, |g x| ≤ w x) (hw₁ : Integrable w μ₁) (hw₂ : Integrable w μ₂) :
    |∫ x, g x ∂μ₁ - ∫ x, g x ∂μ₂| ≤ ∫ x, w x ∂μ₁ + ∫ x, w x ∂μ₂ - 2 * ∫ x, w x ∂θ := by
  have : IsFiniteMeasure θ := isFiniteMeasure_of_le μ₁ h₁
  have hb : ∀ x, ‖g x‖ ≤ w x := fun x ↦ (Real.norm_eq_abs _).trans_le (hgw x)
  have split : ∀ μ : Measure α, θ ≤ μ → ∀ f : α → ℝ, Integrable f μ →
      ∫ x, f x ∂μ = ∫ x, f x ∂(μ - θ) + ∫ x, f x ∂θ := fun μ hμ f hf ↦ by
    conv_lhs => rw [← Measure.sub_add_cancel_of_le hμ]
    exact integral_add_measure (hf.mono_measure Measure.sub_le) (hf.mono_measure hμ)
  have e : ∀ μ : Measure α, Integrable w μ → |∫ x, g x ∂(μ - θ)| ≤ ∫ x, w x ∂(μ - θ) :=
    fun μ hw ↦ abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ abs_nonneg _) (hw.mono_measure Measure.sub_le) (ae_of_all _ hgw))
  rw [split μ₁ h₁ g (hw₁.mono' hg.aestronglyMeasurable (ae_of_all _ hb)),
    split μ₂ h₂ g (hw₂.mono' hg.aestronglyMeasurable (ae_of_all _ hb)), split μ₁ h₁ w hw₁,
    split μ₂ h₂ w hw₂]
  have e₁ := abs_le.1 (e μ₁ hw₁)
  have e₂ := abs_le.1 (e μ₂ hw₂)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A measurable function with increments bounded by `c (2 + β V x + β V y)` is integrable
against every finite measure that integrates `V`. -/
theorem integrable_of_forall_abs_sub_le {μ : Measure α} [IsFiniteMeasure μ] {V : α → ℝ≥0}
    (hV : Measurable V) (hμV : ∫⁻ x, V x ∂μ ≠ ∞) {β c : ℝ} {φ : α → ℝ} (hφ : Measurable φ)
    (hφc : ∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) : Integrable φ μ := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · exact Integrable.of_isEmpty
  · have hVi : Integrable (fun x ↦ (V x : ℝ)) μ := by
      simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable hμV
    have hg : Integrable (fun x ↦ |φ x₀| + c * (2 + β * V x + β * V x₀)) μ :=
      ((integrable_const (|φ x₀| + c * (2 + β * V x₀))).add (hVi.const_mul (c * β))).congr
        (ae_of_all _ fun x ↦ by simp only [Pi.add_apply]; ring)
    exact hg.mono' hφ.aestronglyMeasurable (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le
      (by linarith [abs_sub_abs_le_abs_sub (φ x) (φ x₀), hφc x x₀]))

/-- Two probability measures with a common component `θ`, and `φ` with increments bounded by
`c (2 + β V x + β V y)`: `|∫ φ ∂μ₁ - ∫ φ ∂μ₂| ≤ c (2 + β ∫ V ∂μ₁ + β ∫ V ∂μ₂ - 2 θ(univ))`. -/
theorem abs_integral_sub_integral_le_of_forall_abs_sub_le {μ₁ μ₂ θ : Measure α}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (h₁ : θ ≤ μ₁) (h₂ : θ ≤ μ₂)
    {V : α → ℝ≥0} (hV : Measurable V) (hV₁ : ∫⁻ x, V x ∂μ₁ ≠ ∞) (hV₂ : ∫⁻ x, V x ∂μ₂ ≠ ∞)
    {β c : ℝ} (hβ : 0 ≤ β) {φ : α → ℝ} (hφ : Measurable φ)
    (hφc : ∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) :
    |∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂| ≤
      c * (2 + β * ∫ x, (V x : ℝ) ∂μ₁ + β * ∫ x, (V x : ℝ) ∂μ₂ - 2 * θ.real univ) := by
  obtain ⟨x₀⟩ : Nonempty α := nonempty_of_isProbabilityMeasure μ₁
  have : IsFiniteMeasure θ := isFiniteMeasure_of_le μ₁ h₁
  have hc : 0 ≤ c := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφc x₀ x₀))
    (by linarith [mul_nonneg hβ (V x₀).coe_nonneg])
  have hVi : ∀ μ : Measure α, ∫⁻ x, V x ∂μ ≠ ∞ → Integrable (fun x ↦ (V x : ℝ)) μ := fun μ h ↦ by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable h
  have hw₁ : Integrable (fun x ↦ c * (1 + β * V x)) μ₁ :=
    ((integrable_const 1).add ((hVi μ₁ hV₁).const_mul β)).const_mul c
  have hw₂ : Integrable (fun x ↦ c * (1 + β * V x)) μ₂ :=
    ((integrable_const 1).add ((hVi μ₂ hV₂).const_mul β)).const_mul c
  obtain ⟨b, hb⟩ := exists_forall_abs_add_le (f := φ) (w := fun x ↦ c * (1 + β * V x))
    fun x y ↦ (hφc x y).trans_eq (by ring)
  have key := abs_integral_sub_integral_le_of_le_of_le h₁ h₂ (hφ.add_const b) hb hw₁ hw₂
  have e : ∀ μ : Measure α, IsProbabilityMeasure μ → Integrable φ μ →
      ∫ x, φ x + b ∂μ = ∫ x, φ x ∂μ + b := fun μ _ h ↦ by
    rw [integral_add h (integrable_const b)]
    simp
  have ew : ∀ μ : Measure α, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∫ x, c * (1 + β * V x) ∂μ = c * (1 + β * ∫ x, (V x : ℝ) ∂μ) := fun μ _ h ↦ by
    rw [integral_const_mul, integral_add (integrable_const 1) ((hVi μ h).const_mul β),
      integral_const_mul]
    simp
  have hθ : θ.real univ * c ≤ ∫ x, c * (1 + β * V x) ∂θ := by
    rw [← smul_eq_mul, ← integral_const]
    exact integral_mono (integrable_const c) (hw₁.mono_measure h₁) fun x ↦
      le_mul_of_one_le_right hc (by linarith [mul_nonneg hβ (V x).coe_nonneg])
  rw [e μ₁ ‹_› (integrable_of_forall_abs_sub_le hV hV₁ hφ hφc),
    e μ₂ ‹_› (integrable_of_forall_abs_sub_le hV hV₂ hφ hφc), add_sub_add_right_eq_sub,
    ew μ₁ ‹_› hV₁, ew μ₂ ‹_› hV₂] at key
  calc |∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂|
      ≤ c * (1 + β * ∫ x, (V x : ℝ) ∂μ₁) + c * (1 + β * ∫ x, (V x : ℝ) ∂μ₂) -
          2 * ∫ x, c * (1 + β * V x) ∂θ := key
    _ ≤ c * (1 + β * ∫ x, (V x : ℝ) ∂μ₁) + c * (1 + β * ∫ x, (V x : ℝ) ∂μ₂) -
          2 * (θ.real univ * c) := by linarith
    _ = c * (2 + β * ∫ x, (V x : ℝ) ∂μ₁ + β * ∫ x, (V x : ℝ) ∂μ₂ - 2 * θ.real univ) := by ring

/-- **Hairer–Mattingly, Lemma 2.1, on measures** (`d_β = ρ_β`): for finite measures `μ`, `ν` of
equal mass and `w ≥ 0` integrable against both, `∫ w ∂|μ - ν|` is also the greatest value of
`∫ g ∂μ - ∫ g ∂ν` over measurable `g` with `|g x - g y| ≤ w x + w y`. -/
theorem isGreatest_integral_sub_integral_of_abs_sub_le (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {w : α → ℝ} (hw : Measurable w) (hw0 : 0 ≤ w)
    (hwμ : Integrable w μ) (hwν : Integrable w ν) :
    IsGreatest {r | ∃ g : α → ℝ, Measurable g ∧ (∀ x y, |g x - g y| ≤ w x + w y) ∧
      ∫ x, g x ∂μ - ∫ x, g x ∂ν = r}
      (∫ x, w x ∂(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation) := by
  obtain ⟨⟨g, hg, hgw, he⟩, hup⟩ := isGreatest_integral_sub_integral_of_abs_le μ ν hw hw0 hwμ hwν
  refine ⟨⟨g, hg, fun x y ↦ (abs_sub _ _).trans (add_le_add (hgw x) (hgw y)), he⟩, ?_⟩
  rintro _ ⟨g, hg, hgw, rfl⟩
  obtain ⟨c, hc⟩ := exists_forall_abs_add_le hgw
  have hgc : ∀ ξ : Measure α, IsFiniteMeasure ξ → Integrable w ξ → Integrable g ξ :=
    fun ξ _ hwξ ↦ by
      simpa [Pi.sub_def] using (hwξ.mono' (hg.add_const c).aestronglyMeasurable
        (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hc x))).sub (integrable_const c)
  have hr : μ.real univ = ν.real univ := by rw [measureReal_def, measureReal_def, hμν]
  have e : ∫ x, g x ∂μ - ∫ x, g x ∂ν = ∫ x, g x + c ∂μ - ∫ x, g x + c ∂ν := by
    rw [integral_add (hgc μ ‹_› hwμ) (integrable_const c),
      integral_add (hgc ν ‹_› hwν) (integrable_const c), integral_const, integral_const, hr]
    ring
  exact e ▸ hup ⟨fun x ↦ g x + c, hg.add_const c, hc, rfl⟩

/-- A component `a • ν` of a probability measure, `ν` a probability measure, has `a ≤ 1`. -/
theorem Measure.le_one_of_smul_le {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ≥0} (h : a • ν ≤ μ) : a ≤ 1 := by
  simpa using Measure.le_iff'.1 h univ

end MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X} {V : X → ℝ≥0} {γ K : ℝ≥0}

/-- The drift `∫⁻ V ∂(P x) ≤ γ V x + K`, iterated. -/
theorem lintegral_pow_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (n : ℕ) (x : X) :
    ∫⁻ y, V y ∂((P ^ n) x) ≤ γ ^ n * V x + K * ∑ k ∈ Finset.range n, (γ : ℝ≥0∞) ^ k := by
  have hp : ∀ n, P ^ (n + 1) = P ∘ₖ (P ^ n) := fun n ↦ pow_succ' P n
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    exact (lintegral_dirac' x hV.coe_nnreal_ennreal).le
  | succ n ih =>
    rw [hp, Kernel.lintegral_comp _ _ _ hV.coe_nnreal_ennreal]
    calc ∫⁻ z, ∫⁻ y, V y ∂(P z) ∂((P ^ n) x) ≤ ∫⁻ z, (γ * V z + K) ∂((P ^ n) x) :=
          lintegral_mono hdrift
      _ = γ * ∫⁻ z, V z ∂((P ^ n) x) + K := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul _ hV.coe_nnreal_ennreal]
          simp
      _ ≤ γ * (γ ^ n * V x + K * ∑ k ∈ Finset.range n, (γ : ℝ≥0∞) ^ k) + K := by gcongr
      _ = γ ^ (n + 1) * V x + K * ∑ k ∈ Finset.range (n + 1), (γ : ℝ≥0∞) ^ k := by
          rw [geom_sum_succ]
          ring

/-- The iterated drift, with the geometric sum bounded by `1 / (1 - γ)`. No `γ < 1` is assumed:
for `γ ≥ 1` the truncated `1 - γ` is `0` and the bound is `∞` when `K ≠ 0`. -/
theorem lintegral_pow_le_div_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (n : ℕ) (x : X) :
    ∫⁻ y, V y ∂((P ^ n) x) ≤ γ ^ n * V x + K / (1 - γ) := by
  refine (lintegral_pow_le_of_drift hV hdrift n x).trans ?_
  rw [div_eq_mul_inv, ← ENNReal.tsum_geometric]
  gcongr
  exact ENNReal.sum_le_tsum _

/-- Under a drift, every `P x` integrates `V`. -/
theorem lintegral_ne_top_of_drift (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (x : X) :
    ∫⁻ y, V y ∂(P x) ≠ ∞ :=
  ((hdrift x).trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)).ne

/-- Under a drift, every iterate `Pⁿ x` integrates `V`. -/
theorem lintegral_pow_ne_top_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (n : ℕ) (x : X) :
    ∫⁻ y, V y ∂((P ^ n) x) ≠ ∞ :=
  ((lintegral_pow_le_of_drift hV hdrift n x).trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) (by simp), ENNReal.mul_lt_top (by simp) (by simp)⟩)).ne

/-- The iterated drift for the Bochner integral, `γ < 1`: `∫ V ∂(Pⁿ x) ≤ γⁿ V x + K / (1 - γ)`. -/
theorem integral_pow_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) (n : ℕ) (x : X) :
    ∫ y, (V y : ℝ) ∂((P ^ n) x) ≤ γ ^ n * V x + K / (1 - γ) := by
  have h1 : (1 : ℝ≥0∞) - γ ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hγ)).ne'
  have h2 : (γ : ℝ≥0∞) ^ n * V x ≠ ∞ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (V _).coe_nonneg)
    hV.coe_nnreal_real.aestronglyMeasurable]
  simp only [ENNReal.ofReal_coe_nnreal]
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h2, ENNReal.div_ne_top ENNReal.coe_ne_top h1⟩)
    (lintegral_pow_le_div_of_drift hV hdrift n x)).trans_eq ?_
  rw [ENNReal.toReal_add h2 (ENNReal.div_ne_top ENNReal.coe_ne_top h1), ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_sub_of_le (by exact_mod_cast hγ.le)
    ENNReal.one_ne_top]
  simp

/-- Under a drift, every iterate of a law that integrates `V` integrates `V`. -/
theorem lintegral_comp_pow_ne_top_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : ∫⁻ x, V x ∂μ ≠ ∞) (n : ℕ) : ∫⁻ x, V x ∂((P ^ n) ∘ₘ μ) ≠ ∞ := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hV.coe_nnreal_ennreal.aemeasurable]
  refine ((lintegral_mono (lintegral_pow_le_of_drift hV hdrift n)).trans_lt ?_).ne
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hV.coe_nnreal_ennreal,
    MeasureTheory.lintegral_const]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hμ.lt_top,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) (measure_lt_top μ univ)⟩

/-- A contraction of the weighted oscillation, iterated: `Pⁿ` contracts it with rate `ρⁿ`. -/
theorem abs_integral_pow_sub_integral_pow_le [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ}
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ}
    (hφc : ∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) (n : ℕ) :
    ∀ x y, |∫ z, φ z ∂((P ^ n) x) - ∫ z, φ z ∂((P ^ n) y)| ≤
      ρ ^ n * c * (2 + β * V x + β * V y) := by
  have hp : ∀ n, P ^ (n + 1) = P ∘ₖ (P ^ n) := fun n ↦ pow_succ' P n
  induction n generalizing φ c with
  | zero =>
    intro x y
    have h0 : ∀ u, ∫ z, φ z ∂((P ^ 0) u) = φ u := fun u ↦ by
      rw [pow_zero]
      exact integral_dirac' φ u hφ.stronglyMeasurable
    rw [h0, h0, pow_zero, one_mul]
    exact hφc x y
  | succ n ih =>
    intro x y
    have e : ∀ u, ∫ z, φ z ∂((P ^ (n + 1)) u) = ∫ z, (∫ w, φ w ∂(P z)) ∂((P ^ n) u) :=
      fun u ↦ by
        rw [hp]
        exact Kernel.integral_comp (by
          rw [← hp]
          exact integrable_of_forall_abs_sub_le hV
            (lintegral_pow_ne_top_of_drift hV hdrift (n + 1) u) hφ hφc)
    rw [e, e]
    exact (ih (hφ.stronglyMeasurable.integral_kernel).measurable (hP φ hφ c hφc) x y).trans_eq
      (by ring)

/-- **The iterated contraction against the product coupling**: for initial laws `μ₁`, `μ₂`
integrating `V`, `|∫ φ ∂(Pⁿ ∘ₘ μ₁) - ∫ φ ∂(Pⁿ ∘ₘ μ₂)| ≤ ρⁿ c (2 + β ∫ V ∂μ₁ + β ∫ V ∂μ₂)`. The
right side does not vanish at `μ₁ = μ₂`; the contraction of the weighted total variation between
laws is `ProbabilityTheory.Kernel.lintegral_totalVariation_comp_pow_le`. -/
theorem abs_integral_comp_pow_sub_le [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ}
    (hφc : ∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) {μ₁ μ₂ : Measure X}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (h₁ : ∫⁻ x, V x ∂μ₁ ≠ ∞)
    (h₂ : ∫⁻ x, V x ∂μ₂ ≠ ∞) (n : ℕ) :
    |∫ x, φ x ∂((P ^ n) ∘ₘ μ₁) - ∫ x, φ x ∂((P ^ n) ∘ₘ μ₂)| ≤
      ρ ^ n * c * (2 + β * ∫ x, (V x : ℝ) ∂μ₁ + β * ∫ x, (V x : ℝ) ∂μ₂) := by
  rw [Measure.integral_comp _ _ (integrable_of_forall_abs_sub_le hV
      (lintegral_comp_pow_ne_top_of_drift hV hdrift h₁ n) hφ hφc),
    Measure.integral_comp _ _ (integrable_of_forall_abs_sub_le hV
      (lintegral_comp_pow_ne_top_of_drift hV hdrift h₂ n) hφ hφc)]
  simpa using abs_integral_sub_integral_le_of_forall_abs_sub_le (θ := 0)
    (MeasureTheory.Measure.zero_le _) (MeasureTheory.Measure.zero_le _) hV h₁ h₂ hβ
    (hφ.stronglyMeasurable.integral_kernel).measurable
    (abs_integral_pow_sub_integral_pow_le hV hdrift hP hφ hφc n)

/-- A limit of the iterates `Pⁿ x₀`, uniformly on measurable sets, is invariant. -/
theorem invariant_of_tendstoUniformlyOn [IsMarkovKernel P] {x₀ : X} {π : Measure X}
    [IsFiniteMeasure π]
    (h : TendstoUniformlyOn (fun n s ↦ ((P ^ n) x₀).real s) (fun s ↦ π.real s) atTop
      {s | MeasurableSet s}) : Invariant P π := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  refine tendsto_nhds_unique ((tendsto_lintegral_of_tendstoUniformlyOn h (P.measurable_coe hs)
    (c := 1) fun x ↦ by simp only [ENNReal.coe_one]; exact prob_le_one).congr fun n ↦
      (pow_succ_apply_eq_lintegral P n x₀ hs).symm) ?_
  simpa [Function.comp_def, ofReal_measureReal] using (tendsto_add_atTop_iff_nat 1).2
    ((ENNReal.continuous_ofReal.tendsto _).comp (h.tendsto_at hs))

/-- **Moments of invariant laws**: under a drift with `γ < 1`, every invariant probability
measure has `∫⁻ V ≤ K / (1 - γ)`. No minorization is used. -/
theorem lintegral_le_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) : ∫⁻ x, V x ∂π ≤ K / (1 - γ) := by
  have htop : ∀ x, ⨆ M : ℕ, (V x : ℝ≥0∞) ⊓ M = V x := fun x ↦ by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hn : ∀ (M : ℕ) (n : ℕ), ∫⁻ x, (V x : ℝ≥0∞) ⊓ M ∂π ≤
      ∫⁻ x, ((γ : ℝ≥0∞) ^ n * V x + K / (1 - γ)) ⊓ M ∂π := fun M n ↦ by
    calc ∫⁻ x, (V x : ℝ≥0∞) ⊓ M ∂π = ∫⁻ x, ∫⁻ y, (V y : ℝ≥0∞) ⊓ M ∂((P ^ n) x) ∂π := by
          conv_lhs => rw [← (hπ.pow n).def]
          exact Measure.lintegral_bind (Kernel.aemeasurable _)
            (hV.coe_nnreal_ennreal.min measurable_const).aemeasurable
      _ ≤ _ := lintegral_mono fun x ↦ le_inf ((lintegral_mono fun y ↦ inf_le_left).trans
          (lintegral_pow_le_div_of_drift hV hdrift n x))
          ((lintegral_mono fun y ↦ inf_le_right).trans (by simp))
  have h0 : Tendsto (fun n : ℕ ↦ (γ : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 (by exact_mod_cast hγ)
  have hlim : ∀ M : ℕ, Tendsto (fun n : ℕ ↦ ∫⁻ x, ((γ : ℝ≥0∞) ^ n * V x + K / (1 - γ)) ⊓ M ∂π)
      atTop (𝓝 ((K : ℝ≥0∞) / (1 - γ) ⊓ M)) := fun M ↦ by
    simpa using tendsto_lintegral_of_dominated_convergence (μ := π) (fun _ ↦ (M : ℝ≥0∞))
      (fun n ↦ ((measurable_const.mul hV.coe_nnreal_ennreal).add measurable_const).min
        measurable_const) (fun n ↦ ae_of_all _ fun x ↦ inf_le_right) (by simp)
      (ae_of_all _ fun x ↦ ((ENNReal.Tendsto.mul_const h0 (Or.inr ENNReal.coe_ne_top)).add_const
        ((K : ℝ≥0∞) / (1 - γ))).min tendsto_const_nhds)
  calc ∫⁻ x, V x ∂π = ∫⁻ x, ⨆ M : ℕ, (V x : ℝ≥0∞) ⊓ M ∂π := by simp_rw [htop]
    _ = ⨆ M : ℕ, ∫⁻ x, (V x : ℝ≥0∞) ⊓ M ∂π :=
        lintegral_iSup (fun M ↦ hV.coe_nnreal_ennreal.min measurable_const)
          fun M N hMN x ↦ inf_le_inf_left _ (Nat.cast_le.2 hMN)
    _ ≤ K / (1 - γ) := iSup_le fun M ↦ (ge_of_tendsto' (hlim M) (hn M)).trans inf_le_left

/-- **Moments of invariant laws**, for the Bochner integral: `∫ V ∂π ≤ K / (1 - γ)`. -/
theorem integral_le_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) : ∫ x, (V x : ℝ) ∂π ≤ K / (1 - γ) := by
  have h1 : (1 : ℝ≥0∞) - γ ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hγ)).ne'
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (V _).coe_nonneg)
    hV.coe_nnreal_real.aestronglyMeasurable]
  simp only [ENNReal.ofReal_coe_nnreal]
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top ENNReal.coe_ne_top h1)
    (lintegral_le_of_invariant_of_drift hV hdrift hγ hπ)).trans_eq ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le (by exact_mod_cast hγ.le) ENNReal.one_ne_top]
  simp

/-- Two values of the indicator function of a set differ by at most `1`. -/
theorem _root_.Set.abs_indicator_one_sub_indicator_one_le (s : Set X) (u v : X) :
    |s.indicator (1 : X → ℝ) u - s.indicator 1 v| ≤ 1 := by
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp [hu, hv]

/-- Under a drift with `γ < 1` and a contraction with rate `ρ < 1`, the iterates `Pⁿ x₀`
converge, uniformly on measurable sets, to a probability measure. -/
theorem exists_tendstoUniformlyOn_pow_of_contraction [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    (x₀ : X) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧
      TendstoUniformlyOn (fun n s ↦ ((P ^ n) x₀).real s) (fun s ↦ π.real s) atTop
        {s | MeasurableSet s} := by
  set B : ℝ := V x₀ + K / (1 - γ)
  have hB : ∀ k, ∫ x, (V x : ℝ) ∂((P ^ k) x₀) ≤ B :=
    fun k ↦ (integral_pow_le_of_drift hV hdrift hγ k x₀).trans (add_le_add
      (mul_le_of_le_one_left (V x₀).coe_nonneg (pow_le_one₀ γ.coe_nonneg
        (by exact_mod_cast hγ.le))) le_rfl)
  have hcauchy : ∀ n k s, MeasurableSet s →
      |((P ^ (n + k)) x₀).real s - ((P ^ n) x₀).real s| ≤
        ρ ^ n * 2⁻¹ * (2 + β * B + β * V x₀) := fun n k s hs ↦ calc
    |((P ^ (n + k)) x₀).real s - ((P ^ n) x₀).real s|
        = |∫ x, s.indicator (1 : X → ℝ) x ∂((P ^ n) ∘ₘ (P ^ k) x₀) -
            ∫ x, s.indicator (1 : X → ℝ) x ∂((P ^ n) ∘ₘ Measure.dirac x₀)| := by
          rw [Measure.dirac_bind (Kernel.measurable _), ← Kernel.comp_apply, ← Kernel.pow_add,
            integral_indicator_one hs, integral_indicator_one hs]
      _ ≤ ρ ^ n * 2⁻¹ * (2 + β * ∫ x, (V x : ℝ) ∂((P ^ k) x₀) +
            β * ∫ x, (V x : ℝ) ∂(Measure.dirac x₀)) :=
          abs_integral_comp_pow_sub_le hV hdrift hβ hP (measurable_one.indicator hs) (c := 2⁻¹)
            (fun u v ↦ (abs_indicator_one_sub_indicator_one_le s u v).trans (by
              linarith [mul_nonneg hβ (V u).coe_nonneg, mul_nonneg hβ (V v).coe_nonneg]))
            (lintegral_pow_ne_top_of_drift hV hdrift k x₀)
            (by rw [lintegral_dirac' _ hV.coe_nnreal_ennreal]; exact ENNReal.coe_ne_top) n
      _ ≤ ρ ^ n * 2⁻¹ * (2 + β * B + β * V x₀) := by
          rw [integral_dirac' _ _ hV.coe_nnreal_real.stronglyMeasurable]
          exact mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left (hB k) hβ])
            (mul_nonneg (pow_nonneg hρ0 n) (by norm_num))
  obtain ⟨π, hπ, hlim⟩ := Measure.exists_tendstoUniformlyOn_of_uniformCauchySeqOn
    (uniformCauchySeqOn_of_abs_add_sub_le (F := fun n s ↦ ((P ^ n) x₀).real s) hρ0 hρ
      (C := 2⁻¹ * (2 + β * B + β * V x₀)) fun n k s hs ↦
        (hcauchy n k s hs).trans_eq (mul_assoc _ _ _))
  have h1 : Tendsto (fun n ↦ ((P ^ n) x₀).real univ) atTop (𝓝 (π.real univ)) :=
    hlim.tendsto_at MeasurableSet.univ
  simp only [probReal_univ] at h1
  refine ⟨π, ⟨?_⟩, hlim⟩
  rw [← ENNReal.toReal_eq_one_iff, ← measureReal_def]
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- **Existence of an invariant law**: under a drift with `γ < 1` and a contraction with rate
`ρ < 1`, there is an invariant probability measure `π`, with `∫⁻ V ∂π ≤ K / (1 - γ)`. -/
theorem exists_invariant_of_contraction [IsMarkovKernel P] [Nonempty X] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y)) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧ Invariant P π ∧ ∫⁻ x, V x ∂π ≤ K / (1 - γ) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨π, hπ, hlim⟩ := exists_tendstoUniformlyOn_pow_of_contraction hV hdrift hγ hβ hρ0 hρ hP x₀
  have hinv := invariant_of_tendstoUniformlyOn hlim
  exact ⟨π, hπ, hinv, lintegral_le_of_invariant_of_drift hV hdrift hγ hinv⟩

/-- **Convergence to an invariant law from a contraction**: under a drift with `γ < 1` and a
contraction of the weighted oscillation with `β > 0` and rate `ρ ≥ 0`, for every invariant
probability measure `π`, every initial law `μ` integrating `V` and every measurable `φ` with
`|φ| ≤ M (1 + V)`, `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ρⁿ M (1 + ∫ V ∂μ)` with
`C = max 1 β⁻¹ (2 + β K / (1 - γ) + β)`. -/
theorem abs_integral_comp_pow_sub_integral_le_of_contraction [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {β ρ : ℝ}
    (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : ∫⁻ x, V x ∂μ ≠ ∞) {φ : X → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ x, |φ x| ≤ M * (1 + V x)) (n : ℕ) :
    |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤
      max 1 β⁻¹ * (2 + β * (K / (1 - γ)) + β) * ρ ^ n * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hK' : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  have hm1 : 1 ≤ max 1 β⁻¹ := le_max_left _ _
  have hmβ : 1 ≤ max 1 β⁻¹ * β := (inv_mul_cancel₀ hβ.ne').symm.le.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hβ.le)
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφM x₀)) (by positivity)
  have hμ0 : 0 ≤ ∫ x, (V x : ℝ) ∂μ := integral_nonneg fun _ ↦ (V _).coe_nonneg
  have hπV := integral_le_of_invariant_of_drift hV hdrift hγ hπ
  have hφc : ∀ x y, |φ x - φ y| ≤ M * max 1 β⁻¹ * (2 + β * V x + β * V y) := fun x y ↦ by
    calc |φ x - φ y| ≤ |φ x| + |φ y| := by simpa using abs_sub_le (φ x) 0 (φ y)
      _ ≤ M * (1 + V x) + M * (1 + V y) := add_le_add (hφM x) (hφM y)
      _ = M * (2 + V x + V y) := by ring
      _ ≤ M * (max 1 β⁻¹ * (2 + β * V x + β * V y)) := mul_le_mul_of_nonneg_left (by
          linarith [mul_le_mul_of_nonneg_right hmβ (V x).coe_nonneg,
            mul_le_mul_of_nonneg_right hmβ (V y).coe_nonneg]) hM
      _ = M * max 1 β⁻¹ * (2 + β * V x + β * V y) := by ring
  have h := abs_integral_comp_pow_sub_le hV hdrift hβ.le hP hφ hφc (μ₁ := μ) (μ₂ := π) hμ
    (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top
      (tsub_pos_of_lt (by exact_mod_cast hγ)).ne') (lintegral_le_of_invariant_of_drift hV hdrift
        hγ hπ)) n
  rw [(hπ.pow n).def] at h
  have hin : 2 + β * ∫ x, (V x : ℝ) ∂μ + β * ∫ x, (V x : ℝ) ∂π ≤
      (2 + β * (K / (1 - γ)) + β) * (1 + ∫ x, (V x : ℝ) ∂μ) := by
    nlinarith [mul_le_mul_of_nonneg_left hπV hβ.le, mul_nonneg (mul_nonneg hβ.le hK') hμ0]
  calc |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π|
      ≤ ρ ^ n * (M * max 1 β⁻¹) * (2 + β * ∫ x, (V x : ℝ) ∂μ + β * ∫ x, (V x : ℝ) ∂π) := h
    _ ≤ ρ ^ n * (M * max 1 β⁻¹) * ((2 + β * (K / (1 - γ)) + β) * (1 + ∫ x, (V x : ℝ) ∂μ)) :=
        mul_le_mul_of_nonneg_left hin
          (mul_nonneg (pow_nonneg hρ0 n) (mul_nonneg hM (zero_le_one.trans hm1)))
    _ = _ := by ring

/-- **Uniqueness of the invariant law**: under a contraction with rate `ρ < 1`, every invariant
probability measure equals an invariant probability measure `π₀` that integrates `V`. -/
theorem eq_of_invariant_of_contraction [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 ≤ β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < 1)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {π₀ π₁ : Measure X} [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (h₀ : Invariant P π₀) (h₀V : ∫⁻ x, V x ∂π₀ ≠ ∞) (h₁ : Invariant P π₁) : π₁ = π₀ := by
  ext s hs
  have hbound : ∀ n y, |((P ^ n) y).real s - π₀.real s| ≤
      ρ ^ n * 2⁻¹ * (2 + β * V y + β * ∫ x, (V x : ℝ) ∂π₀) := fun n y ↦ by
    simpa [Measure.dirac_bind (Kernel.measurable _), (h₀.pow n).def, integral_indicator_one hs,
      integral_dirac' _ _ hV.coe_nnreal_real.stronglyMeasurable] using
      abs_integral_comp_pow_sub_le hV hdrift hβ hP (measurable_one.indicator hs) (c := 2⁻¹)
        (fun u v ↦ (abs_indicator_one_sub_indicator_one_le s u v).trans (by
          linarith [mul_nonneg hβ (V u).coe_nonneg, mul_nonneg hβ (V v).coe_nonneg]))
        (μ₁ := Measure.dirac y) (μ₂ := π₀)
        (by rw [lintegral_dirac' _ hV.coe_nnreal_ennreal]; exact ENNReal.coe_ne_top) h₀V n
  have hpt : ∀ y, Tendsto (fun n ↦ (P ^ n) y s) atTop (𝓝 (π₀ s)) := fun y ↦
    (ENNReal.tendsto_toReal_iff (fun n ↦ measure_ne_top _ _) (measure_ne_top _ _)).1
      (tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n ↦ norm_nonneg _)
        (fun n ↦ hbound n y) (by simpa using
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).mul_const _).mul_const _)))
  have hinv : ∀ n, ∫⁻ y, (P ^ n) y s ∂π₁ = π₁ s := fun n ↦ by
    rw [← Measure.bind_apply hs (Kernel.aemeasurable _), (h₁.pow n).def]
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := π₁) (fun _ ↦ 1)
    (fun n ↦ (P ^ n).measurable_coe hs) (fun n ↦ ae_of_all _ fun y ↦ prob_le_one) (by simp)
    (ae_of_all _ hpt)
  simp only [hinv, MeasureTheory.lintegral_const, measure_univ, mul_one] at hdom
  exact tendsto_nhds_unique tendsto_const_nhds hdom

/-- **Existence and uniqueness of the invariant law from a contraction**: under a drift with
`γ < 1` and a contraction of the weighted oscillation with rate `ρ < 1`, the kernel has exactly
one invariant probability measure. -/
theorem existsUnique_invariant_of_contraction [IsMarkovKernel P] [Nonempty X] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y)) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧ Invariant P π := by
  obtain ⟨π, hπ, hinv, hπV⟩ := exists_invariant_of_contraction hV hdrift hγ hβ hρ0 hρ hP
  exact ⟨π, ⟨hπ, hinv⟩, fun π₁ ⟨_, h₁⟩ ↦ eq_of_invariant_of_contraction hV hdrift hβ hρ0 hρ hP
    hinv (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top
      (tsub_pos_of_lt (by exact_mod_cast hγ)).ne') hπV) h₁⟩

/-! ### The contraction of the weighted total variation (Hairer–Mattingly, Theorem 1.3) -/

/-- Under a drift, `P ∘ₘ μ` integrates the weight `1 + β V` when the finite measure `μ` does. -/
theorem integrable_comp_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β : ℝ} {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x ↦ 1 + β * V x) μ) : Integrable (fun x ↦ 1 + β * V x) (P ∘ₘ μ) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · simp
  have hVμ : Integrable (fun x ↦ (V x : ℝ)) μ :=
    ((hμ.sub (integrable_const 1)).const_mul β⁻¹).congr (ae_of_all _ fun x ↦ by
      simp only [Pi.sub_apply]
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ hβ])
  have h : ∫⁻ x, V x ∂(P ∘ₘ μ) ≠ ∞ := by
    simpa using lintegral_comp_pow_ne_top_of_drift hV hdrift (by simpa using
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (V x).coe_nonneg)).1 hVμ.2).ne) 1
  have hV' : Integrable (fun x ↦ (V x : ℝ)) (P ∘ₘ μ) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable h
  exact (integrable_const 1).add (hV'.const_mul β)

/-- A kernel that contracts the weighted oscillation with a rate `ρ ≤ 0` sends all probability
measures to one law. -/
theorem comp_eq_comp_of_contraction_of_nonpos [IsMarkovKernel P] {β ρ : ℝ} (hβ : 0 ≤ β)
    (hρ : ρ ≤ 0) (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    P ∘ₘ μ₁ = P ∘ₘ μ₂ := by
  have hc : ∀ x y s, MeasurableSet s → P x s = P y s := fun x y s hs ↦ by
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
    refine sub_eq_zero.1 (abs_nonpos_iff.1 ?_)
    calc |(P x s).toReal - (P y s).toReal|
        = |∫ z, s.indicator 1 z ∂(P x) - ∫ z, s.indicator 1 z ∂(P y)| := by
          rw [integral_indicator_one hs, integral_indicator_one hs, measureReal_def,
            measureReal_def]
      _ ≤ ρ * 2⁻¹ * (2 + β * V x + β * V y) := hP (s.indicator 1) (measurable_one.indicator hs)
          2⁻¹ (fun u v ↦ (abs_indicator_one_sub_indicator_one_le s u v).trans (by
            linarith [mul_nonneg hβ (V u).coe_nonneg, mul_nonneg hβ (V v).coe_nonneg])) x y
      _ ≤ 0 := by nlinarith [mul_nonneg hβ (V x).coe_nonneg, mul_nonneg hβ (V y).coe_nonneg]
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ₁
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_congr fun x ↦ hc x x₀ s hs, lintegral_congr fun x ↦ hc x x₀ s hs]
  simp

/-- **Hairer–Mattingly, Theorem 1.3, from Theorem 3.1**: a kernel that contracts the weighted
oscillation with rate `ρ` contracts the weighted total variation with rate `ρ`,
`∫ (1 + β V) ∂|P ∘ₘ μ₁ - P ∘ₘ μ₂| ≤ ρ ∫ (1 + β V) ∂|μ₁ - μ₂|`, for finite measures `μ₁`, `μ₂` of
equal mass such that `μ₁`, `μ₂`, `P ∘ₘ μ₁` and `P ∘ₘ μ₂` integrate `1 + β V`. -/
theorem integral_totalVariation_comp_le [IsFiniteKernel P] (hV : Measurable V) {β ρ : ℝ}
    (hβ : 0 ≤ β) (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {μ₁ μ₂ : Measure X} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (hμ : μ₁ univ = μ₂ univ)
    (h₁ : Integrable (fun x ↦ 1 + β * V x) μ₁) (h₂ : Integrable (fun x ↦ 1 + β * V x) μ₂)
    (hP₁ : Integrable (fun x ↦ 1 + β * V x) (P ∘ₘ μ₁))
    (hP₂ : Integrable (fun x ↦ 1 + β * V x) (P ∘ₘ μ₂)) :
    ∫ x, (1 + β * V x) ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ρ * ∫ x, (1 + β * V x) ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  have hw : Measurable fun x ↦ 1 + β * (V x : ℝ) :=
    measurable_const.add (measurable_const.mul hV.coe_nnreal_real)
  obtain ⟨g, hg, hgw, he⟩ := exists_integral_sub_integral_eq_integral_totalVariation _ _ hw hP₁ hP₂
  have hgw' : ∀ x, |g x| ≤ 1 + β * V x :=
    fun x ↦ (hgw x).trans_eq (abs_of_nonneg (by positivity))
  obtain ⟨b, hb⟩ := exists_forall_abs_add_le (f := fun x ↦ ∫ z, g z ∂(P x))
    (w := fun x ↦ ρ * (1 + β * V x)) fun x y ↦ (hP g hg 1 (fun u v ↦ by
      linarith [abs_sub (g u) (g v), hgw' u, hgw' v]) x y).trans_eq (by ring)
  have hPg : Measurable fun x ↦ ∫ z, g z ∂(P x) + b :=
    (hg.stronglyMeasurable.integral_kernel).measurable.add_const b
  have hi : ∀ μ : Measure X, Integrable (fun x ↦ 1 + β * (V x : ℝ)) μ →
      Integrable (fun x ↦ ∫ z, g z ∂(P x) + b) μ := fun μ hμ ↦ (hμ.const_mul ρ).mono'
    hPg.aestronglyMeasurable (ae_of_all _ fun x ↦ (Real.norm_eq_abs _).trans_le (hb x))
  have hi' : ∀ μ : Measure X, IsFiniteMeasure μ → Integrable (fun x ↦ 1 + β * (V x : ℝ)) μ →
      Integrable (fun x ↦ ∫ z, g z ∂(P x)) μ := fun μ _ hμ ↦ by
    simpa [Pi.sub_def] using (hi μ hμ).sub (integrable_const b)
  have e : ∀ μ : Measure X, IsFiniteMeasure μ → Integrable (fun x ↦ 1 + β * (V x : ℝ)) μ →
      Integrable (fun x ↦ 1 + β * (V x : ℝ)) (P ∘ₘ μ) →
      ∫ x, g x ∂(P ∘ₘ μ) = ∫ x, (∫ z, g z ∂(P x) + b) ∂μ - μ.real univ * b :=
    fun μ hfin hμ hPμ ↦ by
      rw [Measure.integral_comp _ _ (hPμ.mono' hg.aestronglyMeasurable (ae_of_all _ fun x ↦
        (Real.norm_eq_abs _).trans_le (hgw' x))), integral_add (hi' μ hfin hμ)
        (integrable_const b), integral_const, smul_eq_mul]
      ring
  have hr : μ₁.real univ = μ₂.real univ := by rw [measureReal_def, measureReal_def, hμ]
  rw [← he, e μ₁ ‹_› h₁ hP₁, e μ₂ ‹_› h₂ hP₂, hr, sub_sub_sub_cancel_right, ← integral_const_mul]
  exact (le_abs_self _).trans (norm_integral_sub_integral_le_integral_totalVariation μ₁ μ₂
    (g := fun x ↦ ∫ z, g z ∂(P x) + b) (w := fun x ↦ ρ * (1 + β * V x))
    hPg.aestronglyMeasurable hPg.aestronglyMeasurable hb (h₁.const_mul ρ) (h₂.const_mul ρ))

/-- **Hairer–Mattingly, Theorem 1.3, from Theorem 3.1, for laws integrating `V`**: under a
drift, a kernel that contracts the weighted oscillation with rate `ρ` satisfies
`∫ (1 + β V) ∂|P ∘ₘ μ₁ - P ∘ₘ μ₂| ≤ ρ ∫ (1 + β V) ∂|μ₁ - μ₂|`. -/
theorem integral_totalVariation_comp_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    {μ₁ μ₂ : Measure X} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : ∫⁻ x, V x ∂μ₁ ≠ ∞) (h₂ : ∫⁻ x, V x ∂μ₂ ≠ ∞) :
    ∫ x, (1 + β * V x) ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ρ * ∫ x, (1 + β * V x) ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  have hw : ∀ μ : Measure X, IsFiniteMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      Integrable (fun x ↦ 1 + β * (V x : ℝ)) μ := fun μ _ h ↦ (integrable_const 1).add
    ((by simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable h :
      Integrable (fun x ↦ (V x : ℝ)) μ).const_mul β)
  exact integral_totalVariation_comp_le hV hβ hP (by simp) (hw μ₁ inferInstance h₁)
    (hw μ₂ inferInstance h₂)
    (integrable_comp_of_drift hV hdrift (hw μ₁ inferInstance h₁))
    (integrable_comp_of_drift hV hdrift (hw μ₂ inferInstance h₂))

/-- **Hairer–Mattingly, Theorem 1.3, from Theorem 3.1**: under a drift, a kernel that contracts
the weighted oscillation with rate `ρ` satisfies `ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ ρ ρ_β(μ₁, μ₂)` for all
probability measures `μ₁`, `μ₂`, where `ρ_β(μ₁, μ₂) = ∫⁻ (1 + β V) ∂|μ₁ - μ₂| ∈ [0, ∞]` is the
weighted total variation. No moment is assumed; when `ρ_β(μ₁, μ₂) = ∞` and `ρ > 0` the bound is
trivial. -/
theorem lintegral_totalVariation_comp_le [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    ∫⁻ x, ENNReal.ofReal (1 + β * V x)
        ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ENNReal.ofReal ρ * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
        ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · simp [comp_eq_comp_of_contraction_of_nonpos hβ hρ hP μ₁ μ₂, SignedMeasure.totalVariation_zero]
  by_cases htop : ∫⁻ x, ENNReal.ofReal (1 + β * V x)
      ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hρ).ne']
    exact le_top
  set θ := μ₁ ⊓ μ₂
  have h₁ : θ + (μ₁ - μ₂) = μ₁ := Measure.inf_add_sub μ₁ μ₂
  have h₂ : θ + (μ₂ - μ₁) = μ₂ := (congrArg (· + (μ₂ - μ₁)) (inf_comm μ₁ μ₂)).trans
    (Measure.inf_add_sub μ₂ μ₁)
  have : IsFiniteMeasure θ := isFiniteMeasure_of_le μ₁ inf_le_left
  have hw0 : ∀ x, 0 ≤ 1 + β * (V x : ℝ) := fun x ↦ by positivity
  have hwm : Measurable fun x ↦ 1 + β * (V x : ℝ) :=
    measurable_const.add (measurable_const.mul hV.coe_nnreal_real)
  have hint : ∀ ξ : Measure X, ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂ξ ≠ ∞ →
      Integrable (fun x ↦ 1 + β * (V x : ℝ)) ξ := fun ξ h ↦
    ⟨hwm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hw0)).2 h.lt_top⟩
  rw [Measure.totalVariation_toSignedMeasure_sub, lintegral_add_measure] at htop
  have ha := hint _ (ENNReal.add_ne_top.1 htop).1
  have hb := hint _ (ENNReal.add_ne_top.1 htop).2
  have hm : (μ₁ - μ₂) univ = (μ₂ - μ₁) univ := (add_right_inj_of_ne_top (measure_ne_top θ univ)).1
    (by rw [← Measure.add_apply, ← Measure.add_apply, h₁, h₂, measure_univ, measure_univ])
  rw [Measure.toSignedMeasure_sub_eq_of_add_eq (θ := P ∘ₘ θ) (ν₁ := P ∘ₘ (μ₁ - μ₂))
      (ν₂ := P ∘ₘ (μ₂ - μ₁)) (by rw [← Measure.comp_add, h₁]) (by rw [← Measure.comp_add, h₂]),
    Measure.toSignedMeasure_sub_eq_of_add_eq h₁ h₂,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_comp_of_drift hV hdrift
      ha).totalVariation_toSignedMeasure_sub (integrable_comp_of_drift hV hdrift hb))
      (ae_of_all _ hw0),
    ← ofReal_integral_eq_lintegral_ofReal (ha.totalVariation_toSignedMeasure_sub hb)
      (ae_of_all _ hw0), ← ENNReal.ofReal_mul hρ.le]
  exact ENNReal.ofReal_le_ofReal (integral_totalVariation_comp_le hV hβ hP hm ha hb
    (integrable_comp_of_drift hV hdrift ha) (integrable_comp_of_drift hV hdrift hb))

/-- **Hairer–Mattingly, Theorem 3.1 from Theorem 1.3** (through their Lemma 2.1): under a drift,
if the weighted total variation contracts with rate `ρ` between the laws `P ∘ₘ dirac x`,
`ρ_β(P ∘ₘ dirac x, P ∘ₘ dirac y) ≤ ρ ρ_β(dirac x, dirac y)` for all `x`, `y`, then `P`
contracts the weighted oscillation with rate `ρ`. With `lintegral_totalVariation_comp_le`, the
contraction of the oscillation and the contraction of the weighted total variation between all
laws are equivalent. -/
theorem forall_abs_integral_sub_le_of_lintegral_totalVariation_le [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ≥0}
    (h : ∀ x y, ∫⁻ z, ENNReal.ofReal (1 + β * V z) ∂((P ∘ₘ Measure.dirac x).toSignedMeasure -
        (P ∘ₘ Measure.dirac y).toSignedMeasure).totalVariation ≤
      ρ * ∫⁻ z, ENNReal.ofReal (1 + β * V z)
        ∂((Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure).totalVariation) :
    ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y) := by
  intro φ hφ c hφc x y
  have hc : 0 ≤ c := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφc x x)) (by positivity)
  have hw0 : ∀ z, 0 ≤ 1 + (β : ℝ) * V z := fun z ↦ by positivity
  have hwm : Measurable fun z ↦ 1 + (β : ℝ) * V z :=
    measurable_const.add (measurable_const.mul hV.coe_nnreal_real)
  have hVi : ∀ u, Integrable (fun z ↦ (V z : ℝ)) (P u) := fun u ↦ by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_ne_top_of_drift hdrift u)
  have hwi : ∀ u, Integrable (fun z ↦ 1 + (β : ℝ) * V z) (P ∘ₘ Measure.dirac u) := fun u ↦ by
    rw [Measure.dirac_bind (Kernel.measurable _)]
    exact (integrable_const 1).add ((hVi u).const_mul β)
  obtain ⟨b, hb⟩ := exists_forall_abs_add_le (f := φ) (w := fun z ↦ c * (1 + β * V z))
    fun u v ↦ (hφc u v).trans_eq (by ring)
  have e : ∀ u, ∫ z, φ z ∂(P u) = ∫ z, φ z + b ∂(P ∘ₘ Measure.dirac u) - b := fun u ↦ by
    rw [Measure.dirac_bind (Kernel.measurable _), integral_add (integrable_of_forall_abs_sub_le hV
      (lintegral_ne_top_of_drift hdrift u) hφ hφc) (integrable_const b)]
    simp
  have hA : ∫ z, (1 + (β : ℝ) * V z) ∂((P ∘ₘ Measure.dirac x).toSignedMeasure -
      (P ∘ₘ Measure.dirac y).toSignedMeasure).totalVariation ≤
        (ρ : ℝ) * (2 + (β : ℝ) * V x + β * V y) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_integral_eq_lintegral_ofReal
      ((hwi x).totalVariation_toSignedMeasure_sub (hwi y)) (ae_of_all _ hw0)]
    refine (h x y).trans ?_
    rw [ENNReal.ofReal_mul ρ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    gcongr
    refine (Measure.lintegral_totalVariation_dirac_sub_dirac_le hwm.ennreal_ofReal x y).trans_eq ?_
    rw [← ENNReal.ofReal_add (hw0 x) (hw0 y)]
    congr 1
    ring
  rw [e x, e y, sub_sub_sub_cancel_right]
  calc _ ≤ ∫ z, c * (1 + β * V z) ∂((P ∘ₘ Measure.dirac x).toSignedMeasure -
        (P ∘ₘ Measure.dirac y).toSignedMeasure).totalVariation :=
        norm_integral_sub_integral_le_integral_totalVariation _ _ (g := fun z ↦ φ z + b)
          (hφ.add_const b).aestronglyMeasurable (hφ.add_const b).aestronglyMeasurable hb
          ((hwi x).const_mul c) ((hwi y).const_mul c)
    _ ≤ c * ((ρ : ℝ) * (2 + (β : ℝ) * V x + β * V y)) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hA hc
    _ = ρ * c * (2 + β * V x + β * V y) := by ring

/-- **Hairer–Mattingly, Theorem 1.3, iterated**: `ρ_β(Pⁿ ∘ₘ μ₁, Pⁿ ∘ₘ μ₂) ≤ ρⁿ ρ_β(μ₁, μ₂)` for
all probability measures `μ₁`, `μ₂`. -/
theorem lintegral_totalVariation_comp_pow_le [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 ≤ β)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (1 + β * V x)
        ∂(((P ^ n) ∘ₘ μ₁).toSignedMeasure - ((P ^ n) ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ENNReal.ofReal ρ ^ n * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
        ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  induction n with
  | zero =>
    have h0 : ∀ μ : Measure X, (1 : Kernel X X) ∘ₘ μ = μ := fun μ ↦ Measure.id_comp
    simp only [pow_zero, h0, one_mul, le_refl]
  | succ n ih =>
    have hs : ∀ μ : Measure X,
        (P ^ (n + 1) : Kernel X X) ∘ₘ μ = P ∘ₘ ((P ^ n : Kernel X X) ∘ₘ μ) := fun μ ↦ by
      rw [Measure.comp_assoc]
      exact congrArg (fun κ : Kernel X X ↦ κ ∘ₘ μ) (pow_succ' P n)
    simp only [hs]
    calc _ ≤ ENNReal.ofReal ρ * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
          ∂(((P ^ n) ∘ₘ μ₁).toSignedMeasure - ((P ^ n) ∘ₘ μ₂).toSignedMeasure).totalVariation :=
          lintegral_totalVariation_comp_le hV hdrift hβ hP _ _
      _ ≤ _ := by
          rw [pow_succ', mul_assoc]
          gcongr

/-- **Some power contracts `ρ₁`** (Hairer–Mattingly, Remark 1.4): if `P` contracts `ρ_β`,
`β > 0`, with rate `ρ`, then `ρ₁(Pⁿ ∘ₘ μ₁, Pⁿ ∘ₘ μ₂) ≤ max 1 β · max 1 β⁻¹ · ρⁿ · ρ₁(μ₁, μ₂)`,
since `1 + V ≤ max 1 β⁻¹ (1 + β V)` and `1 + β V ≤ max 1 β (1 + V)`; so `Pⁿ` contracts `ρ₁` once
`max 1 β · max 1 β⁻¹ · ρⁿ < 1`. -/
theorem lintegral_totalVariation_comp_pow_le_max [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {β ρ : ℝ} (hβ : 0 < β)
    (hP : ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y))
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (1 + V x)
        ∂(((P ^ n) ∘ₘ μ₁).toSignedMeasure - ((P ^ n) ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ENNReal.ofReal (max 1 β⁻¹) * ENNReal.ofReal ρ ^ n * ENNReal.ofReal (max 1 β) *
        ∫⁻ x, ENNReal.ofReal (1 + V x)
          ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  have hm : 1 ≤ max 1 β⁻¹ * β := (inv_mul_cancel₀ hβ.ne').symm.le.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hβ.le)
  have h₁ (x : X) : ENNReal.ofReal (1 + V x) ≤ ENNReal.ofReal (max 1 β⁻¹) *
      ENNReal.ofReal (1 + β * V x) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [le_max_left 1 β⁻¹, (V x).coe_nonneg, mul_le_mul_of_nonneg_right hm (V x).coe_nonneg]
  have h₂ (x : X) : ENNReal.ofReal (1 + β * V x) ≤ ENNReal.ofReal (max 1 β) *
      ENNReal.ofReal (1 + V x) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [le_max_left 1 β, le_max_right 1 β,
      (V x).coe_nonneg])
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (max 1 β⁻¹) * ENNReal.ofReal (1 + β * V x)
        ∂(((P ^ n) ∘ₘ μ₁).toSignedMeasure - ((P ^ n) ∘ₘ μ₂).toSignedMeasure).totalVariation :=
        lintegral_mono h₁
    _ ≤ ENNReal.ofReal (max 1 β⁻¹) * (ENNReal.ofReal ρ ^ n * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
        ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation) := by
        rw [lintegral_const_mul _ (by fun_prop)]
        gcongr
        exact lintegral_totalVariation_comp_pow_le hV hdrift hβ.le hP μ₁ μ₂ n
    _ ≤ ENNReal.ofReal (max 1 β⁻¹) * (ENNReal.ofReal ρ ^ n * ∫⁻ x, ENNReal.ofReal (max 1 β) *
        ENNReal.ofReal (1 + V x) ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation) := by
        gcongr with x
        exact h₂ x
    _ = _ := by rw [lintegral_const_mul _ (by fun_prop)]; ring

end ProbabilityTheory.Kernel
