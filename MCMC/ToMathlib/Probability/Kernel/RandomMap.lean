/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Independence.Basic
public import MCMC.ToMathlib.Probability.Kernel.Harris
public import MCMC.ToMathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Iterated random maps, and the Gaussian autoregression

The one-step law of the recursion `ξ (k + 1) = F (ξ k) (w k)`, `w k ∼ ρ`, is the kernel
`x ↦ ρ.map (F x)`, which is Mathlib's `(Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)`
(`ProbabilityTheory.Kernel.map_prod_const_apply`); no new object is introduced. From a law `μ`
it gives the law of `F ξ w` for `ξ ∼ μ` and an independent `w ∼ ρ`:
`(μ.prod ρ).map (Function.uncurry F)` (`ProbabilityTheory.Kernel.comp_map_prod_const`), and the
joint law `μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2))` for every kernel with
`Q y = ρ.map (F y)` (`MeasureTheory.Measure.compProd_eq_map_prod`).

**The recursion is the Markov chain of this kernel**
(`ProbabilityTheory.map_eq_trajMeasure_of_iIndepFun`): for random variables on a probability
space with `ξ (k + 1) = F (ξ k) (w k)`, the `w k` independent (`iIndepFun`) with law `ρ` and
independent of `ξ 0` (`IndepFun (ξ 0) (fun ω k ↦ w k ω)`), the law of the trajectory `(ξ k)` is
Mathlib's `Kernel.trajMeasure` of the kernel started at the law of `ξ 0`. So the laws of the
chain (`ProbabilityTheory.Kernel.trajMeasure_map_eval`,
`ProbabilityTheory.Kernel.trajMeasure_map_eval_eval_add`) are those of the recursion. The step:
the trajectory up to time `a` is independent of `w a`
(`ProbabilityTheory.indepFun_frestrictLe_of_iIndepFun`).

* `ProbabilityTheory.Kernel.lintegral_map_prod_const_le`: the drift of this kernel from a
  pointwise bound `V (F x w) ≤ γ V x + g w` with `∫⁻ g ∂ρ ≤ K`.
* `MeasureTheory.Measure.smul_restrict_le_withDensity`: a density `f ≥ ε` on `C` dominates
  `ε • μ.restrict C`, the source of a minorization; for Gaussian laws with bounded means,
  `ProbabilityTheory.smul_restrict_le_gaussianReal`.
* `ProbabilityTheory.integral_sq_gaussianReal`: `∫ y² ∂N(m, v) = m² + v`.
* The Gaussian autoregression `y ↦ a y + w`, `w ∼ N(0, v)`: one step maps `N(m, σ)` to
  `N(a m, a² σ + v)` (`ProbabilityTheory.Kernel.comp_gaussianReal_ar`, from Mathlib's
  `gaussianReal_map_const_mul` and `gaussianReal_conv_gaussianReal`), so `n` steps from `x` give
  `N(aⁿ x, v ∑_{k < n} a^{2k})` (`…pow_apply_gaussianReal_ar`). For `|a| < 1` its invariant law is
  `N(0, v / (1 - a²))` (`…invariant_gaussianReal_ar`); it is the only one, at
  `v = 0` too (`…invariant_iff_eq_gaussianReal_ar`, through
  `MeasureTheory.Measure.eq_dirac_zero_of_map_const_mul_eq`), and for `v ≠ 0`, from every initial
  law with a finite second moment the laws converge to it geometrically in the weighted norm
  `1 + y²` (`…exists_abs_integral_comp_pow_sub_integral_le_gaussian_ar`; `v ≠ 0` is forced,
  `…not_exists_abs_integral_comp_pow_sub_integral_le_gaussian_ar_zero`), by Harris' theorem with
  `V y = y²` and the minorization on bounded sets. The constants are existential; the
  minorization constant of the proof is far below the true one and gives no useful rate. For
  `a ≠ 0` Doeblin's theorem does not apply: the laws `N(a y, v)` have no common component
  uniformly in `y`; at `a = 0` all of them are `N(0, v)`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "restrict_le_withDensity\|smul_restrict_le"
MeasureTheory Probability` finds nothing; `Probability/Distributions/Gaussian/Real.lean` has the
mean, the variance and `MemLp` of `gaussianReal`, `gaussianReal_map_const_mul` and
`gaussianReal_conv_gaussianReal`, and no second moment.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Real

namespace ProbabilityTheory

variable {X W : Type*} {mX : MeasurableSpace X} {mW : MeasurableSpace W}

/-- A density at least `ε` on `C` dominates `ε • μ.restrict C`. -/
theorem _root_.MeasureTheory.Measure.smul_restrict_le_withDensity {μ : Measure X}
    {f : X → ℝ≥0∞} {C : Set X} (hC : MeasurableSet C) {ε : ℝ≥0∞} (hf : ∀ x ∈ C, ε ≤ f x) :
    ε • μ.restrict C ≤ μ.withDensity f := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, withDensity_apply _ hs,
    ← setLIntegral_const]
  calc ∫⁻ _ in s ∩ C, ε ∂μ ≤ ∫⁻ x in s ∩ C, f x ∂μ :=
        setLIntegral_mono' (hs.inter hC) fun x hx ↦ hf x hx.2
    _ ≤ ∫⁻ x in s, f x ∂μ := lintegral_mono_set inter_subset_left

/-- The second moment of a Gaussian law: `∫ y² ∂N(m, v) = m² + v`. -/
theorem integral_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ y, y ^ 2 ∂(gaussianReal m v) = m ^ 2 + v := by
  have hvar := variance_eq_sub (memLp_id_gaussianReal (μ := m) (v := v) 2)
  rw [variance_id_gaussianReal] at hvar
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at hvar
  linarith

/-- The second moment of a Gaussian law as a Lebesgue integral of `‖y‖₊²`. -/
theorem lintegral_nnnorm_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫⁻ y, ((‖y‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂(gaussianReal m v) = ((‖m‖₊ ^ 2 + v : ℝ≥0) : ℝ≥0∞) := by
  have hint : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
  rw [← ENNReal.ofReal_coe_nnreal]
  push_cast
  rw [Real.norm_eq_abs, sq_abs, ← integral_sq_gaussianReal, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y ↦ sq_nonneg y)]
  refine lintegral_congr fun y ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  push_cast
  rw [← ENNReal.ofReal_pow (norm_nonneg y), Real.norm_eq_abs, sq_abs]

/-- A Gaussian law with mean `|m| ≤ M` has density at least
`(√(2πv))⁻¹ exp (-(r + M)² / (2v))` on every measurable `C ⊆ [-r, r]`. -/
theorem smul_restrict_le_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {m M r : ℝ} (hm : |m| ≤ M)
    {C : Set ℝ} (hC : MeasurableSet C) (hCr : ∀ z ∈ C, |z| ≤ r) :
    ENNReal.ofReal ((√(2 * π * v))⁻¹ * Real.exp (-(r + M) ^ 2 / (2 * v))) •
      volume.restrict C ≤ gaussianReal m v := by
  rw [gaussianReal_of_var_ne_zero m hv]
  refine Measure.smul_restrict_le_withDensity hC fun z hz ↦ ?_
  rw [gaussianPDF_def, gaussianPDFReal_def]
  have hv0 : (0 : ℝ) < v := by positivity
  have hz' : |z - m| ≤ r + M := (abs_sub _ _).trans (add_le_add (hCr z hz) hm)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (div_le_div_of_nonneg_right (neg_le_neg ?_) (by positivity))) (by positivity))
  exact (sq_abs (z - m)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hz' 2)

namespace Kernel

/-- The kernel of the iterated random map `ξ ↦ F ξ w`, `w ∼ ρ`, at `x` is `ρ.map (F x)`. -/
theorem map_prod_const_apply {F : X → W → X} (hF : Measurable (Function.uncurry F))
    (ρ : Measure W) [SFinite ρ] (x : X) :
    ((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)) x = ρ.map (F x) := by
  rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

/-- The law of `F ξ w` for `ξ ∼ μ` and an independent `w ∼ ρ`: the kernel of the iterated random
map composed with `μ` is `(μ.prod ρ).map (uncurry F)`. -/
theorem comp_map_prod_const {F : X → W → X} (hF : Measurable (Function.uncurry F))
    (ρ : Measure W) [SFinite ρ] (μ : Measure X) [SFinite μ] :
    (Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F) ∘ₘ μ =
      (μ.prod ρ).map (Function.uncurry F) := by
  rw [← Measure.map_comp _ _ hF, ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

/-- **The drift of an iterated random map** from a pointwise bound: if
`V (F x w) ≤ γ V x + g w` for all `x`, `w` and `∫⁻ g ∂ρ ≤ K`, then
`∫⁻ V ∂(P x) ≤ γ V x + K` for the kernel `P x = ρ.map (F x)`. -/
theorem lintegral_map_prod_const_le {F : X → W → X} (hF : Measurable (Function.uncurry F))
    {V : X → ℝ≥0} (hV : Measurable V) {ρ : Measure W} [IsProbabilityMeasure ρ] {γ K : ℝ≥0}
    {g : W → ℝ≥0∞} (h : ∀ x w, (V (F x w) : ℝ≥0∞) ≤ γ * V x + g w) (hg : ∫⁻ w, g w ∂ρ ≤ K)
    (x : X) :
    ∫⁻ y, V y ∂((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F) x) ≤ γ * V x + K := by
  rw [map_prod_const_apply hF]
  calc ∫⁻ y, (V y : ℝ≥0∞) ∂(ρ.map (F x)) = ∫⁻ w, (V (F x w) : ℝ≥0∞) ∂ρ :=
        MeasureTheory.lintegral_map hV.coe_nnreal_ennreal (hF.comp measurable_prodMk_left)
    _ ≤ ∫⁻ w, (γ * V x + g w) ∂ρ := lintegral_mono (h x)
    _ = γ * V x + ∫⁻ w, g w ∂ρ := by
        rw [lintegral_add_left measurable_const, MeasureTheory.lintegral_const, measure_univ,
          mul_one]
    _ ≤ γ * V x + K := by gcongr

/-- The Gaussian autoregression `y ↦ a y + w`, `w ∼ N(0, v)`, moves by `x ↦ N(a x, v)`. -/
theorem map_prod_const_gaussianReal_apply (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ a * p.1 + p.2) x =
      gaussianReal (a * x) v := by
  have h := map_prod_const_apply (F := fun x w ↦ a * x + w)
    ((measurable_const.mul measurable_fst).add measurable_snd) (gaussianReal 0 v) x
  rw [gaussianReal_map_const_add, zero_add] at h
  exact h

/-- **The Gaussian autoregression satisfies Harris' hypotheses** with
`V y = y²`: the drift `γ = a²`, `K = v`, and for some `R` with `2 v + a² R < R` the
minorization `α • λ|[0, 1] ≤ N(a x, v)` on `{x² ≤ R}`, `α > 0`. -/
theorem exists_drift_minorization_gaussian_ar {a : ℝ} (ha : |a| < 1) {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ R α : ℝ≥0, 0 < α ∧ 2 * v + ‖a‖₊ ^ 2 * R < R ∧
      (∀ x : ℝ, ∫⁻ y, ((‖y‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂(((Kernel.id ×ₖ Kernel.const ℝ
        (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ a * p.1 + p.2) x) ≤
          (‖a‖₊ ^ 2 : ℝ≥0) * (‖x‖₊ ^ 2 : ℝ≥0) + v) ∧
      ∀ x : ℝ, ‖x‖₊ ^ 2 ≤ R → α • volume.restrict (Icc (0 : ℝ) 1) ≤
        ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ a * p.1 + p.2) x := by
  have hγ : ‖a‖ ^ 2 < 1 := by
    simpa [sq_abs] using (sq_lt_one_iff_abs_lt_one a).2 ha
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * v : ℝ) / (1 - ‖a‖ ^ 2))
  have hv0 : (0 : ℝ) < v := by positivity
  set ε : ℝ := (√(2 * π * v))⁻¹ * Real.exp (-(1 + (n + 1)) ^ 2 / (2 * v))
  have hε : 0 < ε := by positivity
  refine ⟨n, ε.toNNReal, Real.toNNReal_pos.2 hε, ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · rw [← NNReal.coe_lt_coe]
    push_cast
    nlinarith [(div_lt_iff₀ (by linarith : (0 : ℝ) < 1 - ‖a‖ ^ 2)).1 hn]
  · rw [map_prod_const_gaussianReal_apply, lintegral_nnnorm_sq_gaussianReal, nnnorm_mul,
      mul_pow]
    push_cast
    exact le_rfl
  · rw [map_prod_const_gaussianReal_apply, ENNReal.smul_def]
    have hx' : x ^ 2 ≤ n := by simpa [sq_abs] using NNReal.coe_le_coe.2 hx
    refine smul_restrict_le_gaussianReal hv (M := n + 1) ?_ measurableSet_Icc fun z hz ↦ ?_
    · rw [abs_mul]
      nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1),
        mul_le_mul_of_nonneg_right ha.le (abs_nonneg x)]
    · rw [abs_of_nonneg hz.1]
      exact hz.2

/-- **One step of the Gaussian autoregression from a Gaussian law**: `y ↦ a y + w`, `w ∼ N(0, v)`,
maps `N(m, σ)` to `N(a m, a² σ + v)` (`σ`, `v` the variances). -/
theorem comp_gaussianReal_ar (a : ℝ) (v : ℝ≥0) (m : ℝ) (σ : ℝ≥0) :
    ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ a * p.1 + p.2) ∘ₘ
      gaussianReal m σ = gaussianReal (a * m) (‖a‖₊ ^ 2 * σ + v) := by
  have hF : Function.uncurry (fun x w : ℝ ↦ a * x + w) =
      (fun q : ℝ × ℝ ↦ q.1 + q.2) ∘ Prod.map (a * ·) id := rfl
  refine (comp_map_prod_const (F := fun x w : ℝ ↦ a * x + w) (by fun_prop) _ _).trans ?_
  rw [hF, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_prod_map _ _ (by fun_prop)
    measurable_id, gaussianReal_map_const_mul, Measure.map_id]
  refine (gaussianReal_conv_gaussianReal (m₁ := a * m) (m₂ := 0)).trans ?_
  congr 1
  · rw [add_zero]
  · congr 1
    exact NNReal.eq (by simp)

/-- **The `n`-step law of the Gaussian autoregression**: from `x`, after `n` steps of
`y ↦ a y + w`, `w ∼ N(0, v)`, the law is `N(aⁿ x, v ∑_{k < n} (a²)ᵏ)`. -/
theorem pow_apply_gaussianReal_ar (a : ℝ) (v : ℝ≥0) (n : ℕ) (x : ℝ) :
    (((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ a * p.1 + p.2) ^ n) x =
      gaussianReal (a ^ n * x) (v * ∑ k ∈ Finset.range n, (‖a‖₊ ^ 2) ^ k) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (Kernel.id_apply x).trans (by simp [gaussianReal_zero_var])
  | succ n ih =>
    rw [add_comm, Kernel.pow_add, pow_one, Kernel.comp_apply, ih, comp_gaussianReal_ar]
    congr 1
    · ring
    · rw [add_comm 1 n, Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum,
        Finset.mul_sum, Finset.mul_sum]
      exact congrArg (· + v) (Finset.sum_congr rfl fun k _ ↦ by ring)

/-- **The invariant law of the Gaussian autoregression**: for `|a| < 1`, `N(0, v / (1 - a²))` is
invariant under `y ↦ a y + w`, `w ∼ N(0, v)`. -/
theorem invariant_gaussianReal_ar {a : ℝ} (ha : |a| < 1) (v : ℝ≥0) :
    Invariant ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) (gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2))) := by
  have hc : (‖a‖ : ℝ) ^ 2 < 1 := by simpa [sq_abs] using (sq_lt_one_iff_abs_lt_one a).2 ha
  have hc' : ‖a‖₊ ^ 2 < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; exact hc
  refine (comp_gaussianReal_ar a v 0 _).trans ?_
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_sub hc'.le, NNReal.coe_one, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
    rw [Real.norm_eq_abs, sq_abs] at hc
    have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := (sub_pos.2 hc).ne'
    field_simp
    ring

/-- **A law invariant under `y ↦ a y`, `|a| < 1`, is `dirac 0`**: `μ.map (a * ·) = μ` gives
`μ {ε < |y|} = μ {ε < |aⁿ y|}` for every `n`, and these sets decrease to `∅`. -/
theorem _root_.MeasureTheory.Measure.eq_dirac_zero_of_map_const_mul_eq {a : ℝ} (ha : |a| < 1)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : μ.map (a * ·) = μ) : μ = Measure.dirac 0 := by
  have hn (n : ℕ) : μ.map (a ^ n * ·) = μ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [(funext fun y ↦ by simp only [Function.comp_apply]; ring :
        (a ^ (n + 1) * ·) = (a ^ n * ·) ∘ (a * ·)),
        ← Measure.map_map (by fun_prop) (by fun_prop), h, ih]
  have hm (ε : ℝ) (n : ℕ) : MeasurableSet {y : ℝ | ε < |a ^ n * y|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hanti (ε : ℝ) : Antitone fun n ↦ {y : ℝ | ε < |a ^ n * y|} := fun m n hmn y hy ↦ by
    simp only [Set.mem_ofPred_eq, abs_mul, abs_pow] at hy ⊢
    exact lt_of_lt_of_le hy (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (abs_nonneg a) ha.le hmn) (abs_nonneg y))
  have hempty (ε : ℝ) (hε : 0 < ε) : ⋂ n, {y : ℝ | ε < |a ^ n * y|} = ∅ :=
    Set.iInter_eq_empty_iff.2 fun y ↦ by
      obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (div_pos hε (by positivity : (0 : ℝ) < |y| + 1)) ha
      rw [lt_div_iff₀ (by positivity)] at hn'
      refine ⟨n, fun hy ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, abs_mul, abs_pow] at hy
      nlinarith [pow_nonneg (abs_nonneg a) n, abs_nonneg y]
  have hc (ε : ℝ) (n : ℕ) : μ {y | ε < |a ^ n * y|} = μ {y | ε < |y|} := by
    conv_rhs => rw [← hn n]
    rw [Measure.map_apply (by fun_prop) (measurableSet_lt measurable_const (by fun_prop))]
    rfl
  have hS (ε : ℝ) (hε : 0 < ε) : μ {y | ε < |y|} = 0 :=
    tendsto_nhds_unique (l := atTop) (tendsto_const_nhds.congr fun n ↦ (hc ε n).symm) (by
      rw [← measure_empty (μ := μ), ← hempty ε hε]
      exact tendsto_measure_iInter_atTop (fun n ↦ (hm ε n).nullMeasurableSet) (hanti ε)
        ⟨0, measure_ne_top _ _⟩)
  have hae : (fun y : ℝ ↦ y) =ᵐ[μ] fun _ ↦ 0 := by
    refine measure_mono_null (fun y (hy : y ≠ 0) ↦ ?_) (measure_iUnion_null fun k : ℕ ↦
      hS (1 / (k + 1)) (by positivity))
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.2 hy)
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  calc μ = μ.map fun y ↦ y := Measure.map_id'.symm
    _ = μ.map fun _ ↦ 0 := Measure.map_congr hae
    _ = Measure.dirac 0 := by rw [Measure.map_const, measure_univ, one_smul]

/-- **The Gaussian autoregression has exactly one invariant law, `N(0, v / (1 - a²))`**: for
`|a| < 1`, a probability measure is invariant under `y ↦ a y + w`, `w ∼ N(0, v)`, iff it is
`N(0, v / (1 - a²))`; at `v = 0` this law is `dirac 0` and invariance is `μ.map (a * ·) = μ`
(`MeasureTheory.Measure.eq_dirac_zero_of_map_const_mul_eq`). -/
theorem invariant_iff_eq_gaussianReal_ar {a : ℝ} (ha : |a| < 1) {v : ℝ≥0}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Invariant ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) μ ↔ μ = gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ invariant_gaussianReal_ar ha v⟩
  rcases eq_or_ne v 0 with rfl | hv
  · have hP : ⇑((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 0)).map
        fun p : ℝ × ℝ ↦ a * p.1 + p.2) = fun x ↦ Measure.dirac (a * x) :=
      funext fun x ↦ by rw [map_prod_const_gaussianReal_apply, gaussianReal_zero_var]
    rw [zero_div, gaussianReal_zero_var]
    refine Measure.eq_dirac_zero_of_map_const_mul_eq ha ?_
    rw [← Measure.bind_dirac_eq_map μ (by fun_prop)]
    exact (congrArg μ.bind hP).symm.trans h
  obtain ⟨R, α, hα, hR, hdrift, hmin⟩ := exists_drift_minorization_gaussian_ar ha hv
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have : IsMarkovKernel ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) :=
    IsMarkovKernel.map _ ((measurable_const.mul measurable_fst).add measurable_snd)
  exact (existsUnique_invariant_of_drift_of_minorization (V := fun y ↦ ‖y‖₊ ^ 2)
    (by fun_prop) hdrift hα (lt_of_le_of_lt (by rw [two_mul, add_assoc]; exact le_add_self) hR)
    hmin).unique ⟨inferInstance, h⟩ ⟨inferInstance, invariant_gaussianReal_ar ha v⟩

/-- **Geometric convergence of the Gaussian autoregression** from every initial law with a finite
second moment: for `|a| < 1` and `v ≠ 0` there are `C ≥ 0` and `0 ≤ ρ < 1` with
`|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂N(0, v / (1 - a²))| ≤ C ρⁿ M (1 + ∫ y² ∂μ)` for every measurable `φ` with
`|φ y| ≤ M (1 + y²)`. Here `v ≠ 0` is forced
(`not_exists_abs_integral_comp_pow_sub_integral_le_gaussian_ar_zero`). -/
theorem exists_abs_integral_comp_pow_sub_integral_le_gaussian_ar {a : ℝ} (ha : |a| < 1)
    {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      ∫⁻ y, ((‖y‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂μ ≠ ∞ →
      ∀ φ : ℝ → ℝ, Measurable φ → ∀ M : ℝ, (∀ y, |φ y| ≤ M * (1 + y ^ 2)) → ∀ n : ℕ,
        |∫ y, φ y ∂((((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
          fun p : ℝ × ℝ ↦ a * p.1 + p.2) ^ n) ∘ₘ μ) -
            ∫ y, φ y ∂(gaussianReal 0 (v / (1 - ‖a‖₊ ^ 2)))| ≤
          C * ρ ^ n * M * (1 + ∫ y, y ^ 2 ∂μ) := by
  obtain ⟨R, α, hα, hR, hdrift, hmin⟩ := exists_drift_minorization_gaussian_ar ha hv
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have : IsMarkovKernel ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ a * p.1 + p.2) :=
    IsMarkovKernel.map _ ((measurable_const.mul measurable_fst).add measurable_snd)
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization
    (V := fun y ↦ ‖y‖₊ ^ 2) (by fun_prop) hdrift hα
    (lt_of_le_of_lt (by rw [two_mul, add_assoc]; exact le_add_self) hR) hmin
  refine ⟨C, ρ, hC, hρ0, hρ, fun μ hμ hμV φ hφ M hφM n ↦ ?_⟩
  simpa [sq_abs] using h _ inferInstance (invariant_gaussianReal_ar ha v) μ hμ hμV φ hφ M
    (fun y ↦ by simpa [sq_abs] using hφM y) n

/-- **`v ≠ 0` is forced in the convergence of the Gaussian autoregression**: at `v = 0`,
`a = 1/2`, the laws from `dirac 1` are `dirac 2⁻ⁿ` (`pow_apply_gaussianReal_ar`) and never charge
`{0}`, which carries the invariant law `dirac 0`, so `φ = 1_{y ≠ 0}` keeps
`|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| = 1` and no bound `C ρⁿ M (1 + ∫ y² ∂μ)` with `ρ < 1` holds. -/
theorem not_exists_abs_integral_comp_pow_sub_integral_le_gaussian_ar_zero :
    ¬ ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      ∫⁻ y, ((‖y‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) ∂μ ≠ ∞ →
      ∀ φ : ℝ → ℝ, Measurable φ → ∀ M : ℝ, (∀ y, |φ y| ≤ M * (1 + y ^ 2)) → ∀ n : ℕ,
        |∫ y, φ y ∂((((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 0)).map
          fun p : ℝ × ℝ ↦ 1 / 2 * p.1 + p.2) ^ n) ∘ₘ μ) -
            ∫ y, φ y ∂(gaussianReal 0 (0 / (1 - ‖(1 / 2 : ℝ)‖₊ ^ 2)))| ≤
          C * ρ ^ n * M * (1 + ∫ y, y ^ 2 ∂μ) := by
  rintro ⟨C, ρ, hC, hρ0, hρ, h⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (2 * C + 1)) hρ
  have hφ : Measurable fun y : ℝ ↦ if y = 0 then (0 : ℝ) else 1 :=
    Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
  have hb := h (Measure.dirac 1) inferInstance (by simp) _ hφ 1 (fun y ↦ by
    split_ifs <;> simp <;> positivity) n
  rw [Measure.dirac_bind (Kernel.measurable _), pow_apply_gaussianReal_ar, zero_mul,
    gaussianReal_zero_var, zero_div, gaussianReal_zero_var, integral_dirac, integral_dirac,
    integral_dirac] at hb
  simp only [mul_one, ne_eq, pow_eq_zero_iff', one_div, inv_eq_zero, OfNat.ofNat_ne_zero,
    false_and, ↓reduceIte, sub_zero, abs_one, one_pow] at hb
  rw [lt_div_iff₀ (by positivity)] at hn
  nlinarith [pow_nonneg hρ0 n]

/-- The joint law of `y ∼ μ` and `F y w` for an independent `w ∼ ρ`: if `Q y = ρ.map (F y)`, then
`μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2))`. -/
theorem _root_.MeasureTheory.Measure.compProd_eq_map_prod {Y : Type*} {mY : MeasurableSpace Y}
    {Q : Kernel Y X} [IsSFiniteKernel Q] {F : Y → W → X} (hF : Measurable (Function.uncurry F))
    {ρ : Measure W} [SFinite ρ] (hQ : ∀ y, Q y = ρ.map (F y)) (μ : Measure Y) [SFinite μ] :
    μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2)) := by
  have hG : Measurable fun p : Y × W ↦ (p.1, F p.1 p.2) := measurable_fst.prodMk hF
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hG hs, Measure.prod_apply (hG hs)]
  refine lintegral_congr fun y ↦ ?_
  rw [hQ, Measure.map_apply hF.of_uncurry_left (measurable_prodMk_left hs)]
  rfl


end Kernel

open Finset Preorder in
/-- For the recursion `ξ (k + 1) = F (ξ k) (w k)` with independent `w k`, independent of `ξ 0`,
the trajectory up to time `a` is independent of `w a`. -/
theorem indepFun_frestrictLe_of_iIndepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {F : X → W → X} (hF : Measurable (Function.uncurry F))
    {ξ : ℕ → Ω → X} {w : ℕ → Ω → W} (hξ₀ : Measurable (ξ 0)) (hw : ∀ k, Measurable (w k))
    (hξ : ∀ k ω, ξ (k + 1) ω = F (ξ k ω) (w k ω)) (hind : IndepFun (ξ 0) (fun ω k ↦ w k ω) P)
    (hiid : iIndepFun w P) (a : ℕ) :
    IndepFun (fun ω ↦ frestrictLe a fun k ↦ ξ k ω) (w a) P := by
  have hB : Measurable fun ω (i : range a) ↦ w i ω := measurable_pi_iff.2 fun i ↦ hw i
  have h₂ : IndepFun (fun ω (i : range a) ↦ w i ω) (w a) P :=
    (hiid.indepFun_finset (range a) {a} (by simp) hw).comp measurable_id
      (measurable_pi_apply (⟨a, mem_singleton_self a⟩ : ({a} : Finset ℕ)))
  have h₁ : IndepFun (ξ 0) (fun ω ↦ ((fun i : range a ↦ w i ω), w a ω)) P :=
    hind.comp measurable_id
      ((measurable_pi_iff.2 fun i ↦ measurable_pi_apply _).prodMk (measurable_pi_apply a))
  have hG := @comap_measurable _ (X × (range a → W)) inferInstance
    fun ω ↦ (ξ 0 ω, fun i : range a ↦ w i ω)
  have hm (j : ℕ) (hj : j ≤ a) : Measurable[MeasurableSpace.comap
      (fun ω ↦ (ξ 0 ω, fun i : range a ↦ w i ω)) inferInstance] (ξ j) := by
    induction j with
    | zero => exact measurable_fst.comp hG
    | succ j ih =>
      rw [funext (hξ j)]
      exact hF.comp ((ih (by omega)).prodMk ((measurable_pi_apply
        (⟨j, mem_range.2 (by omega)⟩ : range a)).comp (measurable_snd.comp hG)))
  have hY : Measurable[MeasurableSpace.comap (fun ω ↦ (ξ 0 ω, fun i : range a ↦ w i ω))
      inferInstance] fun ω ↦ frestrictLe a fun k ↦ ξ k ω := by
    let := MeasurableSpace.comap (fun ω ↦ (ξ 0 ω, fun i : range a ↦ w i ω))
      (inferInstance : MeasurableSpace (X × (range a → W)))
    exact measurable_pi_iff.2 fun i ↦ hm i.1 (mem_Iic.1 i.2)
  exact (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1
    (h₁.prodMk_of_indepFun_prodMk hξ₀ hB (hw a) h₂)) (MeasurableSpace.comap_le_iff_le_map.2 hY))

open Finset Preorder in
/-- **An iterated random map is a Markov chain**: if `ξ (k + 1) = F (ξ k) (w k)`, where the `w k`
are independent, have law `ρ` and are independent of `ξ 0`, then the trajectory `(ξ k)` has the law
of the chain of any kernel `Q` with `Q x = ρ.map (F x)`, started at the law of `ξ 0`. -/
theorem map_eq_trajMeasure_of_iIndepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Q : Kernel X X} [IsMarkovKernel Q] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) {ρ : Measure W} (hQ : ∀ x, Q x = ρ.map (F x))
    {ξ : ℕ → Ω → X} {w : ℕ → Ω → W} (hξ₀ : Measurable (ξ 0)) (hw : ∀ k, Measurable (w k))
    (hξ : ∀ k ω, ξ (k + 1) ω = F (ξ k ω) (w k ω)) (hind : IndepFun (ξ 0) (fun ω k ↦ w k ω) P)
    (hiid : iIndepFun w P) (hρ : ∀ k, P.map (w k) = ρ) :
    P.map (fun ω k ↦ ξ k ω) = Kernel.trajMeasure (X := fun _ ↦ X) (P.map (ξ 0)) fun n ↦
      Q.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  have hξm (k : ℕ) : Measurable (ξ k) := by
    induction k with
    | zero => exact hξ₀
    | succ k ih => rw [funext (hξ k)]; exact hF.comp (ih.prodMk (hw k))
  have hpath : Measurable fun ω k ↦ ξ k ω := measurable_pi_iff.2 hξm
  have : IsProbabilityMeasure ρ := hρ 0 ▸ (inferInstance : IsProbabilityMeasure (P.map (w 0)))
  refine Kernel.eq_trajMeasure_iff.2 ⟨Measure.map_map (measurable_pi_apply 0) hpath, fun a ↦ ?_⟩
  have hY : IndepFun (frestrictLe a ∘ fun ω k ↦ ξ k ω) (w a) P :=
    indepFun_frestrictLe_of_iIndepFun hF hξ₀ hw hξ hind hiid a
  have hFa := hF.comp (((measurable_pi_apply (⟨a, mem_Iic.2 le_rfl⟩ : Finset.Iic a)).comp
    (measurable_fst (α := Π i : Finset.Iic a, X) (β := W))).prodMk measurable_snd)
  rw [Measure.map_map (by fun_prop) hpath, Measure.map_map (by fun_prop) hpath,
    Measure.compProd_eq_map_prod (F := fun (y : Π i : Finset.Iic a, X) ↦
      F (y ⟨a, mem_Iic.2 le_rfl⟩)) hFa (fun y ↦ hQ _), ← hρ a,
    ← (indepFun_iff_map_prod_eq_prod_map_map ((measurable_frestrictLe a).comp hpath).aemeasurable
      (hw a).aemeasurable).1 hY,
    Measure.map_map (g := fun p : (Π i : Finset.Iic a, X) × W ↦
      (p.1, F (p.1 ⟨a, mem_Iic.2 le_rfl⟩) p.2)) (measurable_fst.prodMk hFa)
      (((measurable_frestrictLe a).comp hpath).prodMk (hw a))]
  congr 1
  funext ω
  exact Prod.ext rfl (hξ a ω)

end ProbabilityTheory
