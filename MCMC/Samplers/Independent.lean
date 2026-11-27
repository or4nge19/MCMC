/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Probability.Kernel.AcceptReject
public import MCMC.ToMathlib.Probability.Kernel.Doeblin

/-!
# The independent Metropolis–Hastings sampler

The proposal is a fixed law `γ`, the kernel `Kernel.const X γ`; the target is `γ.withDensity w`
and the acceptance is `min 1 (w y / w x)`. The constant kernel is `γ`-reversible, so the sampler
is an instance of `ProbabilityTheory.Kernel.isReversible_acceptReject_min_one_div`. If `w ≤ M`,
the kernel dominates `M⁻¹` times the target from every point, and Doeblin's theorem
(`ProbabilityTheory.Kernel.abs_measureReal_comp_pow_sub_le_of_forall_smul_le`) gives convergence
at rate `(1 - 1/M)ⁿ` from every initial law.

## Main statements

* `inv_smul_withDensity_le_acceptReject_const`: the minorization, for every s-finite `γ`.
* `abs_measureReal_acceptReject_const_pow_sub_le`: `|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - 1/M)ⁿ` for
  probability measures `γ`, `π = γ.withDensity w` and `μ`.
* The bound on `w` at every point, not only `γ`-almost everywhere, is needed in both (two
  `example`s): where `w x = ∞` the chain started at `x` does not move. The other hypotheses are
  not shown to be needed: measurability of `w`, and the probability measures of the second
  statement, on which Doeblin's theorem and `MeasureTheory.Measure.real` rest.

## References

* C. P. Robert, G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer (2004),
  Theorem 7.8 with (7.8) (pp. 276–277), first half: uniform ergodicity when the density of the
  target with respect to the proposal is bounded by `M`. Their bound `2 (1 - 1/M)ⁿ` is the bound
  here in their norm (`2 sup_A`, the first line of (7.9)); the minorization is in their proof
  (p. 277). The converse half (no geometric ergodicity for an unbounded density) is not here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X}

/-- **Minorization of the independent Metropolis–Hastings kernel.** If the density `w` of the
target with respect to the proposal law `γ` is at most `M`, the kernel dominates `M⁻¹` times the
target `γ.withDensity w`, from every point. -/
theorem inv_smul_withDensity_le_acceptReject_const {γ : Measure X} [SFinite γ] {w : X → ℝ≥0∞}
    (hw : Measurable w) {M : ℝ≥0∞} (hwM : ∀ x, w x ≤ M) (x : X) :
    M⁻¹ • γ.withDensity w ≤
      acceptReject (Kernel.const X γ) (fun x y ↦ min 1 (w y / w x)) x := by
  have ha : Measurable (Function.uncurry fun x y ↦ min 1 (w y / w x)) :=
    measurable_const.min ((hw.comp measurable_snd).div (hw.comp measurable_fst))
  have hle : ∀ y, M⁻¹ * w y ≤ min 1 (w y / w x) := fun y ↦ le_min
    (by rw [mul_comm]; exact ENNReal.div_le_of_le_mul (by simpa using hwM y))
    (by rw [mul_comm, div_eq_mul_inv]; exact mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 (hwM x)))
  rw [← MeasureTheory.withDensity_smul _ hw, acceptReject_apply ha x, Kernel.const_apply]
  exact (MeasureTheory.withDensity_mono (ae_of_all _ hle)).trans (Measure.le_add_right le_rfl)

/-- The independent Metropolis–Hastings kernel of a probability proposal is a Markov kernel. -/
theorem isMarkovKernel_acceptReject_const {γ : Measure X} [IsProbabilityMeasure γ]
    {w : X → ℝ≥0∞} (hw : Measurable w) :
    IsMarkovKernel (acceptReject (Kernel.const X γ) fun x y ↦ min 1 (w y / w x)) := by
  have ha : Measurable (Function.uncurry fun x y ↦ min 1 (w y / w x)) :=
    measurable_const.min ((hw.comp measurable_snd).div (hw.comp measurable_fst))
  refine isMarkovKernel_acceptReject_iff.2 fun x ↦ ?_
  rw [Kernel.withDensity_apply' _ ha, Measure.restrict_univ]
  exact (lintegral_mono fun y ↦ min_le_left _ _).trans (by simp)

/-- **The independent Metropolis–Hastings sampler is uniformly ergodic** when the density `w` of
the target with respect to the proposal is bounded by `M`: from every initial law `μ`,
`|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - 1/M)ⁿ` for every measurable set `s`. -/
theorem abs_measureReal_acceptReject_const_pow_sub_le {γ : Measure X} [IsProbabilityMeasure γ]
    {w : X → ℝ≥0∞} (hw : Measurable w) [IsProbabilityMeasure (γ.withDensity w)] {M : ℝ≥0}
    (hwM : ∀ x, w x ≤ M) {μ : Measure X} [IsProbabilityMeasure μ] (n : ℕ)
    {s : Set X} (hs : MeasurableSet s) :
    |(((acceptReject (Kernel.const X γ) fun x y ↦ min 1 (w y / w x)) ^ n) ∘ₘ μ).real s -
      (γ.withDensity w).real s| ≤ (1 - (M⁻¹ : ℝ≥0)) ^ n := by
  have := isMarkovKernel_acceptReject_const (γ := γ) hw
  have hM : M ≠ 0 := fun h ↦ IsProbabilityMeasure.ne_zero (γ.withDensity w) (by
    rw [show w = 0 from funext fun x ↦ nonpos_iff_eq_zero.1 ((hwM x).trans_eq (by simp [h])),
      MeasureTheory.withDensity_zero])
  have hmin : ∀ x, (M⁻¹ : ℝ≥0) • γ.withDensity w ≤
      acceptReject (Kernel.const X γ) (fun x y ↦ min 1 (w y / w x)) x := fun x ↦
    Measure.le_iff.2 fun t ht ↦ by
      simpa [ENNReal.coe_inv hM] using
        Measure.le_iff.1 (inv_smul_withDensity_le_acceptReject_const hw hwM x) t ht
  exact abs_measureReal_comp_pow_sub_le_of_forall_smul_le hmin
    (isReversible_acceptReject_min_one_div (isReversible_const γ) hw
      (ae_of_all _ fun x ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hwM x))).invariant n hs

/-- The hypotheses hold together: the target is the proposal law, with the bound `2`. -/
example {γ μ : Measure X} [IsProbabilityMeasure γ] [IsProbabilityMeasure μ] (n : ℕ) {s : Set X}
    (hs : MeasurableSet s) :
    |(((acceptReject (Kernel.const X γ) fun _ _ ↦ min 1 ((1 : ℝ≥0∞) / 1)) ^ n) ∘ₘ μ).real s -
      (γ.withDensity fun _ ↦ 1).real s| ≤ (1 - ((2 : ℝ≥0)⁻¹ : ℝ≥0)) ^ n := by
  have : IsProbabilityMeasure (γ.withDensity fun _ ↦ 1) := by
    rw [show γ.withDensity (fun _ ↦ 1) = γ from MeasureTheory.withDensity_one]
    infer_instance
  exact abs_measureReal_acceptReject_const_pow_sub_le (w := fun _ ↦ 1) measurable_const
    (fun _ ↦ by norm_num) n hs

/-- The bound on `w` is needed at every point in `inv_smul_withDensity_le_acceptReject_const`, not
only `γ`-almost everywhere: on `Bool` with `γ = δ_false`, `w true = ∞`, `w false = 1` and `M = 1`,
the kernel at `true` is `δ_true`. -/
example : ∃ (γ : Measure Bool) (_ : IsProbabilityMeasure γ) (w : Bool → ℝ≥0∞) (M : ℝ≥0∞),
    Measurable w ∧ (∀ᵐ x ∂γ, w x ≤ M) ∧ ¬ M⁻¹ • γ.withDensity w ≤
      acceptReject (Kernel.const Bool γ) (fun x y ↦ min 1 (w y / w x)) true := by
  refine ⟨Measure.dirac false, inferInstance, fun b ↦ if b then ∞ else 1, 1,
    measurable_of_finite _, ?_, fun h ↦ ?_⟩
  · simp
  · have h1 := h {false}
    rw [acceptReject_apply (measurable_of_finite _)] at h1
    simp at h1

/-- The bound on `w` is needed at every point in `abs_measureReal_acceptReject_const_pow_sub_le`
too: for the same data, the chain started at `true` stays there, and the target `δ_false` gives
`{true}` no mass. -/
example : ∃ (γ : Measure Bool) (_ : IsProbabilityMeasure γ) (w : Bool → ℝ≥0∞) (M : ℝ≥0),
    Measurable w ∧ IsProbabilityMeasure (γ.withDensity w) ∧ (∀ᵐ x ∂γ, w x ≤ M) ∧
      ¬ |(((acceptReject (Kernel.const Bool γ) fun x y ↦ min 1 (w y / w x)) ^ (1 : ℕ)) ∘ₘ
        Measure.dirac true).real {true} - (γ.withDensity w).real {true}| ≤
          (1 - (M⁻¹ : ℝ≥0)) ^ (1 : ℕ) := by
  refine ⟨Measure.dirac false, inferInstance, fun b ↦ if b then ∞ else 1, 1,
    measurable_of_finite _, ⟨?_⟩, by simp, fun h ↦ ?_⟩
  · rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_dirac]
    simp
  · rw [pow_one, Measure.dirac_bind (Kernel.measurable _),
      acceptReject_apply (measurable_of_finite _)] at h
    simp [Measure.real, MeasureTheory.withDensity_apply _ (measurableSet_singleton _)] at h
    exact absurd h (by norm_num)

end ProbabilityTheory.Kernel
