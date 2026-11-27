/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Probability.Distributions.Gaussian.Reversible
public import MCMC.ToMathlib.Probability.Kernel.AcceptReject
public import MCMC.ToMathlib.Probability.Kernel.RandomWalk

/-!
# Two Metropolis samplers: random-walk Metropolis and preconditioned Crank–Nicolson

Both are instances of `ProbabilityTheory.Kernel.isReversible_acceptReject_min_one_div`: a proposal
reversible for a reference measure `μ`, the acceptance `min 1 (f y / f x)`, and the target
`μ.withDensity f`.

* `isReversible_randomWalkMetropolis`: on a group with a right-invariant reference measure `μ`
  (Lebesgue measure on `ℝⁿ`, not finite; the counting measure on `ℤ`) and increments of any
  symmetric law, for every measurable density `f` finite `μ`-almost everywhere; on `ℝ` with
  Gaussian increments it is an `example`. No integrability of `f` is needed.
* `isReversible_pCN`: on a separable Banach space with a centered Gaussian reference `μ₀`, the
  proposal `cos θ • x + sin θ • W`, `W ∼ μ₀`, and the acceptance `min 1 (exp (Φ x - Φ y))` for the
  target `μ₀.withDensity (exp (-Φ))`, for every measurable potential `Φ`.

## References

* M. Hairer, A. M. Stuart, S. J. Vollmer, *Spectral gaps for a Metropolis–Hastings algorithm in
  infinite dimensions*, Ann. Appl. Probab. 24 (2014); arXiv:1112.1392 (the pCN algorithm).
* C. P. Robert, G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer (2004), §7.5,
  Algorithm [A.29] (p. 288).
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer (2021), Lemma 34.28
  (time reversal, Doob): Brownian motion started from Lebesgue measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

section RandomWalk

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

/-- **Random-walk Metropolis** is reversible: on a group with an s-finite right-invariant
reference measure `μ` and increments of a symmetric law `ν`, the kernel with acceptance
`min 1 (f y / f x)` is reversible for `μ.withDensity f`, for every measurable `f` finite
`μ`-almost everywhere. -/
theorem isReversible_randomWalkMetropolis {μ ν : Measure G} [SFinite μ] [SFinite ν]
    [μ.IsAddRightInvariant] (hν : ν.map Neg.neg = ν) {f : G → ℝ≥0∞} (hf : Measurable f)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (Kernel.acceptReject ((Kernel.id ×ₖ Kernel.const G ν).map fun p : G × G ↦ p.1 + p.2)
      fun x y ↦ min 1 (f y / f x)).IsReversible (μ.withDensity f) :=
  Kernel.isReversible_acceptReject_min_one_div (Kernel.isReversible_map_add_of_map_neg hν) hf
    hf_top

end RandomWalk

/-- Random-walk Metropolis on `ℝ` with increments `N(0, v)` is reversible for
`volume.withDensity f`, for every measurable `f` finite almost everywhere. -/
example (v : ℝ≥0) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hf_top : ∀ᵐ x, f x ≠ ∞) :
    (Kernel.acceptReject ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ p.1 + p.2) fun x y ↦ min 1 (f y / f x)).IsReversible (volume.withDensity f) :=
  isReversible_randomWalkMetropolis (by simpa using gaussianReal_map_neg (μ := 0) (v := v)) hf
    hf_top

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- **The preconditioned Crank–Nicolson sampler is reversible** for `μ₀.withDensity (exp (-Φ))`,
for every centered Gaussian `μ₀`, every angle `θ` and every measurable potential `Φ`. -/
theorem isReversible_pCN {μ₀ : Measure E} [IsGaussian μ₀] (hμ₀ : μ₀[id] = 0) (θ : ℝ) {Φ : E → ℝ}
    (hΦ : Measurable Φ) :
    (Kernel.acceptReject ((Kernel.id ×ₖ Kernel.const E μ₀).map
      fun p : E × E ↦ Real.cos θ • p.1 + Real.sin θ • p.2)
        fun x y ↦ min 1 (ENNReal.ofReal (Real.exp (Φ x - Φ y)))).IsReversible
      (μ₀.withDensity fun x ↦ ENNReal.ofReal (Real.exp (-Φ x))) := by
  have hacc : (fun x y ↦ min 1 (ENNReal.ofReal (Real.exp (Φ x - Φ y)))) =
      fun x y ↦ min 1 (ENNReal.ofReal (Real.exp (-Φ y)) / ENNReal.ofReal (Real.exp (-Φ x))) := by
    funext x y
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub, neg_sub_neg]
  rw [hacc]
  exact Kernel.isReversible_acceptReject_min_one_div (isReversible_map_cos_smul_add_sin_smul hμ₀ θ)
    (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top)

/-! ### The hypotheses of the general theorems hold together

Each `example` below applies a general theorem of
`MCMC/ToMathlib/Probability/Kernel/{Invariance, AcceptReject}.lean` with all its hypotheses met by
the random-walk proposal on `ℝ` and Lebesgue measure, which is σ-finite and not finite. -/

section Examples

variable (v : ℝ≥0) {f : ℝ → ℝ≥0∞}

/-- `isReversible_iff_map_swap_compProd`, in its nontrivial direction, for Lebesgue measure. -/
example : (volume ⊗ₘ (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ p.1 + p.2).map Prod.swap =
    volume ⊗ₘ (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ p.1 + p.2 := by
  have := Measure.sigmaFinite_fst_compProd (μ := volume)
    (κ := (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ p.1 + p.2)
    (ae_of_all _ fun _ ↦ measure_ne_top _ _)
  exact Kernel.isReversible_iff_map_swap_compProd.1
    (Kernel.isReversible_map_add_of_map_neg
      (by simpa using gaussianReal_map_neg (μ := 0) (v := v)))

/-- The accepted-flow criterion, in its nontrivial direction, for random-walk Metropolis. -/
example (hf : Measurable f) (hf_top : ∀ᵐ x, f x ≠ ∞) :
    (((volume.withDensity f) ⊗ₘ (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ p.1 + p.2).withDensity
        (Function.uncurry fun x y ↦ min 1 (f y / f x))).map Prod.swap =
      ((volume.withDensity f) ⊗ₘ (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
        fun p : ℝ × ℝ ↦ p.1 + p.2).withDensity (Function.uncurry fun x y ↦ min 1 (f y / f x)) := by
  have := SigmaFinite.withDensity_of_ne_top hf_top
  refine (Kernel.isReversible_acceptReject_iff_map_swap
    (measurable_const.min ((hf.comp measurable_snd).div (hf.comp measurable_fst)))
    (ae_of_all _ fun x ↦ ?_)).1 (isReversible_randomWalkMetropolis
      (by simpa using gaussianReal_map_neg (μ := 0) (v := v)) hf hf_top)
  exact ((lintegral_mono fun _ ↦ min_le_left _ _).trans_lt (by simp)).ne

/-- Maximality for random-walk Metropolis: its acceptance is at most the Metropolis–Hastings
acceptance, almost everywhere for the proposed flow. -/
example (hf : Measurable f) (hf_top : ∀ᵐ x, f x ≠ ∞) :
    Function.uncurry (fun x y ↦ min 1 (f y / f x)) ≤ᵐ[(volume.withDensity f) ⊗ₘ
      (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ p.1 + p.2]
      Function.uncurry ((volume.withDensity f).mhAcceptance
        ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map fun p : ℝ × ℝ ↦ p.1 + p.2)) := by
  have := SigmaFinite.withDensity_of_ne_top hf_top
  exact Kernel.ae_le_mhAcceptance_of_isReversible_acceptReject_of_ae_ne_top
    (ae_of_all _ fun _ ↦ measure_ne_top _ _)
    (measurable_const.min ((hf.comp measurable_snd).div (hf.comp measurable_fst)))
    (ae_of_all _ fun _ ↦ min_le_left _ _) (isReversible_randomWalkMetropolis
      (by simpa using gaussianReal_map_neg (μ := 0) (v := v)) hf hf_top)

/-- The Metropolis–Hastings kernel of the random-walk proposal for `volume.withDensity f` is
reversible. -/
example :
    (Kernel.acceptReject ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
      fun p : ℝ × ℝ ↦ p.1 + p.2) ((volume.withDensity f).mhAcceptance
        ((Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 v)).map
          fun p : ℝ × ℝ ↦ p.1 + p.2))).IsReversible (volume.withDensity f) :=
  Kernel.isReversible_acceptReject_mhAcceptance

end Examples

end ProbabilityTheory
