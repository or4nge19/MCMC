/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.IdentDistrib

/-!
# Convergence in `Lᵖ` of Birkhoff averages

For a map `f` preserving a finite measure `μ` and `φ ∈ Lᵖ(μ)`, `1 ≤ p < ∞`, the Birkhoff averages
of `φ` tend to `μ[φ | MeasurableSpace.invariants f]` in `Lᵖ`
(`MeasureTheory.MeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp`); for an ergodic
map of a probability space the limit is the constant `∫ x, φ x ∂μ`
(`Ergodic.tendsto_eLpNorm_birkhoffAverage_sub_integral`).

The proof is Kallenberg's: the functions `φ ∘ f^[k]` have the law of `φ`, so they are uniformly
integrable in `Lᵖ` (`ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib`), hence so are their
averages (`MeasureTheory.uniformIntegrable_average`), and almost everywhere convergence
(`MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp`) gives convergence in `Lᵖ`
(`MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`).

For `p = 2` this is the statement of von Neumann's mean ergodic theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` for the isometry
`g ↦ g ∘ f` of `L²(μ)`, with the orthogonal projection on its fixed vectors written as a
conditional expectation; that theorem is not used here.

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 25.6 (the `Lᵖ` part
of the statement and of the proof), read from an extracted text of the 3rd edition.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rn "birkhoffAverage" Mathlib` finds no
statement with `eLpNorm` or `Lp` other than the Hilbert space theorem above; the same route is
Mathlib's `ProbabilityTheory.strong_law_Lp`.
-/

@[expose] public section

open Filter MeasureTheory MeasurableSpace
open scoped ENNReal Topology

namespace MeasureTheory.MeasurePreserving

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {φ : α → ℝ} {p : ℝ≥0∞}

theorem aestronglyMeasurable_birkhoffAverage (hf : MeasurePreserving f μ μ)
    (hφ : AEStronglyMeasurable φ μ) (n : ℕ) :
    AEStronglyMeasurable (birkhoffAverage ℝ f φ n) μ :=
  show AEStronglyMeasurable ((n : ℝ)⁻¹ • birkhoffSum f φ n) μ from
    (aemeasurable_birkhoffSum hf.quasiMeasurePreserving
      hφ.aemeasurable n).aestronglyMeasurable.const_smul _

/-- The Birkhoff averages of a function in `Lᵖ` of a finite measure are uniformly integrable in
`Lᵖ`. -/
theorem uniformIntegrable_birkhoffAverage [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hφ : MemLp φ p μ) :
    UniformIntegrable (fun n ↦ birkhoffAverage ℝ f φ n) p μ := by
  have hm : ∀ k, AEMeasurable (φ ∘ f^[k]) μ := fun k ↦
    hφ.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
      (hf.iterate k).quasiMeasurePreserving
  have hUI : UniformIntegrable (fun k ↦ φ ∘ f^[k]) p μ :=
    ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib (j := 0) hp hp' hφ fun k ↦ ⟨hm k, hm 0, by
      rw [← AEMeasurable.map_map_of_aemeasurable (by rw [(hf.iterate k).map_eq]; exact hm 0)
        (hf.iterate k).aemeasurable, (hf.iterate k).map_eq]; rfl⟩
  have heq : (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, φ ∘ f^[i]) =
      fun n ↦ birkhoffAverage ℝ f φ n := by
    ext n x
    simp [birkhoffAverage, birkhoffSum]
  exact heq ▸ uniformIntegrable_average hp hUI

/-- **The mean ergodic theorem in `Lᵖ`**, `1 ≤ p < ∞`: for a map `f` preserving a finite measure
and `φ ∈ Lᵖ`, the Birkhoff averages of `φ` tend in `Lᵖ` to the conditional expectation of `φ`
given the invariant σ-algebra. -/
theorem tendsto_eLpNorm_birkhoffAverage_sub_condExp [IsFiniteMeasure μ]
    (hf : MeasurePreserving f μ μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (hφ : MemLp φ p μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ f φ n - μ[φ | invariants f]) p μ) atTop
      (𝓝 0) :=
  tendsto_Lp_finite_of_tendsto_ae hp hp'
    (fun n ↦ hf.aestronglyMeasurable_birkhoffAverage hφ.aestronglyMeasurable n)
    (hφ.condExp hp) (hf.uniformIntegrable_birkhoffAverage hp hp' hφ).unifIntegrable
    (hf.ae_tendsto_birkhoffAverage_condExp (hφ.integrable hp))

end MeasureTheory.MeasurePreserving

/-- **The mean ergodic theorem in `Lᵖ` for an ergodic map** of a probability space: the Birkhoff
averages of `φ ∈ Lᵖ`, `1 ≤ p < ∞`, tend in `Lᵖ` to the integral of `φ`. -/
theorem Ergodic.tendsto_eLpNorm_birkhoffAverage_sub_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → α} {φ : α → ℝ} {p : ℝ≥0∞}
    (hf : Ergodic f μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (hφ : MemLp φ p μ) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ f φ n - fun _ ↦ ∫ x, φ x ∂μ) p μ) atTop
      (𝓝 0) :=
  tendsto_Lp_finite_of_tendsto_ae hp hp'
    (fun n ↦ hf.toMeasurePreserving.aestronglyMeasurable_birkhoffAverage
      hφ.aestronglyMeasurable n)
    (memLp_const _)
    (hf.toMeasurePreserving.uniformIntegrable_birkhoffAverage hp hp' hφ).unifIntegrable
    (hf.ae_tendsto_birkhoffAverage_integral (hφ.integrable hp))
