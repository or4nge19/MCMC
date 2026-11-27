/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Posterior
public import MCMC.ToMathlib.Probability.Kernel.Invariance

/-!
# A reversible Markov kernel is its own posterior

Mathlib's posterior `κ†μ` (`ProbabilityTheory.posterior`) is the time reversal of `κ`
under `μ`: `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`
(`ProbabilityTheory.compProd_posterior_eq_map_swap`). A Markov kernel is `μ`-reversible iff it
leaves `μ` invariant and is its own posterior, `μ`-almost everywhere.

Staged for `Mathlib/Probability/Kernel/Posterior.lean`. Searched on 2026-11-27 in the pinned
Mathlib: `grep -rn "IsReversible\|Invariant" Mathlib/Probability/Kernel/Posterior.lean` has no
hit.

## References

* C. P. Robert, G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer (2004),
  p. 230 (the display after Theorem 6.46).
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer (2021):
  Theorem 3.4.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {κ : Kernel Ω Ω} {μ : Measure Ω}

/-- **A reversible Markov kernel is its own posterior**, `μ`-almost everywhere. -/
theorem IsReversible.ae_eq_posterior [IsFiniteMeasure μ] [IsMarkovKernel κ]
    (h : κ.IsReversible μ) : κ =ᵐ[μ] κ†μ := by
  have h2 := ae_eq_posterior_of_compProd_eq (κ := κ) (μ := μ) (η := κ)
    (by rw [h.invariant.def, isReversible_iff_map_swap_compProd.1 h])
  rwa [h.invariant.def] at h2

/-- A Markov kernel is `μ`-reversible iff it leaves `μ` invariant and is its own posterior,
`μ`-almost everywhere. -/
theorem isReversible_iff_invariant_and_ae_eq_posterior [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    κ.IsReversible μ ↔ κ.Invariant μ ∧ κ =ᵐ[μ] κ†μ := by
  refine ⟨fun h ↦ ⟨h.invariant, h.ae_eq_posterior⟩, fun ⟨hinv, hpost⟩ ↦ ?_⟩
  refine IsReversible.of_map_swap_compProd ?_
  rw [← compProd_posterior_eq_map_swap, hinv.def]
  exact (Measure.compProd_congr hpost).symm

end ProbabilityTheory.Kernel
