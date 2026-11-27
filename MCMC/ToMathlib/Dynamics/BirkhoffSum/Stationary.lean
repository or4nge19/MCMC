/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.Ergodic

/-!
# The ergodic theorem for a random element with a stationary orbit

Let `ξ : Ω → S` be a random element on `(Ω, P)` and `T : S → S` a measurable map with `T ∘ ξ`
equal in law to `ξ`, that is, `T` preserves the law `P.map ξ`
(`MeasureTheory.measurePreserving_map_iff`). For `φ` integrable for the law of `ξ`, almost surely

`n⁻¹ ∑ k < n, φ (T^[k] (ξ ω)) → P[φ ∘ ξ | (MeasurableSpace.invariants T).comap ξ] ω`

(`MeasureTheory.ae_tendsto_birkhoffAverage_comp_condExp_comap`); the limit is the value at `ξ ω` of
the conditional expectation of `φ` given the invariant σ-algebra for the law of `ξ`
(`MeasureTheory.ae_tendsto_birkhoffAverage_comp_condExp`,
`MeasureTheory.condExp_map_comp_ae_eq`). With `S` a space of paths, `T` the shift and `ξ` the
identity this is the law of large numbers for a functional of a stationary process.

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 25.6, formula (1),
read from an extracted text of the 3rd edition; there `P` is a probability measure.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rn "condExp.*map\|condExp.*comap" Mathlib`
finds Jensen's inequality (`ConcaveOn.condExp_map_le`) and kernels
(`condDistrib_apply_ae_eq_condExpKernel_map`), no change of variables for `condExp` along a map.
-/

@[expose] public section

open Filter MeasureTheory MeasurableSpace
open scoped ENNReal Topology

namespace MeasureTheory

/-- Change of variables for the conditional expectation along a measurable map `ξ`: the
conditional expectation of `φ` given `m` for the law of `ξ`, evaluated at `ξ`, is the conditional
expectation of `φ ∘ ξ` given the pullback of `m`. -/
theorem condExp_map_comp_ae_eq {Ω S E : Type*} {mΩ : MeasurableSpace Ω} {m mS : MeasurableSpace S}
    {P : Measure Ω} {ξ : Ω → S} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ : S → E} (hm : m ≤ mS) (hξ : Measurable ξ) [SigmaFinite ((P.map ξ).trim hm)]
    [SigmaFinite (P.trim ((comap_mono hm).trans hξ.comap_le))] (hφ : Integrable φ (P.map ξ)) :
    (P.map ξ)[φ | m] ∘ ξ =ᵐ[P] P[φ ∘ ξ | m.comap ξ] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq ((comap_mono hm).trans hξ.comap_le)
    ((integrable_map_measure hφ.1 hξ.aemeasurable).1 hφ)
    (fun s _ _ ↦ ((integrable_map_measure integrable_condExp.1 hξ.aemeasurable).1
      integrable_condExp).integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable (comap_measurable ξ)).aestronglyMeasurable
  rintro s ⟨t, ht, rfl⟩ -
  have h1 := setIntegral_map (hm t ht) (integrable_condExp (μ := P.map ξ) (m := m) (f := φ)).1
    hξ.aemeasurable
  have h2 := setIntegral_map (hm t ht) hφ.1 hξ.aemeasurable
  exact h1.symm.trans ((setIntegral_condExp hm hφ ht).trans h2)

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace S} {P : Measure Ω}
  {ξ : Ω → S} {T : S → S} {φ : S → ℝ}

/-- `T ∘ ξ` has the law of `ξ` iff `T` preserves the law of `ξ`. -/
theorem measurePreserving_map_iff (hT : Measurable T) (hξ : AEMeasurable ξ P) :
    MeasurePreserving T (P.map ξ) (P.map ξ) ↔ P.map (T ∘ ξ) = P.map ξ := by
  rw [← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hξ]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨hT, h⟩⟩

/-- **The ergodic theorem for a random element with a stationary orbit**: if `T ∘ ξ` has the law
of `ξ` and `φ` is integrable for that law, then almost surely the averages of `φ` along the orbit
of `ξ` under `T` tend to the conditional expectation of `φ` given the invariant σ-algebra,
evaluated at `ξ`. -/
theorem ae_tendsto_birkhoffAverage_comp_condExp (hT : Measurable T) (hξ : AEMeasurable ξ P)
    (h : P.map (T ∘ ξ) = P.map ξ) [SigmaFinite ((P.map ξ).trim (invariants_le T))]
    (hφ : Integrable φ (P.map ξ)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ birkhoffAverage ℝ T φ n (ξ ω)) atTop
      (𝓝 ((P.map ξ)[φ | invariants T] (ξ ω))) :=
  ae_of_ae_map hξ
    (((measurePreserving_map_iff hT hξ).2 h).ae_tendsto_birkhoffAverage_condExp hφ)

/-- **The ergodic theorem for a random element with a stationary orbit**, with the limit as a
conditional expectation on the underlying probability space. -/
theorem ae_tendsto_birkhoffAverage_comp_condExp_comap [IsFiniteMeasure P] (hT : Measurable T)
    (hξ : Measurable ξ) (h : P.map (T ∘ ξ) = P.map ξ) (hφ : Integrable φ (P.map ξ)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ birkhoffAverage ℝ T φ n (ξ ω)) atTop
      (𝓝 (P[φ ∘ ξ | (invariants T).comap ξ] ω)) := by
  have : IsFiniteMeasure (P.map ξ) := Measure.isFiniteMeasure_map P ξ
  filter_upwards [ae_tendsto_birkhoffAverage_comp_condExp hT hξ.aemeasurable h hφ,
    condExp_map_comp_ae_eq (invariants_le T) hξ hφ] with ω hω hc
  exact (show (P.map ξ)[φ | invariants T] (ξ ω) = _ from hc) ▸ hω

/-- **The ergodic theorem for a random element with a stationary ergodic orbit**: if `T` is
ergodic for the law of `ξ`, the averages of `φ` along the orbit of `ξ` tend almost surely to the
mean of `φ ∘ ξ`. -/
theorem ae_tendsto_birkhoffAverage_comp_integral [IsProbabilityMeasure P]
    (hξ : AEMeasurable ξ P) (hT : Ergodic T (P.map ξ)) (hφ : Integrable φ (P.map ξ)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ birkhoffAverage ℝ T φ n (ξ ω)) atTop (𝓝 (∫ ω, φ (ξ ω) ∂P)) := by
  have : IsProbabilityMeasure (P.map ξ) := (Measure.isProbabilityMeasure_map_iff hξ).2 inferInstance
  rw [← integral_map hξ hφ.1]
  exact ae_of_ae_map hξ (hT.ae_tendsto_birkhoffAverage_integral hφ)

end MeasureTheory
