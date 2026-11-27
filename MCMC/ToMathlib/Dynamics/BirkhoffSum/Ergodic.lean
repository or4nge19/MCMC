/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.Pointwise
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Birkhoff's theorem for an ergodic map

Let `f` be ergodic for `μ` and `φ : α → ℝ` integrable. Almost everywhere the Birkhoff averages of
`φ` tend to

* the mean `⨍ x, φ x ∂μ` if `μ` is finite (`Ergodic.ae_tendsto_birkhoffAverage_average`), which is
  `∫ x, φ x ∂μ` on a probability space (`Ergodic.ae_tendsto_birkhoffAverage_integral`);
* `0` if `μ univ = ∞` (`Ergodic.ae_tendsto_birkhoffAverage_zero_of_measure_univ_eq_top`).

Conversely, a measure-preserving map of a probability space is ergodic iff the frequencies of the
visits to every measurable set `s` tend almost everywhere to `μ.real s`
(`MeasureTheory.MeasurePreserving.ergodic_iff_ae_tendsto_birkhoffAverage_indicator`).

All three limits come from `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_zero`: an
invariant set is null or conull, so the integral of `φ - ⨍ x, φ x ∂μ` (of `φ`, when `μ univ = ∞`)
vanishes on every invariant set of finite measure. No conditional expectation is used.

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 25.6 and the
definition of ergodicity before Lemma 25.5, read from an extracted text of the 3rd edition.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rn "birkhoffAverage" Mathlib/Dynamics/Ergodic`
finds nothing; `Mathlib/Dynamics/Ergodic/Function.lean` has the almost everywhere constancy of
invariant functions, not used here.
-/

@[expose] public section

open Filter MeasureTheory Set MeasurableSpace
open scoped ENNReal Topology

namespace Ergodic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {φ : α → ℝ}

/-- **Birkhoff's ergodic theorem for an ergodic map** of a finite measure space: the Birkhoff
averages of an integrable function tend almost everywhere to its mean. -/
theorem ae_tendsto_birkhoffAverage_average [IsFiniteMeasure μ] (hf : Ergodic f μ)
    (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop (𝓝 (⨍ x, φ x ∂μ)) := by
  have h0 : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ →
      ∫ x in s, (φ x - ⨍ y, φ y ∂μ) ∂μ = 0 := fun s hs _ ↦ by
    rcases hf.toPreErgodic.measure_self_or_compl_eq_zero hs.1 hs.2 with h | h
    · exact setIntegral_measure_zero _ h
    · rw [Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 h |>.mono
        fun x hx ↦ not_not.1 hx), integral_sub_average]
  filter_upwards [hf.toMeasurePreserving.ae_tendsto_birkhoffAverage_zero
    (hφ.sub (integrable_const _)) h0] with x hx
  have h := hx.add_const (⨍ y, φ y ∂μ)
  rw [zero_add] at h
  refine h.congr' ((eventually_ne_atTop 0).mono fun n hn ↦ ?_)
  have hc : (fun _ : α ↦ ⨍ y, φ y ∂μ) ∘ f = fun _ ↦ ⨍ y, φ y ∂μ := rfl
  have hsub := birkhoffAverage_sub_apply (R := ℝ) (f := f) (g := φ)
    (g' := fun _ ↦ ⨍ y, φ y ∂μ) n x
  rw [birkhoffAverage_apply_of_comp_eq ℝ hc (Nat.cast_ne_zero.2 hn)] at hsub
  exact (congrArg (· + ⨍ y, φ y ∂μ) hsub).trans (sub_add_cancel _ _)

/-- **Birkhoff's ergodic theorem for an ergodic map** of a probability space: the Birkhoff
averages of an integrable function tend almost everywhere to its integral. -/
theorem ae_tendsto_birkhoffAverage_integral [IsProbabilityMeasure μ] (hf : Ergodic f μ)
    (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop (𝓝 (∫ x, φ x ∂μ)) :=
  average_eq_integral (μ := μ) (f := φ) ▸ hf.ae_tendsto_birkhoffAverage_average hφ

/-- For an ergodic map of a space of infinite measure, the Birkhoff averages of an integrable
function tend to `0` almost everywhere. -/
theorem ae_tendsto_birkhoffAverage_zero_of_measure_univ_eq_top (hf : Ergodic f μ)
    (hμ : μ univ = ∞) (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop (𝓝 0) := by
  refine hf.toMeasurePreserving.ae_tendsto_birkhoffAverage_zero hφ fun s hs hμs ↦ ?_
  rcases hf.toPreErgodic.measure_self_or_compl_eq_zero hs.1 hs.2 with h | h
  · exact setIntegral_measure_zero _ h
  · have hle : μ univ ≤ μ s + μ sᶜ := union_compl_self s ▸ measure_union_le s sᶜ
    exact absurd hμ (hle.trans_lt (ENNReal.add_lt_top.2 ⟨hμs, h ▸ ENNReal.zero_lt_top⟩)).ne

end Ergodic

namespace MeasureTheory.MeasurePreserving

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- A measure-preserving map of a probability space is ergodic iff, for every measurable set `s`,
the frequency of the visits of almost every orbit to `s` tends to the measure of `s`. -/
theorem ergodic_iff_ae_tendsto_birkhoffAverage_indicator [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) :
    Ergodic f μ ↔ ∀ s, MeasurableSet s → ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ birkhoffAverage ℝ f (s.indicator 1) n x) atTop (𝓝 (μ.real s)) := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ ⟨hf, ⟨fun s hs hfs ↦ ?_⟩⟩⟩
  · have h1 := h.ae_tendsto_birkhoffAverage_integral
      ((integrable_const (1 : ℝ)).indicator hs)
    rw [integral_indicator_const _ hs, smul_eq_mul, mul_one] at h1
    exact h1
  have hc : (s.indicator (1 : α → ℝ)) ∘ f = s.indicator 1 :=
    funext fun x ↦ (indicator_comp_right f (s := s) (g := (1 : α → ℝ)) (x := x)).symm.trans
      (congrFun (congrArg (fun t ↦ indicator t (1 : α → ℝ)) hfs) x)
  have hae : ∀ᵐ x ∂μ, s.indicator (1 : α → ℝ) x = μ.real s := by
    filter_upwards [h s hs] with x hx
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono
      fun n hn ↦ (birkhoffAverage_apply_of_comp_eq ℝ hc (Nat.cast_ne_zero.2 hn) x).symm)) hx
  by_cases hr : μ.real s = 1
  · exact eventuallyEmptyOrUniv_iff'.2 (.inr (eventuallyEqSet_univ.2 (hae.mono fun x hx ↦
      by_contra fun hxs ↦ by
        rw [indicator_of_notMem hxs] at hx
        exact zero_ne_one (hx.trans hr))))
  · exact eventuallyEmptyOrUniv_iff'.2 (.inl (eventuallyEqSet_empty.2 (hae.mono fun x hx hxs ↦
      hr (hx.symm.trans (indicator_of_mem hxs _)))))

end MeasureTheory.MeasurePreserving
