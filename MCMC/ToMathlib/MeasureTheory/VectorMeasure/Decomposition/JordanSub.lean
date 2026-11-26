/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Integrals against the total variation of a difference of finite measures

For finite measures `μ`, `ν`, write `|μ - ν|` for Mathlib's total variation
`(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation`. By Mathlib's
`MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub` it is `(μ - ν) + (ν - μ)`, with
Mathlib's truncated differences of measures
(`MeasureTheory.Measure.totalVariation_toSignedMeasure_sub`), and `μ + ν` when `μ ⟂ₘ ν`
(`MeasureTheory.Measure.totalVariation_toSignedMeasure_sub_of_mutuallySingular`; two distinct
Dirac measures are mutually singular iff their points differ,
`MeasureTheory.mutuallySingular_dirac_dirac_iff`).
This file proves:

* `MeasureTheory.Measure.inf_add_sub`: `μ ⊓ ν + (μ - ν) = μ`, with Mathlib's infimum `μ ⊓ ν`
  (`MeasureTheory.Measure.inf_eq_restrict_add_restrict`: on a Hahn set `s`,
  `μ ⊓ ν = μ.restrict s + ν.restrict sᶜ`);
* `MeasureTheory.Measure.toSignedMeasure_sub_eq_of_add_eq`: adding a common finite measure to `μ`
  and to `ν` does not change `μ.toSignedMeasure - ν.toSignedMeasure`;
* `MeasureTheory.norm_integral_sub_integral_le_integral_totalVariation`: if `‖g‖ ≤ w`, `g` with
  values in a real normed space, then `‖∫ g ∂μ - ∫ g ∂ν‖ ≤ ∫ w ∂|μ - ν|`;
* `MeasureTheory.exists_integral_sub_integral_eq_integral_totalVariation`: the bound is attained
  at `g = w (1_S - 1_Sᶜ)`, `S` a Hahn set (Mathlib's `exists_isHahnDecomposition`);
* `MeasureTheory.isGreatest_integral_sub_integral_of_abs_le`: for `w ≥ 0`, `∫ w ∂|μ - ν|` is the
  greatest value of `∫ g ∂μ - ∫ g ∂ν` over measurable `g` with `|g| ≤ w`. For `w = 1 + β V` this
  is the identity that M. Hairer and J. C. Mattingly (*Yet another look at Harris' ergodic theorem
  for Markov chains*, arXiv:0810.2777, §1) call well known: the metric dual to the weighted
  supremum norm `sup |φ| / (1 + β V)` is the weighted total variation `∫ (1 + β V) ∂|μ - ν|`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "totalVariation" MeasureTheory` finds its
definition, `SignedMeasure.totalVariation_zero`, `SignedMeasure.totalVariation_neg`, the absolute
continuity and mutual singularity criteria, `norm_le_totalVariation`, `enorm_le_totalVariation`
and `SignedMeasure.totalVariation_eq_variation`, the bridge to Mathlib's integral against a signed
measure (`∫ᵛ`), which is bounded by the variation
(`VectorMeasure.norm_integral_le_integral_norm`).
`MeasureTheory.norm_integral_sub_integral_le_integral_totalVariation` below is proved directly,
not through `∫ᵛ`; that the bound is attained, the greatest-value forms and the integral against
`μ - ν` are not in Mathlib;
`grep -rn "integral_sub_measure\|integral_measure_sub" Mathlib` finds nothing;
`grep -rn "dirac.*⟂ₘ\|mutuallySingular_dirac" MeasureTheory` finds only
`MeasureTheory.mutuallySingular_dirac` (a Dirac measure against a measure without atoms).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {X E : Type*} {mX : MeasurableSpace X} [NormedAddCommGroup E]

/-- On a Hahn set `s` of `(μ, ν)` (`μ ≤ ν` on `s`, `ν ≤ μ` off `s`), `μ - ν` lives off `s`. -/
theorem IsHahnDecomposition.sub_eq {μ ν : Measure X} {s : Set X}
    (hs : IsHahnDecomposition μ ν s) : μ - ν = μ.restrict sᶜ - ν.restrict sᶜ := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ - ν) hs.measurableSet]
  rw [Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet,
    Measure.sub_eq_zero_of_le hs.le_on, zero_add,
    Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]

/-- **Two Dirac measures are mutually singular iff their points differ** (measurable
singletons), beside Mathlib's `MeasureTheory.mutuallySingular_dirac`. -/
theorem mutuallySingular_dirac_dirac_iff [MeasurableSingletonClass X] {a b : X} :
    Measure.dirac a ⟂ₘ Measure.dirac b ↔ a ≠ b := by
  refine ⟨fun h hab ↦ ?_, fun h ↦ ⟨{a}ᶜ, (measurableSet_singleton a).compl, by simp,
    by simp [h.symm]⟩⟩
  subst hab
  simpa using congrArg (· univ) ((Measure.MutuallySingular.self_iff (Measure.dirac a)).1 h)

namespace Measure

/-- The total variation of `μ - ν` is `(μ - ν) + (ν - μ)`, with Mathlib's truncated differences. -/
theorem totalVariation_toSignedMeasure_sub (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation = μ - ν + (ν - μ) := by
  rw [SignedMeasure.totalVariation, toJordanDecomposition_toSignedMeasure_sub]
  rfl

/-- Mathlib's truncated difference `μ - ν` is `μ` when `μ` and `ν` are mutually singular. -/
theorem sub_eq_self_of_mutuallySingular {μ ν : Measure X} (h : μ ⟂ₘ ν) : μ - ν = μ := by
  simpa using (add_sub_of_mutuallySingular (ν := 0) h).symm

/-- For mutually singular finite measures, the total variation of `μ - ν` is `μ + ν`. -/
theorem totalVariation_toSignedMeasure_sub_of_mutuallySingular {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation = μ + ν := by
  rw [totalVariation_toSignedMeasure_sub, sub_eq_self_of_mutuallySingular h,
    sub_eq_self_of_mutuallySingular h.symm]

/-- The integral of `f` against `|dirac x - dirac y|` is at most `f x + f y`. -/
theorem lintegral_totalVariation_dirac_sub_dirac_le {f : X → ℝ≥0∞} (hf : Measurable f) (x y : X) :
    ∫⁻ z, f z ∂((dirac x).toSignedMeasure - (dirac y).toSignedMeasure).totalVariation ≤
      f x + f y := by
  rw [totalVariation_toSignedMeasure_sub]
  refine (lintegral_mono' (add_le_add sub_le sub_le) le_rfl).trans_eq ?_
  rw [lintegral_add_measure, lintegral_dirac' x hf, lintegral_dirac' y hf]

/-- **The common part of two measures on a Hahn set**: if `s` is a Hahn set of `(μ, ν)`, Mathlib's
infimum `μ ⊓ ν` is `μ.restrict s + ν.restrict sᶜ`. No finiteness is assumed. -/
theorem inf_eq_restrict_add_restrict {μ ν : Measure X} {s : Set X}
    (hs : IsHahnDecomposition μ ν s) : μ ⊓ ν = μ.restrict s + ν.restrict sᶜ := by
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · calc μ ⊓ ν = (μ ⊓ ν).restrict s + (μ ⊓ ν).restrict sᶜ :=
          (restrict_add_restrict_compl hs.measurableSet).symm
      _ ≤ μ.restrict s + ν.restrict sᶜ :=
          add_le_add (restrict_mono subset_rfl inf_le_left) (restrict_mono subset_rfl inf_le_right)
  · calc μ.restrict s + ν.restrict sᶜ ≤ μ.restrict s + μ.restrict sᶜ :=
          add_le_add le_rfl hs.ge_on_compl
      _ = μ := restrict_add_restrict_compl hs.measurableSet
  · calc μ.restrict s + ν.restrict sᶜ ≤ ν.restrict s + ν.restrict sᶜ :=
          add_le_add hs.le_on le_rfl
      _ = ν := restrict_add_restrict_compl hs.measurableSet

/-- **A finite measure is its common part with another plus the truncated difference**:
`μ ⊓ ν + (μ - ν) = μ`. -/
theorem inf_add_sub (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ ⊓ ν + (μ - ν) = μ := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  rw [inf_eq_restrict_add_restrict hs, hs.sub_eq, add_assoc, add_comm (ν.restrict sᶜ),
    sub_add_cancel_of_le hs.ge_on_compl, restrict_add_restrict_compl hs.measurableSet]

/-- Adding a common finite measure `θ` to `ν₁` and `ν₂` does not change the difference of the
signed measures. -/
theorem toSignedMeasure_sub_eq_of_add_eq {μ₁ μ₂ ν₁ ν₂ θ : Measure X} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [IsFiniteMeasure θ]
    (h₁ : θ + ν₁ = μ₁) (h₂ : θ + ν₂ = μ₂) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = ν₁.toSignedMeasure - ν₂.toSignedMeasure := by
  subst h₁ h₂
  rw [toSignedMeasure_add, toSignedMeasure_add, add_sub_add_left_eq_sub]

end Measure

/-- The integral against `μ - ν` (Mathlib's truncated difference) when `ν ≤ μ`. -/
theorem integral_sub_measure [NormedSpace ℝ E] {μ ν : Measure X} [IsFiniteMeasure ν] (h : ν ≤ μ)
    {f : X → E}
    (hf : Integrable f μ) : ∫ x, f x ∂(μ - ν) = ∫ x, f x ∂μ - ∫ x, f x ∂ν := by
  conv_rhs => rw [← Measure.sub_add_cancel_of_le h]
  rw [integral_add_measure (hf.mono_measure Measure.sub_le) (hf.mono_measure h),
    add_sub_cancel_right]

/-- A function integrable against `μ` and `ν` is integrable against `|μ - ν|`. -/
theorem Integrable.totalVariation_toSignedMeasure_sub {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : X → E} (hμ : Integrable f μ) (hν : Integrable f ν) :
    Integrable f (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation := by
  rw [Measure.totalVariation_toSignedMeasure_sub]
  exact (hμ.mono_measure Measure.sub_le).add_measure (hν.mono_measure Measure.sub_le)

/-- If `‖g‖ ≤ w`, then `‖∫ g ∂μ - ∫ g ∂ν‖ ≤ ∫ w ∂|μ - ν|`. -/
theorem norm_integral_sub_integral_le_integral_totalVariation [NormedSpace ℝ E] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : X → E} {w : X → ℝ}
    (hgμ : AEStronglyMeasurable g μ) (hgν : AEStronglyMeasurable g ν) (hgw : ∀ x, ‖g x‖ ≤ w x)
    (hwμ : Integrable w μ) (hwν : Integrable w ν) :
    ‖∫ x, g x ∂μ - ∫ x, g x ∂ν‖ ≤
      ∫ x, w x ∂(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation := by
  set θ := μ ⊓ ν
  have h₁ : θ + (μ - ν) = μ := Measure.inf_add_sub μ ν
  have h₂ : θ + (ν - μ) = ν := (congrArg (· + (ν - μ)) (inf_comm μ ν)).trans
    (Measure.inf_add_sub ν μ)
  have hθ : θ ≤ μ := inf_le_left
  have hgμ' : Integrable g μ := hwμ.mono' hgμ (ae_of_all _ hgw)
  have hgν' : Integrable g ν := hwν.mono' hgν (ae_of_all _ hgw)
  have e₁ : ∫ x, g x ∂μ = ∫ x, g x ∂θ + ∫ x, g x ∂(μ - ν) := by
    conv_lhs => rw [← h₁]
    exact integral_add_measure (hgμ'.mono_measure hθ) (hgμ'.mono_measure Measure.sub_le)
  have e₂ : ∫ x, g x ∂ν = ∫ x, g x ∂θ + ∫ x, g x ∂(ν - μ) := by
    conv_lhs => rw [← h₂]
    exact integral_add_measure (hgμ'.mono_measure hθ) (hgν'.mono_measure Measure.sub_le)
  have b : ∀ ξ : Measure X, ξ ≤ μ ∨ ξ ≤ ν → ‖∫ x, g x ∂ξ‖ ≤ ∫ x, w x ∂ξ := fun ξ hξ ↦
    (norm_integral_le_integral_norm _).trans (integral_mono (((hξ.elim hwμ.mono_measure
      hwν.mono_measure).mono' (hξ.elim hgμ.mono_measure hgν.mono_measure)
        (ae_of_all _ hgw)).norm) (hξ.elim hwμ.mono_measure hwν.mono_measure) hgw)
  rw [e₁, e₂, add_sub_add_left_eq_sub, Measure.totalVariation_toSignedMeasure_sub,
    integral_add_measure (hwμ.mono_measure Measure.sub_le) (hwν.mono_measure Measure.sub_le)]
  exact (norm_sub_le _ _).trans (add_le_add (b _ (Or.inl Measure.sub_le))
    (b _ (Or.inr Measure.sub_le)))

/-- The bound `|∫ g ∂μ - ∫ g ∂ν| ≤ ∫ w ∂|μ - ν|` is attained at `g = w (1_S - 1_Sᶜ)`, `S` a Hahn
set of `(ν, μ)`. -/
theorem exists_integral_sub_integral_eq_integral_totalVariation (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w : X → ℝ} (hw : Measurable w)
    (hwμ : Integrable w μ) (hwν : Integrable w ν) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, |g x| ≤ |w x|) ∧
      ∫ x, g x ∂μ - ∫ x, g x ∂ν =
        ∫ x, w x ∂(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν μ
  have hsm := hs.measurableSet
  refine ⟨s.indicator w - sᶜ.indicator w, (hw.indicator hsm).sub (hw.indicator hsm.compl),
    fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ s <;> simp [hx]
  · have e : μ - ν = μ.restrict s - ν.restrict s := by simpa using hs.compl.sub_eq
    simp only [Pi.sub_apply]
    rw [integral_sub (hwμ.indicator hsm) (hwμ.indicator hsm.compl),
      integral_sub (hwν.indicator hsm) (hwν.indicator hsm.compl), integral_indicator hsm,
      integral_indicator hsm, integral_indicator hsm.compl, integral_indicator hsm.compl,
      Measure.totalVariation_toSignedMeasure_sub,
      integral_add_measure (hwμ.mono_measure Measure.sub_le) (hwν.mono_measure Measure.sub_le),
      e, hs.sub_eq, integral_sub_measure hs.le_on hwμ.restrict,
      integral_sub_measure hs.ge_on_compl hwν.restrict]
    ring

/-- **The weighted total variation is dual to the weighted supremum norm**: for `w ≥ 0`
integrable against `μ` and `ν`, `∫ w ∂|μ - ν|` is the greatest value of `∫ g ∂μ - ∫ g ∂ν` over
measurable `g` with `|g| ≤ w`. -/
theorem isGreatest_integral_sub_integral_of_abs_le (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : X → ℝ} (hw : Measurable w) (hw0 : 0 ≤ w) (hwμ : Integrable w μ)
    (hwν : Integrable w ν) :
    IsGreatest {r | ∃ g : X → ℝ, Measurable g ∧ (∀ x, |g x| ≤ w x) ∧
      ∫ x, g x ∂μ - ∫ x, g x ∂ν = r}
      (∫ x, w x ∂(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg, hgw, he⟩ :=
      exists_integral_sub_integral_eq_integral_totalVariation μ ν hw hwμ hwν
    exact ⟨g, hg, fun x ↦ (hgw x).trans_eq (abs_of_nonneg (hw0 x)), he⟩
  · rintro _ ⟨g, hg, hgw, rfl⟩
    exact (le_abs_self _).trans (norm_integral_sub_integral_le_integral_totalVariation μ ν
      hg.aestronglyMeasurable hg.aestronglyMeasurable hgw hwμ hwν)

end MeasureTheory
