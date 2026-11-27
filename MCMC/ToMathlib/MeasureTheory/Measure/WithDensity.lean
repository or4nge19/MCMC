/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# Infima, truncations and images of measures with densities

The infimum of `μ.withDensity f` and `μ.withDensity g` is `μ.withDensity (f ⊓ g)`, for measurable
`f` and `g` and any measure `μ`; if `μ.withDensity f ≤ μ`, truncating `f` at `1` does not change
`μ.withDensity f`, with no finiteness of `μ`; and the image of `μ.withDensity (h ∘ g)` under `g` is
`(μ.map g).withDensity h`, for measurable `g` and `h`, or for a measurable embedding `g` and any
`h`.

Staged for `Mathlib/MeasureTheory/Measure/WithDensity.lean`. Searched on 2026-11-26 in the pinned
Mathlib: `grep -rn "withDensity_inf\|inf_withDensity\|withDensity_min" Mathlib` has no hit
(`Measure.rnDeriv_le_one_of_le` gives the truncation for σ-finite measures only);
`grep -rn "map_withDensity\|withDensity_map" Mathlib/MeasureTheory` finds only
`MeasurableEmbedding.map_withDensity_rnDeriv` and the change-of-variables statements of
`Function/Jacobian.lean`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}

/-- The infimum of two measures with densities with respect to `μ` has the pointwise minimum as
density. -/
theorem withDensity_inf_withDensity {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity f ⊓ μ.withDensity g = μ.withDensity (f ⊓ g) := by
  refine le_antisymm (Measure.le_iff.2 fun s hs ↦ ?_)
    (le_inf (withDensity_mono (ae_of_all _ fun _ ↦ inf_le_left))
      (withDensity_mono (ae_of_all _ fun _ ↦ inf_le_right)))
  have hT : MeasurableSet {x | f x ≤ g x} := measurableSet_le hf hg
  rw [Measure.inf_apply hs, withDensity_apply _ hs, ← lintegral_inter_add_sdiff _ s hT]
  calc sInf {m | ∃ t, m = μ.withDensity f (t ∩ s) + μ.withDensity g (tᶜ ∩ s)}
      ≤ μ.withDensity f ({x | f x ≤ g x} ∩ s) + μ.withDensity g ({x | f x ≤ g x}ᶜ ∩ s) :=
        sInf_le ⟨_, rfl⟩
    _ = _ := by
        rw [withDensity_apply _ (hT.inter hs), withDensity_apply _ (hT.compl.inter hs), inter_comm,
          ← sdiff_eq_compl_inter]
        congr 1
        · exact setLIntegral_congr_fun (hs.inter hT) fun x hx ↦ (inf_eq_left.2 hx.2).symm
        · exact setLIntegral_congr_fun (hs.diff hT) fun x hx ↦
            (inf_eq_right.2 (not_le.1 hx.2).le).symm

/-- If `μ.withDensity f ≤ μ`, truncating the density at `1` does not change the measure. No
finiteness is assumed: on `{1 < f}` the measures `μ.withDensity f` and `μ` agree. -/
theorem withDensity_min_one_of_le {f : α → ℝ≥0∞} (hf : Measurable f)
    (h : μ.withDensity f ≤ μ) : μ.withDensity (fun x ↦ min 1 (f x)) = μ.withDensity f := by
  ext s hs
  have hA : MeasurableSet {x | f x ≤ 1} := measurableSet_le hf measurable_const
  have h1 : ∫⁻ x in s \ {x | f x ≤ 1}, min 1 (f x) ∂μ = μ (s \ {x | f x ≤ 1}) := by
    rw [setLIntegral_congr_fun (hs.diff hA) (g := fun _ ↦ 1)
      fun x hx ↦ min_eq_left (not_le.1 hx.2).le]
    simp
  have h2 : μ (s \ {x | f x ≤ 1}) = ∫⁻ x in s \ {x | f x ≤ 1}, f x ∂μ := by
    refine le_antisymm ?_ ((withDensity_apply _ (hs.diff hA)).symm.trans_le (h _))
    calc μ (s \ {x | f x ≤ 1}) = ∫⁻ _ in s \ {x | f x ≤ 1}, 1 ∂μ := by simp
      _ ≤ ∫⁻ x in s \ {x | f x ≤ 1}, f x ∂μ :=
        setLIntegral_mono' (hs.diff hA) fun x hx ↦ (not_le.1 hx.2).le
  rw [withDensity_apply _ hs, withDensity_apply _ hs, ← lintegral_inter_add_sdiff _ s hA,
    ← lintegral_inter_add_sdiff (fun x ↦ f x) s hA, h1, h2]
  congr 1
  exact setLIntegral_congr_fun (hs.inter hA) fun x hx ↦ min_eq_right hx.2

/-- The image of a measure with a density pulled back from the target, for a measurable map and a
measurable density. -/
theorem map_withDensity_comp {g : α → β} (hg : Measurable g) {h : β → ℝ≥0∞} (hh : Measurable h) :
    (μ.withDensity (h ∘ g)).map g = (μ.map g).withDensity h := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hh hg]
  rfl

/-- The image of a measure with a density pulled back from the target, for a measurable embedding
and any density. -/
theorem _root_.MeasurableEmbedding.map_withDensity_comp {g : α → β} (hg : MeasurableEmbedding g)
    (h : β → ℝ≥0∞) : (μ.withDensity (h ∘ g)).map g = (μ.map g).withDensity h := by
  ext s hs
  rw [hg.map_apply, withDensity_apply _ (hg.measurable hs), withDensity_apply _ hs, hg.restrict_map,
    hg.lintegral_map]
  rfl

end MeasureTheory
