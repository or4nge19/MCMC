/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# Infima and images of measures with densities

The infimum of `μ.withDensity f` and `μ.withDensity g` is `μ.withDensity (f ⊓ g)`, for measurable
`f` and `g` and any measure `μ`; and the image of `μ.withDensity f` under a measurable equivalence
`e` is `(μ.map e).withDensity (f ∘ e.symm)`.

Staged for `Mathlib/MeasureTheory/Measure/WithDensity.lean`. Searched on 2026-11-26 in the pinned
Mathlib: `grep -rn "withDensity_inf\|inf_withDensity\|withDensity_min" Mathlib` has no hit;
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

/-- The image of a measure with density under a measurable equivalence. -/
theorem _root_.MeasurableEquiv.map_withDensity (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs, e.restrict_map,
    lintegral_map_equiv]
  simp

end MeasureTheory
