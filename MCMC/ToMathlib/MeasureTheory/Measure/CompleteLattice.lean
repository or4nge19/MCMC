/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# The infimum of two measures on singletons and under a measurable embedding

The infimum `μ ⊓ ν` of two measures (Mathlib's `CompleteLattice (Measure α)`) is the minimum of
`μ {a}` and `ν {a}` on a measurable singleton `{a}`, and `Measure.map f` preserves it for a
measurable embedding `f`: both sides vanish off the range of `f`, and on it `Measure.comap f`
inverts `Measure.map f`.

Staged for `Mathlib/MeasureTheory/Measure/CompleteLattice.lean` and
`Mathlib/MeasureTheory/Measure/Restrict.lean`. Searched on 2026-11-26 in the pinned Mathlib:
`grep -rn "map_inf" Mathlib/MeasureTheory` finds only `MeasurableSpace.map_inf`, for σ-algebras
(`grep -rn "map_inf" Mathlib` finds the statements for filters, sublattices and ideals);
`grep -rn "inf_apply" Mathlib/MeasureTheory` finds only `Measure.inf_apply`.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α}

/-- On a measurable singleton, the infimum of two measures is the minimum of their values. -/
theorem inf_apply_singleton [MeasurableSingletonClass α] (μ ν : Measure α) (a : α) :
    (μ ⊓ ν) {a} = min (μ {a}) (ν {a}) := by
  rw [inf_apply (measurableSet_singleton a)]
  refine le_antisymm (le_min (sInf_le ⟨{a}, by simp⟩) (sInf_le ⟨∅, by simp⟩)) (le_sInf ?_)
  rintro _ ⟨t, rfl⟩
  by_cases ha : a ∈ t
  · simp [ha]
  · simp [ha]

end MeasureTheory.Measure

namespace MeasurableEmbedding

open MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The image of the infimum of two measures under a measurable embedding is the infimum of the
images. -/
theorem map_inf {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α) :
    (μ ⊓ ν).map f = μ.map f ⊓ ν.map f := by
  refine le_antisymm (le_inf (Measure.map_mono inf_le_left hf.measurable)
    (Measure.map_mono inf_le_right hf.measurable)) ?_
  have h0 : (μ.map f ⊓ ν.map f) (range f)ᶜ = 0 :=
    le_antisymm ((Measure.le_iff'.1 inf_le_left _).trans_eq (by rw [hf.map_apply]; simp)) zero_le
  have hle : ∀ m : Measure α, μ.map f ⊓ ν.map f ≤ m.map f →
      (μ.map f ⊓ ν.map f).comap f ≤ m := fun m hm ↦ Measure.le_iff.2 fun s _ ↦ by
    rw [hf.comap_apply]
    calc (μ.map f ⊓ ν.map f) (f '' s) ≤ m.map f (f '' s) := Measure.le_iff'.1 hm _
      _ = m s := by rw [hf.map_apply, preimage_image_eq _ hf.injective]
  calc μ.map f ⊓ ν.map f = ((μ.map f ⊓ ν.map f).comap f).map f := by
        rw [hf.map_comap]
        exact (Measure.restrict_eq_self_of_ae_mem (s := range f) (mem_ae_iff.2 h0)).symm
    _ ≤ (μ ⊓ ν).map f :=
        Measure.map_mono (le_inf (hle μ inf_le_left) (hle ν inf_le_right)) hf.measurable

end MeasurableEmbedding
