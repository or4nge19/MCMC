/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# The infimum of two measures on singletons and under a measurable equivalence

The infimum `μ ⊓ ν` of two measures (Mathlib's `CompleteLattice (Measure α)`) is the minimum of
`μ {a}` and `ν {a}` on a measurable singleton `{a}`, and `Measure.map e` preserves it for a
measurable equivalence `e`, being an order isomorphism of measures with inverse
`Measure.map e.symm`.

Staged for `Mathlib/MeasureTheory/Measure/CompleteLattice.lean` and
`Mathlib/MeasureTheory/Measure/Map.lean`. Searched on 2026-11-26 in the pinned Mathlib:
`grep -rn "map_inf" Mathlib/MeasureTheory` has no hit (`grep -rn "map_inf" Mathlib` finds the
statements for filters, sublattices and ideals only); `grep -rn "inf_apply" Mathlib/MeasureTheory`
finds only `Measure.inf_apply`.
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

namespace MeasurableEquiv

open MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The image of the infimum of two measures under a measurable equivalence is the infimum of the
images. -/
theorem map_inf (e : α ≃ᵐ β) (μ ν : Measure α) : (μ ⊓ ν).map e = μ.map e ⊓ ν.map e := by
  refine le_antisymm (le_inf (Measure.map_mono inf_le_left e.measurable)
    (Measure.map_mono inf_le_right e.measurable)) ?_
  calc μ.map e ⊓ ν.map e = ((μ.map e ⊓ ν.map e).map e.symm).map e := (e.map_map_symm).symm
    _ ≤ (μ ⊓ ν).map e := Measure.map_mono (le_inf
        ((Measure.map_mono inf_le_left e.symm.measurable).trans_eq e.map_symm_map)
        ((Measure.map_mono inf_le_right e.symm.measurable).trans_eq e.map_symm_map)) e.measurable

end MeasurableEquiv
