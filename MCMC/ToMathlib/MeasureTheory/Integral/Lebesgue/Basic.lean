/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# A set integral splits over the fibers of a simple function

Staged for `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`. Searched on 2026-11-27 in the
pinned Mathlib: `grep -rn "lintegral.*fiber\|fiber.*lintegral" Mathlib/MeasureTheory` finds only
the use of `Set.pairwiseDisjoint_fiber` in `Integral/Lebesgue/Countable.lean` (a countable set
split into singletons); `SimpleFunc.lintegral_restrict` is the case of the integrand `f` itself.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.SimpleFunc

variable {α β : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- A set integral is the sum of the integrals over the fibers of a simple function. -/
theorem setLIntegral_eq_sum_fiber (g : SimpleFunc α β) (f : α → ℝ≥0∞) {u : Set α}
    (hu : MeasurableSet u) :
    ∫⁻ x in u, f x ∂μ = ∑ c ∈ g.range, ∫⁻ x in u ∩ g ⁻¹' {c}, f x ∂μ := by
  rw [← lintegral_biUnion_finset (fun c _ d _ hcd ↦ Set.disjoint_left.2 fun x hxc hxd ↦
    hcd (hxc.2.symm.trans hxd.2)) fun c _ ↦ hu.inter (g.measurableSet_fiber c)]
  congr 2
  exact Set.ext fun x ↦ ⟨fun hx ↦ Set.mem_biUnion (g.mem_range_self x) ⟨hx, rfl⟩,
    fun hx ↦ let ⟨_, _, h⟩ := Set.mem_iUnion₂.1 hx; h.1⟩

end MeasureTheory.SimpleFunc
