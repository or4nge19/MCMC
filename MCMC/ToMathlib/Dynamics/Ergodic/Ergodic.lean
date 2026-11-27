/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# An ergodic map returns to every set of positive measure from almost every point

For an ergodic map `T` of a finite measure space and a measurable set `t` of positive measure,
almost every orbit visits `t` infinitely often (`Ergodic.ae_frequently_iterate_mem`): the set of
points whose orbit does so is invariant, and by Poincaré recurrence it contains almost all of `t`.

Staged for `Mathlib/Dynamics/Ergodic/Ergodic.lean`. Searched on 2026-11-27 in the pinned Mathlib:
`grep -rn "frequently" Mathlib/Dynamics/Ergodic | grep "theorem\|lemma"` finds only the
`Conservative` recurrence lemmas (returns of points of the set itself) and
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`.
-/

@[expose] public section

open MeasureTheory Set Filter

/-- An ergodic map of a finite measure space returns to every set of positive measure infinitely
often, from almost every point. -/
theorem Ergodic.ae_frequently_iterate_mem {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    [IsFiniteMeasure μ] {T : X → X} (hT : Ergodic T μ) {t : Set X} (ht : MeasurableSet t)
    (h0 : μ t ≠ 0) : ∀ᵐ x ∂μ, ∃ᶠ n in atTop, T^[n] x ∈ t := by
  have hm : MeasurableSet {x | ∃ᶠ n in atTop, T^[n] x ∈ t} := by
    rw [show {x | ∃ᶠ n in atTop, T^[n] x ∈ t} = limsup (fun n ↦ T^[n] ⁻¹' t) atTop from
      Set.ext fun x ↦ (mem_limsup_iff_frequently_mem (s := fun n ↦ T^[n] ⁻¹' t) (𝓕 := atTop)
        (a := x)).symm]
    exact MeasurableSet.measurableSet_limsup fun n ↦ hT.measurable.iterate n ht
  have hshift : ∀ x, (∃ᶠ n in atTop, T^[n] (T x) ∈ t) ↔ ∃ᶠ n in atTop, T^[n] x ∈ t := fun x ↦
    calc (∃ᶠ n in atTop, T^[n] (T x) ∈ t) ↔ ∃ᶠ n in map (· + 1) atTop, T^[n] x ∈ t :=
          (frequently_map (m := (· + 1)) (P := fun n ↦ T^[n] x ∈ t)).symm
      _ ↔ ∃ᶠ n in atTop, T^[n] x ∈ t := by rw [map_add_atTop_eq_nat]
  have hrec := hT.toMeasurePreserving.conservative.ae_mem_imp_frequently_image_mem
    ht.nullMeasurableSet
  refine (hT.toPreErgodic.ae_mem_or_ae_notMem hm (Set.ext hshift)).resolve_right fun hnot ↦
    h0 (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [hrec, hnot] with x hx hx' hxt using hx' (hx hxt)
