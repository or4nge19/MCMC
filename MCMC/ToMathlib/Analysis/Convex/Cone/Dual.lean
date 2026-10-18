/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Cone.Dual

/-!
# The dual of a salient proper cone separates points

In a locally convex real space, a proper cone `C` is salient iff the functionals nonnegative on `C`
separate points: by Farkas' lemma (`ProperCone.hyperplane_separation_point`) a point `y ∉ C` is
seen by such a functional, and salience puts `-y` outside `C` when `y ∈ C \ {0}`.

## Main statements

* `ProperCone.exists_strongDual_pos_of_salient`
* `ProperCone.exists_strongDual_ne_zero_of_salient`

Staged for `Mathlib/Analysis/Convex/Cone/Dual.lean`, after `ProperCone.hyperplane_separation_point`.
Searched on 2026-10-17: the pinned tree and mathlib master have Farkas' lemma and the double dual
but no statement about salient cones.
-/

namespace ProperCone

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {C : ProperCone ℝ E}

/-- A nonzero point of a salient proper cone is seen by a functional nonnegative on the cone.
This is Farkas' lemma applied to `-x ∉ C`. -/
theorem exists_strongDual_pos_of_salient (hC : (C : ConvexCone ℝ E).Salient) {x : E}
    (hx : x ∈ C) (hx0 : x ≠ 0) : ∃ f : StrongDual ℝ E, (∀ y ∈ C, 0 ≤ f y) ∧ 0 < f x := by
  obtain ⟨f, hfC, hfx⟩ := C.hyperplane_separation_point (x₀ := -x) (hC x hx hx0)
  exact ⟨f, hfC, by simpa using hfx⟩

/-- **The dual of a salient cone separates points**: every `y ≠ 0` is seen by a functional
nonnegative on `C`. -/
theorem exists_strongDual_ne_zero_of_salient (hC : (C : ConvexCone ℝ E).Salient) {y : E}
    (hy : y ≠ 0) : ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ f y ≠ 0 := by
  by_cases hyC : y ∈ C
  · obtain ⟨f, hfC, hfy⟩ := exists_strongDual_pos_of_salient hC hyC hy
    exact ⟨f, hfC, hfy.ne'⟩
  · obtain ⟨f, hfC, hfy⟩ := C.hyperplane_separation_point hyC
    exact ⟨f, hfC, hfy.ne⟩

end ProperCone
