/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Interior points of a proper cone

An interior point `x` of a proper cone `C` absorbs every direction: `x + ε • y ∈ C` for small `ε`.
Hence `C` spans the space, `C` is everything if `0` is interior, positive multiples of interior
points are interior, and a nonzero functional nonnegative on `C` is positive at `x`.

## Main statements

* `ProperCone.eventually_add_smul_mem_of_mem_interior`
* `ProperCone.span_eq_top_of_mem_interior`
* `ProperCone.mem_of_zero_mem_interior`
* `ProperCone.smul_mem_interior`
* `ProperCone.pos_of_mem_interior`

Staged for `Mathlib/Analysis/Convex/Cone/Basic.lean`. Searched on 2026-10-17: the pinned tree and
mathlib master have `interior_smul₀` and convex-set interior lemmas, but no statement about
interior points of a proper cone.
-/

open Filter Topology Set

namespace ProperCone

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {C : ProperCone ℝ E} {x : E}

/-- An interior point of a cone absorbs every direction. -/
theorem eventually_add_smul_mem_of_mem_interior (hx : x ∈ interior (C : Set E)) (y : E) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), x + ε • y ∈ C := by
  have hc : Continuous fun ε : ℝ ↦ x + ε • y := by fun_prop
  have h : Tendsto (fun ε : ℝ ↦ x + ε • y) (𝓝 0) (𝓝 x) := by simpa using hc.tendsto 0
  exact h.eventually (mem_interior_iff_mem_nhds.1 hx)

/-- Points `x + ε • y ∈ C` with `ε > 0`, for an interior point `x`. -/
theorem exists_pos_add_smul_mem_of_mem_interior (hx : x ∈ interior (C : Set E)) (y : E) :
    ∃ ε > (0 : ℝ), x + ε • y ∈ C ∧ x - ε • y ∈ C := by
  obtain ⟨ε, ⟨h₁, h₂⟩, hε⟩ := (((eventually_add_smul_mem_of_mem_interior hx y).and
    (eventually_add_smul_mem_of_mem_interior hx (-y))).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi 0)) |>.exists
  exact ⟨ε, hε, h₁, by simpa [sub_eq_add_neg] using h₂⟩

/-- A proper cone with an interior point spans the space. -/
theorem span_eq_top_of_mem_interior (hx : x ∈ interior (C : Set E)) :
    Submodule.span ℝ (C : Set E) = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨ε, hε, hεC, -⟩ := exists_pos_add_smul_mem_of_mem_interior hx y
  rw [show y = ε⁻¹ • ((x + ε • y) - x) by simp [smul_smul, inv_mul_cancel₀ hε.ne']]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span hεC)
    (Submodule.subset_span (interior_subset hx)))

/-- A proper cone with `0` as an interior point is the whole space. -/
theorem mem_of_zero_mem_interior (h : (0 : E) ∈ interior (C : Set E)) (y : E) : y ∈ C := by
  obtain ⟨ε, hε, hεC, -⟩ := exists_pos_add_smul_mem_of_mem_interior h y
  have hy := C.smul_mem (zero_add (ε • y) ▸ hεC) (inv_nonneg.2 hε.le)
  rwa [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] at hy

omit [IsTopologicalAddGroup E] in
/-- Positive multiples of interior points of a cone are interior points. -/
theorem smul_mem_interior {c : ℝ} (hc : 0 < c) (hx : x ∈ interior (C : Set E)) :
    c • x ∈ interior (C : Set E) := by
  rw [mem_interior_iff_mem_nhds] at hx ⊢
  have h : Tendsto (fun z : E ↦ c⁻¹ • z) (𝓝 (c • x)) (𝓝 x) := by
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using (continuous_const_smul c⁻¹).tendsto (c • x)
  filter_upwards [h hx] with z hz
  simpa [smul_smul, mul_inv_cancel₀ hc.ne'] using C.smul_mem hz hc.le

/-- A nonzero functional nonnegative on a cone is positive at its interior points. -/
theorem pos_of_mem_interior {f : E →L[ℝ] ℝ} (hf : ∀ y ∈ C, 0 ≤ f y) (hf0 : f ≠ 0)
    (hx : x ∈ interior (C : Set E)) : 0 < f x := by
  refine (hf x (interior_subset hx)).lt_of_ne fun hfx ↦ hf0 (ContinuousLinearMap.ext fun y ↦ ?_)
  obtain ⟨ε, hε, h₁, h₂⟩ := exists_pos_add_smul_mem_of_mem_interior hx y
  have hy₁ := hf _ h₁
  have hy₂ := hf _ h₂
  rw [map_add, map_smul, ← hfx, zero_add, smul_eq_mul] at hy₁
  rw [map_sub, map_smul, ← hfx, zero_sub, smul_eq_mul, neg_nonneg] at hy₂
  exact le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.1 hy₂).1 hε)
    ((mul_nonneg_iff_of_pos_left hε).1 hy₁)

end ProperCone
