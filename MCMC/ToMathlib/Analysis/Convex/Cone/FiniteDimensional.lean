/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Proper cones in finite-dimensional normed spaces

A salient proper cone `C` in a finite-dimensional real normed space has a *compact base*: some
continuous functional `f` is positive on `C \ {0}`, and then dominates a positive multiple of the
norm on `C`. Equivalently, every closed salient cone in finite dimension is normal.

Duality exchanges the two halves of "salient and generating": the dual cone
`C* = {f | ∀ x ∈ C, 0 ≤ f x}` in `StrongDual ℝ E` is salient when `C` spans `E`, and spans
`StrongDual ℝ E` when `C` is salient (the compact-base functional is an interior point of `C*`).
An operator preserving `C` has a transpose `f ↦ f ∘L T` preserving `C*`.

## Main statements

* `ProperCone.exists_strongDual_forall_pos`, `ProperCone.exists_strongDual_forall_mul_norm_le`:
  compact base of a closed salient cone in finite dimension.
* `ProperCone.salient_dual_of_span_eq_top`, `ProperCone.span_dual_eq_top_of_salient`,
  `ProperCone.mapsTo_compL_flip_dual`.

Staged for a new `Mathlib/Analysis/Convex/Cone/FiniteDimensional.lean`. Searched on 2026-10-17:
the pinned tree and mathlib master have Farkas' lemma (`ProperCone.hyperplane_separation_point`),
the double dual and inner-product duals, but no strictly positive functional, compact base,
normality, or
salient/generating duality statement.
-/

open Metric Set

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ProperCone ℝ E}

/-- Normalizing a nonzero point of a cone lands in `C ∩ sphere 0 1`. -/
theorem inv_norm_smul_mem_inter_sphere {x : E} (hx : x ∈ C) (hx0 : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ (C : Set E) ∩ sphere 0 1 :=
  ⟨C.smul_mem hx (inv_nonneg.2 (norm_nonneg x)), by simp [norm_smul, hx0]⟩

variable [FiniteDimensional ℝ E]

/-- In finite dimension, a functional positive on `C \ {0}` dominates a positive multiple of the
norm on `C`: its minimum on the compact set `C ∩ sphere 0 1`. -/
theorem exists_pos_forall_mul_norm_le_of_forall_pos {f : StrongDual ℝ E}
    (hf : ∀ x ∈ C, x ≠ 0 → 0 < f x) : ∃ c > 0, ∀ x ∈ C, c * ‖x‖ ≤ f x := by
  have hS : IsCompact ((C : Set E) ∩ sphere 0 1) := (isCompact_sphere 0 1).inter_left C.isClosed
  obtain hSe | hSne := ((C : Set E) ∩ sphere 0 1).eq_empty_or_nonempty
  · refine ⟨1, one_pos, fun x hx ↦ ?_⟩
    obtain rfl | hx0 := eq_or_ne x 0
    · simp
    simpa [hSe] using inv_norm_smul_mem_inter_sphere hx hx0
  obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hSne f.continuous.continuousOn
  refine ⟨f y₀, hf y₀ hy₀.1 (ne_zero_of_mem_unit_sphere ⟨y₀, hy₀.2⟩), fun x hx ↦ ?_⟩
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  have hle : f y₀ ≤ ‖x‖⁻¹ * f x := by simpa using hmin (inv_norm_smul_mem_inter_sphere hx hx0)
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  calc f y₀ * ‖x‖ ≤ ‖x‖⁻¹ * f x * ‖x‖ := by gcongr
    _ = f x := by field_simp

/-- **Strictly positive functional.** In finite dimension a closed salient cone carries a
functional positive on `C \ {0}`: a finite sum of the separating functionals of
`exists_strongDual_pos_of_salient`, by compactness of `C ∩ sphere 0 1`. -/
theorem exists_strongDual_forall_pos (hC : (C : ConvexCone ℝ E).Salient) :
    ∃ f : StrongDual ℝ E, ∀ x ∈ C, x ≠ 0 → 0 < f x := by
  have hS : IsCompact ((C : Set E) ∩ sphere 0 1) := (isCompact_sphere 0 1).inter_left C.isClosed
  have hsep (x : ↥((C : Set E) ∩ sphere 0 1)) :
      ∃ f : StrongDual ℝ E, (∀ y ∈ C, 0 ≤ f y) ∧ 0 < f x :=
    exists_strongDual_pos_of_salient hC x.2.1 (ne_zero_of_mem_unit_sphere ⟨(x : E), x.2.2⟩)
  choose g hgC hgx using hsep
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x ↦ {y | 0 < g x y})
    (fun x ↦ isOpen_lt continuous_const (g x).continuous)
    (fun y hy ↦ mem_iUnion.2 ⟨⟨y, hy⟩, hgx _⟩)
  refine ⟨∑ x ∈ t, g x, fun x hx hx0 ↦ ?_⟩
  obtain ⟨z, hzt, hz⟩ := mem_iUnion₂.1 (ht (inv_norm_smul_mem_inter_sphere hx hx0))
  have hpos : 0 < (∑ x ∈ t, g x) (‖x‖⁻¹ • x) := by
    simp only [FunLike.coe_sum, Finset.sum_apply]
    exact Finset.sum_pos' (fun y _ ↦ hgC y _ (C.smul_mem hx (by positivity))) ⟨z, hzt, hz⟩
  rw [map_smul, smul_eq_mul] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **Compact base of a salient cone**: in finite dimension a closed salient cone carries a
functional bounded below by a positive multiple of the norm. -/
theorem exists_strongDual_forall_mul_norm_le (hC : (C : ConvexCone ℝ E).Salient) :
    ∃ f : StrongDual ℝ E, ∃ c > 0, ∀ x ∈ C, c * ‖x‖ ≤ f x := by
  obtain ⟨f, hf⟩ := exists_strongDual_forall_pos hC
  obtain ⟨c, hc, h⟩ := exists_pos_forall_mul_norm_le_of_forall_pos hf
  exact ⟨f, c, hc, h⟩

@[simp] theorem mem_dual_topDualPairing_flip {f : StrongDual ℝ E} :
    f ∈ dual (topDualPairing ℝ E).flip (C : Set E) ↔ ∀ x ∈ C, 0 ≤ f x := by
  simp

/-- The dual of a generating cone is salient. -/
theorem salient_dual_of_span_eq_top (hCE : Submodule.span ℝ (C : Set E) = ⊤) :
    (dual (topDualPairing ℝ E).flip (C : Set E) : ConvexCone ℝ (StrongDual ℝ E)).Salient := by
  intro f hf hf0 hnf
  refine hf0 (ContinuousLinearMap.ext fun x ↦ ?_)
  have hf' := mem_dual_topDualPairing_flip.1 hf
  have hnf' := mem_dual_topDualPairing_flip.1 hnf
  have hker : Submodule.span ℝ (C : Set E) ≤ LinearMap.ker (f : E →ₗ[ℝ] ℝ) :=
    Submodule.span_le.2 fun y hy ↦ le_antisymm (by simpa using hnf' y hy) (hf' y hy)
  simpa using hker (hCE ▸ Submodule.mem_top (x := x))

/-- In finite dimension, the dual of a salient cone spans the dual space: the compact-base
functional `f` is an interior point of the dual cone. -/
theorem span_dual_eq_top_of_salient (hC : (C : ConvexCone ℝ E).Salient) :
    Submodule.span ℝ (dual (topDualPairing ℝ E).flip (C : Set E) : Set (StrongDual ℝ E)) = ⊤ := by
  obtain ⟨f, c, hc, hf⟩ := exists_strongDual_forall_mul_norm_le hC
  refine eq_top_iff.2 fun g _ ↦ ?_
  set ε := c / (‖g‖ + 1)
  have hε : 0 < ε := by positivity
  have hεg : ε * ‖g‖ ≤ c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg g]
  have hfg : f + ε • g ∈ dual (topDualPairing ℝ E).flip (C : Set E) := by
    refine mem_dual_topDualPairing_flip.2 fun x hx ↦ ?_
    have hgx : -(‖g‖ * ‖x‖) ≤ g x := neg_le_of_abs_le (g.le_opNorm x)
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    nlinarith [hf x hx, mul_le_mul_of_nonneg_right hεg (norm_nonneg x)]
  have hf' : f ∈ dual (topDualPairing ℝ E).flip (C : Set E) :=
    mem_dual_topDualPairing_flip.2 fun x hx ↦ (by positivity : 0 ≤ c * ‖x‖).trans (hf x hx)
  rw [show g = ε⁻¹ • ((f + ε • g) - f) by simp [smul_smul, inv_mul_cancel₀ hε.ne']]
  exact Submodule.smul_mem _ _
    (Submodule.sub_mem _ (Submodule.subset_span hfg) (Submodule.subset_span hf'))

/-- The transpose `f ↦ f ∘L T` of an operator preserving `C` preserves the dual cone. -/
theorem mapsTo_compL_flip_dual {T : E →L[ℝ] E} (hT : MapsTo T C C) :
    MapsTo ((ContinuousLinearMap.compL ℝ E E ℝ).flip T)
      (dual (topDualPairing ℝ E).flip (C : Set E)) (dual (topDualPairing ℝ E).flip (C : Set E)) :=
  fun f hf ↦ mem_dual_topDualPairing_flip.2 fun x hx ↦ by
    simpa using mem_dual_topDualPairing_flip.1 hf (T x) (hT hx)

end ProperCone
