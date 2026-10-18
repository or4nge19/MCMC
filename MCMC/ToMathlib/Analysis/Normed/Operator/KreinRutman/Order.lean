/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Order.Group.PosPart
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.FiniteDimensional
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.OrderBounded

/-!
# Krein–Rutman for positive operators on ordered Banach spaces

Let `E` be a real normed space with a closed vector order (`OrderClosedTopology`,
`IsOrderedAddMonoid`, `PosSMulMono ℝ E`) and `T` a positive operator: `0 ≤ x → 0 ≤ T x`. The
positive cone `ProperCone.positive ℝ E` is salient (`ProperCone.salient_positive`), so the
Krein–Rutman theorems apply once the positive elements span a dense subspace. In a lattice they
span everything (`Submodule.span_Ici_zero_eq_top`, from `x = x⁺ - x⁻`): `ℝⁿ`, `C(K, ℝ)`,
`α →ᵇ ℝ`, `Lᵖ(μ, ℝ)` and every Banach lattice are covered without a new carrier. The strongly
positive case needs order units (`(interior (Set.Ici 0)).Nonempty`), as in `ℝⁿ` and `C(K, ℝ)`.

## Main statements

* `ProperCone.salient_positive`, `Submodule.span_Ici_zero_eq_top` (lattices).
* `IsCompactOperator.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul`: **Krein–Rutman** for
  positive compact operators.
* `IsCompactOperator.exists_nonneg_comp_eq_gelfandRadius_smul`: a positive eigenfunctional of the
  transpose.
* `IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior`: positive
  operators mapping nonzero positive elements to order units, with a spectral gap.
* `IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le`: compact
  `u₀`-positive operators (`ψ x • u₀ ≤ T x ≤ (β * ‖x‖) • u₀`), with spectral gap and no interior
  points: `Lᵖ`, Jentzsch kernels.
* `ContinuousLinearMap.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul`: finite dimension, any
  Gelfand radius.

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: the
pinned tree has `ConvexCone.salient_positive` for the convex cone but not for
`ProperCone.positive`, no span statement for the positive cone of a lattice, and no spectral
statement about positive operators.
-/

open Set

section Order

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [OrderClosedTopology E] {T : E →L[ℝ] E}

/-- The positive cone of an ordered normed space is salient. -/
theorem ProperCone.salient_positive : (ProperCone.positive ℝ E : ConvexCone ℝ E).Salient :=
  fun _ hx hx0 hnx ↦ hx0 (le_antisymm (by simpa using hnx) (by simpa using hx))

/-- **Krein–Rutman theorem for positive compact operators**: if the positive elements of a
Banach space with a closed order span a dense subspace, a positive compact operator with
positive Gelfand radius has a positive eigenvector for its Gelfand radius. -/
theorem IsCompactOperator.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul [CompleteSpace E]
    (hTc : IsCompactOperator T) (hE : Dense (Submodule.span ℝ (Ici (0 : E)) : Set E))
    (hT : ∀ x, 0 ≤ x → 0 ≤ T x) (hr : 0 < gelfandRadius T) :
    ∃ x, 0 ≤ x ∧ x ≠ 0 ∧ T x = gelfandRadius T • x := by
  obtain ⟨x, hx, hxe⟩ := ProperCone.exists_mem_hasEigenvector_gelfandRadius_of_isCompactOperator
    ProperCone.salient_positive hE hTc hT hr
  exact ⟨x, hx, hxe.2, hxe.apply_eq_smul⟩

/-- **Dual Krein–Rutman theorem for positive compact operators**: under the hypotheses of
`IsCompactOperator.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul`, the transpose has a
positive eigenfunctional for the Gelfand radius. -/
theorem IsCompactOperator.exists_nonneg_comp_eq_gelfandRadius_smul [CompleteSpace E]
    (hTc : IsCompactOperator T) (hE : Dense (Submodule.span ℝ (Ici (0 : E)) : Set E))
    (hT : ∀ x, 0 ≤ x → 0 ≤ T x) (hr : 0 < gelfandRadius T) :
    ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ (∀ x, 0 ≤ x → 0 ≤ ℓ x) ∧ ℓ.comp T = gelfandRadius T • ℓ :=
  ProperCone.exists_dual_comp_eq_gelfandRadius_smul_of_isCompactOperator
    ProperCone.salient_positive hE hTc hT hr

/-- **Krein–Rutman theorem for compact operators improving positivity**: if the positive elements
of a Banach space with a closed order have nonempty interior (order units) and a compact `T` maps
nonzero positive elements to interior points, then `r = gelfandRadius T > 0`, `T x₀ = r • x₀` for
an interior `x₀`, the transpose has an eigenfunctional `ℓ` positive on nonzero positive elements
with `ℓ x₀ = 1`, and `gelfandRadius (T - r • ℓ.smulRight x₀) < r`. -/
theorem IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior
    [CompleteSpace E] [Nontrivial E] (hTc : IsCompactOperator T)
    (hi : (interior (Ici (0 : E))).Nonempty)
    (hT : ∀ x, 0 ≤ x → x ≠ 0 → T x ∈ interior (Ici 0)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (Ici (0 : E)), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x, 0 ≤ x → x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T :=
  ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator
    ProperCone.salient_positive hi hTc fun x hx ↦ hT x hx.1 hx.2

/-- **Krein–Rutman theorem for compact `u₀`-positive operators** on an ordered Banach space whose
positive elements span a dense subspace (`Lᵖ`, `C₀`, Banach lattices; no interior points needed):
if `ψ x • u₀ ≤ T x` for `0 ≤ x`, with `ψ > 0` on nonzero positive elements, and
`T x ≤ (β * ‖x‖) • u₀` for all `x`, then `r = gelfandRadius T > 0` has a positive eigenvector
`x₀ ≥ a • u₀` (`a > 0`), the transpose has an eigenfunctional `ℓ` positive on nonzero positive
elements with `ℓ x₀ = 1`, and `gelfandRadius (T - r • ℓ.smulRight x₀) < r`. Integral operators on
`Lᵖ(μ)`, `μ` finite, with kernel `0 < c₁ ≤ k ≤ c₂` satisfy it with `u₀ = 1` (Jentzsch). -/
theorem IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le
    [CompleteSpace E] (hTc : IsCompactOperator T)
    (hE : Dense (Submodule.span ℝ (Ici (0 : E)) : Set E)) {u₀ : E} (hu₀ : 0 ≤ u₀)
    (hu₀0 : u₀ ≠ 0) {ψ : StrongDual ℝ E} (hψ : ∀ x, 0 ≤ x → x ≠ 0 → 0 < ψ x)
    (hlow : ∀ x, 0 ≤ x → ψ x • u₀ ≤ T x) {β : ℝ} (hup : ∀ x, T x ≤ (β * ‖x‖) • u₀) :
    0 < gelfandRadius T ∧ ∃ x₀, 0 ≤ x₀ ∧ ∃ a : ℝ, 0 < a ∧ a • u₀ ≤ x₀ ∧ ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x, 0 ≤ x → x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  obtain ⟨hr, x₀, hx₀, a, ha, hx₀u, ℓ, h⟩ :=
    ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le_of_isCompactOperator
      ProperCone.salient_positive hE hTc hu₀ hu₀0 hψ (fun x hx ↦ sub_nonneg.2 (hlow x hx))
      (fun x ↦ sub_nonneg.2 (hup x))
  exact ⟨hr, x₀, hx₀, a, ha, sub_nonneg.1 hx₀u, ℓ, h⟩

/-- **Perron–Frobenius for positive operators in finite dimension**: if the positive elements of
a finite-dimensional space with a closed order span it, every positive operator has a positive
eigenvector for its Gelfand radius. -/
theorem ContinuousLinearMap.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul
    [FiniteDimensional ℝ E] [Nontrivial E] (hE : Submodule.span ℝ (Ici (0 : E)) = ⊤)
    (hT : ∀ x, 0 ≤ x → 0 ≤ T x) : ∃ x, 0 ≤ x ∧ x ≠ 0 ∧ T x = gelfandRadius T • x := by
  obtain ⟨x, hx, hxe⟩ := ProperCone.exists_mem_hasEigenvector_gelfandRadius
    ProperCone.salient_positive hE hT
  exact ⟨x, hx, hxe.2, hxe.apply_eq_smul⟩

end Order

/-- The nonnegative elements of a lattice-ordered module span it: `x = x⁺ - x⁻`. -/
theorem Submodule.span_Ici_zero_eq_top {R E : Type*} [Ring R] [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [Module R E] : Submodule.span R (Ici (0 : E)) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [← posPart_sub_negPart x]
  exact sub_mem (subset_span (posPart_nonneg x)) (subset_span (negPart_nonneg x))
