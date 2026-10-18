/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Order

/-!
# The self-adjoint part of a C⋆-algebra as an ordered Banach space

For a unital C⋆-algebra `A`, `selfAdjoint A` is a real Banach space (`CompleteSpace`, from
`selfAdjoint.isClosed`) with a closed order compatible with nonnegative scalars (`PosSMulMono`),
whose positive elements span it (`a = a⁺ - a⁻`) and have `1` as an interior point (an order unit:
`‖b - 1‖ < 1` forces `0 ≤ b`). So the Krein–Rutman theorems for ordered Banach spaces apply to
positive maps of `A` restricted to `selfAdjoint A`. For finite-dimensional `A` (matrix algebras)
this is the Perron–Frobenius theorem for positive maps (Evans–Høegh-Krohn): a positive map has a
positive semidefinite eigenvector for its spectral radius, and a positivity improving map has a
positive definite one with a spectral gap.

## Main statements

* `selfAdjoint.isClosed`, `selfAdjoint.span_Ici_zero_eq_top`,
  `selfAdjoint.one_mem_interior_Ici_zero`.
* `selfAdjoint.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul`: **Perron–Frobenius for positive
  maps** on a finite-dimensional C⋆-algebra.
* `selfAdjoint.exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior`: positivity
  improving maps, with a spectral gap.

Staged for `Mathlib/Analysis/CStarAlgebra/` (the instances and lemmas) and
`Mathlib/Analysis/Normed/Operator/KreinRutman.lean` (the corollaries). Searched on 2026-10-17:
the pinned tree has the normed space, order and `OrderClosedTopology` structures on
`selfAdjoint A` but no `CompleteSpace`, `FiniteDimensional` or `PosSMulMono` instance, no
closedness lemma for
`selfAdjoint A`, and no Perron–Frobenius statement for positive maps; `LionSR/QICLean`
(`Channel/Irreducible/PerronFrobenius.lean`) proves the irreducible completely positive case on
matrices.
-/

open Set

namespace selfAdjoint

variable {A : Type*} [CStarAlgebra A]

/-- The self-adjoint elements form a closed set. -/
theorem isClosed : IsClosed (selfAdjoint A : Set A) :=
  isClosed_eq continuous_star continuous_id

instance : CompleteSpace (selfAdjoint A) :=
  isClosed.completeSpace_coe

instance [FiniteDimensional ℝ A] : FiniteDimensional ℝ (selfAdjoint A) :=
  Module.Finite.of_injective
    ({ toFun := Subtype.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      selfAdjoint A →ₗ[ℝ] A) Subtype.val_injective

variable [PartialOrder A] [StarOrderedRing A]

instance : PosSMulMono ℝ (selfAdjoint A) :=
  PosSMulMono.lift (fun a : selfAdjoint A ↦ (a : A)) Iff.rfl fun _ _ ↦ rfl

/-- The positive elements span the self-adjoint part: `a = a⁺ - a⁻`. -/
theorem span_Ici_zero_eq_top : Submodule.span ℝ (Ici (0 : selfAdjoint A)) = ⊤ := by
  refine eq_top_iff.2 fun a _ ↦ ?_
  have h : (⟨(a : A)⁺, (CFC.posPart_nonneg (a : A)).isSelfAdjoint⟩ : selfAdjoint A) -
      ⟨(a : A)⁻, (CFC.negPart_nonneg (a : A)).isSelfAdjoint⟩ = a :=
    Subtype.ext (CFC.posPart_sub_negPart (a : A) a.2)
  rw [← h]
  exact sub_mem (Submodule.subset_span (CFC.posPart_nonneg (a : A)))
    (Submodule.subset_span (CFC.negPart_nonneg (a : A)))

/-- `1` is an order unit: every self-adjoint `b` with `‖b - 1‖ < 1` is positive. -/
theorem one_mem_interior_Ici_zero : (1 : selfAdjoint A) ∈ interior (Ici 0) := by
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds 1 one_pos)
    fun b hb ↦ ?_)
  have hb' : ‖(b : A) - 1‖ < 1 := by simpa [dist_eq_norm] using hb
  have h := IsSelfAdjoint.neg_algebraMap_norm_le_self ((b : A) - 1) (b.2.sub (.one A))
  have hb0 : (0 : A) ≤ b := calc
    (0 : A) ≤ algebraMap ℝ A (1 - ‖(b : A) - 1‖) := algebraMap_nonneg A (by linarith)
    _ = -algebraMap ℝ A ‖(b : A) - 1‖ + 1 := by rw [map_sub, map_one, sub_eq_neg_add]
    _ ≤ (b : A) - 1 + 1 := add_le_add_left h 1
    _ = b := sub_add_cancel _ _
  exact Set.mem_Ici.2 (Subtype.coe_le_coe.1 (by simpa using hb0))

variable [Nontrivial A] [FiniteDimensional ℝ (selfAdjoint A)]
  {T : selfAdjoint A →L[ℝ] selfAdjoint A}

/-- **Perron–Frobenius for positive maps** (Evans–Høegh-Krohn): on a finite-dimensional C⋆-algebra,
a positive real-linear map of the self-adjoint part has a positive eigenvector for its Gelfand
radius. -/
theorem exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul (hT : ∀ a, 0 ≤ a → 0 ≤ T a) :
    ∃ a, 0 ≤ a ∧ a ≠ 0 ∧ T a = gelfandRadius T • a :=
  T.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul span_Ici_zero_eq_top hT

/-- **Perron–Frobenius for positivity improving maps**: on a finite-dimensional C⋆-algebra, if `T`
maps nonzero positive elements to interior points of the positive cone, then `r = gelfandRadius T`
is positive, with an interior eigenvector `a₀`, a positive eigenfunctional `ℓ` of the transpose
with `ℓ a₀ = 1`, and `gelfandRadius (T - r • ℓ.smulRight a₀) < r`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior
    (hT : ∀ a, 0 ≤ a → a ≠ 0 → T a ∈ interior (Ici 0)) :
    0 < gelfandRadius T ∧ ∃ a₀ ∈ interior (Ici (0 : selfAdjoint A)), ∃ ℓ : StrongDual ℝ _,
      T a₀ = gelfandRadius T • a₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ a₀ = 1 ∧
      (∀ a, 0 ≤ a → a ≠ 0 → 0 < ℓ a) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight a₀) < gelfandRadius T :=
  (isCompactOperator_of_locallyCompactSpace_rng T
    ).exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior
    ⟨1, one_mem_interior_Ici_zero⟩ hT

end selfAdjoint
