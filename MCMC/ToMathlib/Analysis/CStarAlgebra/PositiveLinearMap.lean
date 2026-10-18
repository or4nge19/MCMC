/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import MCMC.ToMathlib.Analysis.CStarAlgebra.SelfAdjoint

/-!
# Perron–Frobenius for positive maps of C⋆-algebras

A positive linear map `f : A →ₚ[ℂ] A` of a unital C⋆-algebra is continuous
(`PositiveLinearMap.exists_norm_apply_le`) and maps self-adjoint elements to self-adjoint
elements, so it restricts to a positive real operator `f.toSelfAdjoint` of the ordered real Banach
space `selfAdjoint A`. Both have the same Gelfand radius: `‖(f|ₛₐ)ⁿ‖ ≤ ‖fⁿ‖` by restriction, and
`‖fⁿ‖ ≤ 4 ‖(f|ₛₐ)ⁿ‖` because every element is `∑ i, Iⁱ • yᵢ` with `0 ≤ yᵢ`, `‖yᵢ‖ ≤ ‖x‖`
(`CStarAlgebra.exists_sum_four_nonneg`). The Krein–Rutman theorems for `selfAdjoint A` then give
the Perron–Frobenius theorem for positive maps (Evans–Høegh-Krohn): on a finite-dimensional
C⋆-algebra, such as `Matrix n n ℂ`, the spectral radius of `f` is an eigenvalue with a positive
eigenvector; if `f` maps nonzero positive elements to strictly positive ones, there is a spectral
gap. Completely positive maps, in particular quantum channels, are positive.

## Main statements

* `gelfandRadius_le_of_norm_pow_le`: Gelfand radii compare as norms of powers do.
* `selfAdjoint.mem_interior_Ici_zero`: strictly positive elements are interior points of the
  positive cone of `selfAdjoint A`.
* `PositiveLinearMap.toSelfAdjoint`, `PositiveLinearMap.gelfandRadius_toSelfAdjoint`,
  `PositiveLinearMap.spectralRadius_eq_gelfandRadius_toSelfAdjoint`.
* `PositiveLinearMap.exists_nonneg_ne_zero_apply_eq_spectralRadius_smul`: **Perron–Frobenius for
  positive maps**: the spectral radius is an eigenvalue with a positive eigenvector.
* `PositiveLinearMap.exists_gelfandRadius_sub_smul_smulRight_lt_of_isStrictlyPositive`: positivity
  improving maps, with a spectral gap.

## References

* D. E. Evans, R. Høegh-Krohn, *Spectral properties of positive maps on C⋆-algebras*, J. London
  Math. Soc. (2) 17 (1978), 345–355.

Staged for `Mathlib/Analysis/CStarAlgebra/PositiveLinearMap.lean`. Searched on 2026-10-17: the
pinned tree has continuity of positive maps but neither their self-adjointness nor any spectral
statement; `j-loreaux/LeanOA` (`acede8fd4a8f`, `LeanOA/PositiveContinuousLinearMap.lean`) proves
self-adjointness as `PositiveLinearMap.map_isSelfAdjoint` and lifts positive maps to
`PositiveLinearMap.toContinuousLinearMap`, names avoided here so that both can be imported;
`LionSR/QICLean` proves the irreducible completely positive case on matrices.
-/

open Filter Set Topology

/-- **Comparison of Gelfand radii**: if `‖a ^ n‖ ≤ C * ‖b ^ n‖` for all `n`, then
`gelfandRadius a ≤ gelfandRadius b`. -/
theorem gelfandRadius_le_of_norm_pow_le {A B : Type*} [SeminormedRing A] [SeminormedRing B] {a : A}
    {b : B} {C : ℝ} (h : ∀ n : ℕ, ‖a ^ n‖ ≤ C * ‖b ^ n‖) : gelfandRadius a ≤ gelfandRadius b := by
  refine le_of_forall_gt_imp_ge_of_dense fun s hs ↦ ?_
  obtain ⟨D, -, hD⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hs
  refine gelfandRadius_le_of_bound (C := max C 0 * D) ((gelfandRadius_nonneg b).trans hs.le)
    fun n ↦ ?_
  calc ‖a ^ n‖ ≤ C * ‖b ^ n‖ := h n
    _ ≤ max C 0 * ‖b ^ n‖ := by gcongr; exact le_max_left C 0
    _ ≤ max C 0 * (D * s ^ n) := mul_le_mul_of_nonneg_left (hD n) (le_max_right C 0)
    _ = max C 0 * D * s ^ n := by ring

namespace selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A strictly positive self-adjoint element is an interior point of the positive cone of
`selfAdjoint A`: its spectrum has a positive minimum `c`, and `‖b - a‖ < c` forces `0 ≤ b`. -/
theorem mem_interior_Ici_zero [Nontrivial A] {a : selfAdjoint A}
    (ha : IsStrictlyPositive (a : A)) : a ∈ interior (Ici 0) := by
  obtain ⟨c, hcσ, hmin⟩ := (spectrum.isCompact (𝕜 := ℝ) (a : A)).exists_isMinOn
    (ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (a : A) a.2) continuousOn_id
  have hc : 0 < c :=
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) (a : A) a.2).1 ha c hcσ
  have hca : algebraMap ℝ A c ≤ a := algebraMap_le_of_le_spectrum (fun x hx ↦ hmin hx) a.2
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds a hc)
    fun b hb ↦ ?_)
  have hb' : ‖(b : A) - a‖ < c := by simpa [dist_eq_norm] using hb
  have h := IsSelfAdjoint.neg_algebraMap_norm_le_self ((b : A) - a) (b.2.sub a.2)
  have hb0 : (0 : A) ≤ b := calc
    (0 : A) ≤ algebraMap ℝ A (c - ‖(b : A) - a‖) := algebraMap_nonneg A (by linarith)
    _ = algebraMap ℝ A c + -algebraMap ℝ A ‖(b : A) - a‖ := by rw [map_sub, sub_eq_add_neg]
    _ ≤ a + ((b : A) - a) := add_le_add hca h
    _ = b := add_sub_cancel _ _
  exact Set.mem_Ici.2 (Subtype.coe_le_coe.1 (by simpa using hb0))

end selfAdjoint

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] A)

/-- A positive map sends self-adjoint elements to self-adjoint elements: `a = a⁺ - a⁻`. -/
theorem isSelfAdjoint_apply {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (f a) := by
  rw [← CFC.posPart_sub_negPart a ha, map_sub]
  exact (map_nonneg f (CFC.posPart_nonneg a)).isSelfAdjoint.sub
    (map_nonneg f (CFC.negPart_nonneg a)).isSelfAdjoint

/-- The restriction of a positive map to the self-adjoint part, a positive real operator. -/
noncomputable def toSelfAdjoint : selfAdjoint A →L[ℝ] selfAdjoint A :=
  LinearMap.mkContinuousOfExistsBound
    { toFun a := ⟨f (a : A), f.isSelfAdjoint_apply a.2⟩
      map_add' a b := Subtype.ext (map_add f (a : A) b)
      map_smul' c a := Subtype.ext (by simp) }
    (by
      obtain ⟨C, hC⟩ := f.exists_norm_apply_le
      exact ⟨C, fun a ↦ hC a⟩)

@[simp]
theorem coe_toSelfAdjoint_apply (a : selfAdjoint A) : (f.toSelfAdjoint a : A) = f a := rfl

theorem toSelfAdjoint_nonneg {a : selfAdjoint A} (ha : 0 ≤ a) : 0 ≤ f.toSelfAdjoint a :=
  Subtype.coe_le_coe.1 (by simpa using map_nonneg f (Subtype.coe_le_coe.2 ha))

theorem coe_toSelfAdjoint_pow_apply (n : ℕ) (a : selfAdjoint A) :
    ((f.toSelfAdjoint ^ n) a : A) =
      (ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [pow_succ, mul_apply_eq_comp, ih, pow_succ, mul_apply_eq_comp]; rfl

theorem norm_toSelfAdjoint_pow_le (n : ℕ) :
    ‖f.toSelfAdjoint ^ n‖ ≤ ‖ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a ↦ ?_
  have h := ContinuousLinearMap.le_opNorm
    (ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n) (a : A)
  rw [← coe_toSelfAdjoint_pow_apply] at h
  exact h

/-- Powers of a positive map are controlled by their restrictions to the self-adjoint part: every
`x` is `∑ i, Iⁱ • yᵢ` with `0 ≤ yᵢ`, `‖yᵢ‖ ≤ ‖x‖`. -/
theorem norm_pow_le_four_mul_norm_toSelfAdjoint_pow (n : ℕ) :
    ‖ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n‖ ≤
      4 * ‖f.toSelfAdjoint ^ n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  obtain ⟨y, hy0, hyx, hx⟩ := CStarAlgebra.exists_sum_four_nonneg x
  have hy (i : Fin 4) : ‖(ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n) (y i)‖ ≤
      ‖f.toSelfAdjoint ^ n‖ * ‖x‖ := by
    have h : ‖((f.toSelfAdjoint ^ n) ⟨y i, (hy0 i).isSelfAdjoint⟩ : A)‖ ≤
        ‖f.toSelfAdjoint ^ n‖ * ‖y i‖ := (f.toSelfAdjoint ^ n).le_opNorm _
    rw [coe_toSelfAdjoint_pow_apply] at h
    exact h.trans (by gcongr; exact hyx i)
  calc ‖(ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n) x‖
      ≤ ∑ i : Fin 4, ‖(ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f) ^ n) (y i)‖ := by
        conv_lhs => rw [hx]
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        simp [norm_smul]
    _ ≤ ∑ _i : Fin 4, ‖f.toSelfAdjoint ^ n‖ * ‖x‖ := Finset.sum_le_sum fun i _ ↦ hy i
    _ = 4 * ‖f.toSelfAdjoint ^ n‖ * ‖x‖ := by simp; ring

/-- A positive map and its restriction to the self-adjoint part have the same Gelfand radius:
`‖(f|ₛₐ)ⁿ‖ ≤ ‖fⁿ‖ ≤ 4 ‖(f|ₛₐ)ⁿ‖`. -/
theorem gelfandRadius_toSelfAdjoint :
    gelfandRadius f.toSelfAdjoint =
      gelfandRadius (ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f)) :=
  le_antisymm (gelfandRadius_le_of_norm_pow_le (C := 1) fun n ↦
      (f.norm_toSelfAdjoint_pow_le n).trans_eq (one_mul _).symm)
    (gelfandRadius_le_of_norm_pow_le (f.norm_pow_le_four_mul_norm_toSelfAdjoint_pow))

/-- The spectral radius of a positive map is the Gelfand radius of its restriction to the
self-adjoint part. -/
theorem spectralRadius_eq_gelfandRadius_toSelfAdjoint :
    spectralRadius ℂ (ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f)) =
      ENNReal.ofReal (gelfandRadius f.toSelfAdjoint) := by
  rw [spectrum.spectralRadius_eq_gelfandRadius, gelfandRadius_toSelfAdjoint]

variable [Nontrivial A] [FiniteDimensional ℂ A]

/-- **Perron–Frobenius for positive maps** (Evans–Høegh-Krohn): on a finite-dimensional
C⋆-algebra, the Gelfand radius `r` of the restriction of a positive map `f` to the self-adjoint
part, which is the spectral radius of `f` (`spectralRadius_eq_gelfandRadius_toSelfAdjoint`), is an
eigenvalue of `f` with a positive eigenvector. -/
theorem exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul :
    ∃ a : A, 0 ≤ a ∧ a ≠ 0 ∧ f a = gelfandRadius f.toSelfAdjoint • a := by
  obtain ⟨a, ha, ha0, hTa⟩ := selfAdjoint.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul
    (T := f.toSelfAdjoint) fun a ha ↦ f.toSelfAdjoint_nonneg ha
  exact ⟨a, Subtype.coe_le_coe.2 ha, fun h ↦ ha0 (Subtype.ext h), congrArg Subtype.val hTa⟩

/-- **Perron–Frobenius for positive maps**, spectral form (Evans–Høegh-Krohn): on a
finite-dimensional C⋆-algebra, the spectral radius of a positive map `f` is an eigenvalue of `f`
with a positive eigenvector. Completely positive maps, and so quantum channels on `Matrix n n ℂ`,
are positive maps (`PositiveLinearMap.ofClass`). -/
theorem exists_nonneg_ne_zero_apply_eq_spectralRadius_smul :
    ∃ a : A, 0 ≤ a ∧ a ≠ 0 ∧ f a = (spectralRadius ℂ
      (ContinuousLinearMap.mk (f : A →ₗ[ℂ] A) (map_continuous f))).toReal • a := by
  rw [spectralRadius_eq_gelfandRadius_toSelfAdjoint,
    ENNReal.toReal_ofReal (gelfandRadius_nonneg _)]
  exact f.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul

/-- **Perron–Frobenius for positivity improving maps**: on a finite-dimensional C⋆-algebra, if a
positive map `f` sends nonzero positive elements to strictly positive ones, then
`r = gelfandRadius f.toSelfAdjoint` (the spectral radius of `f`) is positive, with an eigenvector
`a₀` interior to the positive cone, an eigenfunctional `ℓ` of the transpose positive on nonzero
positive elements with `ℓ a₀ = 1`, and a spectral gap. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_isStrictlyPositive
    (hf : ∀ a : A, 0 ≤ a → a ≠ 0 → IsStrictlyPositive (f a)) :
    0 < gelfandRadius f.toSelfAdjoint ∧ ∃ a₀ ∈ interior (Ici (0 : selfAdjoint A)),
      ∃ ℓ : StrongDual ℝ (selfAdjoint A), f a₀ = gelfandRadius f.toSelfAdjoint • (a₀ : A) ∧
      ℓ.comp f.toSelfAdjoint = gelfandRadius f.toSelfAdjoint • ℓ ∧ ℓ a₀ = 1 ∧
      (∀ a, 0 ≤ a → a ≠ 0 → 0 < ℓ a) ∧
      gelfandRadius (f.toSelfAdjoint - gelfandRadius f.toSelfAdjoint • ℓ.smulRight a₀) <
        gelfandRadius f.toSelfAdjoint := by
  obtain ⟨hr, a₀, ha₀, ℓ, hTa₀, h⟩ :=
    selfAdjoint.exists_gelfandRadius_sub_smul_smulRight_lt_of_apply_mem_interior
      (T := f.toSelfAdjoint) fun a ha ha0 ↦ selfAdjoint.mem_interior_Ici_zero
        (hf a (Subtype.coe_le_coe.2 ha) fun h ↦ ha0 (Subtype.ext h))
  exact ⟨hr, a₀, ha₀, ℓ, congrArg Subtype.val hTa₀, h⟩

end PositiveLinearMap
