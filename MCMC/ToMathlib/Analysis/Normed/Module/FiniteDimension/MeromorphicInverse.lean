/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Meromorphic inverses of analytic families of operators in finite dimension

Let `N` be a finite-dimensional normed space over a complete nontrivially normed field `𝕜` and
let `M : 𝕜 → N →L[𝕜] N` be analytic at `x`. In a basis, the entries of `M z` are analytic, so are
its determinant `d z` and the entries of its adjugate (polynomials in the entries); Cramer's rule
gives an analytic `B` with `Ring.inverse (M z) = (d z)⁻¹ • B z` for every `z` (both sides vanish
when `d z = 0`, as `0⁻¹ = 0`). Hence `z ↦ Ring.inverse (M z)` is meromorphic at `x`. By the
isolated zeros of `d`, either `M z` is a unit for all `z ≠ x` near `x`, or for no `z` near `x`.

## Main statements

* `AnalyticAt.matrix_det`, `AnalyticAt.matrix_adjugate`: determinant and adjugate of an
  entrywise analytic family of matrices.
* `AnalyticAt.toMatrix_apply`, `ContinuousLinearMap.analyticAt_det`: matrix entries and
  determinant of an analytic family of operators.
* `ContinuousLinearMap.isUnit_iff_isUnit_det`: in finite dimension, an operator is invertible iff
  its determinant is.
* `AnalyticAt.exists_ringInverse_eq_inv_det_smul`: Cramer's rule with an analytic adjugate.
* `AnalyticAt.meromorphicAt_ringInverse`: the inverse of an analytic family is meromorphic.
* `AnalyticAt.frequently_isUnit_iff_eventually_isUnit`: an analytic family is invertible on a
  punctured neighbourhood as soon as it is invertible at points accumulating at `x`.

Staged for a new file `Mathlib/Analysis/Normed/Module/FiniteDimension/MeromorphicInverse.lean`.
Searched on 2026-10-17: the pinned tree (`v4.34.1`) has `Continuous.matrix_det`,
`ContinuousLinearMap.continuous_det` and `analyticAt_inverse` (inversion is analytic at a unit of
a Banach algebra), but no analyticity of `Matrix.det`, `Matrix.adjugate` or
`ContinuousLinearMap.det` (`grep -rn "AnalyticAt" Mathlib | grep -i "det\|adjugate"` is empty)
and no meromorphic inverse; on mathlib master, `gh api` on `Analysis/Analytic/Constructions.lean`
and `Analysis/Normed/Module/FiniteDimension.lean` finds only `Continuous.matrix_det`, and
`gh pr list -R leanprover-community/mathlib4 --search "analytic determinant"`,
`--search "meromorphic inverse"` return no related PR.
-/

open Filter Topology

section Matrix

variable {𝕜 E A ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing A] [NormedAlgebra 𝕜 A] [Fintype ι] [DecidableEq ι] {f : E → Matrix ι ι A}
  {x : E}

/-- The determinant of an entrywise analytic family of matrices is analytic. -/
theorem AnalyticAt.matrix_det (hf : ∀ i j, AnalyticAt 𝕜 (fun z ↦ f z i j) x) :
    AnalyticAt 𝕜 (fun z ↦ (f z).det) x := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  fun_prop

/-- The adjugate of an entrywise analytic family of matrices is entrywise analytic. -/
theorem AnalyticAt.matrix_adjugate (hf : ∀ i j, AnalyticAt 𝕜 (fun z ↦ f z i j) x) (i j : ι) :
    AnalyticAt 𝕜 (fun z ↦ (f z).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  refine AnalyticAt.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact hf k l

end Matrix

section FiniteDimensional

variable {𝕜 E N ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup N] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
  [Fintype ι] [DecidableEq ι]

/-- The matrix entries of an analytic family of operators on a finite-dimensional space are
analytic. -/
theorem AnalyticAt.toMatrix_apply (b : Module.Basis ι 𝕜 N) {M : E → N →L[𝕜] N} {x : E}
    (hM : AnalyticAt 𝕜 M x) (i j : ι) :
    AnalyticAt 𝕜 (fun z ↦ LinearMap.toMatrix b b (M z) i j) x := by
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, ← b.coord_apply,
    ← LinearMap.coe_toContinuousLinearMap' (b.coord i)]
  exact ((LinearMap.toContinuousLinearMap (b.coord i)).analyticAt _).comp
    (((ContinuousLinearMap.apply 𝕜 N (b j)).analyticAt _).comp hM)

/-- The determinant of operators on a finite-dimensional space is analytic. -/
theorem ContinuousLinearMap.analyticAt_det (f : N →L[𝕜] N) :
    AnalyticAt 𝕜 (fun g : N →L[𝕜] N ↦ g.det) f := by
  simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.finBasis 𝕜 N)]
  exact AnalyticAt.matrix_det (AnalyticAt.toMatrix_apply _ analyticAt_id)

/-- In finite dimension, an operator is invertible iff its determinant is a unit. -/
theorem ContinuousLinearMap.isUnit_iff_isUnit_det (f : N →L[𝕜] N) : IsUnit f ↔ IsUnit f.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.isUnit_iff_isUnit_det]
  refine ⟨fun h ↦ h.map ContinuousLinearMap.toLinearMapRingHom, fun ⟨u, hu⟩ ↦ ?_⟩
  refine ⟨⟨f, LinearMap.toContinuousLinearMap ↑u⁻¹, ?_, ?_⟩, rfl⟩ <;> ext v
  · simpa [hu] using LinearMap.congr_fun u.mul_inv v
  · simpa [hu] using LinearMap.congr_fun u.inv_mul v

/-- **Analytic adjugate**: an analytic family `M` of operators on a finite-dimensional space has an
analytic adjugate `B`: `M z * B z = (M z).det • 1 = B z * M z` for all `z`. -/
theorem AnalyticAt.exists_mul_eq_det_smul_one {M : E → N →L[𝕜] N} {x : E}
    (hM : AnalyticAt 𝕜 M x) :
    ∃ B : E → N →L[𝕜] N, AnalyticAt 𝕜 B x ∧
      ∀ z, M z * B z = (M z).det • 1 ∧ B z * M z = (M z).det • 1 := by
  let b := Module.finBasis 𝕜 N
  let Φ : Matrix (Fin (Module.finrank 𝕜 N)) (Fin (Module.finrank 𝕜 N)) 𝕜 ≃ₗ[𝕜] N →L[𝕜] N :=
    (Matrix.toLin b b).trans LinearMap.toContinuousLinearMap
  have hΦ (C : Matrix (Fin (Module.finrank 𝕜 N)) (Fin (Module.finrank 𝕜 N)) 𝕜) :
      LinearMap.toMatrix b b (Φ C) = C :=
    Φ.symm_apply_apply C
  have hsum (C : Matrix (Fin (Module.finrank 𝕜 N)) (Fin (Module.finrank 𝕜 N)) 𝕜) :
      ∑ i, ∑ j, C i j • Φ (Matrix.single i j 1) = Φ C := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single C]
    simp only [map_sum, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  refine ⟨fun z ↦ Φ (LinearMap.toMatrix b b (M z)).adjugate, ?_, fun z ↦ ⟨?_, ?_⟩⟩
  · refine AnalyticAt.congr ?_ (Eventually.of_forall fun z ↦ hsum _)
    exact Finset.analyticAt_fun_sum _ fun i _ ↦ Finset.analyticAt_fun_sum _ fun j _ ↦
      (AnalyticAt.matrix_adjugate (hM.toMatrix_apply b) i j).smul analyticAt_const
  all_goals
    refine ContinuousLinearMap.coe_injective ((LinearMap.toMatrix b b).injective ?_)
    simp only [ContinuousLinearMap.toLinearMap_mul, LinearMap.toMatrix_mul, hΦ,
      Matrix.mul_adjugate, Matrix.adjugate_mul, ContinuousLinearMap.toLinearMap_smul, map_smul,
      ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix_one, ContinuousLinearMap.det,
      LinearMap.det_toMatrix]

/-- **Cramer's rule for analytic families**: an analytic family `M` of operators on a
finite-dimensional space has an analytic `B` with `Ring.inverse (M z) = (M z).det⁻¹ • B z` for
all `z`. -/
theorem AnalyticAt.exists_ringInverse_eq_inv_det_smul {M : E → N →L[𝕜] N} {x : E}
    (hM : AnalyticAt 𝕜 M x) :
    ∃ B : E → N →L[𝕜] N, AnalyticAt 𝕜 B x ∧ ∀ z, Ring.inverse (M z) = (M z).det⁻¹ • B z := by
  obtain ⟨B, hB, hMB⟩ := hM.exists_mul_eq_det_smul_one
  refine ⟨B, hB, fun z ↦ ?_⟩
  by_cases hd : (M z).det = 0
  · rw [Ring.inverse_non_unit _ (by simp [ContinuousLinearMap.isUnit_iff_isUnit_det, hd]), hd,
      inv_zero, zero_smul]
  · obtain ⟨h₁, h₂⟩ := hMB z
    have hu : M z * ((M z).det⁻¹ • B z) = 1 := by
      rw [mul_smul_comm, h₁, smul_smul, inv_mul_cancel₀ hd, one_smul]
    have hu' : ((M z).det⁻¹ • B z) * M z = 1 := by
      rw [smul_mul_assoc, h₂, smul_smul, inv_mul_cancel₀ hd, one_smul]
    exact Ring.inverse_unit ⟨M z, _, hu, hu'⟩

/-- **Meromorphic inverse**: the inverse of an analytic family of operators on a
finite-dimensional space is meromorphic. -/
theorem AnalyticAt.meromorphicAt_ringInverse {M : 𝕜 → N →L[𝕜] N} {x : 𝕜}
    (hM : AnalyticAt 𝕜 M x) : MeromorphicAt (fun z ↦ Ring.inverse (M z)) x := by
  obtain ⟨B, hB, hMB⟩ := hM.exists_ringInverse_eq_inv_det_smul
  have hd : AnalyticAt 𝕜 (fun z ↦ (M z).det) x :=
    (ContinuousLinearMap.analyticAt_det (M x)).comp hM
  simp only [hMB]
  exact hd.meromorphicAt.inv.smul hB.meromorphicAt

/-- **Invertibility dichotomy**: an analytic family of operators on a finite-dimensional space
that is invertible at points accumulating at `x` is invertible at every `z ≠ x` near `x`. -/
theorem AnalyticAt.frequently_isUnit_iff_eventually_isUnit {M : 𝕜 → N →L[𝕜] N} {x : 𝕜}
    (hM : AnalyticAt 𝕜 M x) :
    (∃ᶠ z in 𝓝[≠] x, IsUnit (M z)) ↔ ∀ᶠ z in 𝓝[≠] x, IsUnit (M z) := by
  refine ⟨fun h ↦ ?_, Eventually.frequently⟩
  have hd : AnalyticAt 𝕜 (fun z ↦ (M z).det) x :=
    (ContinuousLinearMap.analyticAt_det (M x)).comp hM
  simp only [ContinuousLinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h ⊢
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with h₀ | h₀
  · exact ((h.and_eventually (nhdsWithin_le_nhds h₀)).exists.elim fun z hz ↦
      (hz.1 hz.2).elim)
  · exact h₀

end FiniteDimensional
