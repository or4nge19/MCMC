/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Normed.Module.FiniteDimension.MeromorphicInverse
import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.RieszSchauder

/-!
# The analytic Fredholm theorem

Let `F : 𝕜 → X →L[𝕜] X` be analytic at `x` on a Banach space `X` over a complete nontrivially
normed field, with `F x` compact. Then `z ↦ Ring.inverse (1 - F z)` is meromorphic at `x`, and
either `1 - F z` is invertible for every `z ≠ x` near `x`, or for no `z ≠ x` near `x`.

Proof. The Riesz projection `P` of the compact operator `F x` at the eigenvalue `1` has
finite-dimensional range `N`, and `U = (F x - 1) * (1 - P) + P` is invertible. So
`G z = (F z - 1) * (1 - P) + P` is analytic and invertible near `x`, and
`1 - F z = -G z * (1 - H z)` with `H z = -(G z)⁻¹ * (F z - 2) * P` of rank `≤ dim N`. Writing
`P = ι ∘ π` through `N`, `H z = A z ∘ π` with `A` analytic. By Jacobson's lemma `1 - A z ∘ π` is
invertible iff `1 - π ∘ A z` is, with `(1 - A z ∘ π)⁻¹ = 1 + A z ∘ (1 - π ∘ A z)⁻¹ ∘ π`, and
`z ↦ 1 - π ∘ A z` is an analytic family of operators on the finite-dimensional `N`, whose inverse
is meromorphic by Cramer's rule (`AnalyticAt.meromorphicAt_ringInverse`).

## Main statements

* `MeromorphicAt.clm_comp`: composition of meromorphic families of operators.
* `ContinuousLinearMap.isUnit_one_sub_comp_comm`, `ContinuousLinearMap.ringInverse_one_sub_comp`:
  Jacobson's lemma for operators `A : N →L X`, `B : X →L N`.
* `AnalyticAt.meromorphicAt_ringInverse_one_sub_comp`,
  `AnalyticAt.frequently_isUnit_one_sub_comp_iff`: the analytic Fredholm theorem for analytic
  families `A z ∘L B` of finite rank.
* `AnalyticAt.meromorphicAt_ringInverse_one_sub`, `AnalyticAt.frequently_isUnit_one_sub_iff`:
  the **analytic Fredholm theorem**, local form.

Staged for a new file `Mathlib/Analysis/Normed/Operator/Compact/AnalyticFredholm.lean`
(`MeromorphicAt.clm_comp` for `Mathlib/Analysis/Meromorphic/Basic.lean`, Jacobson's lemma for
`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`). Searched on 2026-10-17: the
pinned tree (`v4.34.1`) has the Fredholm alternative
(`Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean`) and Fredholm operators
(`Mathlib/Analysis/Normed/Operator/Fredholm/`), but no analytic Fredholm theorem, no meromorphic
operator-valued compositions (`grep -rn "MeromorphicAt" Mathlib` lists only
`Analysis/Meromorphic`, `Analysis/Complex`, `SpecialFunctions`) and no Jacobson lemma
(`grep -rn "one_sub_mul_comm\|isUnit_one_sub_mul"` is empty; only
`Matrix.det_one_sub_mul_comm`). On mathlib master (`gh api` on the `Mathlib/Analysis` tree) the
only Fredholm files are `FredholmAlternative.lean` and `Fredholm/{Basic,Open}.lean`;
`gh pr list -R leanprover-community/mathlib4 --search "Fredholm"` finds the open #39274 (WIP
Fredholm operators) and #41858 (properness of upper semi-Fredholm operators), the closed #43906
and the merged #42689 (Fredholm projections), none with a parameter;
`--search "analytic Fredholm"`, `"Jacobson lemma"` return nothing related.
AxiomaticX QuantumlibCore (`MathlibPRnew.md`) plans an analytic Fredholm theorem for resolvents
after mathlib's Fredholm-operator PR #39274; this file is that statement for analytic families
with compact value at the point.
-/

open Filter Topology

section Meromorphic

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {x : 𝕜}

/-- The composition of two meromorphic families of continuous linear maps is meromorphic. -/
theorem MeromorphicAt.clm_comp {f : 𝕜 → F →L[𝕜] G} {g : 𝕜 → E →L[𝕜] F}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ (f z).comp (g z)) x := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  convert ((ContinuousLinearMap.compL 𝕜 E F G).analyticAt_bilinear _).comp₂ hm hn using 2 with z
  simp [pow_add, mul_smul, smul_comm ((z - x) ^ m) ((z - x) ^ n)]

end Meromorphic

namespace ContinuousLinearMap

section Jacobson

variable {R X N : Type*} [Ring R] [TopologicalSpace X] [AddCommGroup X] [Module R X]
  [IsTopologicalAddGroup X] [TopologicalSpace N] [AddCommGroup N] [Module R N]
  [IsTopologicalAddGroup N] {A : N →L[R] X} {B : X →L[R] N} {W : N →L[R] N}

/-- A right inverse `W` of `1 - B ∘L A` gives the right inverse `1 + A ∘L W ∘L B` of
`1 - A ∘L B`. -/
theorem one_sub_comp_mul_one_add_comp (hW : (1 - B ∘L A) * W = 1) :
    (1 - A ∘L B) * (1 + A ∘L W ∘L B) = 1 := by
  ext x
  have h := DFunLike.congr_fun hW (B x)
  simp only [mul_apply_eq_comp, coe_comp, Function.comp_apply, sub_apply, one_apply_eq_self,
    add_apply] at h ⊢
  rw [map_add, ← sub_eq_iff_eq_add.mp h, add_sub_cancel_right]

/-- A left inverse `W` of `1 - B ∘L A` gives the left inverse `1 + A ∘L W ∘L B` of
`1 - A ∘L B`. -/
theorem one_add_comp_mul_one_sub_comp (hW : W * (1 - B ∘L A) = 1) :
    (1 + A ∘L W ∘L B) * (1 - A ∘L B) = 1 := by
  ext x
  have h := DFunLike.congr_fun hW (B x)
  simp only [mul_apply_eq_comp, coe_comp, Function.comp_apply, sub_apply, one_apply_eq_self,
    add_apply] at h ⊢
  rw [map_sub B, h, sub_add_cancel]

/-- **Jacobson's lemma**, inverse formula: if `1 - B ∘L A` is invertible, then
`(1 - A ∘L B)⁻¹ = 1 + A ∘L (1 - B ∘L A)⁻¹ ∘L B`. -/
theorem ringInverse_one_sub_comp (h : IsUnit (1 - B ∘L A)) :
    Ring.inverse (1 - A ∘L B) = 1 + A ∘L Ring.inverse (1 - B ∘L A) ∘L B :=
  Ring.inverse_unit ⟨_, _, one_sub_comp_mul_one_add_comp (Ring.mul_inverse_cancel _ h),
    one_add_comp_mul_one_sub_comp (Ring.inverse_mul_cancel _ h)⟩

/-- If `1 - B ∘L A` is invertible, so is `1 - A ∘L B`. -/
theorem isUnit_one_sub_comp_of_isUnit (h : IsUnit (1 - B ∘L A)) : IsUnit (1 - A ∘L B) :=
  ⟨⟨_, _, one_sub_comp_mul_one_add_comp (Ring.mul_inverse_cancel _ h),
    one_add_comp_mul_one_sub_comp (Ring.inverse_mul_cancel _ h)⟩, rfl⟩

/-- **Jacobson's lemma**: `1 - A ∘L B` is invertible iff `1 - B ∘L A` is. -/
theorem isUnit_one_sub_comp_comm : IsUnit (1 - A ∘L B) ↔ IsUnit (1 - B ∘L A) :=
  ⟨isUnit_one_sub_comp_of_isUnit, isUnit_one_sub_comp_of_isUnit⟩

end Jacobson

end ContinuousLinearMap

section FiniteRank

variable {𝕜 X N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup N] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
  {A : 𝕜 → N →L[𝕜] X} {x : 𝕜}

/-- **Analytic Fredholm theorem, finite rank**, dichotomy: if `A` is analytic and `N` is
finite-dimensional, `1 - A z ∘L B` is invertible for all `z ≠ x` near `x` as soon as it is
invertible at points accumulating at `x`. -/
theorem AnalyticAt.frequently_isUnit_one_sub_comp_iff (hA : AnalyticAt 𝕜 A x) (B : X →L[𝕜] N) :
    (∃ᶠ z in 𝓝[≠] x, IsUnit (1 - A z ∘L B)) ↔ ∀ᶠ z in 𝓝[≠] x, IsUnit (1 - A z ∘L B) := by
  have hM : AnalyticAt 𝕜 (fun z ↦ 1 - B ∘L A z) x :=
    analyticAt_const.sub (((ContinuousLinearMap.compL 𝕜 N X N B).analyticAt _).comp hA)
  refine ⟨fun h ↦ ?_, Eventually.frequently⟩
  exact (hM.frequently_isUnit_iff_eventually_isUnit.mp
    (h.mono fun z hz ↦ ContinuousLinearMap.isUnit_one_sub_comp_comm.mp hz)).mono
    fun z hz ↦ ContinuousLinearMap.isUnit_one_sub_comp_comm.mpr hz

/-- **Analytic Fredholm theorem, finite rank**: if `A` is analytic and `N` is finite-dimensional,
`z ↦ (1 - A z ∘L B)⁻¹` is meromorphic. -/
theorem AnalyticAt.meromorphicAt_ringInverse_one_sub_comp (hA : AnalyticAt 𝕜 A x)
    (B : X →L[𝕜] N) : MeromorphicAt (fun z ↦ Ring.inverse (1 - A z ∘L B)) x := by
  have hM : AnalyticAt 𝕜 (fun z ↦ 1 - B ∘L A z) x :=
    analyticAt_const.sub (((ContinuousLinearMap.compL 𝕜 N X N B).analyticAt _).comp hA)
  by_cases h : ∃ᶠ z in 𝓝[≠] x, IsUnit (1 - B ∘L A z)
  · have hm : MeromorphicAt (fun z ↦ 1 + A z ∘L Ring.inverse (1 - B ∘L A z) ∘L B) x :=
      (MeromorphicAt.const 1 x).add (hA.meromorphicAt.clm_comp
        (hM.meromorphicAt_ringInverse.clm_comp (MeromorphicAt.const B x)))
    exact hm.congr ((hM.frequently_isUnit_iff_eventually_isUnit.mp h).mono
      fun z hz ↦ (ContinuousLinearMap.ringInverse_one_sub_comp hz).symm)
  · refine (MeromorphicAt.const 0 x).congr ((not_frequently.mp h).mono fun z hz ↦ ?_)
    exact (Ring.inverse_non_unit _ (mt ContinuousLinearMap.isUnit_one_sub_comp_comm.mp hz)).symm

end FiniteRank

section Compact

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X] {F : 𝕜 → X →L[𝕜] X} {x : 𝕜}

/-- **Finite-rank reduction** of an analytic compact perturbation of the identity: if `F` is
analytic at `x` and `F x` is compact, then near `x`, `1 - F z = G z * (1 - A z ∘L B)` with `G`
analytic and invertible, `A` analytic and `B` valued in a finite-dimensional subspace `N`. -/
theorem AnalyticAt.exists_eventually_one_sub_eq_mul (hF : AnalyticAt 𝕜 F x)
    (hK : IsCompactOperator (F x)) :
    ∃ N : Submodule 𝕜 X, FiniteDimensional 𝕜 N ∧ ∃ (A : 𝕜 → N →L[𝕜] X) (B : X →L[𝕜] N)
      (G : 𝕜 → X →L[𝕜] X), AnalyticAt 𝕜 A x ∧ AnalyticAt 𝕜 G x ∧
        ∀ᶠ z in 𝓝 x, IsUnit (G z) ∧ 1 - F z = G z * (1 - A z ∘L B) := by
  obtain ⟨n, -, P, -, hr, -, -, hU⟩ :=
    hK.exists_isIdempotentElem_range_eq_ker_pow (one_ne_zero (α := 𝕜))
  rw [one_smul] at hU
  have hN : FiniteDimensional 𝕜 P.range := hr ▸ hK.finiteDimensional_ker_pow one_ne_zero n
  let π : X →L[𝕜] P.range := P.codRestrict P.range (LinearMap.mem_range_self (P : X →ₗ[𝕜] X))
  have hιπ : P.range.subtypeL ∘L π = P := rfl
  let G : 𝕜 → X →L[𝕜] X := fun z ↦ -((F z - 1) * (1 - P) + P)
  have hG : AnalyticAt 𝕜 G x := by fun_prop
  have hGx : IsUnit (G x) := hU.neg
  have hGinv : AnalyticAt 𝕜 (fun z ↦ Ring.inverse (G z)) x :=
    (analyticAt_inverse (𝕜 := 𝕜) hGx.unit).comp_of_eq hG hGx.unit_spec
  refine ⟨P.range, hN, fun z ↦ (Ring.inverse (G z) * (F z - 2)) ∘L P.range.subtypeL, π, G,
    (((ContinuousLinearMap.compL 𝕜 P.range X X).flip P.range.subtypeL).analyticAt _).comp
      (hGinv.mul (hF.sub analyticAt_const)), hG, ?_⟩
  filter_upwards [hG.continuousAt.eventually_mem (Units.isOpen.mem_nhds hGx)] with z hz
  refine ⟨hz, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, hιπ, ← ContinuousLinearMap.mul_def, mul_sub, mul_one,
    ← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ hz, one_mul]
  simp only [G]
  noncomm_ring

/-- **Analytic Fredholm theorem**, meromorphy: if `F` is analytic at `x` and `F x` is compact,
then `z ↦ (1 - F z)⁻¹` is meromorphic at `x`. -/
theorem AnalyticAt.meromorphicAt_ringInverse_one_sub (hF : AnalyticAt 𝕜 F x)
    (hK : IsCompactOperator (F x)) : MeromorphicAt (fun z ↦ Ring.inverse (1 - F z)) x := by
  obtain ⟨N, hN, A, B, G, hA, hG, hev⟩ := hF.exists_eventually_one_sub_eq_mul hK
  have hGx : IsUnit (G x) := hev.self_of_nhds.1
  have hGinv : AnalyticAt 𝕜 (fun z ↦ Ring.inverse (G z)) x :=
    (analyticAt_inverse (𝕜 := 𝕜) hGx.unit).comp_of_eq hG hGx.unit_spec
  refine ((hA.meromorphicAt_ringInverse_one_sub_comp B).clm_comp hGinv.meromorphicAt).congr ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with z hz
  rw [hz.2, Ring.inverse_mul (Or.inl hz.1)]
  rfl

/-- **Analytic Fredholm theorem**, dichotomy: if `F` is analytic at `x` and `F x` is compact,
then `1 - F z` is invertible for all `z ≠ x` near `x` as soon as it is invertible at points
accumulating at `x`. -/
theorem AnalyticAt.frequently_isUnit_one_sub_iff (hF : AnalyticAt 𝕜 F x)
    (hK : IsCompactOperator (F x)) :
    (∃ᶠ z in 𝓝[≠] x, IsUnit (1 - F z)) ↔ ∀ᶠ z in 𝓝[≠] x, IsUnit (1 - F z) := by
  obtain ⟨N, hN, A, B, G, hA, -, hev⟩ := hF.exists_eventually_one_sub_eq_mul hK
  have hiff : ∀ᶠ z in 𝓝[≠] x, IsUnit (1 - F z) ↔ IsUnit (1 - A z ∘L B) :=
    (eventually_nhdsWithin_of_eventually_nhds hev).mono fun z hz ↦ hz.2 ▸ hz.1.mul_left_iff
  rw [frequently_congr hiff, eventually_congr hiff]
  exact hA.frequently_isUnit_one_sub_comp_iff B

end Compact
