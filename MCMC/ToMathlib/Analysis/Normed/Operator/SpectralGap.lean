/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Eigenspace.Basic
import MCMC.ToMathlib.Analysis.Normed.Algebra.Resolvent
import MCMC.ToMathlib.Analysis.Normed.Module.TaylorComplexification

/-!
# Rank-one spectral gap

Let `T` be an operator on a real Banach space with an eigenvector `x₀` and a transpose
eigenfunctional `ℓ` for the same `r`, normalized by `ℓ x₀ = 1`, and let `P = ℓ.smulRight x₀`, the
projection `y ↦ ℓ y • x₀`. If `gelfandRadius (T - r • P) < r` (a *spectral gap*), then

* `r` is an algebraically simple eigenvalue: `maxGenEigenspace T r = ℝ ∙ x₀`;
* `(r⁻¹ • T) ^ n → P` in operator norm.

These are the conclusions of Perron–Frobenius and Krein–Rutman for strongly positive and primitive
operators, and the convergence theorem for primitive Markov chains (`r = 1`, `x₀ = 1`, `ℓ` the
stationary law).

## Main statements

* `ContinuousLinearMap.maxGenEigenspace_eq_span_of_gelfandRadius_sub_lt`
* `tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_lt` (any normed `ℝ`-algebra, idempotent `P`) and
  `ContinuousLinearMap.tendsto_inv_smul_pow_of_gelfandRadius_sub_lt`
* `ContinuousLinearMap.eq_smul_of_comp_eq_smul_of_gelfandRadius_sub_lt`: the transpose
  eigenfunctional for `r` is unique up to scaling.
* `ContinuousLinearMap.sub_smul_smulRight_pow_succ`:
  `(T - r P) ^ (k + 1) = T ^ (k + 1) - r ^ (k + 1) P`.
* `spectrum_subset_insert_spectrum_sub_smul` (any algebra over a field) and
  `ContinuousLinearMap.norm_lt_of_mem_spectrum_complexify_of_gelfandRadius_sub_lt`: every complex
  spectral value `μ ≠ r` has `‖μ‖ < r` (Bourbaki TS III §6 Prop. 8 c)).
* `ContinuousLinearMap.smul_mem_of_isClosed_of_mem_invtSubmodule`: `P` preserves closed
  `T`-invariant subspaces (Prop. 8 d); it fails for non-closed ones, e.g. the polynomial span of
  an orbit under a diagonal compact operator with infinitely many eigenvalues).

Staged for `Mathlib/Analysis/Normed/Operator/SpectralGap.lean`. Searched on 2026-10-17: no
spectral-gap or rank-one Perron projection statement in the pinned tree or on mathlib master.
-/

open Filter Topology

section Ring

variable {A : Type*}

/-- Powers of `P + U` for an idempotent `P` annihilating `U` on both sides. -/
theorem add_pow_succ_of_mul_eq_zero [Semiring A] {P U : A} (hP : P * P = P) (hPU : P * U = 0)
    (hUP : U * P = 0) (n : ℕ) : (P + U) ^ (n + 1) = P + U ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, hP, hPU, add_zero, pow_succ U n,
      mul_assoc (U ^ n) U P, hUP, mul_zero, zero_add, ← pow_succ, ← pow_succ]

/-- **Convergence to the Perron projection**, in a normed algebra: if `P` is idempotent,
`T * P = P * T = r • P` and `gelfandRadius (T - r • P) < r`, then `(r⁻¹ • T) ^ n → P`. -/
theorem tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_lt [NormedRing A] [NormedAlgebra ℝ A]
    {T P : A} {r : ℝ} (hP : P * P = P) (hTP : T * P = r • P) (hPT : P * T = r • P)
    (hgap : gelfandRadius (T - r • P) < r) :
    Tendsto (fun n ↦ (r⁻¹ • T) ^ n) atTop (𝓝 P) := by
  have hr : 0 < r := (gelfandRadius_nonneg _).trans_lt hgap
  set U := r⁻¹ • (T - r • P)
  have hU : gelfandRadius U < 1 := by
    rwa [gelfandRadius_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_lt_one₀ hr]
  have hTPU : r⁻¹ • T = P + U := by simp [U, smul_sub, smul_smul, inv_mul_cancel₀ hr.ne']
  have hPU : P * U = 0 := by simp [U, mul_sub, hPT, hP]
  have hUP : U * P = 0 := by simp [U, sub_mul, hTP, hP]
  have hlim : Tendsto (fun n ↦ P + U ^ (n + 1)) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add ((tendsto_add_atTop_iff_nat 1).2
      (gelfandRadius_lt_one_iff_tendsto_pow_atTop_nhds_zero.1 hU))
  refine (tendsto_add_atTop_iff_nat 1).1 (hlim.congr fun n ↦ ?_)
  rw [hTPU, add_pow_succ_of_mul_eq_zero hP hPU hUP]

/-- **Spectrum under a rank-one spectral projection**: if `P` is idempotent and
`T * P = P * T = r • P`, every spectral value of `T` other than `r` is a spectral value of
`T - r • P`. For `z ∉ insert r (spectrum 𝕜 (T - r • P))`, the inverse of `z - T` is
`(z - (T - r • P))⁻¹ * (1 - P) + (z - r)⁻¹ • P`. -/
theorem spectrum_subset_insert_spectrum_sub_smul {𝕜 : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {T P : A} {r : 𝕜} (hP : P * P = P) (hTP : T * P = r • P) (hPT : P * T = r • P) :
    spectrum 𝕜 T ⊆ insert r (spectrum 𝕜 (T - r • P)) := by
  intro z hz
  rw [Set.mem_insert_iff, or_iff_not_imp_left]
  intro hzr hzS
  obtain ⟨u, hu⟩ := spectrum.mem_resolventSet_iff.1 hzS
  have huP : (u : A) * P = z • P := by
    rw [hu, sub_mul, sub_mul, hTP, smul_mul_assoc, hP, sub_self, sub_zero,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hPu : P * u = z • P := by
    rw [hu, mul_sub, mul_sub, hPT, mul_smul_comm, hP, sub_self, sub_zero,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hcu : Commute (u : A) P := huP.trans hPu.symm
  have hc : Commute (↑u⁻¹ : A) P := hcu.units_inv_left
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP1' : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hzr' : z - r ≠ 0 := sub_ne_zero.2 hzr
  have hzT : algebraMap 𝕜 A z - T = u - r • P := by rw [hu]; abel
  have hcoef : (z - r)⁻¹ • z • P - (z - r)⁻¹ • r • P = P := by
    rw [smul_smul, smul_smul, ← sub_smul, ← mul_sub, inv_mul_cancel₀ hzr', one_smul]
  refine spectrum.mem_iff.1 hz ⟨⟨_, ↑u⁻¹ * (1 - P) + (z - r)⁻¹ • P, ?_, ?_⟩, rfl⟩
  · rw [hzT, sub_mul, mul_add, mul_add, ← mul_assoc, u.mul_inv, one_mul, mul_smul_comm, huP,
      smul_mul_assoc, ← mul_assoc, ← hc.eq, mul_assoc, hP1, mul_zero, smul_zero, zero_add,
      mul_smul_comm, smul_mul_assoc, hP, add_sub_assoc, hcoef, sub_add_cancel]
  · rw [hzT, mul_sub, add_mul, add_mul, mul_assoc, ((Commute.one_left (u : A)).sub_left
      hcu.symm).eq, ← mul_assoc, u.inv_mul, one_mul, smul_mul_assoc, hPu, mul_smul_comm,
      mul_assoc, hP1', mul_zero, smul_zero, zero_add, smul_mul_assoc, mul_smul_comm, hP,
      add_sub_assoc, hcoef, sub_add_cancel]

end Ring

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : E →L[ℝ] E} {x₀ : E}
  {ℓ : StrongDual ℝ E} {r : ℝ}

theorem smulRight_mul_smulRight_self (hℓx₀ : ℓ x₀ = 1) :
    ℓ.smulRight x₀ * ℓ.smulRight x₀ = ℓ.smulRight x₀ := by
  ext y
  simp [hℓx₀]

theorem mul_smulRight_of_apply_eq_smul (hTx₀ : T x₀ = r • x₀) :
    T * ℓ.smulRight x₀ = r • ℓ.smulRight x₀ := by
  ext y
  simp [hTx₀, smul_smul, mul_comm]

theorem smulRight_mul_of_comp_eq_smul (hℓT : ℓ.comp T = r • ℓ) :
    ℓ.smulRight x₀ * T = r • ℓ.smulRight x₀ := by
  ext y
  simpa [smul_smul] using congr($hℓT y • x₀)

/-- **Convergence to the Perron projection**: with a spectral gap, `(r⁻¹ • T) ^ n → P`. -/
theorem tendsto_inv_smul_pow_of_gelfandRadius_sub_lt (hTx₀ : T x₀ = r • x₀)
    (hℓT : ℓ.comp T = r • ℓ) (hℓx₀ : ℓ x₀ = 1)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) :
    Tendsto (fun n ↦ (r⁻¹ • T) ^ n) atTop (𝓝 (ℓ.smulRight x₀)) :=
  tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_lt (smulRight_mul_smulRight_self hℓx₀)
    (mul_smulRight_of_apply_eq_smul hTx₀) (smulRight_mul_of_comp_eq_smul hℓT) hgap

/-- An invertible operator has trivial kernel. -/
theorem eq_zero_of_isUnit_of_apply_eq_zero {A : E →L[ℝ] E} (hA : IsUnit A) {z : E}
    (hz : A z = 0) : z = 0 := by
  obtain ⟨u, rfl⟩ := hA
  have h := congrArg (fun w ↦ ((u⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) w) hz
  rwa [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_zero] at h

theorem pow_mul_smulRight_of_apply_eq_smul (hTx₀ : T x₀ = r • x₀) (n : ℕ) :
    T ^ n * ℓ.smulRight x₀ = r ^ n • ℓ.smulRight x₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, mul_smulRight_of_apply_eq_smul hTx₀, smul_smul,
      pow_succ]

/-- `(T - r P) ^ (k + 1) = T ^ (k + 1) - r ^ (k + 1) P` when `x₀` and `ℓ` are eigenvectors of `T`
and of its transpose for `r`, with `ℓ x₀ = 1`. -/
theorem sub_smul_smulRight_pow_succ (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (k : ℕ) :
    (T - r • ℓ.smulRight x₀) ^ (k + 1) = T ^ (k + 1) - r ^ (k + 1) • ℓ.smulRight x₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ _ (k + 1), ih]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      pow_mul_smulRight_of_apply_eq_smul hTx₀, smulRight_mul_of_comp_eq_smul hℓT,
      smulRight_mul_smulRight_self hℓx₀]
    rw [← pow_succ]
    module

/-- A transpose eigenfunctional for `r` vanishing at `x₀` vanishes, given a spectral gap. -/
theorem eq_zero_of_comp_eq_smul_of_gelfandRadius_sub_lt
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {φ : StrongDual ℝ E}
    (hφT : φ.comp T = r • φ) (hφx₀ : φ x₀ = 0) : φ = 0 := by
  have hr : 0 < r := (gelfandRadius_nonneg _).trans_lt hgap
  have hφS : φ.comp (T - r • ℓ.smulRight x₀) = r • φ := by
    ext y
    simpa [hφx₀] using congr($hφT y)
  have hφSn (n : ℕ) : φ.comp ((T - r • ℓ.smulRight x₀) ^ n) = r ^ n • φ := by
    induction n with
    | zero => ext; simp
    | succ n ih => rw [pow_succ, mul_def, ← comp_assoc, ih, smul_comp, hφS, smul_smul, pow_succ]
  by_contra hφ
  refine (not_le.2 hgap) (le_gelfandRadius_of_pow_le_norm_pow hr.le fun n ↦ ?_)
  have hn := φ.opNorm_comp_le ((T - r • ℓ.smulRight x₀) ^ n)
  rw [hφSn, norm_smul, Real.norm_of_nonneg (by positivity), mul_comm] at hn
  exact le_of_mul_le_mul_left hn (norm_pos_iff.2 hφ)

/-- **Uniqueness of the transpose eigenfunctional** given a spectral gap: every `φ` with
`φ ∘ T = r • φ` is `φ x₀ • ℓ`. -/
theorem eq_smul_of_comp_eq_smul_of_gelfandRadius_sub_lt (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {φ : StrongDual ℝ E}
    (hφT : φ.comp T = r • φ) : φ = φ x₀ • ℓ :=
  sub_eq_zero.1 <| eq_zero_of_comp_eq_smul_of_gelfandRadius_sub_lt hgap
    (by rw [sub_comp, smul_comp, hφT, hℓT, smul_sub, smul_comm]) (by simp [hℓx₀])

/-- **Closed invariant subspaces** (Bourbaki TS III §6 Prop. 8 d), for closed subspaces): given a
spectral gap, the Perron projection `y ↦ ℓ y • x₀` maps every closed `T`-invariant subspace into
itself, as the limit of `(r⁻¹ • T) ^ n`. -/
theorem smul_mem_of_isClosed_of_mem_invtSubmodule (hTx₀ : T x₀ = r • x₀)
    (hℓT : ℓ.comp T = r • ℓ) (hℓx₀ : ℓ x₀ = 1)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {F : Submodule ℝ E}
    (hF : IsClosed (F : Set E)) (hTF : F ∈ Module.End.invtSubmodule (T : Module.End ℝ E))
    {y : E} (hy : y ∈ F) : ℓ y • x₀ ∈ F := by
  have hlim := ((ContinuousLinearMap.apply ℝ E y).continuous.tendsto _).comp
    (tendsto_inv_smul_pow_of_gelfandRadius_sub_lt hTx₀ hℓT hℓx₀ hgap)
  refine hF.mem_of_tendsto (by simpa using hlim) (.of_forall fun n ↦ ?_)
  have hT : Set.MapsTo T F F := hTF
  have hTn : ((T ^ n : E →L[ℝ] E) : E → E) y ∈ F := by
    simpa [FunLike.coe_pow_eq_iterate] using hT.iterate n hy
  simpa [smul_pow] using F.smul_mem ((r⁻¹) ^ n) hTn

variable [CompleteSpace E]

open TaylorComplexification in
/-- **Peripheral spectrum from a spectral gap** (Bourbaki TS III §6 Prop. 8 c)): every complex
spectral value `μ ≠ r` of `T` has `‖μ‖ < r`. -/
theorem norm_lt_of_mem_spectrum_complexify_of_gelfandRadius_sub_lt (hTx₀ : T x₀ = r • x₀)
    (hℓT : ℓ.comp T = r • ℓ) (hℓx₀ : ℓ x₀ = 1)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify T)) (hμr : μ ≠ r) : ‖μ‖ < r := by
  have hsmul (X : TaylorComplexification E →L[ℂ] TaylorComplexification E) :
      (r : ℂ) • X = r • X := Complex.coe_smul r X
  have hP : complexify (ℓ.smulRight x₀) * complexify (ℓ.smulRight x₀) =
      complexify (ℓ.smulRight x₀) := by
    rw [← complexify_mul, smulRight_mul_smulRight_self hℓx₀]
  have hTP : complexify T * complexify (ℓ.smulRight x₀) = (r : ℂ) • complexify (ℓ.smulRight x₀) :=
    by rw [← complexify_mul, mul_smulRight_of_apply_eq_smul hTx₀, complexify_smul, hsmul]
  have hPT : complexify (ℓ.smulRight x₀) * complexify T = (r : ℂ) • complexify (ℓ.smulRight x₀) :=
    by rw [← complexify_mul, smulRight_mul_of_comp_eq_smul hℓT, complexify_smul, hsmul]
  obtain h | h := spectrum_subset_insert_spectrum_sub_smul hP hTP hPT hμ
  · exact absurd h hμr
  · rw [hsmul, ← complexify_smul, ← complexify_sub] at h
    refine lt_of_le_of_lt (not_lt.1 fun h' ↦ h (mem_resolventSet_of_gelfandRadius_lt ?_)) hgap
    rwa [gelfandRadius_complexify]

/-- **Algebraic simplicity from a spectral gap**: the generalized eigenspace of `T` for `r` is the
line `ℝ ∙ x₀`. -/
theorem maxGenEigenspace_eq_span_of_gelfandRadius_sub_lt (hTx₀ : T x₀ = r • x₀)
    (hℓT : ℓ.comp T = r • ℓ) (hℓx₀ : ℓ x₀ = 1)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) :
    Module.End.maxGenEigenspace (T : Module.End ℝ E) r = ℝ ∙ x₀ := by
  have hr : 0 < r := (gelfandRadius_nonneg _).trans_lt hgap
  set S := T - r • ℓ.smulRight x₀
  set D := T - r • (1 : E →L[ℝ] E)
  have hℓD (w : E) : ℓ (D w) = 0 := by simpa [D, sub_eq_zero] using congr($hℓT w)
  have hSD (w : E) (hw : ℓ w = 0) : (S - r • 1) w = D w := by simp [S, D, hw]
  have hpow (y : E) (hy : ℓ y = 0) (m : ℕ) : ((S - r • 1) ^ m) y = (D ^ m) y := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, hSD _ ?_, pow_succ', mul_apply_eq_comp]
      cases m with
      | zero => simpa using hy
      | succ m => rw [pow_succ', mul_apply_eq_comp, hℓD]
  have hunit : IsUnit (algebraMap ℝ (E →L[ℝ] E) r - S) :=
    mem_resolventSet_of_gelfandRadius_lt (by rwa [Real.norm_of_nonneg hr.le])
  have hD : ((D : E →L[ℝ] E) : Module.End ℝ E) = (T : Module.End ℝ E) - r • 1 := by
    ext
    simp [D]
  have hDx₀ : D x₀ = 0 := by simp [D, hTx₀]
  refine le_antisymm (fun y hy ↦ ?_) ?_
  · obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hy
    rw [← hD, ← toLinearMap_pow] at hk
    have hz : ((S - r • 1) ^ (k + 1)) (y - ℓ y • x₀) = 0 := by
      rw [hpow _ (by simp [hℓx₀]) (k + 1), map_sub, map_smul, pow_succ, mul_apply_eq_comp,
        mul_apply_eq_comp, hDx₀, map_zero, smul_zero, sub_zero, ← mul_apply_eq_comp, ← pow_succ,
        pow_succ', mul_apply_eq_comp]
      exact congr(D $hk).trans (map_zero D)
    have hz' : ((algebraMap ℝ (E →L[ℝ] E) r - S) ^ (k + 1)) (y - ℓ y • x₀) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, ← neg_sub, neg_pow, mul_apply_eq_comp, hz, map_zero]
    have hy0 : y - ℓ y • x₀ = 0 := eq_zero_of_isUnit_of_apply_eq_zero (hunit.pow (k + 1)) hz'
    exact Submodule.mem_span_singleton.2 ⟨ℓ y, (sub_eq_zero.1 hy0).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hTx₀)

end ContinuousLinearMap
