/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Topology.Instances.Matrix
import MCMC.ToMathlib.Analysis.Matrix.PerronFrobenius

/-!
# Convergence of primitive stochastic matrices

A row-stochastic matrix `P` has Gelfand radius `1` (`‖P‖ = 1` for the `ℓ∞` operator norm and
`P *ᵥ 1 = 1`). If `P` is moreover primitive, the Perron–Frobenius spectral gap
(`Matrix.IsPrimitive.exists_gelfandRadius_sub_smul_vecMulVec_lt`) gives the convergence theorem for
finite Markov chains: there is a unique positive stationary law `π` and `P ^ m → 1 πᵀ`, i.e. every
row of `P ^ m` tends to `π`. The limit is identified without an eigenvector-uniqueness argument:
`P ^ m *ᵥ 1 = 1` passes to the limit `vecMulVec v w`, which forces `v` to be a multiple of `1`.

## Main statements

* `Matrix.gelfandRadius_eq_one_of_mem_rowStochastic`
* `Matrix.eq_of_vecMul_eq_of_tendsto_pow`: the limit determines the stationary law.
* `Matrix.IsPrimitive.exists_tendsto_pow_of_mem_rowStochastic`

Staged for `Mathlib/Analysis/Matrix/Stochastic.lean` (open PR #42626 creates that file with the
operator norm and spectral radius bounds). Searched on 2026-10-17: mathlib has no convergence
theorem for stochastic matrices; open PR #34713 proves existence of a stationary distribution.
-/

open Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}

section Norm

open scoped Matrix.Norms.Operator

/-- A row-stochastic matrix has `ℓ∞` operator norm at most `1`. -/
theorem linfty_opNorm_le_one_of_mem_rowStochastic (hP : P ∈ rowStochastic ℝ n) : ‖P‖ ≤ 1 := by
  rw [linfty_opNorm_def, NNReal.coe_le_one]
  refine Finset.sup_le fun i _ ↦ ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one, ← sum_row_of_mem_rowStochastic hP i]
  exact (Finset.sum_congr rfl fun j _ ↦ by
    rw [coe_nnnorm, Real.norm_of_nonneg (nonneg_of_mem_rowStochastic hP)]).le

/-- A row-stochastic matrix has Gelfand radius `1`. -/
theorem gelfandRadius_eq_one_of_mem_rowStochastic [Nonempty n] (hP : P ∈ rowStochastic ℝ n) :
    gelfandRadius P = 1 := by
  refine le_antisymm ((gelfandRadius_le_norm P).trans
    (linfty_opNorm_le_one_of_mem_rowStochastic hP)) ?_
  refine le_gelfandRadius_of_pow_le_norm_pow zero_le_one fun k ↦ ?_
  have h := linfty_opNorm_mulVec (P ^ k) 1
  rw [one_vecMul_of_mem_rowStochastic (pow_mem hP k)] at h
  simpa using h

end Norm

/-- A vector fixed by `P` is fixed by its powers. -/
theorem vecMul_pow_eq_self {π : n → ℝ} (hπ : π ᵥ* P = π) (m : ℕ) : π ᵥ* (P ^ m) = π := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← vecMul_vecMul, ih, hπ]

/-- If `P ^ m → vecMulVec 1 π`, every `π'` with `π' ᵥ* P = π'` and total mass `1` is `π`. -/
theorem eq_of_vecMul_eq_of_tendsto_pow {π π' : n → ℝ}
    (hlim : Tendsto (fun m ↦ P ^ m) atTop (𝓝 (vecMulVec 1 π))) (hπ' : π' ᵥ* P = π')
    (hπ'1 : ∑ i, π' i = 1) : π' = π := by
  have h := tendsto_nhds_unique (((continuous_const.matrix_vecMul continuous_id).tendsto _).comp
    hlim) (tendsto_const_nhds.congr fun m ↦ (vecMul_pow_eq_self hπ' m).symm)
  rw [id, vecMul_vecMulVec, dotProduct_one, hπ'1, one_smul] at h
  exact h.symm

/-- **Convergence theorem for primitive stochastic matrices**: a primitive row-stochastic matrix
has a positive stationary law `π`, it is the only `π'` with `π' ᵥ* P = π'` and `∑ π' = 1`, and
`P ^ m → vecMulVec 1 π`: every row of `P ^ m` tends to `π`. -/
theorem IsPrimitive.exists_tendsto_pow_of_mem_rowStochastic [Nonempty n]
    (hP : P ∈ rowStochastic ℝ n) (hprim : P.IsPrimitive) :
    ∃ π : n → ℝ, (∀ i, 0 < π i) ∧ ∑ i, π i = 1 ∧ π ᵥ* P = π ∧
      (∀ π' : n → ℝ, π' ᵥ* P = π' → ∑ i, π' i = 1 → π' = π) ∧
      Tendsto (fun m ↦ P ^ m) atTop (𝓝 (vecMulVec 1 π)) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨-, v, w, -, hw, hPv, hwP, hwv, hgap⟩ := hprim.exists_gelfandRadius_sub_smul_vecMulVec_lt
  open scoped Matrix.Norms.Operator in
  rw [gelfandRadius_eq_one_of_mem_rowStochastic hP] at hPv hwP hgap
  have hlim : Tendsto (fun m ↦ P ^ m) atTop (𝓝 (vecMulVec v w)) := by
    simpa using tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_vecMulVec_lt hPv hwP hwv hgap
  have h1 : vecMulVec v w *ᵥ 1 = 1 :=
    tendsto_nhds_unique (((continuous_id.matrix_mulVec continuous_const).tendsto _).comp hlim)
      (tendsto_const_nhds.congr fun m ↦ (one_vecMul_of_mem_rowStochastic (pow_mem hP m)).symm)
  have hs : 0 < ∑ i, w i := Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty
  have hv' : v = (∑ i, w i)⁻¹ • 1 := by
    rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_one] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hv', smul_vecMulVec, ← vecMulVec_smul] at hlim
  refine ⟨(∑ i, w i)⁻¹ • w, fun i ↦ by simpa using mul_pos (inv_pos.2 hs) (hw i), ?_, ?_,
    fun π' hπ' hπ'1 ↦ eq_of_vecMul_eq_of_tendsto_pow hlim hπ' hπ'1, hlim⟩
  · simp [← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
  · simp [smul_vecMul, hwP]

end Matrix
