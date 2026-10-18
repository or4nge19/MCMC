/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import MCMC.ToMathlib.Analysis.Matrix.GelfandRadius
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Order
import MCMC.ToMathlib.Analysis.Normed.Operator.SpectralGap

/-!
# Perron–Frobenius for nonnegative matrices

For a real square matrix `A` with the `ℓ∞` operator norm (`Matrix.Norms.Operator`), the Gelfand
radius `gelfandRadius A` is its spectral radius (`Matrix/GelfandRadius.lean`). If `A` is entrywise
nonnegative, `gelfandRadius A` is an eigenvalue of `A` with a nonnegative eigenvector (Bourbaki,
*Théories spectrales*, III §6, Théorème 5 a), also for `gelfandRadius A = 0`): Krein–Rutman for
`n → ℝ` with its lattice order
(`ContinuousLinearMap.exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul`).

## Main statements

* `Matrix.exists_nonneg_ne_zero_mulVec_eq_gelfandRadius_smul`: nonnegative matrices.
* `Matrix.IsPrimitive.exists_gelfandRadius_sub_smul_vecMulVec_lt`: primitive matrices, with
  positive right and left Perron vectors and a spectral gap.
* `Matrix.tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_vecMulVec_lt`: `(r⁻¹ A)ᵐ → v wᵀ`.
* `Matrix.norm_lt_of_mem_spectrum_of_gelfandRadius_sub_smul_vecMulVec_lt`: every other complex
  eigenvalue has modulus `< r`.

Staged for `Mathlib/Analysis/Matrix/PerronFrobenius.lean`. Searched on 2026-10-17: the open
Perron–Frobenius PR series (#39913–#39927) proves the irreducible and primitive cases through
Collatz–Wielandt; no PR states the nonnegative case or uses `gelfandRadius`.
-/

open Filter Topology
open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The interior of the positive orthant is the set of positive vectors. -/
theorem interior_positive_pi :
    interior (ProperCone.positive ℝ (n → ℝ) : Set (n → ℝ)) = {x | ∀ i, 0 < x i} := by
  have h : (ProperCone.positive ℝ (n → ℝ) : Set (n → ℝ)) = Set.pi Set.univ fun _ ↦ Set.Ici 0 := by
    ext
    simp [Pi.le_def]
  rw [h, interior_pi_set Set.finite_univ]
  ext
  simp

/-- A nonnegative matrix preserves the positive orthant. -/
theorem mapsTo_toLin'_positive {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    Set.MapsTo (LinearMap.toContinuousLinearMap (toLin' A)) (ProperCone.positive ℝ (n → ℝ))
      (ProperCone.positive ℝ (n → ℝ)) := fun x hx i ↦ by
  simpa [mulVec, dotProduct] using
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (by simpa using hx j)

/-- A positive matrix maps nonzero vectors of the positive orthant to positive vectors. -/
theorem mapsTo_toLin'_interior_positive {A : Matrix n n ℝ} (hA : ∀ i j, 0 < A i j) :
    Set.MapsTo (LinearMap.toContinuousLinearMap (toLin' A))
      ((ProperCone.positive ℝ (n → ℝ) : Set (n → ℝ)) \ {0})
      (interior (ProperCone.positive ℝ (n → ℝ))) := fun x hx ↦ by
  rw [interior_positive_pi]
  intro i
  have hx0 : 0 ≤ x := by simpa using hx.1
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx.2
  simpa [mulVec, dotProduct] using Finset.sum_pos' (fun j _ ↦ mul_nonneg (hA i j).le (hx0 j))
    ⟨j, Finset.mem_univ j, mul_pos (hA i j) ((hx0 j).lt_of_ne' hj)⟩

/-- **Perron–Frobenius for nonnegative matrices**: the Gelfand radius of an entrywise
nonnegative matrix is an eigenvalue with a nonnegative eigenvector. -/
theorem exists_nonneg_ne_zero_mulVec_eq_gelfandRadius_smul [Nonempty n] {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∃ v : n → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ A *ᵥ v = gelfandRadius A • v := by
  obtain ⟨v, hv, hv0, hAv⟩ := (LinearMap.toContinuousLinearMap (toLin' A)
    ).exists_nonneg_ne_zero_apply_eq_gelfandRadius_smul Submodule.span_Ici_zero_eq_top
    (mapsTo_toLin'_positive hA)
  exact ⟨v, hv, hv0, by simpa [gelfandRadius_toContinuousLinearMap_toLin'] using hAv⟩

/-- A functional on `n → ℝ` is the dot product with its values on the standard basis. -/
theorem _root_.ContinuousLinearMap.apply_eq_dotProduct_single (ℓ : StrongDual ℝ (n → ℝ))
    (x : n → ℝ) : ℓ x = (fun j ↦ ℓ (Pi.single j 1)) ⬝ᵥ x := by
  refine (LinearMap.pi_apply_eq_sum_univ (ℓ : (n → ℝ) →ₗ[ℝ] ℝ) x).trans ?_
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show (fun j ↦ if i = j then (1 : ℝ) else 0) = Pi.single i 1 from
    funext fun j ↦ by simp [Pi.single_apply, eq_comm]]
  rfl

/-- **Perron–Frobenius for primitive matrices**: for a primitive matrix `A` with Gelfand radius
`r`, `r > 0`, there are positive right and left eigenvectors `v`, `w` for `r` with `w ⬝ᵥ v = 1`,
and `A - r • vecMulVec v w` has Gelfand radius `< r` (spectral gap). -/
theorem IsPrimitive.exists_gelfandRadius_sub_smul_vecMulVec_lt [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsPrimitive) :
    0 < gelfandRadius A ∧ ∃ v w : n → ℝ, (∀ i, 0 < v i) ∧ (∀ i, 0 < w i) ∧
      A *ᵥ v = gelfandRadius A • v ∧ w ᵥ* A = gelfandRadius A • w ∧ w ⬝ᵥ v = 1 ∧
      gelfandRadius (A - gelfandRadius A • vecMulVec v w) < gelfandRadius A := by
  obtain ⟨hA0, k, hk, hAk⟩ := hA
  have hTk := mapsTo_toLin'_interior_positive hAk
  rw [← toContinuousLinearMap_toLin'_pow] at hTk
  obtain ⟨hr, x₀, hx₀, ℓ, hTx₀, hℓT, hℓx₀, hℓ, hgap⟩ :=
    ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_pow ProperCone.salient_positive
      ⟨fun _ ↦ 1, by rw [interior_positive_pi]; simp⟩ (mapsTo_toLin'_positive hA0) hk.ne' hTk
  rw [gelfandRadius_toContinuousLinearMap_toLin'] at hr hTx₀ hℓT hgap
  set w : n → ℝ := fun j ↦ ℓ (Pi.single j 1)
  have hℓw (x : n → ℝ) : ℓ x = w ⬝ᵥ x := ℓ.apply_eq_dotProduct_single x
  rw [interior_positive_pi] at hx₀
  refine ⟨hr, x₀, w, hx₀,
    fun j ↦ hℓ _ (by simp [Pi.single_nonneg]) (by simp), by simpa using hTx₀, ?_,
    by rw [← hℓw, hℓx₀], ?_⟩
  · ext j
    have h := congr($hℓT (Pi.single j 1))
    rw [ContinuousLinearMap.comp_apply, hℓw] at h
    simpa [mulVec_single_one, vecMul, dotProduct, w] using h
  · rw [← gelfandRadius_toContinuousLinearMap_toLin']
    convert hgap using 2
    ext x : 1
    simp [vecMulVec_mulVec, hℓw]

/-- **Convergence to the Perron projection** for matrices: given right and left eigenvectors
`v`, `w` for `r` with `w ⬝ᵥ v = 1` and a spectral gap, `(r⁻¹ • A) ^ m → vecMulVec v w`. -/
theorem tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_vecMulVec_lt {A : Matrix n n ℝ} {r : ℝ}
    {v w : n → ℝ} (hv : A *ᵥ v = r • v) (hw : w ᵥ* A = r • w) (hwv : w ⬝ᵥ v = 1)
    (hgap : gelfandRadius (A - r • vecMulVec v w) < r) :
    Tendsto (fun m ↦ (r⁻¹ • A) ^ m) atTop (𝓝 (vecMulVec v w)) :=
  tendsto_inv_smul_pow_of_gelfandRadius_sub_smul_lt (by rw [vecMulVec_mul_vecMulVec, hwv, one_smul])
    (by rw [mul_vecMulVec, hv, smul_vecMulVec]) (by rw [vecMulVec_mul, hw, vecMulVec_smul]) hgap

/-- **Spectral dominance** for matrices: if `w` is a left eigenvector for `r` and
`A - r • vecMulVec v w` has Gelfand radius `< r`, every complex eigenvalue `μ ≠ r` of `A` has
`‖μ‖ < r`: an eigenvector for `μ` is orthogonal to `w`, hence an eigenvector of the gapped
matrix. -/
theorem norm_lt_of_mem_spectrum_of_gelfandRadius_sub_smul_vecMulVec_lt {A : Matrix n n ℝ}
    {r : ℝ} {v w : n → ℝ} (hw : w ᵥ* A = r • w)
    (hgap : gelfandRadius (A - r • vecMulVec v w) < r) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) (hμr : μ ≠ r) : ‖μ‖ < r := by
  set f := algebraMap ℝ ℂ
  rw [← spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have hAu : A.map f *ᵥ u = μ • u := by simpa using hu.apply_eq_smul
  have hwA : (f ∘ w) ᵥ* A.map f = (r : ℂ) • (f ∘ w) := by
    ext j
    simpa [f] using (RingHom.map_vecMul f A w j).symm.trans congr(f ($hw j))
  have h := dotProduct_mulVec (f ∘ w) (A.map f) u
  rw [hAu, hwA, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  have hwu : (f ∘ w) ⬝ᵥ u = 0 := by_contra fun hd ↦ hμr (mul_right_cancel₀ hd h)
  have hM : (A - r • vecMulVec v w).map f = A.map f - (r : ℂ) • vecMulVec (f ∘ v) (f ∘ w) := by
    ext i j
    simp [vecMulVec_apply, f]
  have hMu : (A - r • vecMulVec v w).map f *ᵥ u = μ • u := by
    rw [hM, sub_mulVec, smul_mulVec, vecMulVec_mulVec, hwu, hAu]
    simp
  have hμM : μ ∈ spectrum ℂ ((A - r • vecMulVec v w).map f) := by
    rw [← spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hMu), hu.2⟩).mem_spectrum
  have hle : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ ((A - r • vecMulVec v w).map f) := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ _) ↦ (‖k‖₊ : ENNReal)) μ hμM
  rw [spectralRadius_map_algebraMap_eq_gelfandRadius, ← enorm_eq_nnnorm, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (gelfandRadius_nonneg _)] at hle
  exact hle.trans_lt hgap

end Matrix
