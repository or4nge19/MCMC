/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import MCMC.ToMathlib.Analysis.Matrix.PerronFrobenius

/-!
# The Perron root is the Gelfand radius

For every entrywise nonnegative square matrix, the Collatz–Wielandt Perron root
`CollatzWielandt.perronRoot A = sup {min_{xᵢ > 0} (A x)ᵢ / xᵢ | x ≥ 0, x ≠ 0}` is the Gelfand
radius `gelfandRadius A` (`ℓ∞` operator norm), i.e. the spectral radius of `A` as a complex matrix
(`Matrix.spectralRadius_map_algebraMap_eq_gelfandRadius`). No irreducibility is needed: a
nonnegative sub-eigenvector `c • x ≤ A *ᵥ x` gives `cᵏ ≤ ‖Aᵏ‖`, and the Krein–Rutman eigenvector
`A *ᵥ v = gelfandRadius A • v`, `v ≥ 0`
(`Matrix.exists_nonneg_ne_zero_mulVec_eq_gelfandRadius_smul`) has Collatz–Wielandt value
`gelfandRadius A`.

So the finite Perron–Frobenius theory of `MCMC.PF` and the cone theory of `MCMC.ToMathlib` speak
about the same number.

## Main statements

* `Matrix.le_gelfandRadius_of_smul_le_mulVec`: the subinvariance bound.
* `Matrix.perronRoot_eq_gelfandRadius`.
* `Matrix.IsIrreducible.exists_gelfandRadius_one_add_sub_smul_vecMulVec_lt`: Perron–Frobenius for
  irreducible matrices from Krein–Rutman for the primitive matrix `1 + A`.
-/

open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **Subinvariance bound**: a nonzero nonnegative `x` with `c • x ≤ A *ᵥ x` for a nonnegative
matrix `A` forces `c ≤ gelfandRadius A`. -/
theorem le_gelfandRadius_of_smul_le_mulVec (hA : ∀ i j, 0 ≤ A i j) {x : n → ℝ} (hx : 0 ≤ x)
    (hx0 : x ≠ 0) {c : ℝ} (hcx : c • x ≤ A *ᵥ x) : c ≤ gelfandRadius A := by
  obtain hc | hc := le_or_gt c 0
  · exact hc.trans (gelfandRadius_nonneg A)
  have hmono {y z : n → ℝ} (hyz : y ≤ z) : A *ᵥ y ≤ A *ᵥ z := fun i ↦
    Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hyz j) (hA i j)
  have hpow (k : ℕ) : c ^ k • x ≤ (A ^ k) *ᵥ x := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc c ^ (k + 1) • x = c ^ k • (c • x) := by rw [pow_succ, mul_smul]
        _ ≤ c ^ k • (A *ᵥ x) := smul_le_smul_of_nonneg_left hcx (by positivity)
        _ = A *ᵥ (c ^ k • x) := by rw [mulVec_smul]
        _ ≤ A *ᵥ ((A ^ k) *ᵥ x) := hmono ih
        _ = (A ^ (k + 1)) *ᵥ x := by rw [mulVec_mulVec, pow_succ']
  have hx₀ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine le_gelfandRadius_of_pow_le_norm_pow hc.le fun k ↦ le_of_mul_le_mul_right ?_ hx₀
  calc c ^ k * ‖x‖ = ‖c ^ k • x‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ ‖(A ^ k) *ᵥ x‖ := by
      refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i ↦ ?_
      rw [Pi.smul_apply, Real.norm_of_nonneg (smul_nonneg (by positivity) (hx i))]
      exact (hpow k i).trans ((Real.le_norm_self _).trans (norm_le_pi_norm _ i))
    _ ≤ ‖A ^ k‖ * ‖x‖ := linfty_opNorm_mulVec _ _

/-- **The Collatz–Wielandt Perron root is the Gelfand radius**, for every nonnegative matrix. -/
theorem perronRoot_eq_gelfandRadius [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) :
    CollatzWielandt.perronRoot A = gelfandRadius A := by
  refine le_antisymm (csSup_le CollatzWielandt.set_nonempty ?_) ?_
  · rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩
    exact le_gelfandRadius_of_smul_le_mulVec hA hx hx0 (CollatzWielandt.le_mulVec hA hx hx0)
  obtain ⟨v, hv, hv0, hAv⟩ := exists_nonneg_ne_zero_mulVec_eq_gelfandRadius_smul hA
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv0
  have hsupp : ({i | 0 < v i}.toFinset).Nonempty :=
    ⟨i₀, by simpa using (hv i₀).lt_of_ne' hi₀⟩
  have hterm (i : n) (hi : i ∈ {i | 0 < v i}.toFinset) : (A *ᵥ v) i / v i = gelfandRadius A := by
    rw [hAv, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (by simp at hi; exact hi.ne'),
      mul_one]
  refine le_csSup (CollatzWielandt.bddAbove A hA) ⟨v, ⟨hv, hv0⟩, ?_⟩
  rw [CollatzWielandt.collatzWielandtFn_eq_inf' A hsupp]
  exact le_antisymm (Finset.inf'_le_of_le _ hsupp.choose_spec (hterm _ hsupp.choose_spec).le)
    (Finset.le_inf' _ _ fun i hi ↦ (hterm i hi).ge)

/-- **Perron–Frobenius for irreducible matrices**, from Krein–Rutman for the primitive `1 + A`:
an irreducible matrix `A` has positive right and left eigenvectors `v`, `w` for
`r = gelfandRadius A` with `w ⬝ᵥ v = 1`, and `1 + A` has the spectral gap
`gelfandRadius (1 + A - (1 + r) • vecMulVec v w) < 1 + r`, so `r` is algebraically simple. -/
theorem IsIrreducible.exists_gelfandRadius_one_add_sub_smul_vecMulVec_lt [Nonempty n]
    (hA : A.IsIrreducible) :
    ∃ v w : n → ℝ, (∀ i, 0 < v i) ∧ (∀ i, 0 < w i) ∧ A *ᵥ v = gelfandRadius A • v ∧
      w ᵥ* A = gelfandRadius A • w ∧ w ⬝ᵥ v = 1 ∧
      gelfandRadius (1 + A - (1 + gelfandRadius A) • vecMulVec v w) < 1 + gelfandRadius A := by
  obtain ⟨-, v, w, hv, hw, hBv, hwB, hwv, hgap⟩ :=
    (one_add_isPrimitive_of_irreducible hA).exists_gelfandRadius_sub_smul_vecMulVec_lt
  obtain ⟨u, hu, hu0, hAu⟩ := exists_nonneg_ne_zero_mulVec_eq_gelfandRadius_smul hA.nonneg
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hu0
  have hwu : 0 < w ⬝ᵥ u := Finset.sum_pos' (fun i _ ↦ mul_nonneg (hw i).le (hu i))
    ⟨j, Finset.mem_univ j, mul_pos (hw j) ((hu j).lt_of_ne' hj)⟩
  have hρ : gelfandRadius (1 + A) = 1 + gelfandRadius A := by
    have h := dotProduct_mulVec w (1 + A) u
    rw [hwB, add_mulVec, one_mulVec, hAu, dotProduct_add, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul] at h
    exact mul_right_cancel₀ hwu.ne' (by linarith)
  rw [hρ] at hBv hwB hgap
  refine ⟨v, w, hv, hw, ?_, ?_, hwv, hgap⟩
  · rw [add_mulVec, one_mulVec, add_smul, one_smul] at hBv
    exact add_left_cancel hBv
  · rw [vecMul_add, vecMul_one, add_smul, one_smul] at hwB
    exact add_left_cancel hwB

end Matrix
