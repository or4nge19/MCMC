/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import Mathlib.Tactic

/-!
# Perron-Frobenius for primitive matrices

Theorem 1.1 in Seneta, *Non-negative Matrices and Markov Chains*: Collatz–Wielandt supremum,
existence of a simplex maximizer, then primitivity forces a strictly positive eigenvector.

-/

namespace Matrix

open Set Finset MetricSpace Topology Convex Quiver.Path Matrix Matrix.CollatzWielandt IsCompact
section PerronFrobenius
open scoped Convex Pointwise

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ}

/-- Normalizing a strictly positive vector by its sum gives a point of the standard simplex. -/
lemma inv_sum_smul_mem_stdSimplex_of_pos {x : n → ℝ} (hx_pos : ∀ i, 0 < x i) :
    (∑ i, x i)⁻¹ • x ∈ stdSimplex ℝ n :=
  CollatzWielandt.inv_sum_smul_mem_stdSimplex_of_nonneg_ne_zero
    (fun i => (hx_pos i).le) (Pi.ne_zero_of_pos hx_pos)

/-- Collatz-Wielandt is unchanged by normalizing a strictly positive vector by its sum. -/
lemma collatzWielandtFn_inv_sum_smul_of_pos (A : Matrix n n ℝ)
    {x : n → ℝ} (hx_pos : ∀ i, 0 < x i) :
    collatzWielandtFn A ((∑ i, x i)⁻¹ • x) = collatzWielandtFn A x :=
  CollatzWielandt.collatzWielandtFn_inv_sum_smul_of_nonneg_ne_zero
    (fun i => (hx_pos i).le) (Pi.ne_zero_of_pos hx_pos)

omit [DecidableEq n] in
/-- Strict coordinate inequalities `r * xᵢ < (Ax)ᵢ` force `r < r(x)`. -/
lemma lt_collatzWielandtFn_of_forall_mul_lt_mulVec
    {A : Matrix n n ℝ} {x : n → ℝ} {r : ℝ}
    (hx_pos : ∀ i, 0 < x i) (h_lt : ∀ i, r * x i < (A *ᵥ x) i) :
    r < collatzWielandtFn A x := by
  have hsupp : ({i | 0 < x i}.toFinset).Nonempty := by
    obtain ⟨i⟩ := inferInstanceAs (Nonempty n)
    exact ⟨i, by simpa using hx_pos i⟩
  rw [collatzWielandtFn_eq_inf' A hsupp]
  exact (Finset.lt_inf'_iff hsupp).mpr fun i _ => (lt_div_iff₀ (hx_pos i)).mpr (h_lt i)

omit [Nonempty n] in
/-- If the residual `A *ᵥ v - r • v` is nonzero nonnegative, a positive power gives
strict Collatz-Wielandt inequalities for `(A ^ k) *ᵥ v`. -/
lemma forall_mul_mulVec_pow_lt_mulVec_mulVec_pow_of_residual
    {A : Matrix n n ℝ} {v z : n → ℝ} {r : ℝ} {k : ℕ}
    (hz : z = A *ᵥ v - r • v) (hAk_pos : ∀ i j, 0 < (A ^ k) i j)
    (hz_nonneg : ∀ i, 0 ≤ z i) (hz_ne_zero : z ≠ 0) :
    ∀ i, r * ((A ^ k) *ᵥ v) i < (A *ᵥ ((A ^ k) *ᵥ v)) i := by
  intro i
  let Az := (A ^ k) *ᵥ z
  have h_pos_term : 0 < Az i := (positive_mul_vec_of_nonneg_vec hAk_pos hz_nonneg hz_ne_zero) i
  have h_calc : (A *ᵥ ((A ^ k) *ᵥ v)) i = r * ((A ^ k) *ᵥ v) i + Az i := by
    subst z
    simp only [Az, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_comm, ← sub_eq_iff_eq_add, mulVec_mulVec, mulVec_mulVec, ← pow_succ', pow_succ]
  rw [h_calc]
  exact lt_add_of_pos_right _ h_pos_term

/-- A nonzero nonnegative residual for a primitive matrix produces a strictly better
Collatz-Wielandt test vector. -/
lemma exists_pos_vector_collatzWielandtFn_gt_of_residual
    {A : Matrix n n ℝ} {v z : n → ℝ} {r : ℝ} (hA_prim : IsPrimitive A)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0)
    (hz : z = A *ᵥ v - r • v) (hz_nonneg : ∀ i, 0 ≤ z i) (hz_ne_zero : z ≠ 0) :
    ∃ y : n → ℝ, (∀ i, 0 < y i) ∧ r < collatzWielandtFn A y := by
  obtain ⟨_, k, _, hk_pos⟩ := hA_prim
  let y := (A ^ k) *ᵥ v
  have hy_pos : ∀ i, 0 < y i := positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero
  refine ⟨y, hy_pos, ?_⟩
  exact lt_collatzWielandtFn_of_forall_mul_lt_mulVec hy_pos <| by
    simpa [y] using forall_mul_mulVec_pow_lt_mulVec_mulVec_pow_of_residual
      (A := A) (v := v) (z := z) (r := r) (k := k) hz hk_pos hz_nonneg hz_ne_zero

/-- For a maximizer `v` of the Collatz-Wielandt function, `A * v = r • v`. -/
theorem maximizer_is_eigenvector (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v)
    (hv_simplex : v ∈ stdSimplex ℝ n) (r : ℝ) (hr_def : r = collatzWielandtFn A v) :
    A *ᵥ v = r • v := by
  have hv_nonneg : ∀ i, 0 ≤ v i := hv_simplex.1
  have hv_ne_zero : v ≠ 0 := ne_zero_of_mem_stdSimplex hv_simplex
  have h_fund_ineq : r • v ≤ A *ᵥ v := by
    simpa [hr_def] using CollatzWielandt.le_mulVec hA_nonneg hv_nonneg hv_ne_zero
  by_contra h_ne
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i ↦ by simp [z, sub_nonneg]; exact h_fund_ineq i
  have hz_ne_zero : z ≠ 0 := by
    contrapose! h_ne
    ext i
    simpa [z, sub_eq_zero] using congr_fun h_ne i
  obtain ⟨y, hy_pos, r_lt_r_y⟩ :=
    exists_pos_vector_collatzWielandtFn_gt_of_residual
      hA_prim hv_nonneg hv_ne_zero rfl hz_nonneg hz_ne_zero
  have r_ge_r_y_norm : collatzWielandtFn A ((∑ i, y i)⁻¹ • y) ≤ r := by
    simpa [hr_def] using hv_max (inv_sum_smul_mem_stdSimplex_of_pos hy_pos)
  have r_y_norm_eq_r_y : collatzWielandtFn A ((∑ i, y i)⁻¹ • y) = collatzWielandtFn A y :=
    collatzWielandtFn_inv_sum_smul_of_pos A hy_pos
  linarith

omit [Nonempty n] in
/-- An eigenvector `v` of a primitive matrix `A` corresponding to a positive eigenvalue `r` must be strictly positive. -/
lemma eigenvector_of_primitive_is_positive {r : ℝ} (hA_prim : IsPrimitive A) (hr_pos : 0 < r)
    {v : n → ℝ} (h_eigen : A *ᵥ v = r • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  obtain ⟨_, k, hk_gt_zero, hk_pos⟩ := hA_prim
  have h_Ak_v : (A ^ k) *ᵥ v = (r ^ k) • v :=
    mulVec_pow_eq_smul_pow_of_mulVec_smul h_eigen k
  have h_Ak_v_pos : ∀ i, 0 < ((A ^ k) *ᵥ v) i :=
    positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero
  intro i
  rw [h_Ak_v] at h_Ak_v_pos
  exact (mul_pos_iff_of_pos_left (pow_pos hr_pos k)).mp (h_Ak_v_pos i)

/-- Collatz-Wielandt is unchanged by normalizing the all-ones vector by `Fintype.card`. -/
lemma collatzWielandtFn_ones_norm_eq (A : Matrix n n ℝ) :
    collatzWielandtFn A (fun _ => (Fintype.card n : ℝ)⁻¹) =
      collatzWielandtFn A (fun _ : n => (1 : ℝ)) := by
  let c := (Fintype.card n : ℝ)⁻¹
  let x : n → ℝ := fun _ => 1
  have hx_ne_zero : x ≠ 0 := by
    intro h
    obtain ⟨i⟩ := inferInstanceAs (Nonempty n)
    exact one_ne_zero (congr_fun h i)
  have h_eq : (fun _ : n => (Fintype.card n : ℝ)⁻¹) = c • x := by
    ext
    simp [c, x]
  rw [h_eq]
  exact CollatzWielandt.collatzWielandtFn_smul
    (A := A) (c := c) (inv_pos.mpr <| Nat.cast_pos.mpr Fintype.card_pos)
    (fun _ => zero_le_one) hx_ne_zero

/-- The Perron root `r = collatzWielandtFn A v` is positive. -/
lemma perron_root_pos_of_primitive
  (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {v : n → ℝ} (_ : v ∈ stdSimplex ℝ n) (hvM : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v) :
  0 < collatzWielandtFn A v := by
  let ones_norm : n → ℝ := fun _ => (Fintype.card n : ℝ)⁻¹
  have h₁ : ones_norm ∈ stdSimplex ℝ n := by
    simpa [ones_norm] using ones_norm_mem_simplex
  have cw_one_pos : 0 < collatzWielandtFn A (fun _ => 1) :=
    collatzWielandtFn_of_ones_is_pos (Matrix.IsPrimitive.isIrreducible (A := A) hA_prim) hA_nonneg
  have cw_le_max : collatzWielandtFn A ones_norm ≤ collatzWielandtFn A v := hvM h₁
  calc
    0 < collatzWielandtFn A (fun _ => 1) := cw_one_pos
    _ = collatzWielandtFn A ones_norm := (by simpa [ones_norm] using
        (collatzWielandtFn_ones_norm_eq A).symm)
    _ ≤ collatzWielandtFn A v := cw_le_max

/-- **Perron-Frobenius theorem for primitive matrices - Existence part**-/
theorem exists_positive_eigenvector_of_primitive
  (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
  ∃ (r : ℝ) (v : n → ℝ), r > 0 ∧ (∀ i, v i > 0) ∧ A *ᵥ v = r • v := by
  haveI : Nonempty (stdSimplex ℝ n) :=
    ⟨⟨_, ones_norm_mem_simplex⟩⟩
  obtain ⟨v, hvS, hvM⟩ := CollatzWielandt.exists_maximizer (A := A)
  let r := collatzWielandtFn A v
  have hr : 0 < r := perron_root_pos_of_primitive hA_prim hA_nonneg hvS hvM
  have h_eig := maximizer_is_eigenvector hA_prim hA_nonneg hvM hvS r rfl
  exact ⟨r, v, hr,
    eigenvector_of_primitive_is_positive hA_prim hr h_eig hvS.1 (ne_zero_of_mem_stdSimplex hvS),
    h_eig⟩


end PerronFrobenius
end Matrix
