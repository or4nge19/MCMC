/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Perron-Frobenius for primitive matrices

Theorem 1.1 in Seneta, *Non-negative Matrices and Markov Chains*: Collatz–Wielandt supremum,
existence of a simplex maximizer, then primitivity forces a strictly positive eigenvector.
Irreducible facts such as `perronRoot_pos_of_irreducible` live in `CollatzWielandt.lean` next to
`perronRoot`.

-/

namespace Matrix

open Set Finset MetricSpace Topology Convex Quiver.Path Matrix Matrix.CollatzWielandt IsCompact
section PerronFrobenius
open scoped Convex Pointwise

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ}

/-- For a maximizer `v` of the Collatz-Wielandt function, `A * v = r • v`. -/
theorem maximizer_is_eigenvector (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v)
    (hv_simplex : v ∈ stdSimplex ℝ n) (r : ℝ) (hr_def : r = collatzWielandtFn A v) :
    A *ᵥ v = r • v := by
  have hv_nonneg : ∀ i, 0 ≤ v i := hv_simplex.1
  have hv_ne_zero : v ≠ 0 := fun h => by simpa [h, stdSimplex] using hv_simplex.2
  have h_fund_ineq : r • v ≤ A *ᵥ v := by
    rw [hr_def]; exact CollatzWielandt.le_mulVec hA_nonneg hv_nonneg hv_ne_zero
  by_contra h_ne
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i ↦ by simp [z, sub_nonneg]; exact h_fund_ineq i
  have hz_ne_zero : z ≠ 0 := by
    intro hz_zero
    apply h_ne
    ext i
    simpa [z, sub_eq_zero] using congr_fun hz_zero i
  obtain ⟨_, k, hk_gt_zero, hk_pos⟩ := hA_prim
  let y := (A ^ k) *ᵥ v
  have hy_pos : ∀ i, 0 < y i := positive_mul_vec_of_nonneg_vec hk_pos hv_nonneg hv_ne_zero
  have h_Ay_gt_ry : ∀ i, r * y i < (A *ᵥ y) i := by
    intro i
    let Az := (A ^ k) *ᵥ z
    have h_pos_term : 0 < Az i := (positive_mul_vec_of_nonneg_vec hk_pos hz_nonneg hz_ne_zero) i
    have h_calc : (A *ᵥ y) i = r * y i + Az i := by
      simp only [y, z, Az, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [add_comm, ← sub_eq_iff_eq_add]
      rw [mulVec_mulVec, mulVec_mulVec, ← pow_succ', pow_succ]
    rw [h_calc]; exact lt_add_of_pos_right (r * y i) h_pos_term
  have r_lt_r_y : r < collatzWielandtFn A y := by
    have h_y_supp_nonempty : ({i | 0 < y i}.toFinset).Nonempty := by
      rw [Set.toFinset_nonempty_iff]; exact ⟨(Classical.arbitrary n), hy_pos _⟩
    rw [collatzWielandtFn, dif_pos h_y_supp_nonempty]; apply (Finset.lt_inf'_iff h_y_supp_nonempty).mpr
    intro i _;
    exact (lt_div_iff₀ (hy_pos i)).mpr (h_Ay_gt_ry i)
  let y_norm_factor := (∑ i, y i)⁻¹
  let y_norm := y_norm_factor • y
  have hy_norm_in_simplex : y_norm ∈ stdSimplex ℝ n := by
    have : Nonempty n := by
      subst hr_def
      simp_all only [ne_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg, mulVec_mulVec, y, z]
    refine ⟨?_, ?_⟩
    · intro i
      have h_sum_nonneg : 0 ≤ ∑ j, y j := sum_nonneg (fun j _ => (hy_pos j).le)
      exact smul_nonneg (inv_nonneg.mpr h_sum_nonneg) (hy_pos i).le
    · have h_sum_pos : 0 < ∑ i, y i :=
        Finset.sum_pos (fun i _ => hy_pos i) Finset.univ_nonempty
      have h_sum_ne_zero : (∑ i, y i) ≠ 0 := ne_of_gt h_sum_pos
      calc
        ∑ x, (∑ j, y j)⁻¹ • y x
            = ∑ x, (∑ j, y j)⁻¹ * y x   := by simp [smul_eq_mul]
        _  = (∑ j, y j)⁻¹ * ∑ x, y x      := by simp [Finset.mul_sum]
        _  = (∑ i, y i) * (∑ j, y j)⁻¹   := by rw [mul_comm]
        _  = 1                           := mul_inv_cancel₀ h_sum_ne_zero
  have r_ge_r_y_norm : collatzWielandtFn A y_norm ≤ r := by
    rw [hr_def]
    exact hv_max hy_norm_in_simplex
  have r_y_norm_eq_r_y : collatzWielandtFn A y_norm = collatzWielandtFn A y := by
    have sum_pos : 0 < ∑ i, y i :=
      Finset.sum_pos (fun _ _ => hy_pos _) Finset.univ_nonempty
    have ne0 : (∑ i, y i) ≠ 0 := ne_of_gt sum_pos
    have sup_eq : ({i | 0 < y_norm i}.toFinset : Finset n) =
                  ({i | 0 < y i}.toFinset : Finset n) := by
      have h_set_eq : {i | 0 < y_norm i} = {i | 0 < y i} := by
        ext i
        have sum_pos : 0 < ∑ j, y j := Finset.sum_pos (fun j _ => hy_pos j) Finset.univ_nonempty
        subst hr_def
        simp_all only [ne_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg, mulVec_mulVec, inv_pos,
          mul_pos_iff_of_pos_left, setOf_true, Set.mem_univ, y, y_norm, y_norm_factor, z]
      subst hr_def
      simp_all only [ne_eq, Pi.smul_apply, smul_eq_mul, inv_pos, mul_pos_iff_of_pos_left, setOf_true,
        Pi.sub_apply, sub_nonneg, mulVec_mulVec, toFinset_univ, y, y_norm_factor, y_norm, z]
    have fun_eq : (fun i => (A *ᵥ y_norm) i / y_norm i) =
                 fun i => (A *ᵥ y) i / y i := by
      funext i
      calc
        (A *ᵥ y_norm) i / y_norm i
            = ((∑ j, y j)⁻¹ * (A *ᵥ y) i) / ((∑ j, y j)⁻¹ * y i) := by
              simp [y_norm, y_norm_factor, mulVec_smul]
        _ = (A *ᵥ y) i / y i := by
              exact mul_div_mul_eq_div (inv_ne_zero ne0) (hy_pos i).ne'
    dsimp [collatzWielandtFn, y_norm, y_norm_factor]
    split_ifs with h₁ h₂
    · simp
      subst hr_def
      simp_all only [ne_eq, Pi.smul_apply, smul_eq_mul, inv_pos, mul_pos_iff_of_pos_left, setOf_true,
        toFinset_univ, mulVec_mulVec, Pi.sub_apply, sub_nonneg, Finset.filter_true,
        y, y_norm_factor, y_norm, z]
    · subst hr_def
      simp_all only [ne_eq, Pi.smul_apply, smul_eq_mul, inv_pos, mul_pos_iff_of_pos_left, setOf_true,
        toFinset_univ, mulVec_mulVec, Finset.univ_nonempty, not_true_eq_false, y, y_norm_factor, y_norm]
    · subst hr_def
      simp_all only [ne_eq, Pi.smul_apply, smul_eq_mul, inv_pos, mul_pos_iff_of_pos_left, setOf_true,
        toFinset_univ, mulVec_mulVec, Finset.univ_nonempty, not_true_eq_false, y, y_norm_factor, y_norm]
    · rfl
  linarith [r_ge_r_y_norm, r_y_norm_eq_r_y, r_lt_r_y]

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

/-- The Perron root `r = collatzWielandtFn A v` is positive. -/
lemma perron_root_pos_of_primitive
  (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {v : n → ℝ} (_ : v ∈ stdSimplex ℝ n) (hvM : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v) :
  0 < collatzWielandtFn A v := by
  -- lower-bound sup by the CW-value at the all-ones vector (up to scale)
  let ones_norm : n → ℝ := fun _ => (Fintype.card n : ℝ)⁻¹
  have h₁ : ones_norm ∈ stdSimplex ℝ n := by
    simpa [ones_norm] using ones_norm_mem_simplex
  have cw_one_pos : 0 < collatzWielandtFn A (fun _ => 1) :=
    collatzWielandtFn_of_ones_is_pos (Matrix.IsPrimitive.isIrreducible (A := A) hA_prim) hA_nonneg
  have cw_scale : collatzWielandtFn A ones_norm = collatzWielandtFn A (fun _ => 1) := by
    let c := (Fintype.card n : ℝ)⁻¹
    have hc_pos : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    let x : n → ℝ := fun _ => 1
    have hx_nonneg : ∀ i, 0 ≤ x i := fun _ => zero_le_one
    have hx_ne_zero : x ≠ 0 := by
      intro h
      have : (1 : ℝ) = 0 := congr_fun h (Classical.arbitrary n)
      exact one_ne_zero this
    have h_eq : ones_norm = c • x := by ext; simp [c, x, ones_norm]
    rw [h_eq]
    exact CollatzWielandt.collatzWielandtFn_smul hc_pos hx_nonneg hx_ne_zero
  have cw_le_max : collatzWielandtFn A ones_norm ≤ collatzWielandtFn A v := hvM h₁
  calc
    0 < collatzWielandtFn A (fun _ => 1) := cw_one_pos
    _ = collatzWielandtFn A ones_norm := cw_scale.symm
    _ ≤ collatzWielandtFn A v := cw_le_max

/-- **Perron-Frobenius theorem for primitive matrices - Existence part**-/
theorem exists_positive_eigenvector_of_primitive
  (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
  ∃ (r : ℝ) (v : n → ℝ), r > 0 ∧ (∀ i, v i > 0) ∧ A *ᵥ v = r • v := by
  -- 1) We get maximizer v on the simplex
  haveI : Nonempty (stdSimplex ℝ n) :=
    ⟨⟨_, ones_norm_mem_simplex⟩⟩
  obtain ⟨v, hvS, hvM⟩ := CollatzWielandt.exists_maximizer (A := A)
  let r := collatzWielandtFn A v
  -- 2) We show r>0
  have hr : 0 < r := perron_root_pos_of_primitive hA_prim hA_nonneg hvS hvM
  -- 3) maximizer ⇒ eigenvector
  have h_eig := maximizer_is_eigenvector hA_prim hA_nonneg hvM hvS r rfl
  -- 4) primitive ⇒ strict positivity of v
  have hv0 : v ≠ 0 := by
    intro h
    have h_sum_zero : ∑ i, v i = 0 := by rw [h]; simp
    have h_sum_one : ∑ i, v i = 1 := hvS.2
    linarith [h_sum_zero, h_sum_one]
  have hvp := eigenvector_of_primitive_is_positive hA_prim hr h_eig hvS.1 hv0
  use r, v


end PerronFrobenius
end Matrix
