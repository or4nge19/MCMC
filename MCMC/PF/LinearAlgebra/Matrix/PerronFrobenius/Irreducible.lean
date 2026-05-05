/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Path
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness

/-!
# Irreducible nonnegative matrices

Quivers, path lifting, `1 + A` irreducibility, and consequences for nonnegative eigenvectors.
-/

open Quiver.Path
namespace Matrix
open Quiver CollatzWielandt

variable {n : Type*} [DecidableEq n] {A : Matrix n n ℝ}

/-- Lift a path from `toQuiver A` to `toQuiver B` when every positive entry of `A`
is a positive entry of `B`, preserving path length. -/
def pathToQuiverOfForallPosImpPos {A B : Matrix n n ℝ}
    (hAB : ∀ {u v : n}, 0 < A u v → 0 < B u v) :
    ∀ {u v : n} (p : @Quiver.Path n (toQuiver A) u v),
      Σ p' : @Quiver.Path n (toQuiver B) u v,
        PLift
          ((@Quiver.Path.length n (toQuiver B) u v p') =
            (@Quiver.Path.length n (toQuiver A) u v p))
  | u, _, @Quiver.Path.nil n (toQuiver A) u =>
      ⟨@Quiver.Path.nil n (toQuiver B) u, ⟨by simp⟩⟩
  | u, _, @Quiver.Path.cons n (toQuiver A) u b c p e =>
      let ⟨p', hp'⟩ := pathToQuiverOfForallPosImpPos hAB p
      ⟨@Quiver.Path.cons n (toQuiver B) u b c p' ⟨hAB e.down⟩, ⟨by simp [hp'.down]⟩⟩

/-- A positive entry of a nonnegative matrix remains positive after adding the identity. -/
lemma one_add_pos_of_pos {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {i j : n} (hij : 0 < A i j) :
    0 < (1 + A) i j := by
  by_cases h : i = j
  · subst h
    simpa using Matrix.one_add_diag_pos (fun k => hA_nonneg k k) i
  · simpa [Matrix.add_apply, Matrix.one_apply, h] using hij

/-- If `A` is irreducible then so is `1 + A`. -/
theorem Irreducible.add_one (h_irred : A.IsIrreducible) : (1 + A).IsIrreducible := by
  let B := (1 : Matrix n n ℝ) + A
  constructor
  · exact fun i j => Matrix.one_add_apply_nonneg h_irred.nonneg i j
  · intro i j
    letI : Quiver n := toQuiver A
    obtain ⟨pA, hpA_pos⟩ := h_irred.connected i j
    let pA' : @Quiver.Path n (toQuiver A) i j := pA
    obtain ⟨pB, hp_len⟩ := pathToQuiverOfForallPosImpPos
      (A := A) (B := B) (fun {u v} huv => by
        simpa [B] using one_add_pos_of_pos h_irred.nonneg huv) pA'
    letI : Quiver n := toQuiver B
    exact ⟨pB, by simpa [hp_len.down] using hpA_pos⟩

/-
A non-zero, non-negative eigenvector of an irreducible matrix is
in fact strictly positive.
-/
omit [DecidableEq n] in
lemma exists_zero_to_pos_edge_of_irreducible [Fintype n]
    (hA_irred : A.IsIrreducible) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0)
    {i₀ : n} (hi₀_zero : v i₀ = 0) :
    ∃ j i : n, v j = 0 ∧ 0 < v i ∧ 0 < A j i := by
  let T : Set n := {i | v i = 0}
  have hT_nonempty : T.Nonempty := ⟨i₀, by simp [T, hi₀_zero]⟩
  have hT_ne_univ : T ≠ Set.univ := by
    intro h_univ
    exact hv_ne_zero <| funext fun i => by
      have : i ∈ T := by rw [h_univ]; exact Set.mem_univ i
      simpa [T] using this
  obtain ⟨j, hj_T, i, hi_not_T, hAji_pos⟩ :=
    Irreducible.exists_edge_out (A := A) hA_irred T hT_nonempty hT_ne_univ
  exact ⟨j, i, by simpa [T] using hj_T,
    pos_of_nonneg_of_not_mem_zero_set hv_nonneg (by simpa [T] using hi_not_T), hAji_pos⟩

omit [DecidableEq n] in
lemma eigenvector_is_positive_of_irreducible_aux [Fintype n]
  {r : ℝ} (hA_irred : A.IsIrreducible)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  by_contra h_has_zero
  push_neg at h_has_zero
  obtain ⟨i₀, hi₀_zero⟩ := h_has_zero
  have hi₀_eq_zero : v i₀ = 0 := le_antisymm hi₀_zero (hv_nonneg i₀)
  obtain ⟨j, i, vj_zero, vi_pos, h_Aji_pos⟩ :=
    exists_zero_to_pos_edge_of_irreducible hA_irred hv_nonneg hv_ne_zero hi₀_eq_zero
  have h_Aji_zero : A j i = 0 :=
    entry_eq_zero_of_mulVec_eq_zero hA_irred.1 hv_nonneg
      (mulVec_apply_eq_zero_of_eigenvector_apply_eq_zero j h_eig vj_zero) vi_pos
  simp [h_Aji_zero] at h_Aji_pos

omit [DecidableEq n] in
lemma eigenvector_no_zero_entries_of_irreducible [Fintype n]
  {r : ℝ} (hA_irred : A.IsIrreducible) (_ : 0 < r)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i :=
  eigenvector_is_positive_of_irreducible_aux hA_irred h_eig hv_nonneg hv_ne_zero

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] in
/-- An irreducible matrix has a positive entry. -/
lemma Irreducible.exists_pos_entry [Nonempty n] (hA_irred : A.IsIrreducible) :
    ∃ i j : n, 0 < A i j := by
  letI : Quiver n := toQuiver A
  exact Nonempty.elim ‹Nonempty n› fun i₀ => by
    obtain ⟨p, hp_pos⟩ := hA_irred.connected i₀ i₀
    rcases Quiver.Path.path_decomposition_first_edge p hp_pos with
      ⟨j, e, -, -, -⟩
    exact ⟨i₀, j, e.down⟩

/-- Translate an eigenvector equation for `1 + A` into one for `A`. -/
lemma mulVec_eq_sub_one_smul_of_one_add_mulVec
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : (1 + A) *ᵥ v = r • v) :
    A *ᵥ v = (r - 1) • v := by
  have h_exp : v + A *ᵥ v = r • v := by
    simpa [add_mulVec, one_mulVec] using h
  have : A *ᵥ v = r • v - v := eq_sub_of_add_eq' h_exp
  simpa [sub_smul, one_smul] using this

/-- For irreducible `A`, a positive eigenvector of `1 + A` has eigenvalue strictly larger than `1`. -/
lemma one_lt_eigenvalue_one_add_of_irreducible [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {r : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (h_eig : (1 + A) *ᵥ v = r • v) :
    1 < r := by
  rcases Irreducible.exists_pos_entry (A := A) hA_irred with ⟨i, j, hA_pos⟩
  have hAv_pos : 0 < (A *ᵥ v) i :=
    mulVec_pos_of_exists_pos_mul_pos i j (fun k => hA_irred.1 i k) hv_pos hA_pos
  have h_comp : v i + (A *ᵥ v) i = r * v i := by
    simpa [add_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul] using congr_fun h_eig i
  have h_lt : v i < r * v i := by linarith
  exact (mul_lt_mul_iff_of_pos_right (hv_pos i)).1 (by simpa [one_mul] using h_lt)

/-- **Perron–Frobenius, irreducible case (Existence part)**
If `A` is a non-negative irreducible matrix, then there exists a strictly positive eigenvalue `r > 0`
and a strictly positive eigenvector `v` (`∀ i, 0 < v i`) such that `A *ᵥ v = r • v`.

The proof uses the auxiliary matrix `B = 1 + A`, which is primitive, to apply the Perron-Frobenius theorem
for primitive matrices and translate the result back to `A`. -/
theorem exists_positive_eigenvector_of_irreducible [Nonempty n]
  (hA_irred : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => Matrix.one_add_apply_nonneg hA_irred.nonneg i j
  have hB_diag_pos : ∀ i, 0 < B i i := fun i => Matrix.one_add_diag_pos (fun j => hA_irred.nonneg j j) i
  have hB_irred : (1 + A).IsIrreducible := Irreducible.add_one (A := A) hA_irred
  have hB_prim : B.IsPrimitive :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  obtain ⟨rB, v, hrB_pos, hv_pos, h_eig_B⟩ :=
    exists_positive_eigenvector_of_primitive (A := B) hB_prim hB_nonneg
  have h_eig_A : A *ᵥ v = (rB - 1) • v := by
    simpa [B] using mulVec_eq_sub_one_smul_of_one_add_mulVec h_eig_B
  have hrB_gt_one : 1 < rB := by
    simpa [B] using one_lt_eigenvalue_one_add_of_irreducible hA_irred hv_pos h_eig_B
  have hrA_pos : 0 < rB - 1 := sub_pos.mpr hrB_gt_one
  exact ⟨rB - 1, v, hrA_pos, hv_pos, h_eig_A⟩

/-! A non-zero, non-negative eigenvector of an irreducible matrix is in fact **strictly** positive. -/
omit [DecidableEq n] in
lemma eigenvector_is_positive_of_irreducible [Nonempty n] {r : ℝ}
  (hA_irred : A.IsIrreducible)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i :=
  eigenvector_is_positive_of_irreducible_aux hA_irred h_eig hv_nonneg hv_ne_zero

open Finset
/--
Given an irreducible non-negative matrix `A` and two strictly positive
eigenvectors for the same positive eigenvalue, they differ by a positive
scalar.
-/
theorem uniqueness_of_positive_eigenvector_gen
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  {A : Matrix n n ℝ} {r : ℝ} (hA_irred : A.IsIrreducible) (hr_pos : 0 < r)
    {v w : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i)
    (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = r • w) :
    ∃ c : ℝ, 0 < c ∧ v = c • w := by
  -- 1.  c := infᵢ (vᵢ / wᵢ)
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : n => v i / w i)
  have hc_pos : 0 < c := by
    apply Finset.inf'_pos Finset.univ_nonempty
    intro i _
    exact div_pos (hv_pos i) (hw_pos i)
  -- 2.  z := v − c•w  (still an eigenvector)
  let z : n → ℝ := v - c • w
  have hz_eig : A *ᵥ z = r • z := by
    dsimp [z]
    exact mulVec_sub_smul_eq_smul_sub_of_mulVec_smul hv_eig hw_eig
  -- 3.  z ≥ 0
  have hz_nonneg : ∀ i, 0 ≤ z i := fun i => by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    exact (le_div_iff₀ (hw_pos i)).mp (Finset.inf'_le _ (Finset.mem_univ i))
  -- 4.  analyse `z`
  by_cases hz_zero : z = 0
  · -- 4a. (`z = 0`)  ⇒  `v = c • w`
    refine ⟨c, hc_pos, ?_⟩
    have h_v_eq : v = c • w := by
      have : v - c • w = 0 := by
        simpa [z] using hz_zero
      exact (sub_eq_zero.1 this)
    exact h_v_eq
  · -- 4b. (`z ≠ 0`)  ⇒  contradiction
    have hz_pos : ∀ i, 0 < z i :=
      eigenvector_no_zero_entries_of_irreducible
        hA_irred hr_pos hz_eig hz_nonneg hz_zero
    -- the infimum is attained
    obtain ⟨i₀, _, h_inf_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n => v i / w i)
    -- at the attaining index we must have `z i₀ = 0`, contradiction
    have hzi₀_zero : z i₀ = 0 := by
      have hv_eq : v i₀ = c * w i₀ :=
        eq_mul_of_eq_div (ne_of_gt (hw_pos i₀)) h_inf_eq
      simp only [Pi.sub_apply, hv_eq, Pi.smul_apply, smul_eq_mul, sub_self, z]
    have hlt := hz_pos i₀
    rw [hzi₀_zero] at hlt
    exact False.elim (lt_irrefl (0 : ℝ) hlt)


omit [DecidableEq n] in
/-- Normalizing a positive eigenvector by the sum of its entries preserves its eigen-equation. -/
lemma inv_sum_smul_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ} (hv_eig : A *ᵥ v = r • v) :
    A *ᵥ ((∑ i, v i)⁻¹ • v) = r • ((∑ i, v i)⁻¹ • v) := by
  rw [mulVec_smul, hv_eig, smul_comm]

omit [DecidableEq n] in
/-- Normalizing a strictly positive vector by its coordinate sum preserves strict positivity. -/
lemma inv_sum_smul_pos_of_pos [Nonempty n] {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) :
    ∀ i, 0 < ((∑ i, v i)⁻¹ • v) i := by
  intro i
  exact mul_pos (inv_pos.mpr <| Finset.sum_pos (fun j _ => hv_pos j) Finset.univ_nonempty)
    (hv_pos i)

omit [DecidableEq n] in
/-- If two positive eigenvectors of a nonnegative matrix have eigenvalues `r` and `s`,
then comparing them by the infimum of coordinate ratios gives `s ≤ r`. -/
lemma eigenvalue_le_of_positive_eigenvectors [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {r s : ℝ} {v w : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i)
    (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = s • w) :
    s ≤ r := by
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : n => v i / w i)
  have hc_pos : 0 < c := Finset.inf'_pos Finset.univ_nonempty fun i _ =>
    div_pos (hv_pos i) (hw_pos i)
  obtain ⟨i₀, _, hc_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : n => v i / w i)
  have hle : ∀ j, c * w j ≤ v j := fun j =>
    (le_div_iff₀ (hw_pos j)).mp (Finset.inf'_le _ (Finset.mem_univ j))
  have h_sum := mulVec_smul_le_mulVec_of_forall_smul_le i₀ (fun j => hA_nonneg i₀ j) c hle
  have h_eq : v i₀ = c * w i₀ := eq_mul_of_eq_div (ne_of_gt <| hw_pos i₀) hc_eq
  have h_pos : 0 < c * w i₀ := mul_pos hc_pos (hw_pos i₀)
  apply le_of_mul_le_mul_right _ h_pos
  calc
    s * (c * w i₀) = c * (s * w i₀) := by ring
    _ ≤ (A *ᵥ v) i₀ := by simpa [hw_eig, Pi.smul_apply, smul_eq_mul] using h_sum
    _ = r * (c * w i₀) := by simp [hv_eig, h_eq, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq n] in
/-- A scalar multiple of a simplex vector is the same simplex vector only when the scalar is `1`. -/
lemma eq_one_of_smul_eq_of_sum_eq_one {c : ℝ} {v w : n → ℝ}
    (hvw : v = c • w) (hv_sum : ∑ i, v i = 1) (hw_sum : ∑ i, w i = 1) :
    c = 1 := by
  calc
    c = c * 1 := (mul_one c).symm
    _ = c * (∑ i, w i) := by rw [hw_sum]
    _ = ∑ i, c * w i := by rw [Finset.mul_sum]
    _ = ∑ i, v i := by simp [hvw, smul_eq_mul]
    _ = 1 := hv_sum

/-- In the simplex, a primitive nonnegative matrix has at most one positive eigenvector,
even if the eigenvalue is not specified in advance. -/
lemma stdSimplex_eigenvector_eq_of_primitive [Nonempty n]
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {r s : ℝ} (hr_pos : 0 < r) (hs_pos : 0 < s)
    {v w : stdSimplex ℝ n} (hv_eig : A *ᵥ v.1 = r • v.1)
    (hw_eig : A *ᵥ w.1 = s • w.1) :
    v = w := by
  have hv_pos := eigenvector_of_primitive_is_positive hA_prim hr_pos
    hv_eig v.2.1 (ne_zero_of_mem_stdSimplex v.2)
  have hw_pos := eigenvector_of_primitive_is_positive hA_prim hs_pos
    hw_eig w.2.1 (ne_zero_of_mem_stdSimplex w.2)
  have hs_le_hr := eigenvalue_le_of_positive_eigenvectors hA_nonneg hv_pos hw_pos hv_eig hw_eig
  have hr_le_hs := eigenvalue_le_of_positive_eigenvectors hA_nonneg hw_pos hv_pos hw_eig hv_eig
  have hr_eq : r = s := le_antisymm hr_le_hs hs_le_hr
  have hw_eig' : A *ᵥ w.1 = r • w.1 := by simp [hw_eig, hr_eq]
  obtain ⟨c, _, hcv⟩ :=
    uniqueness_of_positive_eigenvector hA_prim hr_pos v.1 w.1 hv_eig hw_eig' hv_pos hw_pos
  exact Subtype.val_injective <| by
    simp [hcv, eq_one_of_smul_eq_of_sum_eq_one hcv v.2.2 w.2.2]

/-- **Perron–Frobenius, primitive case (existence, positvity and uniqueness)** -/
theorem pft_primitive
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ) (_ : r > 0), A *ᵥ v.val = r • v.val := by
  obtain ⟨r, v_raw, hr_pos, hv_raw_pos, hv_raw_eig⟩ :=
    exists_positive_eigenvector_of_primitive hA_prim hA_nonneg
  let v0 : n → ℝ := (∑ i, v_raw i)⁻¹ • v_raw
  have hv0_simplex : v0 ∈ stdSimplex ℝ n := by
    simpa [v0] using inv_sum_smul_mem_stdSimplex_of_pos hv_raw_pos
  have hv0_pos : ∀ i, 0 < v0 i := by
    simpa [v0] using inv_sum_smul_pos_of_pos hv_raw_pos
  have hv0_eig : A *ᵥ v0 = r • v0 := by
    simpa [v0] using inv_sum_smul_eigenvector hv_raw_eig
  refine ⟨⟨v0, hv0_simplex⟩, ?_, ?_⟩
  · exact ⟨r, hr_pos, hv0_eig⟩
  · intro w ⟨r', hr'_pos, hw_eig⟩
    exact (stdSimplex_eigenvector_eq_of_primitive
      (v := ⟨v0, hv0_simplex⟩) (w := w)
      hA_prim hA_nonneg hr_pos hr'_pos hv0_eig hw_eig).symm

/-- Adding the identity to an irreducible nonnegative matrix makes it primitive. -/
lemma one_add_isPrimitive_of_irreducible [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) :
    (1 + A).IsPrimitive := by
  exact IsPrimitive.of_irreducible_pos_diagonal (1 + A)
    (fun i j => Matrix.one_add_apply_nonneg hA_irred.nonneg i j)
    (Irreducible.add_one (A := A) hA_irred)
    (fun i => Matrix.one_add_diag_pos (fun j => hA_irred.nonneg j j) i)

/-- In the simplex, an irreducible nonnegative matrix has at most one positive eigenvector,
even if the positive eigenvalue is not specified in advance. -/
lemma stdSimplex_eigenvector_eq_of_irreducible [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {r s : ℝ} (hr_pos : 0 < r) (hs_pos : 0 < s)
    {v w : stdSimplex ℝ n} (hv_eig : A *ᵥ v.1 = r • v.1)
    (hw_eig : A *ᵥ w.1 = s • w.1) :
    v = w := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => Matrix.one_add_apply_nonneg hA_irred.nonneg i j
  obtain ⟨u, hu⟩ := pft_primitive (by simpa [B] using one_add_isPrimitive_of_irreducible hA_irred) hB_nonneg
  have hvB : B *ᵥ v.1 = (r + 1) • v.1 := by
    simp [B, add_mulVec, one_mulVec, add_smul, one_smul, hv_eig, add_comm]
  have hwB : B *ᵥ w.1 = (s + 1) • w.1 := by
    simp [B, add_mulVec, one_mulVec, add_smul, one_smul, hw_eig, add_comm]
  exact (hu.2 v ⟨r + 1, by linarith, hvB⟩).trans
    (hu.2 w ⟨s + 1, by linarith, hwB⟩).symm
/--
**Perron–Frobenius theorem for irreducible real matrices (Existence, positivity, uniqueness)**.

Let A : Matrix n n ℝ be an irreducible nonnegative matrix indexed by a finite nonempty type n.
Then there exists a unique eigenpair (v, r) where
  • v : stdSimplex ℝ n is a probability vector (i.e. v.val has nonnegative entries summing to 1),
  • r : ℝ is a positive scalar,
such that
  A *ᵥ v.val = r • v.val   and   r > 0.
Moreover, this eigenvector v in the standard simplex is unique, and the corresponding eigenvalue r
is the Perron root of A.
-/
theorem pft_irreducible {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
  {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ), r > 0 ∧ A *ᵥ v.val = r • v.val := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => Matrix.one_add_apply_nonneg hA_irred.nonneg i j
  have hB_prim : B.IsPrimitive :=
    by simpa [B] using one_add_isPrimitive_of_irreducible hA_irred
  obtain ⟨v, hv_unique⟩ := pft_primitive hB_prim hB_nonneg
  obtain ⟨rB, hrB_pos, h_eig_B⟩ := hv_unique.1
  let r : ℝ := rB - 1
  have h_eig_A : A *ᵥ v.val = r • v.val := by
    simpa [B, r] using mulVec_eq_sub_one_smul_of_one_add_mulVec h_eig_B
  have hr_pos : 0 < r := by
    exact sub_pos.mpr <| by
      simpa [B] using one_lt_eigenvalue_one_add_of_irreducible hA_irred
        (eigenvector_of_primitive_is_positive hB_prim hrB_pos h_eig_B v.2.1
          (ne_zero_of_mem_stdSimplex v.2))
        h_eig_B
  refine ⟨v, ⟨r, hr_pos, h_eig_A⟩, ?_⟩
  · intro v' ⟨r', hr'_pos, h_eig_A'⟩
    exact (stdSimplex_eigenvector_eq_of_irreducible
      (v := v) (w := v') hA_irred hr_pos hr'_pos h_eig_A h_eig_A').symm
