/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import MCMC.PF.Combinatorics.Quiver.Path

/-!
# Perron-Frobenius support lemmas

These results connect `Matrix.IsIrreducible` and `Matrix.IsPrimitive` to the quiver `Matrix.toQuiver A`.

## Main statements

- `Matrix.path_exists_in_support_of_irreducible` lifts irreducibility of a principal submatrix to a
  path in the ambient quiver that stays inside the support.
- `Matrix.positive_mul_vec_of_nonneg_vec` shows that a matrix with strictly positive entries sends
  a nonnegative nonzero vector to a strictly positive vector.
- `Matrix.exists_connecting_edge_of_irreducible` produces an edge from the zero set of a
  nonnegative vector to its positive support.
- `Matrix.irreducible_mulVec_ne_zero` shows that an irreducible nonnegative matrix cannot kill a
  nonnegative nonzero vector.
- `Matrix.IsPrimitive.of_irreducible_pos_diagonal` upgrades irreducibility together with a
  positive diagonal to primitivity.
- `Matrix.mulVec_pow_eq_smul_pow_of_mulVec_smul` packages induction for `(A ^ m) *ᵥ v` when
  `A *ᵥ v = r • v`.
- `Matrix.mulVec_map_pow_eq_smul_pow_of_mulVec_map_smul` is the same after applying a ring
  homomorphism entrywise (`Matrix.map`).
- `Matrix.one_add_apply_nonneg` / `Matrix.one_add_diag_pos` package the entrywise bounds for `1 + A`
  used when passing from `A` to a primitive shift `1 + A`.
- `Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg` turns a vanishing finite sum of nonnegative
  reals into pointwise vanishing (used for nonnegative matrix rows).
- `Matrix.mul_eq_zero_of_mulVec_eq_zero_of_row_nonneg` packages the same principle for one row of
  `A *ᵥ v`.
- `Matrix.sum_mul_le_sum_mul_const_of_forall_le` bounds a weighted sum by the total weight times the
  largest factor (nonnegative weights).
- `Matrix.mulVec_smul_le_mulVec_of_forall_smul_le` compares one row of `A *ᵥ` after scaling the
  input vector, when that row of `A` is nonnegative and the scaling holds entrywise.
- `Matrix.mulVec_apply_eq_zero_of_eigenvector_apply_eq_zero` rewrites one coordinate of `A *ᵥ v`
  from `A *ᵥ v = r • v` when `v j = 0`.
- `Matrix.mulVec_sub_smul_eq_smul_sub_of_mulVec_smul`: a difference of two `r`-eigenvectors scaled by
  `c` is still an `r`-eigenvector.
- `Matrix.mulVec_pos_of_exists_pos_mul_pos` gives `(A *ᵥ v) i > 0` from one positive summand
  `A i j * v j` in a nonnegative row against a positive vector.
- `Matrix.row_sum_pos_of_irreducible_nonneg`: each row sum of an irreducible nonnegative matrix is
  strictly positive (no zero row).

-/

namespace Pi

/-- A strictly positive dependent function on a nonempty type is nonzero. -/
lemma ne_zero_of_pos {ι α : Type*} [Nonempty ι] [Zero α] [Preorder α]
    {v : ι → α} (hv_pos : ∀ i, 0 < v i) :
    v ≠ 0 := by
  rintro rfl
  let i := Classical.arbitrary ι
  exact (hv_pos i).false

end Pi

namespace Matrix
section PerronFrobenius
open Matrix Finset Quiver Quiver.Path
variable {n : Type*}

/-! ### Paths in induced subquivers -/

/-- A path in the submatrix `A.submatrix Subtype.val Subtype.val` lifts to a path in the
original quiver `toQuiver A`, and all vertices along that lifted path lie in `S`. -/
lemma path_in_submatrix_to_original {A : Matrix n n ℝ}
  (S : Set n)
  {i j : S}
  (p : @Quiver.Path S (letI := Matrix.toQuiver A; inducedQuiver S) i j) :
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  ∃ p' : @Path n (Matrix.toQuiver A) i.val j.val,
    ∀ k, k ∈ p'.activeVertices → k ∈ S := by
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  let p' := (Subquiver.embedding S).mapPath p
  exact ⟨p', Subquiver.mapPath_embedding_vertices_in_set S p⟩

/-- If the principal submatrix supported on `S` is irreducible, then any two vertices of `S`
can be joined by a path in `toQuiver A` whose active vertices all lie in `S`. -/
lemma path_exists_in_support_of_irreducible {A : Matrix n n ℝ}
    (S : Set n)
    (hS : IsIrreducible (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n)))
    (i j : n) (hi : i ∈ S) (hj : j ∈ S) :
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
    ∃ p : Quiver.Path i j, ∀ k, k ∈ p.activeVertices → k ∈ S := by
  letI : Quiver n := Matrix.toQuiver A
  letI : Quiver S := inducedQuiver S
  let i' : S := ⟨i, hi⟩
  let j' : S := ⟨j, hj⟩
  obtain ⟨p_sub, _hp_sub_pos⟩ := hS.connected i' j'
  have p_sub' : @Quiver.Path S (letI := Matrix.toQuiver A; inducedQuiver S) i' j' := by
    simpa [Matrix.toQuiver, Matrix.submatrix_apply] using p_sub
  obtain ⟨p, hp⟩ := path_in_submatrix_to_original S p_sub'
  exact ⟨p, hp⟩

/-! ### Positivity of matrix-vector products -/

lemma positive_mul_vec_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A.mulVec x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_univ]  --  `k ∈ Finset.univ`
    · exact mul_pos (hA_pos i k) hk_pos

variable {A : Matrix n n ℝ} --[DecidableEq n] [Nonempty n]

/-! ### Entrywise bounds for `1 + A` -/

/-- For a nonnegative real matrix `A`, every entry of `1 + A` is nonnegative. -/
lemma one_add_apply_nonneg [DecidableEq n] {A : Matrix n n ℝ} (h_nonneg : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ (1 + A) i j := by
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    linarith [h_nonneg i i]
  · simpa [Matrix.add_apply, Matrix.one_apply, h] using h_nonneg i j

/-- For a matrix with nonnegative diagonal, each diagonal entry of `1 + A` is strictly positive. -/
lemma one_add_diag_pos [DecidableEq n] {A : Matrix n n ℝ} (h_diag : ∀ i, 0 ≤ A i i) (i : n) :
    0 < (1 + A) i i := by
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  linarith [h_diag i]

/-- If `∑ j, f j = 0` and every `f j` is nonnegative, then `f j = 0` for all `j`. -/
lemma forall_eq_zero_of_finset_sum_eq_zero_of_nonneg {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h_nonneg : ∀ j, 0 ≤ f j) (hsum : ∑ j, f j = 0) (j : ι) : f j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h_nonneg k)).1 hsum j (Finset.mem_univ j)

/-- If `(A *ᵥ v) j = 0` and row `j` of `A` and `v` are nonnegative, then each product `A j k * v k`
is zero. -/
lemma mul_eq_zero_of_mulVec_eq_zero_of_row_nonneg [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (j k : n)
    (hAj : ∀ l, 0 ≤ A j l) (hv : ∀ l, 0 ≤ v l) (hAv : (A *ᵥ v) j = 0) :
    A j k * v k = 0 := by
  rw [mulVec, dotProduct] at hAv
  exact forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
    (fun l => mul_nonneg (hAj l) (hv l)) hAv k

/-- If `A *ᵥ v = r • v` and `v j = 0`, then `(A *ᵥ v) j = 0`. -/
lemma mulVec_apply_eq_zero_of_eigenvector_apply_eq_zero [Fintype n] {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (j : n) (h : A *ᵥ v = r • v) (hj : v j = 0) :
    (A *ᵥ v) j = 0 := by
  rw [congrFun h j, Pi.smul_apply, hj, smul_zero]

/-- If `A *ᵥ v = r • v` and `A *ᵥ w = r • w`, then `v - c • w` is again an `r`-eigenvector. -/
lemma mulVec_sub_smul_eq_smul_sub_of_mulVec_smul [Fintype n] {A : Matrix n n ℝ} {r c : ℝ} {v w : n → ℝ}
    (hv : A *ᵥ v = r • v) (hw : A *ᵥ w = r • w) :
    A *ᵥ (v - c • w) = r • (v - c • w) := by
  calc
    A *ᵥ (v - c • w) = A *ᵥ v - A *ᵥ (c • w) := by simp only [mulVec_sub]
    _ = r • v - c • (r • w) := by simp only [hv, mulVec_smul, hw]
    _ = r • v - r • (c • w) := by rw [smul_comm c r w]
    _ = r • (v - c • w) := by rw [← smul_sub]

/-- If row `i` of `A` is nonnegative, `v` is everywhere positive, and some `A i j` is positive,
then `(A *ᵥ v) i > 0`. -/
lemma mulVec_pos_of_exists_pos_mul_pos [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i j : n)
    (hA_nonneg : ∀ k, 0 ≤ A i k) (hv_pos : ∀ k, 0 < v k) (hij : 0 < A i j) :
    0 < (A *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hA_nonneg k) (hv_pos k).le
  · refine ⟨j, ?_, ?_⟩
    · simp
    · exact mul_pos hij (hv_pos j)

/-- If `a` is nonnegative and `f j ≤ f k` for all `j`, then `∑ j, a j * f j ≤ (∑ j, a j) * f k`. -/
lemma sum_mul_le_sum_mul_const_of_forall_le {ι : Type*} [Fintype ι] (a f : ι → ℝ) (k : ι)
    (ha : ∀ j, 0 ≤ a j) (hf : ∀ j, f j ≤ f k) :
    ∑ j, a j * f j ≤ (∑ j, a j) * f k := by
  calc
    ∑ j, a j * f j ≤ ∑ j, a j * f k := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j) (ha j)
    _ = (∑ j, a j) * f k := by rw [Finset.sum_mul]

/-- If row `i` of `A` is nonnegative and `c * w j ≤ v j` for every `j`, then
`c * (A *ᵥ w) i ≤ (A *ᵥ v) i`. -/
lemma mulVec_smul_le_mulVec_of_forall_smul_le [Fintype n] {A : Matrix n n ℝ} (i : n)
    (hA : ∀ j, 0 ≤ A i j) (c : ℝ) {v w : n → ℝ} (hle : ∀ j, c * w j ≤ v j) :
    c * (A *ᵥ w) i ≤ (A *ᵥ v) i := by
  simp_rw [mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    rw [← mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hle j) (hA j)

/-- A matrix with strictly positive entries sends every nonnegative nonzero vector to a strictly
positive vector. -/
lemma positive_mul_vec_of_nonneg_vec [Fintype n] (hA_pos : ∀ i j, 0 < A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < (A *ᵥ v) i := by
  simpa only [Matrix.mulVec] using
    positive_mul_vec_pos (A := A) hA_pos hv_nonneg hv_ne_zero

/-! ### Support and boundary edges -/

/-- For a nonnegative vector, any index outside the zero set has positive value. -/
lemma pos_of_nonneg_of_not_mem_zero_set {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) {i : n} (hi : i ∉ {j | v j = 0}) :
    0 < v i := by
  have hvi_ne_zero : v i ≠ 0 := by
    simpa using hi
  exact lt_of_le_of_ne (hv_nonneg i) (Ne.symm hvi_ne_zero)

/-- The positive support of a nonnegative nonzero vector is nonempty. -/
lemma pos_support_nonempty_of_nonneg_ne_zero {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ({i | 0 < v i} : Set n).Nonempty := by
  by_contra h_empty
  apply hv_ne_zero
  ext i
  have hi_not_pos : ¬ 0 < v i := by
    intro hi_pos
    exact h_empty ⟨i, hi_pos⟩
  exact le_antisymm (not_lt.mp hi_not_pos) (hv_nonneg i)

/-- Every nontrivial proper subset of vertices in the quiver of an irreducible matrix has an
outgoing positive edge. -/
lemma Irreducible.exists_edge_out {A : Matrix n n ℝ}
    (hA_irred : A.IsIrreducible)
    (S : Set n) (hS_ne_empty : S.Nonempty) (hS_ne_univ : S ≠ Set.univ) :
    ∃ (i : n) (_ : i ∈ S) (j : n) (_ : j ∉ S), 0 < A i j := by
  letI : Quiver n := toQuiver A
  obtain ⟨i, hi⟩ := hS_ne_empty
  obtain ⟨j, hj_compl⟩ := Set.nonempty_compl.mpr hS_ne_univ
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected i j
  have hj : j ∉ S := by simpa using hj_compl
  obtain ⟨u, v, e, _p₁, _p₂, hu_in_S, hv_not_in_S, _hp⟩ :=
    Quiver.Path.exists_boundary_edge_from_set p S hi hj
  exact ⟨u, hu_in_S, v, hv_not_in_S, e.down⟩

/-- Let `S = {i | 0 < v i}` and `T = {i | v i = 0}` for a nonnegative vector `v`. If `A` is
irreducible and both sets are nonempty, then there is a positive edge from `T` to `S`. -/
lemma exists_connecting_edge_of_irreducible {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S T : Set n) (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (h_partition : ∀ i, i ∈ S ↔ v i > 0)
    (h_complement : ∀ i, i ∈ T ↔ v i = 0) :
    ∃ (i j : n), i ∈ T ∧ j ∈ S ∧ 0 < A i j := by
  have hT_ne_univ : T ≠ Set.univ := by
    intro hT_univ
    obtain ⟨j, hj_S⟩ := hS_nonempty
    have hj_T : j ∈ T := by
      rw [hT_univ]
      simp
    exact (ne_of_gt ((h_partition j).mp hj_S)) ((h_complement j).mp hj_T)
  obtain ⟨i, hi_T, j, hj_not_T, hA_ij_pos⟩ :=
    Irreducible.exists_edge_out (A := A) hA_irred T hT_nonempty hT_ne_univ
  have hj_S : j ∈ S := by
    have hvj_ne_zero : v j ≠ 0 := by
      intro h_zero
      exact hj_not_T ((h_complement j).mpr h_zero)
    exact (h_partition j).mpr <| lt_of_le_of_ne (hv_nonneg j) (Ne.symm hvj_ne_zero)
  exact ⟨i, j, hi_T, hj_S, hA_ij_pos⟩

/-- If the `i`th entry of `A *ᵥ v` is zero and `v j` is positive, then `A i j = 0`. -/
lemma entry_eq_zero_of_mulVec_eq_zero [Fintype n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) {i j : n}
    (h_Av_i_zero : (A *ᵥ v) i = 0) (hv_j_pos : 0 < v j) :
    A i j = 0 := by
  have hmul := mul_eq_zero_of_mulVec_eq_zero_of_row_nonneg i j (fun l => hA_nonneg i l) hv_nonneg h_Av_i_zero
  exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hv_j_pos)

/-- A nonnegative matrix that annihilates a strictly positive vector is the zero matrix. -/
lemma eq_zero_of_mulVec_eq_zero_of_pos [Fintype n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (h_Av_zero : A *ᵥ v = 0) :
    A = 0 := by
  ext i j
  exact entry_eq_zero_of_mulVec_eq_zero (A := A) hA_nonneg (fun k => (hv_pos k).le)
    (by simpa using congrFun h_Av_zero i) (hv_pos j)

/-- A zero matrix is not irreducible if the dimension is greater than `1`. -/
lemma not_irreducible_of_zero_matrix {n : Type*} [Fintype n]
    (h_card_gt_one : 1 < Fintype.card n) :
    ¬ IsIrreducible (0 : Matrix n n ℝ) := by
  intro h
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h_card_gt_one
  obtain ⟨p, hp_pos⟩ := h.connected i j
  cases p with
  | nil => simp at hp_pos
  | cons p' e => exact (lt_irrefl (0 : ℝ)) e.down

/-- For an irreducible matrix on a one-element type, the diagonal entry is positive. -/
lemma irreducible_one_element_implies_diagonal_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_irred : IsIrreducible A)
    (h_card_one : Fintype.card n = 1) (i : n) :
    0 < A i i := by
  letI : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA_irred.connected i i
  obtain ⟨j, p', e, rfl⟩ := Quiver.Path.path_decomposition_last_edge p hp_pos
  have h_sub : Subsingleton n := by
    rcases (Fintype.card_eq_one_iff).1 h_card_one with ⟨a, ha⟩
    exact ⟨fun x y => by simp [ha x, ha y]⟩
  haveI : Subsingleton n := h_sub
  have hji : j = i := Subsingleton.elim _ _
  have e_pos : 0 < A j i := e.down
  simpa [hji] using e_pos

/-- Every row sum of an irreducible nonnegative matrix is strictly positive
(no zero row). -/
lemma row_sum_pos_of_irreducible_nonneg [Fintype n] [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : IsIrreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) (i : n) :
    0 < ∑ j, A i j := by
  rw [lt_iff_le_and_ne]
  refine ⟨Finset.sum_nonneg fun j _ => hA_nonneg i j, ?_⟩
  intro h0
  have h_sum0 : ∑ j, A i j = 0 := Eq.symm h0
  have h_zero_row : ∀ j, A i j = 0 := fun j =>
    forall_eq_zero_of_finset_sum_eq_zero_of_nonneg (fun k => hA_nonneg i k) h_sum0 j
  by_cases h_card_one : Fintype.card n = 1
  · exact lt_irrefl (0 : ℝ) <|
      (h_zero_row i).symm ▸ irreducible_one_element_implies_diagonal_pos hA_irred h_card_one i
  · have h_card_gt_one : 1 < Fintype.card n :=
      Nat.lt_of_le_of_ne (Nat.succ_le_iff.mpr Fintype.card_pos) (Ne.symm h_card_one)
    haveI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 h_card_gt_one
    obtain ⟨j, hj_pos⟩ := Matrix.IsIrreducible.exists_pos (A := A) hA_irred i
    exact lt_irrefl (0 : ℝ) <| (h_zero_row j).symm ▸ hj_pos

/-- An irreducible matrix cannot send a nonnegative nonzero vector to `0`. -/
theorem irreducible_mulVec_ne_zero [Fintype n]
    (hA_irred : IsIrreducible A)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    A *ᵥ v ≠ 0 := by
  by_contra h_Av_zero
  let T : Set n := {i | v i = 0}
  by_cases hT_is_empty : T = ∅
  · have v_all_pos : ∀ i, v i > 0 := by
      intro i
      have hi_not_in_T : i ∉ T := by simp [hT_is_empty]
      exact pos_of_nonneg_of_not_mem_zero_set hv_nonneg (by simpa [T] using hi_not_in_T)
    have hA_eq_zero :=
      eq_zero_of_mulVec_eq_zero_of_pos (A := A) (hA_nonneg := hA_irred.1) v_all_pos h_Av_zero
    have h0_irred : IsIrreducible (0 : Matrix n n ℝ) := by
      simpa [hA_eq_zero] using hA_irred
    obtain ⟨i₀, hi₀⟩ := pos_support_nonempty_of_nonneg_ne_zero hv_nonneg hv_ne_zero
    letI : Nonempty n := ⟨i₀⟩
    have h_card_pos : 0 < Fintype.card n := Fintype.card_pos
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt h_card_pos) with h_card_one | h_card_gt_one
    · simpa using
        irreducible_one_element_implies_diagonal_pos (A := (0 : Matrix n n ℝ)) h0_irred
          h_card_one.symm i₀
    · exact not_irreducible_of_zero_matrix h_card_gt_one h0_irred
  · have hT_nonempty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hT_is_empty
    have hT_ne_univ : T ≠ Set.univ := by
      intro hT_univ
      obtain ⟨i, hi_pos⟩ := pos_support_nonempty_of_nonneg_ne_zero hv_nonneg hv_ne_zero
      have hi_zero : v i = 0 := by
        have : i ∈ T := by
          simp [hT_univ]
        simpa [T] using this
      exact hi_pos.ne' hi_zero
    obtain ⟨i, hi_T, j, hj_not_T, hA_ij_pos⟩ :=
      Irreducible.exists_edge_out (A := A) hA_irred T hT_nonempty hT_ne_univ
    have hA_ij_zero : A i j = 0 := by
      have hv_j_pos : v j > 0 := by
        exact pos_of_nonneg_of_not_mem_zero_set hv_nonneg (by simpa [T] using hj_not_T)
      exact entry_eq_zero_of_mulVec_eq_zero (A := A) (hA_nonneg := hA_irred.1) hv_nonneg
        (by simpa using congrFun h_Av_zero i) hv_j_pos
    exact (ne_of_gt hA_ij_pos) hA_ij_zero

/-- An irreducible matrix with a positive diagonal is primitive. -/
theorem IsPrimitive.of_irreducible_pos_diagonal [Fintype n] [Nonempty n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_irred : IsIrreducible A) (hA_diag_pos : ∀ i, 0 < A i i) :
    IsPrimitive A := by
  let N := Fintype.card n
  let k := (N - 1) * N + 1
  have hk_pos : 0 < k := by
    have h_card_pos : 0 < N := Fintype.card_pos
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt h_card_pos) with hN | hN_lt
    · simp_all only [le_refl, tsub_self, List.Nat.eq_of_le_zero, zero_mul, zero_add, N, k]
    · omega
  constructor
  · exact hA_nonneg
  · use k, hk_pos
    intro i j
    letI : Quiver n := toQuiver A
    rw [Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i j]
    obtain ⟨p_any, _hp_any_pos⟩ := hA_irred.connected i j
    obtain ⟨p_ij, hp_len_le⟩ :=
      Quiver.Path.exists_path_length_le_card_sub_one (a := i) (b := j) ⟨p_any⟩
    let p_loop : Path i i :=
      Quiver.Hom.toPath (⟨hA_diag_pos i⟩ : @Quiver.Hom n (toQuiver A) i i)
    have hp_loop_len : p_loop.length = 1 := by
      simp [p_loop]
    have hp_len_le_k : p_ij.length ≤ k := by
      have h_card_ge_one : 1 ≤ N := Nat.one_le_of_lt Fintype.card_pos
      have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one h_card_ge_one
      have hk_ge : N - 1 ≤ k := by
        dsimp [k]
        calc
          N - 1 ≤ (N - 1) * N := by
            simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (N - 1) hN_pos
          _ ≤ (N - 1) * N + 1 := Nat.le_succ _
      exact le_trans hp_len_le hk_ge
    refine ⟨⟨(Path.replicate (k - p_ij.length) p_loop).comp p_ij, ?_⟩⟩
    rw [Path.length_comp, Path.length_replicate, hp_loop_len, mul_one,
      Nat.sub_add_cancel hp_len_le_k]

/-! ### Right eigenvectors and matrix powers -/

section MulVecPow

variable {R : Type*} [CommSemiring R] {n : Type*} [Fintype n] [DecidableEq n]
  {A : Matrix n n R} {r : R} {v : n → R}

/-- If `A *ᵥ v = r • v`, then `(A ^ m) *ᵥ v = (r ^ m) • v` for every `m : ℕ`. -/
lemma mulVec_pow_eq_smul_pow_of_mulVec_smul (h : A *ᵥ v = r • v) (m : ℕ) :
    (A ^ m) *ᵥ v = (r ^ m) • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      (A ^ m.succ) *ᵥ v = (A ^ m * A) *ᵥ v := by simp [pow_succ]
      _ = A ^ m *ᵥ (A *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = A ^ m *ᵥ (r • v) := by rw [h]
      _ = r • (A ^ m *ᵥ v) := by rw [mulVec_smul]
      _ = r • (r ^ m • v) := by rw [ih]
      _ = r ^ (m + 1) • v := by simp [pow_succ', smul_smul]

end MulVecPow

section MulVecPowMap

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] {n : Type*} [Fintype n]
  [DecidableEq n] (f : R →+* S) {A : Matrix n n R} {μ : S} {v : n → S}

/-- If `(A.map f) *ᵥ v = μ • v`, then `((A ^ m).map f) *ᵥ v = (μ ^ m) • v` for every `m`. -/
lemma mulVec_map_pow_eq_smul_pow_of_mulVec_map_smul
    (h : (A.map f) *ᵥ v = μ • v) (m : ℕ) :
    ((A ^ m).map f) *ᵥ v = (μ ^ m) • v := by
  induction m with
  | zero => simp [pow_zero, Matrix.map_one, one_mulVec, one_smul]
  | succ m ih =>
    calc
      ((A ^ (m + 1)).map f) *ᵥ v = ((A * A ^ m).map f) *ᵥ v := by simp [pow_succ']
      _ = ((A.map f) * ((A ^ m).map f)) *ᵥ v := by rw [Matrix.map_mul]
      _ = (A.map f) *ᵥ (((A ^ m).map f) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = (A.map f) *ᵥ ((μ ^ m) • v) := by rw [ih]
      _ = (μ ^ m) • ((A.map f) *ᵥ v) := by rw [mulVec_smul]
      _ = (μ ^ m) • (μ • v) := by rw [h]
      _ = ((μ ^ m) * μ) • v := by rw [smul_smul]
      _ = (μ ^ (m + 1)) • v := by rw [← pow_succ]

end MulVecPowMap

section ShiftAndMap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `v` is an `r`-eigenvector for `A`, then it is an `(r + 1)`-eigenvector for `1 + A`. -/
lemma toLin'_one_add_eigenvector {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : toLin' A v = r • v) :
    toLin' (1 + A) v = (r + 1) • v := by
  simp [LinearMap.add_apply, toLin'_one, add_smul, one_smul, h, add_comm]

/-- A real eigenvector equation, coerced to the complexified matrix. -/
lemma mulVec_map_complex_of_real_eigenvector {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : toLin' A v = r • v) :
    (A.map (algebraMap ℝ ℂ)) *ᵥ (fun i => (v i : ℂ)) =
      (r : ℂ) • fun i => (v i : ℂ) := by
  ext i
  have h_real : ∑ j, A i j * v j = r * v i := by
    have := congr_fun (by simpa [toLin'_apply, Pi.smul_apply] using h) i
    simpa [Matrix.mulVec, dotProduct] using this
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) h_real

end ShiftAndMap

end PerronFrobenius

end Matrix

#lint