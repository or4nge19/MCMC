/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import MCMC.PF.Combinatorics.Quiver.Path

/-!
# Perron-Frobenius support lemmas

This file collects auxiliary lemmas used in the Perron-Frobenius development for irreducible and
primitive nonnegative real matrices. The results connect `Matrix.IsIrreducible` and
`Matrix.IsPrimitive` to the quiver `Matrix.toQuiver A`.

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

-/

namespace Matrix
section PerronFrobenius
open Matrix Finset Quiver Quiver.Path
variable {n : Type*}

/-! ### Paths in induced subquivers -/

/-- A path in the submatrix `A.submatrix Subtype.val Subtype.val` lifts to a path in the
original quiver `toQuiver A`, and all vertices along that lifted path lie in `S`. -/
private theorem path_in_submatrix_to_original [DecidableEq n] {A : Matrix n n ℝ}
  (S : Set n) [DecidablePred S]
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
theorem path_exists_in_support_of_irreducible [DecidableEq n] {A : Matrix n n ℝ}
    (S : Set n) [DecidablePred S]
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

private lemma positive_mul_vec_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A.mulVec x) i := by
  intro i
  --  `A.mulVec x i = ∑ j, A i j * x j`
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

/-- A matrix with strictly positive entries sends every nonnegative nonzero vector to a strictly
positive vector. -/
theorem positive_mul_vec_of_nonneg_vec [Fintype n] (hA_pos : ∀ i j, 0 < A i j)
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
lemma pos_support_nonempty_of_nonneg_ne_zero [Fintype n] {v : n → ℝ}
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
  exact ⟨u, hu_in_S, v, hv_not_in_S, e⟩

/-- Let `S = {i | 0 < v i}` and `T = {i | v i = 0}` for a nonnegative vector `v`. If `A` is
irreducible and both sets are nonempty, then there is a positive edge from `T` to `S`. -/
theorem exists_connecting_edge_of_irreducible {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
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
  rw [mulVec, dotProduct] at h_Av_i_zero
  have h_terms_nonneg : ∀ k ∈ Finset.univ, 0 ≤ A i k * v k := by
    intro k _
    exact mul_nonneg (hA_nonneg i k) (hv_nonneg k)
  have h_term_zero :=
    (Finset.sum_eq_zero_iff_of_nonneg h_terms_nonneg).mp h_Av_i_zero j (Finset.mem_univ _)
  exact (mul_eq_zero.mp h_term_zero).resolve_right (ne_of_gt hv_j_pos)

/-- A nonnegative matrix that annihilates a strictly positive vector is the zero matrix. -/
lemma eq_zero_of_mulVec_eq_zero_of_pos [Fintype n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (h_Av_zero : A *ᵥ v = 0) :
    A = 0 := by
  ext i j
  exact entry_eq_zero_of_mulVec_eq_zero (A := A) hA_nonneg (fun k => (hv_pos k).le)
    (by simpa using congrFun h_Av_zero i) (hv_pos j)

/-- A zero matrix is not irreducible if the dimension is greater than `1`. -/
private lemma not_irreducible_of_zero_matrix {n : Type*} [Fintype n] [Nonempty n]
    (h_card_gt_one : 1 < Fintype.card n) :
    ¬ IsIrreducible (0 : Matrix n n ℝ) := by
  intro h
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h_card_gt_one
  obtain ⟨p, hp_pos⟩ := h.connected i j
  cases p with
  | nil => simp at hp_pos
  | cons p' e => exact (lt_irrefl (0 : ℝ)) e

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
  have e_pos : 0 < A j i := e
  simpa [hji] using e_pos

/-- An irreducible matrix cannot send a nonnegative nonzero vector to `0`. -/
theorem irreducible_mulVec_ne_zero [DecidableEq n] [Fintype n]
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
    let p_loop : Path i i := (show i ⟶ i from hA_diag_pos i).toPath
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
