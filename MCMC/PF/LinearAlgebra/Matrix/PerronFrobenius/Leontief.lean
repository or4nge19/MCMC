import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Dominance

/-!
# Leontief systems and Hawkins-Simon criteria

This file starts a Chapter 2 style formalization of Seneta's treatment of Leontief systems
`(s • 1 - A) *ᵥ x = c`, using the matrix resolvent.
-/

namespace Matrix

open scoped BigOperators
open Filter Topology CollatzWielandt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-
This file uses the existing algebraic `resolvent` from mathlib, specialized to the matrix algebra.
-/

/-- The finite Neumann sums approximating the resolvent. -/
noncomputable def resolventPartialSums (A : Matrix n n ℝ) (s : ℝ) (N : ℕ) :
    Matrix n n ℝ :=
  Finset.sum (Finset.range N) fun k => s⁻¹ • ((s⁻¹ • A) ^ k)

@[simp] theorem resolventPartialSums_zero (A : Matrix n n ℝ) (s : ℝ) :
    Matrix.resolventPartialSums A s 0 = 0 := by
  simp [Matrix.resolventPartialSums]

private theorem resolventPartialSums_succ (A : Matrix n n ℝ) (s : ℝ) (N : ℕ) :
    Matrix.resolventPartialSums A s (N + 1) =
      Matrix.resolventPartialSums A s N + s⁻¹ • ((s⁻¹ • A) ^ N) := by
  simp [Matrix.resolventPartialSums, Finset.sum_range_succ]

private lemma resolventPartialSums_le_succ
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} (hs_pos : 0 < s)
    (N : ℕ) (i j : n) :
    Matrix.resolventPartialSums A s N i j ≤ Matrix.resolventPartialSums A s (N + 1) i j := by
  rw [resolventPartialSums_succ]
  rw [Matrix.add_apply]
  exact le_add_of_nonneg_right <|
    mul_nonneg (inv_nonneg.mpr hs_pos.le) <|
      pow_entrywise_nonneg
        (fun i j => mul_nonneg (inv_nonneg.mpr hs_pos.le) (hA_nonneg i j)) N i j

/-- Entrywise, the finite Neumann sums are monotone for nonnegative matrices and positive `s`. -/
private lemma monotone_resolventPartialSums_apply
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} (hs_pos : 0 < s)
    (i j : n) :
    Monotone fun N : ℕ => Matrix.resolventPartialSums A s N i j :=
  monotone_nat_of_le_succ fun N => resolventPartialSums_le_succ hA_nonneg hs_pos N i j

/-- The finite Neumann resolvent partial sums are entrywise nonnegative in the productive regime. -/
private lemma resolventPartialSums_nonneg
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} (hs_pos : 0 < s)
    (N : ℕ) :
    ∀ i j, 0 ≤ Matrix.resolventPartialSums A s N i j := by
  intro i j
  simp only [resolventPartialSums, Matrix.sum_apply]
  refine Finset.sum_nonneg ?_
  intro k _
  exact mul_nonneg (inv_nonneg.mpr hs_pos.le) <|
    pow_entrywise_nonneg
      (fun i j => mul_nonneg (inv_nonneg.mpr hs_pos.le) (hA_nonneg i j)) k i j

/-- Perron-root domination gives positivity of the scalar in the finite Neumann sums. -/
private lemma resolventPartialSums_nonneg_of_perronRoot_lt
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot A < s) (N : ℕ) :
    ∀ i j, 0 ≤ Matrix.resolventPartialSums A s N i j := by
  have hs_pos : 0 < s := lt_of_le_of_lt (perronRoot_nonneg hA_nonneg) hs
  exact resolventPartialSums_nonneg hA_nonneg hs_pos N

/-- Irreducibility gives a strictly positive term in each entry of the Neumann partial sums. -/
private lemma exists_pos_resolventPartialSums_of_irreducible
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ} (hs_pos : 0 < s)
    (i j : n) :
    ∃ N, 0 < Matrix.resolventPartialSums A s N i j := by
  letI : Quiver n := Matrix.toQuiver A
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected i j
  refine ⟨p.length + 1, ?_⟩
  simp only [resolventPartialSums, Matrix.sum_apply]
  refine Finset.sum_pos' ?_ ?_
  · intro k _
    exact mul_nonneg (inv_nonneg.mpr hs_pos.le) <|
      pow_entrywise_nonneg
        (fun i j => mul_nonneg (inv_nonneg.mpr hs_pos.le) (hA_irred.nonneg i j)) k i j
  · refine ⟨p.length, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    have hpow_pos : 0 < (A ^ p.length) i j := by
      rw [Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_irred.nonneg p.length i j]
      exact ⟨⟨p, rfl⟩⟩
    have hscaled_pow_pos : 0 < ((s⁻¹ • A) ^ p.length) i j := by
      rw [smul_pow]
      exact mul_pos (pow_pos (inv_pos.mpr hs_pos) _) hpow_pos
    exact mul_pos (inv_pos.mpr hs_pos) hscaled_pow_pos

/--
Neumann-series expansion of the resolvent in the productive regime `perronRoot A < s`.

This is the analytic bridge still to be proved: it should ultimately follow from a Neumann-series
or spectral-radius argument, rather than bespoke entrywise manipulation.
-/
theorem tendsto_resolventPartialSums
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot A < s) :
    Tendsto (fun N : ℕ => Matrix.resolventPartialSums A s N) atTop
      (nhds (resolvent A s)) := by
  sorry

/-- Entrywise form of `tendsto_resolventPartialSums`. -/
theorem tendsto_resolventPartialSums_apply
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot A < s) (i j : n) :
    Tendsto (fun N : ℕ => Matrix.resolventPartialSums A s N i j) atTop
      (nhds (resolvent A s i j)) := by
  have h_matrix := Matrix.tendsto_resolventPartialSums (A := A) hA_nonneg hs
  have h_eval : Continuous fun M : Matrix n n ℝ => M i j := by
    simpa using ((continuous_apply j).comp (continuous_apply i))
  exact (h_eval.tendsto _).comp h_matrix

/--
If the Perron root lies strictly below `s`, the resolvent is entrywise nonnegative.
This is the matrix-valued Neumann positivity statement.
-/
theorem resolvent_nonneg_of_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot A < s) :
    ∀ i j, 0 ≤ resolvent A s i j := by
  intro i j
  have h_tendsto :
      Tendsto (fun N : ℕ => Matrix.resolventPartialSums A s N i j) atTop
        (nhds (resolvent A s i j)) := by
    exact tendsto_resolventPartialSums_apply hA_nonneg hs i j
  exact ge_of_tendsto h_tendsto <|
    Filter.Eventually.of_forall fun N =>
      resolventPartialSums_nonneg_of_perronRoot_lt hA_nonneg hs N i j

/--
In the productive regime, irreducibility upgrades nonnegativity of the resolvent to strict
entrywise positivity.
-/
theorem resolvent_pos_of_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ}
    (hs : perronRoot A < s) :
    ∀ i j, 0 < resolvent A s i j := by
  intro i j
  have hA_nonneg : ∀ i j, 0 ≤ A i j := hA_irred.nonneg
  have hs_pos : 0 < s := lt_of_le_of_lt (perronRoot_nonneg hA_nonneg) hs
  obtain ⟨N, hN_pos⟩ :=
    exists_pos_resolventPartialSums_of_irreducible hA_irred hs_pos i j
  have h_tendsto :
      Tendsto (fun M : ℕ => Matrix.resolventPartialSums A s M i j) atTop
        (nhds (resolvent A s i j)) := by
    exact tendsto_resolventPartialSums_apply hA_nonneg hs i j
  have h_lower : Matrix.resolventPartialSums A s N i j ≤ resolvent A s i j := by
    exact ge_of_tendsto h_tendsto <|
      Filter.eventually_atTop.2 ⟨N, fun M hNM =>
        monotone_resolventPartialSums_apply hA_nonneg hs_pos i j hNM⟩
  exact lt_of_lt_of_le hN_pos h_lower

private lemma resolvent_eq_nonsing_inv (A : Matrix n n ℝ) (s : ℝ) :
    resolvent A s = (s • (1 : Matrix n n ℝ) - A)⁻¹ := by
  dsimp [resolvent]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

private lemma isUnit_det_sub_of_resolvent_pos
    [Nonempty n]
    {A : Matrix n n ℝ} {s : ℝ} (h_pos : ∀ i j, 0 < resolvent A s i j) :
    IsUnit (s • (1 : Matrix n n ℝ) - A).det := by
  by_contra hnot
  have hres_zero : resolvent A s = 0 := by
    rw [resolvent_eq_nonsing_inv, Matrix.inv_def, Ring.inverse_non_unit _ hnot]
    simp
  obtain ⟨i, _⟩ := Finset.univ_nonempty (α := n)
  have hi_pos := h_pos i i
  simp [hres_zero] at hi_pos

/--
For an irreducible nonnegative matrix, entrywise positivity of the resolvent forces the
strict productivity inequality `perronRoot A < s`.
-/
theorem perronRoot_lt_of_resolvent_pos
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ}
    (h_pos : ∀ i j, 0 < resolvent A s i j) :
    perronRoot A < s := by
  let M : Matrix n n ℝ := s • (1 : Matrix n n ℝ) - A
  let R : Matrix n n ℝ := resolvent A s
  have hR_eq : R = M⁻¹ := by
    simpa [R, M] using resolvent_eq_nonsing_inv A s
  have hM_det_unit : IsUnit M.det := by
    simpa [M] using isUnit_det_sub_of_resolvent_pos (A := A) (s := s) h_pos
  obtain ⟨r, v, _hr_pos, hv_pos, hv_eig, hr_eq⟩ :=
    perron_root_eq_positive_eigenvalue hA_irred hA_irred.nonneg
  let y : n → ℝ := R *ᵥ v
  have hy_pos : ∀ i, 0 < y i := by
    intro i
    dsimp [y]
    rw [Matrix.mulVec]
    exact Finset.sum_pos (fun j _ => mul_pos (h_pos i j) (hv_pos j)) Finset.univ_nonempty
  have hR_M : R * M = 1 := by
    rw [hR_eq]
    exact Matrix.nonsing_inv_mul M hM_det_unit
  have hM_v : M *ᵥ v = (s - r) • v := by
    dsimp [M]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv_eig]
    ext i
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hR_M_v : R *ᵥ (M *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec]
    rw [hR_M]
    simp
  have hscale_y : (s - r) • y = v := by
    dsimp [y]
    rw [← Matrix.mulVec_smul]
    rw [← hM_v]
    exact hR_M_v
  have hs_sub_pos : 0 < s - r := by
    obtain ⟨i, _⟩ := Finset.univ_nonempty (α := n)
    have hcomp := congr_fun hscale_y i
    have hyi := hy_pos i
    have hvi := hv_pos i
    rw [Pi.smul_apply] at hcomp
    change (s - r) * y i = v i at hcomp
    exact (mul_pos_iff_of_pos_right hyi).mp (by rw [hcomp]; exact hvi)
  rw [hr_eq]
  linarith

/--
For an irreducible nonnegative matrix, entrywise positivity of the resolvent exactly detects the
strict inequality `perronRoot A < s`.
-/
theorem resolvent_pos_iff_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ} :
    (∀ i j, 0 < resolvent A s i j) ↔ perronRoot A < s := by
  constructor
  · exact perronRoot_lt_of_resolvent_pos hA_irred
  · exact resolvent_pos_of_perronRoot_lt hA_irred

/--
Leontief-Seneta positivity criterion:
for an irreducible nonnegative matrix, solvability of the Leontief system by a strictly positive
vector for every strictly positive demand vector forces strict productivity.
-/
theorem perronRoot_lt_of_exists_unique_pos_solution
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ}
    (h_solve : ∀ c : n → ℝ, (∀ i, 0 < c i) →
      ∃! x : n → ℝ, (∀ i, 0 < x i) ∧ (s • (1 : Matrix n n ℝ) - A) *ᵥ x = c) :
    perronRoot A < s := by
  let c : n → ℝ := fun _ => 1
  have hc_pos : ∀ i, 0 < c i := by
    intro i
    simp [c]
  obtain ⟨x, hx_prop, _hx_unique⟩ := h_solve c hc_pos
  have hx_pos : ∀ i, 0 < x i := hx_prop.1
  have hx_eq : (s • (1 : Matrix n n ℝ) - A) *ᵥ x = c := hx_prop.2
  obtain ⟨u, hu_pos, hu_left_eig⟩ :=
    exists_positive_left_perron_eigenvector hA_irred hA_irred.nonneg
  have h_sub_eq : s • x - A *ᵥ x = c := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hx_eq
  have hA_lt : ∀ i, (A *ᵥ x) i < (s • x) i := by
    intro i
    have hi := congr_fun h_sub_eq i
    have hc := hc_pos i
    rw [Pi.sub_apply] at hi
    linarith
  have h_dot_lt : u ⬝ᵥ (A *ᵥ x) < u ⬝ᵥ (s • x) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (le_of_lt (hA_lt i)) (le_of_lt (hu_pos i))
    · obtain ⟨i, _⟩ := Finset.univ_nonempty (α := n)
      refine ⟨i, Finset.mem_univ i, ?_⟩
      exact mul_lt_mul_of_pos_left (hA_lt i) (hu_pos i)
  rw [dotProduct_mulVec, hu_left_eig, dotProduct_smul_left, dotProduct_smul] at h_dot_lt
  have h_dot_pos : 0 < u ⬝ᵥ x := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hu_pos i) (hx_pos i)
    · exact Finset.univ_nonempty
  exact lt_of_mul_lt_mul_right h_dot_lt h_dot_pos.le

/--
Leontief-Seneta positivity criterion:
for an irreducible nonnegative matrix, strict productivity is equivalent to solvability of the
Leontief system by a strictly positive vector for every strictly positive demand vector.
-/
theorem exists_unique_pos_solution_iff_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ} :
    (∀ c : n → ℝ, (∀ i, 0 < c i) →
      ∃! x : n → ℝ, (∀ i, 0 < x i) ∧ (s • (1 : Matrix n n ℝ) - A) *ᵥ x = c) ↔
      perronRoot A < s := by
  constructor
  · exact perronRoot_lt_of_exists_unique_pos_solution hA_irred
  · intro hs c hc_pos
    let M : Matrix n n ℝ := s • (1 : Matrix n n ℝ) - A
    let R : Matrix n n ℝ := resolvent A s
    let x : n → ℝ := R *ᵥ c
    have hR_pos : ∀ i j, 0 < R i j := by
      intro i j
      exact resolvent_pos_of_perronRoot_lt hA_irred hs i j
    have hx_pos : ∀ i, 0 < x i := by
      intro i
      dsimp [x]
      rw [Matrix.mulVec]
      exact Finset.sum_pos (fun j _ => mul_pos (hR_pos i j) (hc_pos j)) Finset.univ_nonempty
    have hR_eq : R = M⁻¹ := by
      simpa [R, M] using resolvent_eq_nonsing_inv A s
    have hM_det_unit : IsUnit M.det := by
      simpa [M, R] using isUnit_det_sub_of_resolvent_pos (A := A) (s := s) hR_pos
    have hM_R : M * R = 1 := by
      rw [hR_eq]
      exact Matrix.mul_nonsing_inv M hM_det_unit
    have hR_M : R * M = 1 := by
      rw [hR_eq]
      exact Matrix.nonsing_inv_mul M hM_det_unit
    have hx_eq : M *ᵥ x = c := by
      dsimp [x]
      rw [Matrix.mulVec_mulVec, hM_R]
      simp
    refine ⟨x, ⟨hx_pos, by simpa [M] using hx_eq⟩, ?_⟩
    intro y hy_prop
    have hy_eq : M *ᵥ y = c := by
      simpa [M] using hy_prop.2
    calc
      y = R *ᵥ (M *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hR_M]
        simp
      _ = R *ᵥ c := by rw [hy_eq]
      _ = x := by rfl

/--
Coordinate-free Hawkins-Simon statement: all principal minors of `s I - A` are positive exactly in
the strictly productive regime.
-/
theorem perronRoot_lt_iff_principalMinors_pos
    {m : ℕ} [Nonempty (Fin m)]
    {A : Matrix (Fin m) (Fin m) ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} :
    perronRoot A < s ↔
      ∀ {k : ℕ} (e : Fin k ↪ Fin m),
        0 < Matrix.det ((s • (1 : Matrix (Fin m) (Fin m) ℝ) - A).submatrix e e) := by
  sorry

end Matrix
