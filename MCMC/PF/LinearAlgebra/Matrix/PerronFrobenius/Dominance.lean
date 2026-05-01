import Mathlib.Analysis.Normed.Algebra.Spectrum
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import MCMC.PF.Analysis.CstarAlgebra.Classes

open Quiver.Path
namespace Matrix
open CollatzWielandt

open Quiver
open Matrix Complex
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] in
/-- A complex number with norm `1` is nonzero. -/
lemma _root_.Complex.ne_zero_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c ≠ 0 := by
  rintro rfl
  norm_num at hc

omit [Fintype n] [DecidableEq n] in
/-- Cancel a nonzero scalar multiplying two dependent functions over a division ring. -/
lemma _root_.Pi.smul_left_cancel₀ {ι 𝕜 : Type*} [DivisionRing 𝕜] {c : 𝕜}
    (hc : c ≠ 0) {v w : ι → 𝕜} (h : c • v = c • w) :
    v = w := by
  ext i
  exact mul_left_cancel₀ hc <| by
    simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h i

omit [Fintype n] [DecidableEq n] in
/-- If `x : n → ℂ` is nonzero, then `fun i ↦ ‖x i‖` is nonzero as a dependent function. -/
lemma normFun_complex_ne_zero_of_ne_zero {x : n → ℂ} (hx : x ≠ 0) : (fun i ↦ ‖x i‖) ≠ 0 := by
  contrapose! hx
  ext i
  exact norm_eq_zero.mp (congr_fun hx i)

/-- Reconstruct `z : ℂ` from its phase `z / ‖z‖` and its modulus `‖z‖` (as a real coercion). -/
lemma eq_mul_div_ofReal_norm_complex (z : ℂ) (hz : ‖z‖ ≠ 0) :
    z = (z / (↑‖z‖ : ℂ)) * (↑‖z‖ : ℂ) := by
  have hn : (↑‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz
  exact (div_mul_cancel₀ z hn).symm

omit [Fintype n] [DecidableEq n] in
/-- If a property `P` holds for at least one vertex `i₀` and propagates along the edges
of an irreducible matrix's graph (`P i ∧ A i j > 0 → P j`), then `P` holds for all vertices. -/
lemma IsIrreducible.eq_univ_of_propagate (hA_irred : A.IsIrreducible) (P : n → Prop)
    (h_nonempty : ∃ i₀, P i₀)
    (h_propagate : ∀ i j, P i → 0 < A i j → P j) :
    ∀ i, P i := by
  let S : Set n := {i | P i}
  let T : Set n := {i | ¬ P i}
  by_contra h_not_all
  push_neg at h_not_all
  have hS_nonempty : (S : Set n).Nonempty := h_nonempty
  have hT_nonempty : (T : Set n).Nonempty := h_not_all
  have hS_ne_univ : (S : Set n) ≠ Set.univ := by
    intro h_eq
    rcases hT_nonempty with ⟨i, hi_T⟩
    have hPi : P i := by
      have : i ∈ S := by
        rw [h_eq]
        exact Set.mem_univ i
      simpa [S] using this
    exact hi_T hPi
  obtain ⟨i, hi_S, j, hj_not_S, hAij_pos⟩ :=
    Matrix.Irreducible.exists_edge_out (A := A) hA_irred S hS_nonempty hS_ne_univ
  have hPi : P i := by
    simpa [S] using hi_S
  have hPj : P j := h_propagate i j hPi hAij_pos
  exact hj_not_S (by
    simpa [S] using hPj)

omit [DecidableEq n] in
/-- For an irreducible, non-negative matrix `A`, if `v` is an eigenvector for an eigenvalue `μ`,
then the vector `w` of absolute values of `v` satisfies the inequality `|μ| • w ≤ A *ᵥ w`.
This is a key step in the Perron-Frobenius theorem. -/
lemma abs_eigenvector_inequality
  (hA_nonneg : ∀ i j, 0 ≤ A i j)
  {μ : ℝ} {v : n → ℝ} (h_eig : A *ᵥ v = μ • v) :
  let w := fun i ↦ |v i|; |μ| • w ≤ A *ᵥ w := by
  intro w i
  calc
    (|μ| • w) i = |μ| * |v i| := by simp [w]
    _ = |μ * v i| := by rw [abs_mul]
    _ = |(μ • v) i| := by simp
    _ = |(A *ᵥ v) i| := by rw [← h_eig]
    _ = |∑ j, A i j * v j| := by simp [mulVec, dotProduct]
    _ ≤ ∑ j, |A i j * v j| := by exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (A i j) * |v j| := by simp_rw [abs_mul, abs_of_nonneg (hA_nonneg i _)]
    _ = (A *ᵥ w) i := by simp [w, mulVec, dotProduct]

omit [DecidableEq n] in
/--
If the triangle equality holds for the complex eigenvector equation `A * x = lam * x`,
then the vector of norms `‖x‖` is a real eigenvector of `A` with eigenvalue `‖lam‖`.
-/
lemma norm_eigenvector_is_eigenvector_of_triangle_eq
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {lam : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = lam • x)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
    A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖) := by
  funext i
  calc
    (A *ᵥ fun i => ‖x i‖) i
        = ∑ j, A i j * ‖x j‖ := by simp [mulVec_apply]
    _   = ∑ j, ‖(A i j : ℂ)‖ * ‖x j‖ := by simp_rw [Complex.norm_ofReal, abs_of_nonneg (hA_nonneg _ _)]
    _   = ∑ j, ‖(A i j : ℂ) * x j‖ := by simp_rw [norm_mul]
    _   = ‖∑ j, (A i j : ℂ) * x j‖ := (h_triangle_eq i).symm
    _   = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by simp; rfl
    _   = ‖(lam • x) i‖ := by rw [hx_eig]
    _   = ‖lam * x i‖ := by rw [Pi.smul_apply]; rfl
    _   = ‖lam‖ * ‖x i‖ := by rw [norm_mul]
    _   = ((‖lam‖ : ℝ) • fun i => ‖x i‖) i := by simp [smul_eq_mul]

/-! ### Norm sums

`Finset`/`Fintype` vanishing for sums of complex norms, and a consequence of global
triangle equality. -/

lemma norm_eq_zero_of_finset_sum_norm_eq_zero {ι : Type*} {s : Finset ι} (v : ι → ℂ)
    (h : ∑ i ∈ s, ‖v i‖ = 0) (i : ι) (hi : i ∈ s) : ‖v i‖ = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg (v j))).1 h i hi

lemma norm_eq_zero_of_fintype_sum_norm_eq_zero {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (h : ∑ i, ‖v i‖ = 0) (i : ι) : ‖v i‖ = 0 :=
  norm_eq_zero_of_finset_sum_norm_eq_zero v h i (Finset.mem_univ i)

/-- Triangle equality and one nonzero term imply the complex sum is nonzero. -/
lemma Fintype.sum_ne_zero_of_triangle_norm_exists_nonzero {ι : Type*} [Fintype ι] {v : ι → ℂ}
    (hτ : ‖∑ i, v i‖ = ∑ i, ‖v i‖) {j : ι} (hj : v j ≠ 0) : ∑ i, v i ≠ 0 := by
  intro hsum0
  have h_norms : ∑ i, ‖v i‖ = 0 := by rw [← hτ, hsum0, norm_zero]
  exact hj <| norm_eq_zero.mp (norm_eq_zero_of_fintype_sum_norm_eq_zero v h_norms j)

omit [DecidableEq n] in
/--
If equality holds in the triangle inequality for `∑ z_j`, then all non-zero `z_j`
are aligned with the sum.
-/
lemma aligned_of_all_nonneg_re_im
    {A : Matrix n n ℝ} {i : n} {x : n → ℂ}
    (h_sum_eq : ‖∑ j, (A i j : ℂ) * x j‖ =
                ∑ j, ‖(A i j : ℂ) * x j‖) :
    ∀ j, (A i j : ℂ) * x j ≠ 0 →
      ∃ c : ℝ, 0 ≤ c ∧
        (A i j : ℂ) * x j = c • (∑ k, (A i k : ℂ) * x k) := by
  let z : n → ℂ := fun j => (A i j : ℂ) * x j
  let s : ℂ     := ∑ j, z j
  have h_z_sum : ‖s‖ = ∑ j, ‖z j‖ := by
    simpa [z, s] using h_sum_eq
  intro j hz_ne_zero
  have hs_ne_zero : s ≠ 0 := by
    simpa [s] using Fintype.sum_ne_zero_of_triangle_norm_exists_nonzero
      (show ‖∑ j : n, z j‖ = ∑ j : n, ‖z j‖ by simpa [z, s] using h_z_sum) hz_ne_zero
  have h_align :=
    Complex.each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq
      (s := Finset.univ)
      (v := z)
      (u := s)
      (by simp [s])
      (by simpa [s] using h_z_sum)
      hs_ne_zero
  rcases h_align j (by simp) with ⟨c, hc_nonneg, hcz⟩
  refine ⟨c, hc_nonneg, ?_⟩
  simpa [z, s, smul_eq_mul] using hcz

omit [DecidableEq n] in
/-- For a non-negative matrix A, if the row sums are all equal to λ, then λ is an eigenvalue
    with the all-ones vector as its eigenvector. -/
lemma row_sum_eigenvalue
    (_ : ∀ i j, 0 ≤ A i j) (lambda : ℝ) (h_row_sums : ∀ i, ∑ j, A i j = lambda) :
    A *ᵥ (fun _ => (1 : ℝ)) = lambda • (fun _ => (1 : ℝ)) := by
  ext i
  rw [mulVec_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_one]
  rw [h_row_sums i]

omit [DecidableEq n] in
/-- If the dot product of a non-negative vector `v` and a strictly positive vector `w` is zero,
    then `v` must be the zero vector. -/
lemma eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos
    {v w : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hw_pos : ∀ i, 0 < w i)
    (h_dot : v ⬝ᵥ w = 0) :
    v = 0 := by
  rw [dotProduct] at h_dot
  funext i
  have hi := forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
    (fun j => mul_nonneg (hv_nonneg j) (hw_pos j).le) h_dot i
  rw [mul_eq_zero] at hi
  exact hi.resolve_right (hw_pos i).ne'

/--
If a scalar `μ` is in the spectrum of a complex matrix `A`, then there exists a non-zero
eigenvector `x` for that eigenvalue.
-/
theorem exists_eigenvector_of_mem_spectrum
    {A' : Matrix n n ℝ} {μ : ℂ} (h : μ ∈ spectrum ℂ (A'.map (algebraMap ℝ ℂ))) :
    ∃ x, x ≠ 0 ∧ (A'.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x := by
  let B := A'.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by
    rwa [spectrum.Matrix_toLin'_eq_spectrum]
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig⟩
  refine ⟨x, hx_ne_zero, ?_⟩
  have h_mul_eq := hx_eig
  rw [toLin'_apply] at h_mul_eq
  exact h_mul_eq

variable [Nonempty n]

omit [Nonempty n] in
lemma sum_component_norms_eq_perron_power_norm
    {A : Matrix n n ℝ} {x : n → ℂ}
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (k : ℕ) (m : n) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
    ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ := by
  have h_pow_eig : (A ^ k) *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) ^ k • (fun i ↦ ‖x i‖) :=
    mulVec_pow_eq_smul_pow_of_mulVec_smul h_x_abs_eig k
  calc ∑ l, ‖((A ^ k) m l : ℂ) * x l‖
    = ∑ l, |(A ^ k) m l| * ‖x l‖ := by
        simp_rw [norm_mul, Complex.norm_ofReal]
    _ = ∑ l, (A ^ k) m l * ‖x l‖ := by
      simp_rw [abs_of_pos (hAk_pos m _)]
    _ = ((A ^ k) *ᵥ (fun i ↦ ‖x i‖)) m := by simp [mulVec_apply]
    _ = ((perronRoot A) ^ k • (fun i ↦ ‖x i‖)) m := by rw [h_pow_eig]
    _ = (perronRoot A) ^ k * ‖x m‖ := by simp [Pi.smul_apply, smul_eq_mul]

omit [DecidableEq n] [Nonempty n] in
/--
For an eigenvalue μ of a nonnegative matrix A with eigenvector x,
the absolute value |μ| satisfies the sub-invariant relation: |μ|⋅|x| ≤ A⋅|x|.
This is the fundamental inequality in spectral analysis of nonnegative matrices.
-/
theorem eigenvalue_abs_subinvariant
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    (‖μ‖ : ℝ) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
  intro i
  calc
    (‖μ‖ : ℝ) * ‖x i‖ = ‖μ * x i‖ := by rw [← norm_mul]
    _ = ‖(μ • x) i‖ := by simp [Pi.smul_apply]
    _ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by rw [← hx_eig]
    _ = ‖∑ j, (A i j : ℂ) * x j‖ := by simp; rfl
    _ ≤ ∑ j, ‖(A i j : ℂ) * x j‖ := by apply norm_sum_le
    _ = ∑ j, A i j * ‖x j‖ := by
      simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA_nonneg _ _)]
    _ = (A *ᵥ fun i => ‖x i‖) i := by simp [mulVec_apply]

omit [DecidableEq n] in
/--
Under the conditions of the main theorem, the eigenvalue `lam` must be non-zero.
-/
lemma eigenvalue_ne_zero_of_irreducible
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {lam : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (‖lam‖ : ℝ) • (fun i => ‖x i‖)) :
    lam ≠ 0 := by
  intro h_lam_zero
  have h_norm_lam_zero : ‖lam‖ = 0 := by rwa [norm_eq_zero]
  have h_eig_zero_smul : A *ᵥ (fun i => ‖x i‖) = (0 : ℝ) • (fun i => ‖x i‖) := by
    rw [h_norm_lam_zero] at h_x_abs_eig
    exact h_x_abs_eig
  have h_eig_zero : A *ᵥ (fun i => ‖x i‖) = 0 := by
    simpa [zero_smul] using h_eig_zero_smul
  have h_x_abs_nonneg : ∀ i, 0 ≤ ‖x i‖ := fun i => norm_nonneg _
  have h_x_abs_ne_zero : (fun i => ‖x i‖) ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_x_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_is_positive_of_irreducible hA_irred h_eig_zero_smul h_x_abs_nonneg h_x_abs_ne_zero
  obtain ⟨i, j, hAij_pos⟩ := Matrix.Irreducible.exists_pos_entry (A := A) hA_irred
  have h_Axi : (A *ᵥ fun k => ‖x k‖) i = 0 := by rw [h_eig_zero]; rfl
  have h_pos : 0 < (A *ᵥ fun k => ‖x k‖) i :=
    mulVec_pos_of_exists_pos_mul_pos i j (fun k => hA_irred.nonneg i k) h_x_abs_pos hAij_pos
  exact h_pos.ne' h_Axi

theorem eigenvalue_is_perron_root_of_positive_eigenvector
    {r : ℝ} {v : n → ℝ}
    (_ : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hr_pos   : 0 < r)
    (hv_pos   : ∀ i, 0 < v i)
    (h_eig    : A *ᵥ v = r • v) :
    r = perronRoot A := by
  have h_ge : perronRoot A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector
      (A := A) hA_nonneg hr_pos hv_pos h_eig
  have h_le : r ≤ perronRoot A := by
    rw [← eq_eigenvalue_of_positive_eigenvector hv_pos h_eig]
    have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
    have hv_ne_zero : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
    apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
    rw [@Set.mem_image]
    exact ⟨v, ⟨hv_nonneg, hv_ne_zero⟩, rfl⟩
  exact le_antisymm h_le h_ge

/-- Positive right and left eigenvectors for a matrix have the same eigenvalue. -/
lemma eigenvalue_eq_of_positive_right_left_eigenvectors
    {A : Matrix n n ℝ} {r s : ℝ} {v u : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hu_pos : ∀ i, 0 < u i)
    (hv_eig : A *ᵥ v = r • v) (hu_left_eig : u ᵥ* A = s • u) :
    r = s := by
  have h_dot_pos : 0 < u ⬝ᵥ v :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos (fun i => (hv_pos i).le)
      (Pi.ne_zero_of_pos hv_pos)
  apply (mul_left_inj' h_dot_pos.ne').mp
  calc
    r * (u ⬝ᵥ v) = u ⬝ᵥ (A *ᵥ v) := by simp [hv_eig, dotProduct_smul, smul_eq_mul]
    _ = (u ᵥ* A) ⬝ᵥ v := by simpa using dotProduct_mulVec u A v
    _ = s * (u ⬝ᵥ v) := by simp [hu_left_eig, smul_dotProduct, smul_eq_mul]

theorem perronRoot_transpose_eq
    (A : Matrix n n ℝ) (hA_irred : A.IsIrreducible) :
    perronRoot A = perronRoot Aᵀ := by
  obtain ⟨r, v, hr_pos, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hA_irred
  have hr_eq_perron : r = perronRoot A :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hA_irred hA_irred.nonneg hr_pos hv_pos hv_eig
  have hAT_irred : Aᵀ.IsIrreducible :=
    Matrix.IsIrreducible.transpose hA_irred
  obtain ⟨r', u, hr'_pos, hu_pos, hu_eig_T⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have hr'_eq_perron : r' = perronRoot Aᵀ :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hAT_irred (fun i j ↦ hA_irred.nonneg j i) hr'_pos hu_pos hu_eig_T
  have hu_eig_left : u ᵥ* A = r' • u := by
    have : Aᵀ *ᵥ u = r' • u := hu_eig_T
    simpa [vecMul_eq_mulVec_transpose] using this
  have hr_eq_r' : r = r' :=
    eigenvalue_eq_of_positive_right_left_eigenvectors hv_pos hu_pos hv_eig hu_eig_left
  calc
    perronRoot A   = r   := by symm; simpa using hr_eq_perron
    _                  = r'  := hr_eq_r'
    _                  = perronRoot Aᵀ := hr'_eq_perron

/-- An irreducible nonnegative matrix has a positive left Perron eigenvector. -/
lemma exists_positive_left_perron_eigenvector
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ u : n → ℝ, (∀ i, 0 < u i) ∧ u ᵥ* A = perronRoot A • u := by
  have hAT_irred : Aᵀ.IsIrreducible := Matrix.IsIrreducible.transpose hA_irred
  obtain ⟨r, u, hr_pos, hu_pos, hu_eig⟩ := exists_positive_eigenvector_of_irreducible hAT_irred
  have hr_eq : r = perronRoot A := by
    calc
      r = perronRoot Aᵀ :=
        eigenvalue_is_perron_root_of_positive_eigenvector
          hAT_irred (fun i j => hA_nonneg j i) hr_pos hu_pos hu_eig
      _ = perronRoot A := (perronRoot_transpose_eq A hA_irred).symm
  exact ⟨u, hu_pos, by simpa [hr_eq, vecMul_eq_mulVec_transpose] using hu_eig⟩

omit [Nonempty n] [DecidableEq n] in
/-- A positive left Perron eigenvector annihilates `A *ᵥ y - r • y` in the dot product. -/
lemma dotProduct_left_perron_sub_eq_zero
    {A : Matrix n n ℝ} {u y : n → ℝ}
    (hu_left_eig : u ᵥ* A = perronRoot A • u) :
    u ⬝ᵥ (A *ᵥ y - perronRoot A • y) = 0 := by
  rw [dotProduct_sub, dotProduct_mulVec, hu_left_eig, dotProduct_smul_left,
    dotProduct_smul, smul_eq_mul, sub_self]

/--
If for a non-negative, irreducible matrix `A`, there exists
a non-negative, non-zero vector `y` and a positive scalar `s` such that `A *ᵥ y ≤ s • y`,
then the Perron root of `A` is at most `s`.
-/
lemma perron_root_le_of_subinvariant
    (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {s : ℝ} (_ : 0 < s)
    {y : n → ℝ} (hy_nonneg : ∀ i, 0 ≤ y i)
    (hy_ne_zero : y ≠ 0)
    (h_subinv : A *ᵥ y ≤ s • y) :
    perronRoot A ≤ s := by
  obtain ⟨u, hu_pos, hu_left_eig⟩ :=
    exists_positive_left_perron_eigenvector hA_irred hA_nonneg
  have h_dot_le : u ⬝ᵥ (A *ᵥ y) ≤ u ⬝ᵥ (s • y) :=
    dotProduct_le_dotProduct_of_nonneg_left' (fun i => (hu_pos i).le) h_subinv
  rw [dotProduct_mulVec, hu_left_eig, dotProduct_smul_left, dotProduct_smul] at h_dot_le
  have h_dot_pos : 0 < u ⬝ᵥ y := dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hy_nonneg hy_ne_zero
  exact le_of_mul_le_mul_right h_dot_le h_dot_pos

/-- If equality holds in the subinvariance inequality `r • v ≤ A *ᵥ v` for the Perron root `r`,
    then `v` must be an eigenvector. -/
lemma subinvariant_equality_implies_eigenvector
    (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (_ : ∀ i, 0 ≤ v i) (_ : v ≠ 0)
    (h_subinv : perronRoot A • v ≤ A *ᵥ v) :
    A *ᵥ v = perronRoot A • v := by
  let r := perronRoot A
  let z := A *ᵥ v - r • v
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg, z]
    exact h_subinv i
  by_cases hz_zero : z = 0
  · simp only [sub_eq_zero, z] at hz_zero
    exact hz_zero
  · obtain ⟨u, hu_pos, hu_left_eig⟩ :=
      exists_positive_left_perron_eigenvector hA_irred hA_nonneg
    have h_dot_z : u ⬝ᵥ z = 0 := by
      simpa [z, r] using dotProduct_left_perron_sub_eq_zero (u := u) (y := v) hu_left_eig
    have h_z_eq_zero : z = 0 :=
      eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos hz_nonneg hu_pos (by rwa [dotProduct_comm])
    exact (hz_zero h_z_eq_zero).elim

/--
The value of the Collatz-Wielandt function for any non-negative, non-zero vector
is less than or equal to the Perron root.
-/
lemma collatzWielandtFn_le_perronRoot
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A x ≤ perronRoot A := by
  apply le_csSup (CollatzWielandt.bddAbove A hA_nonneg)
  rw [Set.mem_image]
  exact ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩

/--
Any eigenvalue μ of a nonnegative irreducible matrix A has absolute value
at most equal to the Perron root.
-/
theorem eigenvalue_abs_le_perron_root
    {A : Matrix n n ℝ} (_ : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ‖μ‖ ≤ perronRoot A := by
  let B := A.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by rwa [spectrum.Matrix_toLin'_eq_spectrum]
  rcases Module.End.exists_eigenvector_of_mem_spectrum h_spec with ⟨x, hx_ne_zero, hx_eig_lin⟩
  have hx_eig : B *ᵥ x = μ • x := by rwa [toLin'_apply] at hx_eig_lin
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_subinv : (‖μ‖ : ℝ) • x_abs ≤ A *ᵥ x_abs :=
    eigenvalue_abs_subinvariant hA_nonneg hx_eig
  have h_le_collatz : (‖μ‖ : ℝ) ≤ collatzWielandtFn A x_abs :=
    le_of_subinvariant hA_nonneg hx_abs_nonneg hx_abs_ne_zero h_subinv
  have h_le_perron : collatzWielandtFn A x_abs ≤ perronRoot A :=
    collatzWielandtFn_le_perronRoot hA_nonneg hx_abs_nonneg hx_abs_ne_zero
  exact le_trans h_le_collatz h_le_perron

/-- For an irreducible, non-negative matrix, the Perron root (defined as the Collatz-Wielandt
supremum) is equal to the unique positive eigenvalue `r` from the existence theorem. -/
lemma perron_root_eq_positive_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ r v, 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v ∧ perronRoot A = r := by
  obtain ⟨r, v, hr_pos, hv_pos, h_eig⟩ := exists_positive_eigenvector_of_irreducible hA_irred
  have h_le : perronRoot A ≤ r :=
    eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_ge : r ≤ perronRoot A :=
    eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig
  have h_eq : perronRoot A = r := le_antisymm h_le h_ge
  exact ⟨r, v, hr_pos, hv_pos, h_eig, h_eq⟩

/--
If a matrix `A` has an eigenvector `v` for an eigenvalue `μ`, then `μ` is in the spectrum of `A`.
This is a direct consequence of the definition of an eigenvalue and the spectrum.
-/
lemma mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} {μ : K} {v : V} (h : Module.End.HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h

lemma mem_spectrum_of_eigenvalue
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n K} {μ : K} {v : n → K}
    (hv_ne_zero : v ≠ 0) (h_eig : A *ᵥ v = μ • v) :
    μ ∈ spectrum K A := by
  let f := toLin' A
  have h_eig_f : f v = μ • v := by
    simpa [toLin'_apply, f] using h_eig
  have h_has_eigvec : Module.End.HasEigenvector f μ v :=
    ⟨by
      rwa [← Module.End.mem_eigenspace_iff] at h_eig_f,
      hv_ne_zero⟩
  have h_mem_f : μ ∈ spectrum K f :=
    mem_spectrum_of_hasEigenvector h_has_eigvec
  simpa [f, spectrum.Matrix_toLin'_eq_spectrum] using h_mem_f

/-- The Perron root of an irreducible, non-negative matrix is an eigenvalue. -/
theorem perron_root_is_eigenvalue (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    perronRoot A ∈ spectrum ℝ A := by
  obtain ⟨r', v, _, hv_pos, h_eig, h_eq⟩ := perron_root_eq_positive_eigenvalue hA_irred hA_nonneg
  have hv_ne_0 : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
  rw [h_eq]
  exact mem_spectrum_of_eigenvalue hv_ne_0 h_eig

/-- **Perron-Frobenius Theorem (Dominance)**: The Perron root of an irreducible, non-negative
matrix is an eigenvalue and its modulus is greater than or equal to the modulus of any other
eigenvalue. It is the spectral radius. -/
theorem perron_root_is_spectral_radius (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot A
    r ∈ spectrum ℝ A ∧ ∀ μ ∈ spectrum ℝ A, |μ| ≤ r := by
  constructor
  · exact perron_root_is_eigenvalue hA_irred hA_nonneg
  · intro μ hμ
    have hμ_complex : (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
      have hμ_lin : μ ∈ spectrum ℝ (toLin' A) := by
        simpa [spectrum.Matrix_toLin'_eq_spectrum] using hμ
      obtain ⟨v, hv_ne_zero, hv_eig⟩ :=
        Module.End.exists_eigenvector_of_mem_spectrum hμ_lin
      let v_complex : n → ℂ := fun i => (v i : ℂ)
      have hvc_ne_zero : v_complex ≠ 0 := by
        intro h
        have : v = 0 := by
          ext i
          have : (v i : ℂ) = 0 := congr_fun h i
          exact_mod_cast this
        exact hv_ne_zero this
      have hv_eig_vec : A *ᵥ v = μ • v := by
        simpa [toLin'_apply] using hv_eig
      have hvc_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ v_complex = (μ : ℂ) • v_complex := by
        ext i
        have h_eq : (A *ᵥ v) i = μ * v i := by
          simpa using congr_fun hv_eig_vec i
        simpa [v_complex, smul_eq_mul, mulVec, dotProduct, map_apply] using
          congrArg (fun x : ℝ => (x : ℂ)) h_eq
      exact mem_spectrum_of_eigenvalue hvc_ne_zero hvc_eig
    have h_bound := eigenvalue_abs_le_perron_root hA_irred hA_nonneg hμ_complex
    rwa [Complex.norm_ofReal] at h_bound

/-- For an irreducible nonnegative real matrix, the spectral radius as an extended nonnegative real
agrees with the norm of the Perron root. -/
theorem spectralRadius_eq_nnnorm_perronRoot (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    spectralRadius ℝ A = ‖(perronRoot A : ℝ)‖₊ := by
  have h_in_spec : perronRoot A ∈ spectrum ℝ A := perron_root_is_eigenvalue hA_irred hA_nonneg
  have h_dom : ∀ μ ∈ spectrum ℝ A, |μ| ≤ perronRoot A :=
    (perron_root_is_spectral_radius hA_irred hA_nonneg).2
  have h_r_nonneg : 0 ≤ perronRoot A := perronRoot_nonneg hA_nonneg
  have h_nnnorm_dom : ∀ μ ∈ spectrum ℝ A, ‖μ‖₊ ≤ ‖(perronRoot A : ℝ)‖₊ := by
    intro μ hμ
    have h_abs_nonneg : 0 ≤ |μ| := abs_nonneg μ
    rw [← Real.toNNReal_eq_nnnorm_of_nonneg h_r_nonneg]
    rw [← Real.nnnorm_abs, ← Real.toNNReal_eq_nnnorm_of_nonneg h_abs_nonneg]
    exact Real.toNNReal_le_toNNReal (h_dom μ hμ)
  apply le_antisymm
  · -- Upper bound: spectralRadius ≤ ‖perronRoot A‖₊
    apply iSup₂_le
    intro μ hμ
    exact ENNReal.coe_le_coe.mpr (h_nnnorm_dom μ hμ)
  · -- Lower bound: ‖perronRoot A‖₊ ≤ spectralRadius
    apply le_iSup₂_of_le (perronRoot A) h_in_spec
    exact le_refl _

/-- The spectral radius of an irreducible nonnegative matrix is the Perron root as a real number. -/
theorem spectralRadius_toReal_eq_perronRoot (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    (spectralRadius ℝ A).toReal = perronRoot A := by
  obtain ⟨hr_spec, hr_bound⟩ := perron_root_is_spectral_radius hA_irred hA_nonneg
  have hr_nonneg : 0 ≤ perronRoot A := (perronRoot_pos_of_irreducible hA_irred hA_nonneg).le
  have h_eq : spectralRadius ℝ A = ‖perronRoot A‖₊ := by
    apply le_antisymm
    · apply iSup₂_le
      intro μ hμ
      simp only [ENNReal.coe_le_coe]
      have h_abs_le : |μ| ≤ perronRoot A := hr_bound μ hμ
      calc ‖μ‖₊ = ‖|μ|‖₊ := (Real.nnnorm_abs μ).symm
           _ = |μ|.toNNReal := (Real.toNNReal_eq_nnnorm_of_nonneg (abs_nonneg μ)).symm
           _ ≤ (perronRoot A).toNNReal := Real.toNNReal_le_toNNReal h_abs_le
           _ = ‖perronRoot A‖₊ := Real.toNNReal_eq_nnnorm_of_nonneg hr_nonneg
    · apply le_iSup₂_of_le (perronRoot A) hr_spec
      rfl
  rw [h_eq]
  simp [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]

/--
**Perron–Frobenius at the spectral radius:** an irreducible nonnegative matrix admits a strictly
positive right eigenvector for `(spectralRadius ℝ A).toReal`, the common value of the spectral radius
and the Perron root. (From https://lean-lang.org/eval/problems/irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius/)
-/
theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) := by
  sorry

omit [Nonempty n] [DecidableEq n] in
/-- If an eigenvalue `μ` has a norm equal to the Perron root `r`, then the triangle inequality
for the eigenvector equation holds with equality. -/
lemma triangle_equality_of_norm_eq_perron_root
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    {r : ℝ} (h_norm_eq_r : ‖μ‖ = r)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = r • (fun i => ‖x i‖)) :
    ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖ := by
  intro i
  let x_abs := fun i => ‖x i‖
  calc
    ‖∑ j, (A i j : ℂ) * x j‖ = ‖((A.map (algebraMap ℝ ℂ)) *ᵥ x) i‖ := by simp; rfl
    _ = ‖(μ • x) i‖ := by rw [hx_eig]
    _ = ‖μ‖ * ‖x i‖ := by simp
    _ = r * x_abs i := by rw [h_norm_eq_r];
    _ = (r • x_abs) i := by simp [smul_eq_mul]
    _ = (A *ᵥ x_abs) i := by rw [h_x_abs_eig]
    _ = ∑ j, A i j * x_abs j := by simp [mulVec_apply]
    _ = ∑ j, ‖(A i j : ℂ) * x j‖ := by
        simp_rw [x_abs, norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg _ _)]

/--
If `|x|` is a positive eigenvector of an irreducible non-negative matrix `A`, then for any `i`,
the `i`-th component of `A * |x|` is positive.
-/
lemma mulVec_x_abs_pos_of_irreducible {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {x_abs : n → ℝ} (h_x_abs_nonneg : ∀ i, 0 ≤ x_abs i)
    (h_x_abs_eig : A *ᵥ x_abs = (perronRoot A) • x_abs)
    (hx_abs_ne_zero : x_abs ≠ 0) (i : n) :
    0 < (A *ᵥ x_abs) i := by
  have h_x_abs_pos : ∀ k, 0 < x_abs k :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig h_x_abs_nonneg hx_abs_ne_zero
  have h_r_pos : 0 < perronRoot A := perronRoot_pos_of_irreducible hA_irred hA_irred.nonneg
  have h_eq_i : (A *ᵥ x_abs) i = (perronRoot A) * x_abs i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun h_x_abs_eig i
  have : 0 < (perronRoot A) * x_abs i :=
    mul_pos h_r_pos (h_x_abs_pos i)
  simpa [h_eq_i] using this

/--
If the triangle equality holds for an eigenvector `x` of a non-negative irreducible matrix `A`,
then the sum `s = (A * x) i` is non-zero.
-/
lemma sum_s_ne_zero_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (hx_ne_zero : x ≠ 0) (i : n) :
    (∑ j, (A i j : ℂ) * x j) ≠ 0 := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  intro hs_zero
  have h_norm_s_zero : ‖∑ j, (A i j : ℂ) * x j‖ = 0 := by rw [hs_zero]; exact norm_zero
  have h_sum_norm_zero : ∑ j, ‖(A i j : ℂ) * x j‖ = 0 := h_triangle_eq i ▸ h_norm_s_zero
  have h_sum_A_x_abs_zero : ∑ j, A i j * x_abs j = 0 := by
    simpa [norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg _ _)] using h_sum_norm_zero
  have h_Ax_abs_i_zero : (A *ᵥ x_abs) i = 0 := by simpa [mulVec_apply]
  have h_pos := mulVec_x_abs_pos_of_irreducible hA_irred
      (by
        intro k
        simp)
      h_x_abs_eig hx_abs_ne_zero i
  exact h_pos.ne' h_Ax_abs_i_zero

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- If `A i j > 0` and `x j ≠ 0`, then the term `(A i j : ℂ) * x j` is non-zero. -/
lemma term_ne_zero_of_pos_entry {A : Matrix n n ℝ} {x : n → ℂ}
    {i j : n} (hAij_pos : 0 < A i j) (hxj_ne_zero : x j ≠ 0) :
    (A i j : ℂ) * x j ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hAij_pos.ne') hxj_ne_zero

omit [DecidableEq n] in
/-- From an irreducible Perron eigenvector equation on `‖x‖`, every component `‖x k‖` is positive. -/
lemma norm_entries_pos_of_irreducible_abs_perron_eigenvector {x : n → ℂ}
    (hA_irred : A.IsIrreducible)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (hx_ne_zero : x ≠ 0) : ∀ k, 0 < ‖x k‖ :=
  eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig (fun _ => norm_nonneg _)
    (normFun_complex_ne_zero_of_ne_zero hx_ne_zero)

/-- For any row `k` of an irreducible matrix with triangle equality,
all `x l` where `A k l > 0` have the same phase. -/
lemma aligned_neighbors_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖)) :
    ∀ k l m, 0 < A k l → 0 < A k m → x l / ↑‖x l‖ = x m / ↑‖x m‖ := by
  intro k l m hAkl_pos hAkm_pos
  let z l' := (A k l' : ℂ) * x l'
  let s := ∑ l', z l'
  have hs_ne_zero : s ≠ 0 :=
    sum_s_ne_zero_of_triangle_eq hA_irred hA_nonneg h_triangle_eq h_x_abs_eig hx_ne_zero k
  have hx_pos := norm_entries_pos_of_irreducible_abs_perron_eigenvector hA_irred h_x_abs_eig hx_ne_zero
  have h_sum_term (l' : n) (hl' : z l' ≠ 0) : z l' / ↑‖z l'‖ = s / ↑‖s‖ :=
    Complex.aligned_of_triangle_eq rfl (h_triangle_eq k) hs_ne_zero l' (by simp) hl'
  have h_zl_ne_zero : z l ≠ 0 := term_ne_zero_of_pos_entry hAkl_pos (norm_pos_iff.mp (hx_pos l))
  have h_zm_ne_zero : z m ≠ 0 := term_ne_zero_of_pos_entry hAkm_pos (norm_pos_iff.mp (hx_pos m))
  have hxl_nz : x l ≠ 0 := norm_pos_iff.mp (hx_pos l)
  have hxm_nz : x m ≠ 0 := norm_pos_iff.mp (hx_pos m)
  calc
    x l / ↑‖x l‖ = z l / ↑‖z l‖ := (Complex.aligned_of_mul_of_real_pos hAkl_pos rfl hxl_nz).symm
    _ = z m / ↑‖z m‖ := (h_sum_term l h_zl_ne_zero).trans (h_sum_term m h_zm_ne_zero).symm
    _ = x m / ↑‖x m‖ := Complex.aligned_of_mul_of_real_pos hAkm_pos rfl hxm_nz

omit [DecidableEq n] in
/-- The reference phase has norm 1. -/
lemma reference_phase_norm_one {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (j₀ : n) :
    ‖x j₀ / ↑‖x j₀‖‖ = 1 := by
  have h_pos := norm_entries_pos_of_irreducible_abs_perron_eigenvector hA_irred h_x_abs_eig hx_ne_zero j₀
  simp_rw [norm_div, Complex.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  exact div_self h_pos.ne'

/--
All non-zero entries in the same row have aligned phases when triangle equality holds.
-/
lemma row_entries_aligned_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (k : n) :
    ∀ l m, 0 < A k l → 0 < A k m → x l / ↑‖x l‖ = x m / ↑‖x m‖ :=
  aligned_neighbors_of_triangle_eq hA_irred hA_nonneg hx_ne_zero h_triangle_eq h_x_abs_eig k

omit [DecidableEq n] in
/-- For an irreducible matrix, every row has at least one positive entry. -/
lemma IsIrreducible.exists_pos_entry_in_row {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_no_pos
  push_neg at h_no_pos
  have h_row_zero : ∀ j, A i j = 0 := fun j =>
    le_antisymm (h_no_pos j) (hA_irred.nonneg i j)
  obtain ⟨_, j₀, _⟩ := Matrix.Irreducible.exists_pos_entry (A := A) hA_irred
  letI : Quiver n := toQuiver A
  have hconn := hA_irred.connected i j₀
  obtain ⟨p, hp_pos⟩ := hconn
  have h_pos : p.length > 0 := hp_pos
  obtain ⟨c, e, p', hp_eq, hp_len_eq⟩ :=
    Quiver.Path.path_decomposition_first_edge p h_pos
  have hic_pos : 0 < A i c := e
  exact (h_row_zero c).symm.not_lt hic_pos

/-! ### Triangle equality and phases

Further lemmas building on norm-sum layer (`aligned_term_of_triangle_eq`, etc.). -/

lemma phase_eq_of_positive_real_multiple {z w : ℂ} {c : ℝ}
    (h_c_pos : 0 < c) (h_eq : z = (c : ℂ) * w) (h_w_ne_zero : w ≠ 0) :
    z / ↑‖z‖ = w / ↑‖w‖ := by
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr h_c_pos.ne'
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr h_w_ne_zero
  have hnorm : ‖z‖ = c * ‖w‖ := by
    rw [h_eq, norm_mul, norm_ofReal, abs_of_nonneg h_c_pos.le]
  have hzℂ : (↑‖z‖ : ℂ) = (c : ℂ) * ↑‖w‖ := by
    rw [← ofReal_mul, hnorm]
  calc
    z / ↑‖z‖ = ((c : ℂ) * w) / ((c : ℂ) * ↑‖w‖) := by
      rw [hzℂ, h_eq]
    _ = w / ↑‖w‖ := by rw [mul_div_mul_left w (↑‖w‖) hc0]

lemma aligned_term_of_triangle_eq {ι : Type*} {s : Finset ι} {v : ι → ℂ}
    (h_sum : ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖)
    {j : ι} (h_j : j ∈ s) (h_vj_ne_zero : v j ≠ 0) :
    let sum := ∑ i ∈ s, v i
    v j / ↑‖v j‖ = sum / ↑‖sum‖ := by
  intro sum
  have h_sum_ne_zero : sum ≠ 0 := by
    intro h_sum_zero
    have h_norm_sum : ‖sum‖ = 0 := by rw [h_sum_zero, norm_zero]
    have h_sum_norms : ∑ i ∈ s, ‖v i‖ = 0 := by rw [← h_sum, h_norm_sum]
    have h_vj_zero : ‖v j‖ = 0 := norm_eq_zero_of_finset_sum_norm_eq_zero v h_sum_norms j h_j
    exact h_vj_ne_zero (norm_eq_zero.mp h_vj_zero)
  have h_aligned := Complex.aligned_of_triangle_eq rfl h_sum h_sum_ne_zero j h_j h_vj_ne_zero
  exact h_aligned

/-- Nonzero terms in a global triangle equality share the phase of the total sum. -/
lemma Complex.phase_eq_of_fintype_triangle_eq {ι : Type*} [Fintype ι] {v : ι → ℂ}
    (hτ : ‖∑ i, v i‖ = ∑ i, ‖v i‖) {i j : ι} (hi : v i ≠ 0) (hj : v j ≠ 0) :
    v i / ↑‖v i‖ = v j / ↑‖v j‖ :=
    (aligned_term_of_triangle_eq hτ (Finset.mem_univ i) hi).trans
    (aligned_term_of_triangle_eq hτ (Finset.mem_univ j) hj).symm

/-- Common phase alignment identifies `(∑ i, v i) / ‖∑ i, v i‖` with the shared phase `c`. -/
lemma Complex.norm_div_norm_eq_of_triangle_aligned {ι : Type*} [Fintype ι] {v : ι → ℂ} {c : ℂ}
    (hτ : ‖∑ i, v i‖ = ∑ i, ‖v i‖)
    (h_alg : ∀ i, v i ≠ 0 → v i / ↑‖v i‖ = c) {j : ι} (hj : v j ≠ 0) :
    (∑ i, v i) / ↑‖∑ i, v i‖ = c :=
  (aligned_term_of_triangle_eq hτ (Finset.mem_univ j) hj).symm.trans (h_alg j hj)

/-- When triangle equality holds for a sum and all non-zero terms have the same phase factor,
    then the sum equals the sum of magnitudes times that common phase factor.
    This is a key property for proving eigenvalue relationships in the complex case. -/
lemma Complex.triangle_eq_sum_with_common_phase {ι : Type*} [Fintype ι]
    {v : ι → ℂ} {c : ℂ} (_ : ‖c‖ = 1)
    (h_triangle_eq : ‖∑ i, v i‖ = ∑ i, ‖v i‖)
    (h_aligned : ∀ i, v i ≠ 0 → v i / ↑‖v i‖ = c) :
    ∑ i, v i = (∑ i, ‖v i‖ : ℂ) * c := by
  by_cases h_all_zero : ∀ i, v i = 0
  · simp only [h_all_zero, Finset.sum_const_zero, norm_zero, ofReal_zero, zero_mul]
  push_neg at h_all_zero
  rcases h_all_zero with ⟨j, hj_ne_zero⟩
  have hsum_ne := Fintype.sum_ne_zero_of_triangle_norm_exists_nonzero h_triangle_eq hj_ne_zero
  have h_phase := Complex.norm_div_norm_eq_of_triangle_aligned h_triangle_eq h_aligned hj_ne_zero
  calc ∑ i, v i
      = ‖∑ i, v i‖ * ((∑ i, v i) / ↑‖∑ i, v i‖) := by
          rw [← mul_comm]; exact eq_mul_div_ofReal_norm_complex _ (norm_ne_zero_iff.mpr hsum_ne)
      _ = ‖∑ i, v i‖ * c := by rw [h_phase]
      _ = (∑ i, ‖v i‖ : ℂ) * c := by rw [h_triangle_eq, ofReal_sum]

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- Multiplication by a positive real scalar preserves the phase of a complex term. -/
lemma weighted_phase_aligned_of_nonzero
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} {i j : n} {c : ℂ}
    (h_aligned : ∀ j, 0 < A i j → x j ≠ 0 → x j / ↑‖x j‖ = c)
    (hz : (A i j : ℂ) * x j ≠ 0) :
    ((A i j : ℂ) * x j) / ↑‖(A i j : ℂ) * x j‖ = c := by
  have hA_pos : 0 < A i j := by
    by_contra h_not_pos
    exact hz <| by simp [le_antisymm (not_lt.mp h_not_pos) (hA_nonneg i j)]
  have hx_ne_zero : x j ≠ 0 := by
    intro hx_zero
    exact hz <| by simp [hx_zero]
  rw [Complex.aligned_of_mul_of_real_pos hA_pos rfl hx_ne_zero]
  exact h_aligned j hA_pos hx_ne_zero

omit [Nonempty n] [DecidableEq n] in
/-- The row sum of weighted complex norms is the real matrix-vector product on norms. -/
lemma sum_norm_weighted_row_eq_mulVec_norm
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (x : n → ℂ) (i : n) :
    ∑ j, ‖(A i j : ℂ) * x j‖ = (A *ᵥ (fun j => ‖x j‖)) i := by
  calc
    ∑ j, ‖(A i j : ℂ) * x j‖ = ∑ j, A i j * ‖x j‖ := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg i j)]
    _ = (A *ᵥ (fun j => ‖x j‖)) i := by simp [mulVec_apply]

/-- In the specific context of the Perron-Frobenius theorem, if we have an irreducible
    non-negative matrix A with triangle equality for the eigenvector equation,
    then the complex sum equals the real Perron root times the phase-aligned eigenvector. -/
lemma sum_eq_perron_root_times_phase_aligned_vector
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ}
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    {i : n} (c : ℂ) (h_norm_c : ‖c‖ = 1)
    (h_aligned : ∀ j, A i j > 0 → x j ≠ 0 → x j / ↑‖x j‖ = c) :
    ∑ j, (A i j : ℂ) * x j = (perronRoot A : ℂ) * (‖x i‖ : ℂ) * c := by
  let z : n → ℂ := fun j => (A i j : ℂ) * x j
  have h_z_aligned : ∀ j, z j ≠ 0 → z j / ↑‖z j‖ = c := by
    intro j hz_ne_zero
    exact weighted_phase_aligned_of_nonzero hA_nonneg h_aligned (by simpa [z] using hz_ne_zero)
  have h_sum_eq := Complex.triangle_eq_sum_with_common_phase h_norm_c (h_triangle_eq i) h_z_aligned
  have h_sum_norms : ∑ j, ‖z j‖ = perronRoot A * ‖x i‖ := by
    calc ∑ j, ‖z j‖
      = (A *ᵥ (fun j => ‖x j‖)) i := by
          simpa [z] using sum_norm_weighted_row_eq_mulVec_norm hA_nonneg x i
      _ = ((perronRoot A) • (fun j => ‖x j‖)) i := by rw [h_x_abs_eig]
      _ = perronRoot A * ‖x i‖ := by simp [Pi.smul_apply, smul_eq_mul]
  calc ∑ j, z j
    = (∑ j, ‖z j‖ : ℂ) * c := h_sum_eq
    _ = (perronRoot A * ‖x i‖ : ℂ) * c := by
        have h_sum_norms_cast : (∑ j, ‖z j‖ : ℂ) = (perronRoot A * ‖x i‖ : ℂ) := by
          rw [← ofReal_mul, ← h_sum_norms]; rw [ofReal_eq_coe]; exact
            Eq.symm (ofReal_sum Finset.univ fun i ↦ ‖z i‖)
        rw [h_sum_norms_cast]

/-- When triangle equality holds for a complex eigenvector equation, the vector of component norms
    is an eigenvector of the real matrix with eigenvalue equal to the norm of the complex eigenvalue. -/
lemma norm_vector_is_eigenvector_of_triangle_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖) :
    A *ᵥ (fun i => ‖x i‖) = (‖μ‖ : ℝ) • (fun i => ‖x i‖) := by
  exact norm_eigenvector_is_eigenvector_of_triangle_eq hA_nonneg hx_eig h_triangle_eq

/-- For an irreducible non-negative matrix, if the absolute values of a complex eigenvector form
    a real eigenvector, then the eigenvalue's norm equals the Perron root. -/
lemma eigenvalue_norm_eq_perron_root_of_triangle_eq
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (‖μ‖ : ℝ) • (fun i => ‖x i‖)) :
    ‖μ‖ = perronRoot A := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have hx_abs_pos : ∀ i, 0 < x_abs i :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig hx_abs_nonneg hx_abs_ne_zero
  have h_mu_norm_pos : 0 < ‖μ‖ := by
    have h_mu_ne_zero : μ ≠ 0 :=
      eigenvalue_ne_zero_of_irreducible hA_irred hx_ne_zero h_x_abs_eig
    exact norm_pos_iff.mpr h_mu_ne_zero
  exact eigenvalue_is_perron_root_of_positive_eigenvector
    hA_irred hA_nonneg h_mu_norm_pos hx_abs_pos h_x_abs_eig

/-- In a matrix with triangle equality, vertices that share a common predecessor have aligned phases. -/
lemma phase_aligned_within_row
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (i : n) (j k : n) (h_ij_pos : 0 < A i j) (h_ik_pos : 0 < A i k) :
    x j / ↑‖x j‖ = x k / ↑‖x k‖ := by
  apply row_entries_aligned_of_triangle_eq hA_irred hA_nonneg hx_ne_zero
        h_triangle_eq h_x_abs_eig i j k h_ij_pos h_ik_pos

/-- Phase propagation within a row: if vertices j and k both have incoming edges from i,
    then they share the same phase. This is already proven as `phase_aligned_within_row`. -/
lemma phase_propagates_within_row
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    {i j k : n} (h_ij_pos : 0 < A i j) (h_ik_pos : 0 < A i k) :
    x j / ↑‖x j‖ = x k / ↑‖x k‖ :=
  row_entries_aligned_of_triangle_eq hA_irred hA_nonneg hx_ne_zero
    h_triangle_eq h_x_abs_eig i j k h_ij_pos h_ik_pos

/--
If an eigenvalue `μ` of a primitive matrix `A` has norm equal to the Perron root,
then the vector of norms of its eigenvector `x`, `|x|`, is strictly positive.
-/
lemma eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (_ : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (_ : ‖μ‖ = perronRoot A)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0) (_ : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖)) :
    ∀ i, 0 < ‖x i‖ := by
  have h_x_abs_ne_zero : (fun j => ‖x j‖) ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_x_abs_nonneg : ∀ j, 0 ≤ ‖x j‖ := fun j => norm_nonneg _
  have h_r_pos : 0 < perronRoot A :=
    perronRoot_pos_of_irreducible (Matrix.IsPrimitive.isIrreducible hA_prim) hA_nonneg
  exact eigenvector_of_primitive_is_positive hA_prim h_r_pos h_x_abs_eig h_x_abs_nonneg h_x_abs_ne_zero

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- Reference phase is unit: `‖x i₀ / ‖x i₀‖‖ = 1`. -/
lemma reference_phase_norm_one_of_primitive
    {_ : Matrix n n ℝ} {x : n → ℂ} {i₀ : n}
    (hx_abs_pos : 0 < ‖x i₀‖) :
    ‖x i₀ / ‖x i₀‖‖ = (1 : ℝ) := by
  simp [hx_abs_pos.ne']

omit [Nonempty n] in
/-- The norm of a matrix-vector product equals the perron root to the kth power times the norm of the vector component. -/
lemma norm_matrix_power_vec_eq_perron_power_norm
    {A : Matrix n n ℝ} {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (k : ℕ) (m : n) :
    ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ = (perronRoot A) ^ k * ‖x m‖ := by
  have h_k_power : ((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x = (μ ^ k) • x :=
    mulVec_map_pow_eq_smul_pow_of_mulVec_map_smul (algebraMap ℝ ℂ) hx_eig k
  have h_component : ((μ ^ k) • x) m = (μ ^ k) * x m := by simp [Pi.smul_apply]
  calc ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖
    = ‖((μ ^ k) • x) m‖ := by rw [h_k_power]
    _ = ‖(μ ^ k) * x m‖ := by rw [h_component]
    _ = ‖μ ^ k‖ * ‖x m‖ := by rw [norm_mul]
    _ = ‖μ‖ ^ k * ‖x m‖ := by rw [norm_pow]
    _ = (perronRoot A) ^ k * ‖x m‖ := by rw [h_norm_eq_r]

omit [Nonempty n] in
/-- For a primitive matrix power, triangle equality holds for the eigenvector equation. -/
lemma triangle_equality_for_primitive_power
    {A : Matrix n n ℝ} (_ : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (m : n) (k : ℕ) (hAk_pos : ∀ i j, 0 < (A ^ k) i j) :
    ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ := by
  have h_left : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ := by
    have h_eq : ‖∑ l, ((A ^ k) m l : ℂ) * x l‖ = ‖(((A ^ k).map (algebraMap ℝ ℂ)) *ᵥ x) m‖ := by
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [h_eq]
    exact norm_matrix_power_vec_eq_perron_power_norm hx_eig h_norm_eq_r k m
  have h_right : ∑ l, ‖((A ^ k) m l : ℂ) * x l‖ = (perronRoot A) ^ k * ‖x m‖ :=
    sum_component_norms_eq_perron_power_norm h_x_abs_eig k m hAk_pos
  rw [h_left, h_right]

omit [Nonempty n] in
/-- Components align with their weighted versions under positive scaling. -/
lemma component_phase_alignment
    {A : Matrix n n ℝ} {x : n → ℂ} {k : ℕ} {m i : n}
    (hAk_pos : 0 < (A ^ k) m i)
    (hx_abs_pos : 0 < ‖x i‖) :
    x i / ‖x i‖ = ((A ^ k) m i : ℂ) * x i / ‖((A ^ k) m i : ℂ) * x i‖ := by
  have h_ne : x i ≠ 0 := norm_pos_iff.mp hx_abs_pos
  exact (Complex.aligned_of_mul_of_real_pos hAk_pos rfl h_ne).symm

/--  Phase propagation along a strictly-positive power of a primitive matrix. -/
lemma entries_share_phase_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    {μ : ℂ} {x : n → ℂ}
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) =
                     (perronRoot A) • (fun i ↦ ‖x i‖))
    (h_norm_eq_r : ‖μ‖ = perronRoot A)
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∀ i j : n, x i / ‖x i‖ = x j / ‖x j‖ := by
  obtain ⟨k, _hk_pos, hAk_pos⟩ := hA_prim.2
  intro i j
  obtain ⟨m⟩ := inferInstanceAs (Nonempty n)
  let v l := ((A ^ k) m l : ℂ) * x l
  have hτ := triangle_equality_for_primitive_power hA_prim hx_eig h_x_abs_eig h_norm_eq_r m k hAk_pos
  have hi := term_ne_zero_of_pos_entry (hAk_pos m i) (norm_pos_iff.mp (hx_abs_pos i))
  have hj := term_ne_zero_of_pos_entry (hAk_pos m j) (norm_pos_iff.mp (hx_abs_pos j))
  calc
    x i / ‖x i‖ = v i / ‖v i‖ := component_phase_alignment (hAk_pos m i) (hx_abs_pos i)
    _ = v j / ‖v j‖ := Complex.phase_eq_of_fintype_triangle_eq hτ hi hj
    _ = x j / ‖x j‖ := (component_phase_alignment (hAk_pos m j) (hx_abs_pos j)).symm

lemma eigenvector_phase_aligned_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (_ : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_norm_eq_r : ‖μ‖ = perronRoot A)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = (perronRoot A) • (fun i ↦ ‖x i‖))
    (hx_abs_pos : ∀ i, 0 < ‖x i‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = fun i ↦ c * ‖x i‖ := by
  obtain ⟨i₀⟩ := inferInstanceAs (Nonempty n)
  let c   : ℂ := x i₀ / ‖x i₀‖
  have hc_norm : ‖c‖ = 1 := by
    have h_pos : 0 < ‖x i₀‖ := hx_abs_pos i₀
    simp [c, h_pos.ne']
  have h_same_phase : ∀ j : n, x j / ‖x j‖ = c := by
    intro j
    simp_rw [c]
    exact entries_share_phase_of_primitive hA_prim hx_eig h_x_abs_eig h_norm_eq_r hx_abs_pos j i₀
  refine ⟨c, hc_norm, ?_⟩
  funext j
  have hnorm_ne_zero : ‖x j‖ ≠ 0 := (hx_abs_pos j).ne'
  calc
    x j = (x j / ‖x j‖) * ‖x j‖ := by
      simpa using eq_mul_div_ofReal_norm_complex (x j) hnorm_ne_zero
    _ = c * ‖x j‖ := by rw [h_same_phase j]

omit [Nonempty n] [DecidableEq n] in
/-- Cancel a nonzero scalar from a scalar multiple eigenvector equation. -/
lemma mulVec_eq_smul_of_smul_eigenvector
    {B : Matrix n n ℂ} {μ c : ℂ} {x y : n → ℂ} (hc : c ≠ 0)
    (hx : x = c • y) (h_eig : B *ᵥ x = μ • x) :
    B *ᵥ y = μ • y := by
  apply Pi.smul_left_cancel₀ hc
  simpa [hx, Matrix.mulVec_smul, smul_comm μ c y] using h_eig

omit [Nonempty n] [DecidableEq n] in
/-- Read a real `mulVec` eigenvector equation after complexifying the matrix and vector. -/
lemma mulVec_map_complex_apply_of_real_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : A *ᵥ v = r • v) (i : n) :
    ((A.map (algebraMap ℝ ℂ)) *ᵥ (fun j => (v j : ℂ))) i = (r : ℂ) * (v i : ℂ) := by
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) (congr_fun h i)

omit [Nonempty n] [DecidableEq n] in
/--
If an eigenvector `x` is phase‐aligned, i.e. `x i = c * ‖x i‖` for every `i`,
then its eigenvalue `μ` is real and coincides with the eigenvalue `r`
of the real vector `‖x‖`.
-/
lemma eigenvalue_eq_of_phase_aligned
    {A : Matrix n n ℝ} {μ : ℂ} {c : ℂ} (hc_norm : ‖c‖ = 1)
    {x : n → ℂ} (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_phase : ∀ i, x i = c * ‖x i‖)
    {r : ℝ} (h_x_abs_eig : A *ᵥ (fun i ↦ ‖x i‖) = r • (fun i ↦ ‖x i‖))
    {i : n} (hx_abs_pos_i : 0 < ‖x i‖) :
    μ = r := by
  let xAbs : n → ℝ := fun j => ‖x j‖
  let xAbsC : n → ℂ := fun j => (xAbs j : ℂ)
  have hx_repr : x = c • xAbsC := by
    funext j
    change x j = c * xAbsC j
    rw [h_phase j]
  have h_cancelled :
      (A.map (algebraMap ℝ ℂ)) *ᵥ xAbsC = μ • xAbsC := by
    exact mulVec_eq_smul_of_smul_eigenvector
      (Complex.ne_zero_of_norm_eq_one hc_norm) hx_repr hx_eig
  have h_real_C :
      ((A.map (algebraMap ℝ ℂ)) *ᵥ xAbsC) i = (r : ℂ) * xAbsC i := by
    simpa [xAbs, xAbsC] using
      mulVec_map_complex_apply_of_real_eigenvector h_x_abs_eig i
  have h_norm_ne_zero : xAbsC i ≠ 0 := by
    change ((‖x i‖ : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr hx_abs_pos_i.ne'
  exact (mul_right_cancel₀ h_norm_ne_zero (by
    rw [← h_real_C]
    simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h_cancelled i)).symm

lemma norm_eigenvector_is_perron_eigenvector_of_primitive_boundary
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (hx_eig : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x)
    (h_norm_eq_r : ‖μ‖ = perronRoot A) :
    A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖) := by
  have h_subinv :
      (perronRoot A) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
    simpa [h_norm_eq_r] using eigenvalue_abs_subinvariant hA_nonneg hx_eig
  exact subinvariant_equality_implies_eigenvector
    (Matrix.IsPrimitive.isIrreducible (A := A) hA_prim)
    hA_nonneg
    (fun _ => norm_nonneg _)
    (normFun_complex_ne_zero_of_ne_zero hx_ne_zero)
    h_subinv

theorem spectral_dominance_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_norm_eq_r : ‖μ‖ = perronRoot A) :
    μ = perronRoot A := by
  obtain ⟨x, hx_ne_zero, hx_eig⟩ := exists_eigenvector_of_mem_spectrum h_is_eigenvalue
  have h_x_abs_eig :
      A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖) :=
    norm_eigenvector_is_perron_eigenvector_of_primitive_boundary
      hA_prim hA_nonneg hx_ne_zero hx_eig h_norm_eq_r
  have hx_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
      hA_prim hA_nonneg h_is_eigenvalue h_norm_eq_r
      hx_ne_zero hx_eig h_x_abs_eig
  obtain ⟨c, hc_norm, h_phase⟩ :=
    eigenvector_phase_aligned_of_primitive
      hA_prim hA_nonneg h_norm_eq_r
      hx_eig h_x_abs_eig hx_abs_pos
  obtain ⟨i⟩ := inferInstanceAs (Nonempty n)
  exact eigenvalue_eq_of_phase_aligned
    hc_norm hx_eig (fun i => congrFun h_phase i) h_x_abs_eig (hx_abs_pos i)

/--
**Spectral Dominance for Primitive Matrices**
(Seneta 1.1 (c)).
If `A` is primitive with Perron root `r`, every eigenvalue `μ ≠ r`
satisfies `‖μ‖ < r`.
-/
theorem spectral_dominance_of_primitive'
    (hA_prim   : IsPrimitive A) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (μ : ℂ) (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_ne_perron : μ ≠ perronRoot A) :
    ‖μ‖ < perronRoot A := by
  have hA_irred : A.IsIrreducible := Matrix.IsPrimitive.isIrreducible (A := A) hA_prim
  have h_le : ‖μ‖ ≤ perronRoot A := by
    exact @eigenvalue_abs_le_perron_root n _ _ _ A hA_irred hA_nonneg μ h_is_eigenvalue
  exact lt_of_le_of_ne h_le fun h_eq =>
    h_ne_perron <| @spectral_dominance_of_primitive n _ _ _ A hA_prim hA_nonneg μ h_is_eigenvalue h_eq
