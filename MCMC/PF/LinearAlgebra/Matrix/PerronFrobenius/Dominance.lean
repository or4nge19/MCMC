import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import MCMC.PF.Analysis.CstarAlgebra.Classes

open Quiver.Path
namespace Matrix
open CollatzWielandt

open Quiver
open Matrix Classical Complex

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

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

omit [DecidableEq n] in
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
    intro hs
    have h_norms_zero : ∑ j, ‖z j‖ = 0 := by
      rw [← h_z_sum, hs, norm_zero]
    have h_all_zero : ∀ k, ‖z k‖ = 0 := by
      intro k
      exact eq_zero_of_sum_eq_zero
              (fun k => ‖z k‖) (fun _ => norm_nonneg _) h_norms_zero k
    have h_zj_zero : z j = 0 := by
      apply norm_eq_zero.mp
      simpa using h_all_zero j
    exact hz_ne_zero h_zj_zero
  have h_align :=
    Complex.each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq
      (s := Finset.univ)
      (v := z)
      (u := s)
      (by simp [s])
      (by simpa [s] using h_z_sum)
      hs_ne_zero
  rcases h_align j (by simp) with ⟨c, hc_nonneg, hcz⟩
  have hcz' : z j = (c : ℂ) * s := hcz
  have hcz_smul : z j = c • s := by simpa [smul_eq_mul] using hcz'
  refine ⟨c, hc_nonneg, ?_⟩
  simpa [z, s] using hcz_smul

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
private lemma sum_component_norms_eq_perron_power_norm
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
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
  have hv_ne_zero : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
  have h_dot_pos : 0 < u ⬝ᵥ v :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hv_nonneg hv_ne_zero
  have h1 : u ⬝ᵥ (A *ᵥ v) = r * (u ⬝ᵥ v) := by
    simp only [hv_eig, dotProduct_smul, smul_eq_mul]
  have h2 : (u ᵥ* A) ⬝ᵥ v = r' * (u ⬝ᵥ v) := by
    simp only [hu_eig_left, smul_dotProduct, smul_eq_mul]
  have h_eq : r * (u ⬝ᵥ v) = r' * (u ⬝ᵥ v) := by
    calc
      r * (u ⬝ᵥ v) = u ⬝ᵥ (A *ᵥ v) := (h1.symm)
      _             = (u ᵥ* A) ⬝ᵥ v := by
                        simpa using dotProduct_mulVec u A v
      _             = r' * (u ⬝ᵥ v) := h2
  have hr_eq_r' : r = r' :=
    (mul_left_inj' (ne_of_gt h_dot_pos)).mp h_eq
  calc
    perronRoot A   = r   := by symm; simpa using hr_eq_perron
    _                  = r'  := hr_eq_r'
    _                  = perronRoot Aᵀ := hr'_eq_perron

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
  let A_T := Aᵀ
  have hAT_irred : A_T.IsIrreducible := Matrix.IsIrreducible.transpose hA_irred
  have hAT_nonneg : ∀ i j, 0 ≤ A_T i j := by simp [A_T]; exact fun i j ↦ hA_nonneg j i
  obtain ⟨r, u, hr_pos, hu_pos, hu_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have h_r_eq_perron : r = perronRoot A := by
    calc
      r = perronRoot Aᵀ := eigenvalue_is_perron_root_of_positive_eigenvector
        hAT_irred hAT_nonneg hr_pos hu_pos hu_eig
      _ = perronRoot A  := by rw [← perronRoot_transpose_eq A hA_irred]
  have h_u_left_eig : u ᵥ* A = r • u := by
    rwa [vecMul_eq_mulVec_transpose]
  have h_dot_le : u ⬝ᵥ (A *ᵥ y) ≤ u ⬝ᵥ (s • y) :=
    dotProduct_le_dotProduct_of_nonneg_left' (fun i => (hu_pos i).le) h_subinv
  rw [dotProduct_mulVec, h_u_left_eig, dotProduct_smul_left, dotProduct_smul] at h_dot_le
  have h_dot_pos : 0 < u ⬝ᵥ y := dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hy_nonneg hy_ne_zero
  have h_r_le_s : r ≤ s := by
    have h_mul_le : r * (u ⬝ᵥ y) ≤ s * (u ⬝ᵥ y) := h_dot_le
    exact le_of_mul_le_mul_right h_mul_le h_dot_pos
  rwa [h_r_eq_perron] at h_r_le_s

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
  · obtain ⟨r_T, u, hr_T_pos, hu_pos, hu_eig⟩ :=
      exists_positive_eigenvector_of_irreducible (Matrix.IsIrreducible.transpose hA_irred)
    have h_u_left_eig : u ᵥ* A = r_T • u := by
      rwa [vecMul_eq_mulVec_transpose]
    have h_rT_eq_r : r_T = r := by
      calc
        r_T = perronRoot Aᵀ :=
          eigenvalue_is_perron_root_of_positive_eigenvector
            (Matrix.IsIrreducible.transpose hA_irred)
            (fun i j ↦ hA_nonneg j i) hr_T_pos hu_pos hu_eig
        _   = perronRoot A   := (perronRoot_transpose_eq A hA_irred).symm
        _   = r                 := rfl
    have h_dot_z : u ⬝ᵥ z = 0 := by
      rw [dotProduct_sub, dotProduct_mulVec, h_u_left_eig, h_rT_eq_r, dotProduct_smul_left, dotProduct_smul, smul_eq_mul, sub_self]
    have h_z_is_zero' := eq_zero_of_dotProduct_eq_zero_of_nonneg_of_pos hz_nonneg hu_pos (by rwa [dotProduct_comm])
    contradiction

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

/-- For any row `k` of an irreducible matrix with triangle equality,
all `x l` where `A k l > 0` have the same phase. -/
lemma aligned_neighbors_of_triangle_eq {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖)) :
    ∀ k l m, 0 < A k l → 0 < A k m → x l / ↑‖x l‖ = x m / ↑‖x m‖ := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_x_abs_pos : ∀ k, 0 < x_abs k :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig hx_abs_nonneg hx_abs_ne_zero
  intro k l m hAkl_pos hAkm_pos
  let z l' := (A k l' : ℂ) * x l'
  let s := ∑ l', z l'
  have hs_ne_zero : s ≠ 0 :=
    sum_s_ne_zero_of_triangle_eq hA_irred hA_nonneg h_triangle_eq h_x_abs_eig hx_ne_zero k
  have h_aligned_with_sum : ∀ l', z l' ≠ 0 → z l' / ↑‖z l'‖ = s / ↑‖s‖ := by
    intro l' hz
    have h := Complex.aligned_of_triangle_eq rfl (h_triangle_eq k) hs_ne_zero l' (by simp) hz
    exact h
  have h_zl_ne_zero : z l ≠ 0 := by
    apply term_ne_zero_of_pos_entry hAkl_pos
    exact norm_pos_iff.mp (h_x_abs_pos l)
  have h_zm_ne_zero : z m ≠ 0 := by
    apply term_ne_zero_of_pos_entry hAkm_pos
    exact norm_pos_iff.mp (h_x_abs_pos m)
  have h_align_l := h_aligned_with_sum l h_zl_ne_zero
  have h_align_m := h_aligned_with_sum m h_zm_ne_zero
  have h_xl_aligned : x l / ↑‖x l‖ = z l / ↑‖z l‖ := by
    have h_xl_ne_zero : x l ≠ 0 := norm_pos_iff.mp (h_x_abs_pos l)
    apply (Complex.aligned_of_mul_of_real_pos hAkl_pos rfl h_xl_ne_zero).symm
  have h_xm_aligned : x m / ↑‖x m‖ = z m / ↑‖z m‖ := by
    have h_xm_ne_zero : x m ≠ 0 := norm_pos_iff.mp (h_x_abs_pos m)
    apply (Complex.aligned_of_mul_of_real_pos hAkm_pos rfl h_xm_ne_zero).symm
  rw [h_xl_aligned, h_xm_aligned, h_align_l, h_align_m]

/-- The reference phase has norm 1. -/
lemma reference_phase_norm_one {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    (j₀ : n) :
    ‖x j₀ / ↑‖x j₀‖‖ = 1 := by
  let x_abs := fun i => ‖x i‖
  have hx_abs_nonneg : ∀ i, 0 ≤ x_abs i := fun i => norm_nonneg _
  have hx_abs_ne_zero : x_abs ≠ 0 := normFun_complex_ne_zero_of_ne_zero hx_ne_zero
  have h_x_abs_pos : ∀ k, 0 < x_abs k :=
    eigenvector_is_positive_of_irreducible hA_irred h_x_abs_eig hx_abs_nonneg hx_abs_ne_zero
  simp_rw [norm_div, Complex.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
  exact div_self (h_x_abs_pos j₀).ne'

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

/-- For an irreducible matrix, every row has at least one positive entry. -/
lemma IsIrreducible.exists_pos_entry_in_row {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_no_pos
  push_neg at h_no_pos
  have h_row_zero : ∀ j, A i j = 0 := by
    intro j
    have h_nonneg := hA_irred.nonneg i j
    have h_not_pos := h_no_pos j
    exact le_antisymm (h_no_pos j) h_nonneg
  obtain ⟨i₀, j₀, hA_pos⟩ := Matrix.Irreducible.exists_pos_entry (A := A) hA_irred
  letI : Quiver n := toQuiver A
  have hconn := hA_irred.connected i j₀
  obtain ⟨p, hp_pos⟩ := hconn
  have h_pos : p.length > 0 := hp_pos
  obtain ⟨c, e, p', hp_eq, hp_len_eq⟩ :=
    Quiver.Path.path_decomposition_first_edge p h_pos
  have hic_pos : 0 < A i c := e
  exact (h_row_zero c).symm.not_lt hic_pos

/-! ### Norm sums (triangle-equality layer)

Small lemmas packaging `Finset.sum_eq_zero_iff_of_nonneg` for sums of complex norms. -/

lemma norm_eq_zero_of_finset_sum_norm_eq_zero {ι : Type*} {s : Finset ι} (v : ι → ℂ)
    (h : ∑ i ∈ s, ‖v i‖ = 0) (i : ι) (hi : i ∈ s) : ‖v i‖ = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg (v j))).1 h i hi

lemma norm_eq_zero_of_fintype_sum_norm_eq_zero {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (h : ∑ i, ‖v i‖ = 0) (i : ι) : ‖v i‖ = 0 :=
  norm_eq_zero_of_finset_sum_norm_eq_zero v h i (Finset.mem_univ i)

/-- If a complex number `z` is a positive real multiple of `w ≠ 0`, then `z` and `w` have the same
  phase: `z / ‖z‖ = w / ‖w‖` (with `‖z‖` coerced to `ℂ` on the left-hand side). -/
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
  have h_sum_ne_zero : ∑ i, v i ≠ 0 := by
    intro h_sum_zero
    have h_norms_sum : ∑ i, ‖v i‖ = 0 := by
      rw [← h_triangle_eq, h_sum_zero, norm_zero]
    have h_vj_zero : ‖v j‖ = 0 := norm_eq_zero_of_fintype_sum_norm_eq_zero v h_norms_sum j
    exact hj_ne_zero (norm_eq_zero.mp h_vj_zero)
  have h_sum_phase : (∑ i, v i) / ↑‖∑ i, v i‖ = c := by
    have h_j_aligned := h_aligned j hj_ne_zero
    have h_j_sum_aligned : v j / ↑‖v j‖ = (∑ i, v i) / ↑‖∑ i, v i‖ := by
      apply Complex.aligned_of_triangle_eq rfl h_triangle_eq h_sum_ne_zero j (by simp) hj_ne_zero
    rw [h_j_aligned] at h_j_sum_aligned
    exact id (Eq.symm h_j_sum_aligned)
  calc ∑ i, v i
    = ‖∑ i, v i‖ * ((∑ i, v i) / ↑‖∑ i, v i‖) := by
        rw [← mul_comm]
        exact eq_mul_div_ofReal_norm_complex (∑ i, v i) (norm_ne_zero_iff.mpr h_sum_ne_zero)
    _ = ‖∑ i, v i‖ * c := by rw [h_sum_phase]
    _ = (∑ i, ‖v i‖ : ℂ) * c := by rw [h_triangle_eq]; rw [@ofReal_sum]

/-- In the specific context of the Perron-Frobenius theorem, if we have an irreducible
    non-negative matrix A with triangle equality for the eigenvector equation,
    then the complex sum equals the real Perron root times the phase-aligned eigenvector. -/
lemma sum_eq_perron_root_times_phase_aligned_vector
    {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {x : n → ℂ} (hx_ne_zero : x ≠ 0)
    (h_triangle_eq : ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖)
    (h_x_abs_eig : A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖))
    {i : n} (c : ℂ) (h_norm_c : ‖c‖ = 1)
    (h_aligned : ∀ j, A i j > 0 → x j ≠ 0 → x j / ↑‖x j‖ = c) :
    ∑ j, (A i j : ℂ) * x j = (perronRoot A : ℂ) * (‖x i‖ : ℂ) * c := by
  let z : n → ℂ := fun j => (A i j : ℂ) * x j
  have h_sum_ne_zero : ∑ j, z j ≠ 0 := by
    apply sum_s_ne_zero_of_triangle_eq hA_irred hA_nonneg h_triangle_eq h_x_abs_eig hx_ne_zero i
  have h_z_aligned : ∀ j, z j ≠ 0 → z j / ↑‖z j‖ = c := by
    intro j hz_ne_zero
    have h_A_pos : A i j > 0 := by
      by_contra h_not_pos
      push_neg at h_not_pos
      have h_Aij_zero : A i j = 0 := by
        apply le_antisymm _ (hA_nonneg i j)
        exact h_not_pos
      have h_z_j_zero : z j = 0 := by
        simp [z, h_Aij_zero, ofReal_zero]
      contradiction
    have h_xj_ne_zero : x j ≠ 0 := by
      by_contra h_xj_zero
      have h_z_j_zero : z j = 0 := by
        simp [z, h_xj_zero, mul_zero]
      contradiction
    have h_term_aligned : z j / ↑‖z j‖ = x j / ↑‖x j‖ := by
      apply Complex.aligned_of_mul_of_real_pos h_A_pos rfl h_xj_ne_zero
    rw [h_term_aligned]
    exact h_aligned j h_A_pos h_xj_ne_zero
  have h_sum_eq := Complex.triangle_eq_sum_with_common_phase h_norm_c (h_triangle_eq i) h_z_aligned
  have h_sum_norms : ∑ j, ‖z j‖ = perronRoot A * ‖x i‖ := by
    calc ∑ j, ‖z j‖
      = ∑ j, ‖(A i j : ℂ) * x j‖ := by rfl
      _ = ∑ j, A i j * ‖x j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, norm_ofReal, abs_of_nonneg (hA_nonneg i j)]
      _ = (A *ᵥ (fun j => ‖x j‖)) i := by simp [mulVec_apply]
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
  have tri := triangle_equality_for_primitive_power
              hA_prim hx_eig h_x_abs_eig h_norm_eq_r m k hAk_pos
  have align_i :=
    aligned_term_of_triangle_eq tri (Finset.mem_univ i)
      (term_ne_zero_of_pos_entry (hAk_pos m i) (norm_pos_iff.mp (hx_abs_pos i)))
  have align_j :=
    aligned_term_of_triangle_eq tri (Finset.mem_univ j)
      (term_ne_zero_of_pos_entry (hAk_pos m j) (norm_pos_iff.mp (hx_abs_pos j)))
  have phase_i := component_phase_alignment (hAk_pos m i) (hx_abs_pos i)
  have phase_j := component_phase_alignment (hAk_pos m j) (hx_abs_pos j)
  trans ((A ^ k) m i : ℂ) * x i / ‖((A ^ k) m i : ℂ) * x i‖
  · exact phase_i
  trans (∑ l, ((A ^ k) m l : ℂ) * x l) / ‖∑ l, ((A ^ k) m l : ℂ) * x l‖
  · exact align_i
  trans ((A ^ k) m j : ℂ) * x j / ‖((A ^ k) m j : ℂ) * x j‖
  · exact align_j.symm
  · exact phase_j.symm

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
  have hc_ne_zero : c ≠ 0 := by
    intro hc
    have : (‖(0 : ℂ)‖ : ℝ) = 1 := by
      rw [hc, norm_zero] at hc_norm
      simp at hc_norm
    norm_num at this
  set x_abs : n → ℂ := fun j ↦ (‖x j‖ : ℂ) with hx_abs_def
  have hx_repr : x = fun j ↦ c * x_abs j := by
    funext j
    rw [h_phase j, hx_abs_def]
  have h_factored :
      c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) = c • (μ • x_abs) := by
    have : (A.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x := hx_eig
    rw [hx_repr] at this
    have h_left : (A.map (algebraMap ℝ ℂ)) *ᵥ (fun j ↦ c * x_abs j) =
                  c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) := by
      rw [← mulVec_smul]; rw [hx_abs_def]; simp; rfl
    have h_right : μ • (fun j ↦ c * x_abs j) = c • (μ • x_abs) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h_left, h_right] at this
    exact this
  have h_cancelled :
      (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs = μ • x_abs := by
    have := congrArg (fun v : n → ℂ ↦ c⁻¹ • v) h_factored
    simp only at this
    have h_left : c⁻¹ • (c • ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs)) = (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs := by
      rw [smul_smul, inv_mul_cancel₀ hc_ne_zero, one_smul]
    have h_right : c⁻¹ • (c • (μ • x_abs)) = μ • x_abs := by
      rw [smul_smul, ← smul_smul]
      have : c⁻¹ * c * μ = μ := by
        rw [mul_assoc]; rw [propext (inv_mul_eq_iff_eq_mul₀ hc_ne_zero)]
      rw [propext (inv_smul_eq_iff₀ hc_ne_zero)]
    rw [h_left, h_right] at this
    exact this
  have h_real :
      (A *ᵥ fun j ↦ ‖x j‖) i = r * ‖x i‖ := by
    rw [h_x_abs_eig]
    simp only [Pi.smul_apply, smul_eq_mul]
  have h_real_C :
      ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) i = (r : ℂ) * x_abs i := by
    have h_sum : (A.map (algebraMap ℝ ℂ)) *ᵥ x_abs =
                fun j ↦ ∑ k, (A j k : ℂ) * (‖x k‖ : ℂ) := by
      ext j
      rfl
    have h_real_sum : (A *ᵥ fun j ↦ ‖x j‖) i =
                     ∑ k, A i k * ‖x k‖ := by
      rfl
    calc ((A.map (algebraMap ℝ ℂ)) *ᵥ x_abs) i
        = ∑ k, (A i k : ℂ) * (‖x k‖ : ℂ) := by rw [h_sum]
      _ = (∑ k, A i k * ‖x k‖ : ℂ) := by
          simp only
      _ = ((A *ᵥ fun j ↦ ‖x j‖) i : ℂ) := by
          rw [h_real_sum]; simp
      _ = (r * ‖x i‖ : ℂ) := by rw [h_real]; simp
      _ = (r : ℂ) * (‖x i‖ : ℂ) := by simp only
      _ = (r : ℂ) * x_abs i := by rw [hx_abs_def]
  have h_key : (r : ℂ) * x_abs i = μ * x_abs i := by
    rw [← h_real_C]
    have := congr_fun h_cancelled i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  have h_norm_ne_zero : x_abs i ≠ 0 := by
    rw [hx_abs_def]
    exact Complex.ofReal_ne_zero.mpr hx_abs_pos_i.ne'
  have h_final : (r : ℂ) = μ := by
    apply (mul_right_cancel₀ h_norm_ne_zero)
    exact h_key
  exact h_final.symm

theorem spectral_dominance_of_primitive
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {μ : ℂ} (h_is_eigenvalue : μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)))
    (h_norm_eq_r : ‖μ‖ = perronRoot A) :
    μ = perronRoot A := by
  -- 1.  we obtain a (non-zero) eigenvector `x` corresponding to `μ`.
  let B := A.map (algebraMap ℝ ℂ)
  have h_spec : μ ∈ spectrum ℂ (toLin' B) := by
    rwa [spectrum.Matrix_toLin'_eq_spectrum]
  obtain ⟨x, hx_ne_zero, hx_eig_lin⟩ := Module.End.exists_eigenvector_of_mem_spectrum h_spec
  have hx_eig : B *ᵥ x = μ • x := by rwa [toLin'_apply] at hx_eig_lin
  -- 2.  we build the sub-invariance inequality  r • |x| ≤ A ⋅ |x|.
  have h_subinv :
      (perronRoot A) • (fun i => ‖x i‖) ≤ A *ᵥ (fun i => ‖x i‖) := by
    have := eigenvalue_abs_subinvariant hA_nonneg hx_eig
    simpa [h_norm_eq_r] using this
  -- 3. we upgrade sub-invariance to equality, so `|x|` is a Perron eigenvector.
  have h_x_abs_eig :
      A *ᵥ (fun i => ‖x i‖) = (perronRoot A) • (fun i => ‖x i‖) := by
    have hA_irred : A.IsIrreducible := Matrix.IsPrimitive.isIrreducible (A := A) hA_prim
    have hx_abs_nonneg : ∀ i, 0 ≤ ‖x i‖ := fun _ ↦ norm_nonneg _
    have hx_abs_ne_zero : (fun i => ‖x i‖) ≠ 0 := by
      intro h_abs
      have : x = 0 := by
        funext i
        have : ‖x i‖ = 0 := congrFun h_abs i
        exact (norm_eq_zero).1 this
      exact hx_ne_zero this
    exact
      subinvariant_equality_implies_eigenvector
        hA_irred hA_nonneg hx_abs_nonneg hx_abs_ne_zero h_subinv
  -- 4. we turn the triangle inequality into equality.
  have h_triangle_eq :
      ∀ i, ‖∑ j, (A i j : ℂ) * x j‖ = ∑ j, ‖(A i j : ℂ) * x j‖ :=
    triangle_equality_of_norm_eq_perron_root
      hA_nonneg hx_eig h_norm_eq_r h_x_abs_eig
  -- 5.  Strict positivity of `|x|`.
  have hx_abs_pos : ∀ i, 0 < ‖x i‖ :=
    eigenvector_norm_pos_of_primitive_and_norm_eq_perron_root
      hA_prim hA_nonneg h_is_eigenvalue h_norm_eq_r
      hx_ne_zero hx_eig h_x_abs_eig
  -- 6.  Global phase alignment of the complex eigenvector `x`.
  obtain ⟨c, hc_norm, h_phase⟩ :=
    eigenvector_phase_aligned_of_primitive
      hA_prim hA_nonneg h_norm_eq_r
      hx_eig h_x_abs_eig hx_abs_pos
  -- μ = r  from the phase-aligned situation.
  obtain ⟨i⟩ := inferInstanceAs (Nonempty n)
  have hμ_eq_r :
      μ = perronRoot A :=
    eigenvalue_eq_of_phase_aligned
      hc_norm
      hx_eig
      (by
        intro i
        exact congrFun h_phase i)
      h_x_abs_eig
      (hx_abs_pos i)
  exact hμ_eq_r

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
  have h_lt_or_eq : ‖μ‖ < perronRoot A ∨ ‖μ‖ = perronRoot A :=
    lt_or_eq_of_le h_le
  cases h_lt_or_eq with
  | inl h_lt   => exact h_lt
  | inr h_eq   =>
      have h_eqμ : μ = perronRoot A := by
        exact @spectral_dominance_of_primitive n _ _ _ A hA_prim hA_nonneg μ h_is_eigenvalue h_eq
      exact (h_ne_perron h_eqμ).elim
