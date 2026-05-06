import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Multiplicity

/-!
# ML-matrices

This file contains the continuous-time Perron-Frobenius API for Metzler-Leontief matrices
from Seneta's Section 2.3.

## Main definitions

* `Matrix.IsMLMatrix`: off-diagonal nonnegativity.
* `Matrix.mlShift`: a diagonal shift making an ML-matrix entrywise nonnegative.
* `Matrix.mlShifted`: the shifted nonnegative matrix.
* `Matrix.IsMLIrreducible`: irreducibility of the shifted matrix.
* `Matrix.mlPerronRoot`: the dominant real eigenvalue obtained from the shifted Perron root.

## Main statements

* `Matrix.exists_positive_eigenvector_of_irreducible_mlMatrix`: the shifted Perron root gives a
  positive eigenvector for the original ML-matrix.
* `Matrix.mlPerronRoot_is_spectral_bound`: the ML Perron root dominates the real parts of the other
  complex spectral values.
* `Matrix.isMLIrreducible_iff_forall_exp_pos`: for nontrivial index types, irreducibility is
  equivalent to strict positivity of the matrix exponential for positive times.
* `Matrix.exp_asymptotics_of_irreducible_mlMatrix`: the continuous-time rank-one asymptotic
  expansion.

## Implementation notes

The whole file is deliberately built by reducing ML-matrices to the existing nonnegative finite
matrix API through the diagonal shift `mlShifted`.

-/

namespace Matrix

open NormedSpace
open CollatzWielandt

section MLMatrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/--
An ML-matrix has nonnegative off-diagonal entries.
-/
def IsMLMatrix (B : Matrix n n ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ B i j

/--
A diagonal shift large enough to make every diagonal entry nonnegative.
-/
noncomputable def mlShift (B : Matrix n n ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty fun i => -B i i

/--
The nonnegative matrix obtained from an ML-matrix by adding the diagonal shift `mlShift B`.
-/
noncomputable def mlShifted (B : Matrix n n ℝ) : Matrix n n ℝ :=
  mlShift B • 1 + B

/--
Irreducibility for an ML-matrix is defined by irreducibility of its shifted nonnegative companion.
-/
def IsMLIrreducible (B : Matrix n n ℝ) : Prop :=
  (mlShifted B).IsIrreducible

/--
The dominant real eigenvalue of an ML-matrix, defined by shifting back the Perron root of
`mlShifted B`.
-/
noncomputable def mlPerronRoot (B : Matrix n n ℝ) : ℝ :=
  perronRoot (mlShifted B) - mlShift B

/--
The Perron-Frobenius existence theorem needed for ML-matrices is already available via
`perron_root_eq_positive_eigenvalue` applied to `mlShifted B`.
The missing local API is only the algebraic bridge from the shifted eigen-equation back to `B`.
-/
@[simp] lemma mlShifted_mulVec (B : Matrix n n ℝ) (v : n → ℝ) :
    mlShifted B *ᵥ v = mlShift B • v + B *ᵥ v := by
  simp [mlShifted, add_mulVec, one_mulVec, Matrix.smul_mulVec]

/--
An eigenvector of the shifted nonnegative companion matrix yields an eigenvector of the original
ML-matrix after subtracting the diagonal shift from the eigenvalue.
-/
lemma eig_of_mlShifted_eig {B : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : mlShifted B *ᵥ v = r • v) :
    B *ᵥ v = (r - mlShift B) • v := by
  have h' : mlShift B • v + B *ᵥ v = r • v := by
    simpa using h
  have : B *ᵥ v = r • v - mlShift B • v := eq_sub_of_add_eq' h'
  simpa [sub_smul] using this

/--
The shifted matrix of an ML-matrix is entrywise nonnegative.
-/
theorem mlShifted_nonneg {B : Matrix n n ℝ} (hB : IsMLMatrix B) :
    ∀ i j, 0 ≤ mlShifted B i j := by
  intro i j
  unfold mlShifted
  rw [Matrix.add_apply, Matrix.smul_one_eq_diagonal]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    have h : -B i i ≤ mlShift B := by
      apply Finset.le_sup'_of_le (f := fun k => -B k k) (Finset.mem_univ i) (le_refl _)
    linarith
  · rw [Matrix.diagonal_apply_ne _ hij, zero_add]
    exact hB i j hij

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/-- The transpose of an ML-matrix is again an ML-matrix. -/
theorem IsMLMatrix.transpose {B : Matrix n n ℝ} (hB : IsMLMatrix B) : IsMLMatrix Bᵀ := by
  intro i j hij
  exact hB j i (Ne.symm hij)

omit [Fintype n] [DecidableEq n] [Nonempty n] in
@[simp] theorem isMLMatrix_transpose_iff {B : Matrix n n ℝ} :
    IsMLMatrix Bᵀ ↔ IsMLMatrix B := by
  constructor
  · intro hB
    simpa using hB.transpose
  · exact IsMLMatrix.transpose

omit [DecidableEq n] in
@[simp] theorem mlShift_transpose (B : Matrix n n ℝ) :
    mlShift Bᵀ = mlShift B := by
  simp [mlShift, transpose_apply]

@[simp] theorem mlShifted_transpose (B : Matrix n n ℝ) :
    mlShifted Bᵀ = (mlShifted B)ᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [mlShifted, transpose_apply, Matrix.add_apply, Matrix.smul_apply]
  · have hji : j ≠ i := Ne.symm hij
    simp [mlShifted, transpose_apply, Matrix.add_apply, Matrix.smul_apply, hij, hji]

/-- A complex eigenvector of an ML-matrix is an eigenvector of its shifted companion. -/
theorem mlShifted_map_eig_of_eig {B : Matrix n n ℝ} {μ : ℂ} {x : n → ℂ}
    (hx_eig : (B.map (algebraMap ℝ ℂ)) *ᵥ x = μ • x) :
    ((mlShifted B).map (algebraMap ℝ ℂ)) *ᵥ x =
      (μ + (mlShift B : ℂ)) • x := by
  rw [show (mlShifted B).map (algebraMap ℝ ℂ) =
      (mlShift B : ℂ) • (1 : Matrix n n ℂ) + B.map (algebraMap ℝ ℂ) by
    ext i j
    rw [Matrix.smul_one_eq_diagonal]
    by_cases hij : i = j
    · subst hij
      simp [mlShifted, Matrix.map_apply, Matrix.add_apply, Matrix.smul_one_eq_diagonal]
    · simp [mlShifted, Matrix.map_apply, Matrix.add_apply, Matrix.smul_one_eq_diagonal, hij]]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hx_eig]
  ext i
  change (mlShift B : ℂ) * x i + μ * x i = (μ + (mlShift B : ℂ)) * x i
  ring

/-- Complex spectral values shift along the nonnegative companion matrix `mlShifted`. -/
theorem mem_spectrum_mlShifted_add_of_mem_spectrum
    {B : Matrix n n ℝ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ))) :
    μ + (mlShift B : ℂ) ∈ spectrum ℂ ((mlShifted B).map (algebraMap ℝ ℂ)) := by
  obtain ⟨x, hx_ne, hx_eig⟩ := exists_eigenvector_of_mem_spectrum (A' := B) hμ
  exact mem_spectrum_of_eigenvalue hx_ne (mlShifted_map_eig_of_eig hx_eig)

/-- ML-irreducibility is invariant under transpose. -/
theorem IsMLIrreducible.transpose {B : Matrix n n ℝ} (hB : IsMLIrreducible B) :
    IsMLIrreducible Bᵀ := by
  unfold IsMLIrreducible at hB ⊢
  rw [mlShifted_transpose]
  exact Matrix.IsIrreducible.transpose hB

@[simp] theorem isMLIrreducible_transpose_iff {B : Matrix n n ℝ} :
    IsMLIrreducible Bᵀ ↔ IsMLIrreducible B := by
  constructor
  · intro hB
    simpa using hB.transpose
  · exact IsMLIrreducible.transpose

/-- The ML Perron root is invariant under transpose for irreducible ML-matrices. -/
theorem mlPerronRoot_transpose_eq {B : Matrix n n ℝ} (hB : IsMLIrreducible B) :
    mlPerronRoot Bᵀ = mlPerronRoot B := by
  calc
    mlPerronRoot Bᵀ = perronRoot ((mlShifted B)ᵀ) - mlShift B := by
      simp [mlPerronRoot]
    _ = perronRoot (mlShifted B) - mlShift B := by
      rw [perronRoot_transpose_eq (mlShifted B) hB]
    _ = mlPerronRoot B := by rfl

/--
An irreducible ML-matrix admits a strictly positive eigenvector for its dominant real eigenvalue.
-/
theorem exists_positive_eigenvector_of_irreducible_mlMatrix
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ B *ᵥ v = mlPerronRoot B • v := by
  obtain ⟨r, v, _hr_pos, hv_pos, hv_eig, hperron_eq⟩ :=
    perron_root_eq_positive_eigenvalue hB_irred (mlShifted_nonneg hB_ml)
  refine ⟨v, hv_pos, ?_⟩
  have hB_eig : B *ᵥ v = (r - mlShift B) • v :=
    eig_of_mlShifted_eig hv_eig
  simpa [mlPerronRoot, hperron_eq] using hB_eig

/--
An irreducible ML-matrix admits a strictly positive left eigenvector for its dominant real
eigenvalue.
-/
theorem exists_positive_left_eigenvector_of_irreducible_mlMatrix
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ w ᵥ* B = mlPerronRoot B • w := by
  obtain ⟨w, hw_pos, hw_eig⟩ :=
    exists_positive_eigenvector_of_irreducible_mlMatrix hB_ml.transpose hB_irred.transpose
  refine ⟨w, hw_pos, ?_⟩
  have hw_eig' : Bᵀ *ᵥ w = mlPerronRoot B • w := by
    simpa [mlPerronRoot_transpose_eq hB_irred] using hw_eig
  simpa [vecMul_eq_mulVec_transpose] using hw_eig'

/-- The ML Perron root is a complex spectral value of the original ML-matrix. -/
theorem mlPerronRoot_mem_complex_spectrum
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    (mlPerronRoot B : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
  obtain ⟨v, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible_mlMatrix hB_ml hB_irred
  let vC : n → ℂ := fun i => (v i : ℂ)
  have hvC_ne_zero : vC ≠ 0 := by
    intro h
    obtain ⟨i, _⟩ := Finset.univ_nonempty (α := n)
    exact (Complex.ofReal_ne_zero.mpr (hv_pos i).ne') (congr_fun h i)
  have hvC_eig :
      (B.map (algebraMap ℝ ℂ)) *ᵥ vC = (mlPerronRoot B : ℂ) • vC := by
    ext i
    simpa [vC, Pi.smul_apply, smul_eq_mul] using
      mulVec_map_complex_apply_of_real_eigenvector hv_eig i
  exact mem_spectrum_of_eigenvalue hvC_ne_zero hvC_eig

/--
The ML Perron root lies in the complex spectrum and strictly dominates the real parts of the other
spectral values.
-/
theorem mlPerronRoot_is_spectral_bound
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    (mlPerronRoot B : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) ∧
      ∀ μ ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)),
        μ ≠ (mlPerronRoot B : ℂ) → μ.re < mlPerronRoot B := by
  refine ⟨mlPerronRoot_mem_complex_spectrum hB_ml hB_irred, ?_⟩
  intro μ hμ hμ_ne
  let c : ℝ := mlShift B
  let N : Matrix n n ℝ := mlShifted B
  have h_shift_spec : μ + (c : ℂ) ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)) :=
    by simpa [N, c] using mem_spectrum_mlShifted_add_of_mem_spectrum (B := B) hμ
  have hN_nonneg : ∀ i j, 0 ≤ N i j := by
    simpa [N] using mlShifted_nonneg hB_ml
  have h_abs : ‖μ + (c : ℂ)‖ ≤ perronRoot N :=
    eigenvalue_abs_le_perron_root hB_irred hN_nonneg h_shift_spec
  have h_ne_shift : μ + (c : ℂ) ≠ (perronRoot N : ℂ) := by
    intro h_eq
    apply hμ_ne
    calc
      μ = (μ + (c : ℂ)) - (c : ℂ) := by ring
      _ = (perronRoot N : ℂ) - (c : ℂ) := by rw [h_eq]
      _ = (mlPerronRoot B : ℂ) := by simp [N, c, mlPerronRoot]
  have h_re_le : (μ + (c : ℂ)).re ≤ perronRoot N :=
    le_trans (Complex.re_le_norm _) h_abs
  have h_re_ne : (μ + (c : ℂ)).re ≠ perronRoot N := by
    intro h_re_eq
    have hnorm_eq : ‖μ + (c : ℂ)‖ = perronRoot N := by
      apply le_antisymm h_abs
      calc
        perronRoot N = (μ + (c : ℂ)).re := h_re_eq.symm
        _ ≤ ‖μ + (c : ℂ)‖ := Complex.re_le_norm _
    have hnormsq : Complex.normSq (μ + (c : ℂ)) = (perronRoot N) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hnorm_eq]
    rw [Complex.normSq_apply] at hnormsq
    have h_re_sq : (μ + (c : ℂ)).re * (μ + (c : ℂ)).re =
        (perronRoot N) ^ 2 := by
      rw [h_re_eq]
      ring
    have him_mul_zero : (μ + (c : ℂ)).im * (μ + (c : ℂ)).im = 0 := by
      nlinarith [hnormsq, h_re_sq]
    have him_zero : (μ + (c : ℂ)).im = 0 := mul_self_eq_zero.mp him_mul_zero
    exact h_ne_shift <| Complex.ext h_re_eq (by simpa using him_zero)
  have h_re_lt : (μ + (c : ℂ)).re < perronRoot N :=
    lt_of_le_of_ne h_re_le h_re_ne
  have : μ.re + c < perronRoot N := by
    simpa [c] using h_re_lt
  have htarget : μ.re < perronRoot N - c := by
    linarith
  simpa [N, c, mlPerronRoot] using htarget

section ExponentialPositivity

open scoped Matrix.Norms.Operator

omit [Nonempty n] in
private lemma exp_entry_eq_tsum (A : Matrix n n ℝ) (t : ℝ) (i j : n) :
    exp (t • A) i j =
      ∑' k : ℕ, (((k.factorial : ℝ)⁻¹) • ((t • A) ^ k) : Matrix n n ℝ) i j := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  let φ : Matrix n n ℝ →L[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  change φ (∑' k : ℕ, (((k.factorial : ℝ)⁻¹) • ((t • A) ^ k) : Matrix n n ℝ)) = _
  rw [ContinuousLinearMap.map_tsum]
  · rfl
  · simpa [NormedSpace.expSeries_apply_eq] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) (t • A))

omit [Nonempty n] in
/-- An irreducible nonnegative matrix has strictly positive exponential entries at positive times. -/
private theorem exp_pos_of_irreducible
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) :
    ∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • A) i j := by
  intro t ht i j
  rw [exp_entry_eq_tsum A t i j]
  let f : ℕ → ℝ :=
    fun k => (((k.factorial : ℝ)⁻¹) • ((t • A) ^ k) : Matrix n n ℝ) i j
  change 0 < ∑' k : ℕ, f k
  have hf_summable : Summable f := by
    let φ : Matrix n n ℝ →L[ℝ] ℝ :=
      (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    change Summable fun k : ℕ =>
      φ ((((k.factorial : ℝ)⁻¹) • ((t • A) ^ k) : Matrix n n ℝ))
    apply ContinuousLinearMap.summable φ
    simpa [NormedSpace.expSeries_apply_eq] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) (t • A))
  have hf_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) <|
      pow_entrywise_nonneg (fun a b => mul_nonneg ht.le (hA_irred.nonneg a b)) k i j
  letI : Quiver n := Matrix.toQuiver A
  obtain ⟨p, _hp_pos⟩ := hA_irred.connected i j
  have hpow_pos : 0 < (A ^ p.length) i j := by
    rw [Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_irred.nonneg p.length i j]
    exact ⟨⟨p, rfl⟩⟩
  have hf_pos : 0 < f p.length := by
    dsimp [f]
    rw [smul_pow]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))) <|
      mul_pos (pow_pos ht _) hpow_pos
  exact hf_summable.tsum_pos hf_nonneg p.length hf_pos

omit [Nonempty n] in
private lemma exp_entry_eq_zero_of_forall_pow_eq_zero
    {A : Matrix n n ℝ} {t : ℝ} {i j : n}
    (hpow_zero : ∀ k : ℕ, ((t • A) ^ k) i j = 0) :
    exp (t • A) i j = 0 := by
  rw [exp_entry_eq_tsum A t i j]
  let f : ℕ → ℝ :=
    fun k => (((k.factorial : ℝ)⁻¹) • ((t • A) ^ k) : Matrix n n ℝ) i j
  change (∑' k : ℕ, f k) = 0
  have hf_zero : ∀ k, f k = 0 := by
    intro k
    simp [f, hpow_zero k]
  simp [hf_zero]

omit [Nonempty n] in
private lemma exists_path_of_exp_pos_of_nonneg_of_ne
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {i j : n} (hij : i ≠ j)
    (hpos : 0 < exp ((1 : ℝ) • A) i j) :
    (letI : Quiver n := Matrix.toQuiver A; ∃ p : Quiver.Path i j, 0 < p.length) := by
  letI : Quiver n := Matrix.toQuiver A
  by_contra h_no
  push Not at h_no
  have hpow_zero : ∀ k : ℕ, (((1 : ℝ) • A) ^ k) i j = 0 := by
    intro k
    rw [one_smul]
    by_cases hk : k = 0
    · subst hk
      simp [hij]
    · have hpow_nonneg : 0 ≤ (A ^ k) i j := pow_entrywise_nonneg hA_nonneg k i j
      have hnotpos : ¬ 0 < (A ^ k) i j := by
        intro hpow_pos
        obtain ⟨p⟩ :=
          (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i j).mp hpow_pos
        exact not_lt_of_ge (h_no p) (by simpa [p.property] using Nat.pos_of_ne_zero hk)
      exact le_antisymm (not_lt.mp hnotpos) hpow_nonneg
  have hzero :=
    exp_entry_eq_zero_of_forall_pow_eq_zero (A := A) (t := 1) (i := i) (j := j) hpow_zero
  linarith

omit [Nonempty n] in
/--
For a nontrivially indexed nonnegative matrix, irreducibility is equivalent to strict positivity of
the matrix exponential at every positive time.
-/
private theorem isIrreducible_iff_forall_exp_pos_of_nonneg
    [Nontrivial n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    A.IsIrreducible ↔ ∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • A) i j := by
  constructor
  · intro hA_irred
    exact exp_pos_of_irreducible hA_irred
  · intro h_exp
    refine ⟨hA_nonneg, ?_⟩
    intro i j
    letI : Quiver n := Matrix.toQuiver A
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hki⟩ := exists_ne i
      obtain ⟨p1, hp1⟩ :=
        exists_path_of_exp_pos_of_nonneg_of_ne hA_nonneg (Ne.symm hki)
          (h_exp 1 zero_lt_one i k)
      obtain ⟨p2, hp2⟩ :=
        exists_path_of_exp_pos_of_nonneg_of_ne hA_nonneg hki
          (h_exp 1 zero_lt_one k i)
      refine ⟨p1.comp p2, ?_⟩
      rw [Quiver.Path.length_comp]
      exact Nat.add_pos_left hp1 _
    · exact exists_path_of_exp_pos_of_nonneg_of_ne hA_nonneg hij
        (h_exp 1 zero_lt_one i j)

omit [Nonempty n] in
private lemma exp_smul_one_real (a : ℝ) :
    exp (a • (1 : Matrix n n ℝ)) = Real.exp a • (1 : Matrix n n ℝ) := by
  rw [show a • (1 : Matrix n n ℝ) = diagonal fun _ : n => a by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]]
  rw [Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Real.exp_eq_exp_ℝ]
  · simp [Real.exp_eq_exp_ℝ, hij]

/-- Exponentiating the shifted companion only rescales `exp (t • B)` by a positive scalar. -/
private theorem exp_mlShifted_eq (B : Matrix n n ℝ) (t : ℝ) :
    exp (t • mlShifted B) = Real.exp (t * mlShift B) • exp (t • B) := by
  have harg : t • mlShifted B = (t * mlShift B) • (1 : Matrix n n ℝ) + t • B := by
    rw [mlShifted, smul_add]
    congr 1
    ext i j
    simp [Matrix.smul_apply, mul_assoc]
  have hcomm : Commute ((t * mlShift B) • (1 : Matrix n n ℝ)) (t • B) := by
    simpa using (Commute.one_left (t • B)).smul_left (t * mlShift B)
  rw [harg]
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  rw [exp_smul_one_real]
  simp

/-- The diagonal ML shift preserves strict positivity of every matrix exponential entry. -/
private theorem exp_mlShifted_apply_pos_iff (B : Matrix n n ℝ) (t : ℝ) (i j : n) :
    0 < exp (t • mlShifted B) i j ↔ 0 < exp (t • B) i j := by
  rw [exp_mlShifted_eq]
  simp [Matrix.smul_apply, Real.exp_pos]

/--
For an ML-matrix on a nontrivial finite index type, irreducibility is equivalent to strict
positivity of the matrix exponential at all positive times.
-/
theorem isMLIrreducible_iff_forall_exp_pos
    [Nontrivial n]
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) :
    IsMLIrreducible B ↔ ∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • B) i j := by
  have h_exp_pos_iff :
      (∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • B) i j) ↔
        ∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • mlShifted B) i j := by
    constructor
    · intro h t ht i j
      exact (exp_mlShifted_apply_pos_iff B t i j).2 (h t ht i j)
    · intro h t ht i j
      exact (exp_mlShifted_apply_pos_iff B t i j).1 (h t ht i j)
  change (mlShifted B).IsIrreducible ↔ ∀ t : ℝ, t > 0 → ∀ i j, 0 < exp (t • B) i j
  exact (isIrreducible_iff_forall_exp_pos_of_nonneg (mlShifted_nonneg hB_ml)).trans
    h_exp_pos_iff.symm

end ExponentialPositivity

/--
Continuous-time Perron-Frobenius asymptotics for an irreducible ML-matrix.

The Perron right/left eigenvectors are already supplied by the shifted finite Perron-Frobenius API;
the remaining analytic content is the exponential decay estimate.
-/
theorem exp_asymptotics_of_irreducible_mlMatrix
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    ∃ τ' C : ℝ, τ' < mlPerronRoot B ∧ 0 < C ∧
      ∃ v w : n → ℝ,
        (∀ i, 0 < v i) ∧
        (∀ i, 0 < w i) ∧
        B *ᵥ v = mlPerronRoot B • v ∧
        w ᵥ* B = mlPerronRoot B • w ∧
        ∀ t > 0, ∀ i j,
          |exp (t • B) i j - Real.exp (mlPerronRoot B * t) * v i * w j|
            ≤ C * Real.exp (τ' * t) := by
  obtain ⟨v, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible_mlMatrix hB_ml hB_irred
  obtain ⟨w, hw_pos, hw_eig⟩ :=
    exists_positive_left_eigenvector_of_irreducible_mlMatrix hB_ml hB_irred
  obtain ⟨τ', C, hτ', hC, h_bound⟩ :
      ∃ τ' C : ℝ, τ' < mlPerronRoot B ∧ 0 < C ∧
        ∀ t > 0, ∀ i j,
          |exp (t • B) i j - Real.exp (mlPerronRoot B * t) * v i * w j|
            ≤ C * Real.exp (τ' * t) := by
    sorry
  exact ⟨τ', C, hτ', hC, v, w, hv_pos, hw_pos, hv_eig, hw_eig, h_bound⟩

end MLMatrix

end Matrix
