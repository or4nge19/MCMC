import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Multiplicity

/-!
# ML-matrices

This file contains the continuous-time Perron-Frobenius scaffold for Metzler-Leontief matrices
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
* `Matrix.isMLIrreducible_iff_forall_exp_pos`: irreducibility is equivalent to strict positivity of
  the matrix exponential for positive times.
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
  perronRoot_alt (mlShifted B) - mlShift B

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

/--
An irreducible ML-matrix admits a strictly positive eigenvector for its dominant real eigenvalue.
-/
theorem exists_positive_eigenvector_of_irreducible_mlMatrix
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ B *ᵥ v = mlPerronRoot B • v := by
  sorry

/--
The ML Perron root lies in the complex spectrum and strictly dominates the real parts of the other
spectral values.
-/
theorem mlPerronRoot_is_spectral_bound
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    (mlPerronRoot B : ℂ) ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) ∧
      ∀ μ ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)),
        μ ≠ (mlPerronRoot B : ℂ) → μ.re < mlPerronRoot B := by
  sorry

/--
For an ML-matrix, irreducibility is equivalent to strict positivity of the matrix exponential at
all positive times.
-/
theorem isMLIrreducible_iff_forall_exp_pos
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) :
    IsMLIrreducible B ↔ ∀ t > 0, ∀ i j, 0 < exp (t • B) i j := by
  sorry

/--
Continuous-time Perron-Frobenius asymptotics for an irreducible ML-matrix.
-/
theorem exp_asymptotics_of_irreducible_mlMatrix
    {B : Matrix n n ℝ} (hB_ml : IsMLMatrix B) (hB_irred : IsMLIrreducible B) :
    ∃ τ' C : ℝ, τ' < mlPerronRoot B ∧ 0 < C ∧
      ∃ v w : n → ℝ,
        (∀ i, 0 < v i) ∧
        (∀ i, 0 < w i) ∧
        B *ᵥ v = mlPerronRoot B • v ∧
        Bᵀ *ᵥ w = mlPerronRoot B • w ∧
        ∀ t > 0, ∀ i j,
          |exp (t • B) i j - Real.exp (mlPerronRoot B * t) * v i * w j|
            ≤ C * Real.exp (τ' * t) := by
  sorry

end MLMatrix

end Matrix
