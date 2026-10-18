/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import MCMC.ToMathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Gelfand radius of real matrices

With the `ℓ∞` operator norm (`Matrix.Norms.Operator`), the Gelfand radius of a real matrix `A` is
the spectral radius of `A` as a complex matrix and the Gelfand radius of `x ↦ A *ᵥ x` on `n → ℝ`
with the sup norm.

## Main statements

* `Matrix.gelfandRadius_toContinuousLinearMap_toLin'`
* `Matrix.spectralRadius_map_algebraMap_eq_gelfandRadius`

Staged for `Mathlib/Analysis/Matrix/GelfandRadius.lean` (created by #44891, merged 2026-10-17 as
`6f48dc052ef6`, with `Matrix.gelfandRadius_mul_comm`). Searched on 2026-10-17: that file and
mathlib master relate neither the matrix Gelfand radius to the complex spectral radius nor to the
operator `toLin'`.
-/

open Filter Topology
open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Gelfand radius of a real matrix is that of `x ↦ A *ᵥ x` on `n → ℝ` with the sup norm. -/
theorem gelfandRadius_toContinuousLinearMap_toLin' (A : Matrix n n ℝ) :
    gelfandRadius (LinearMap.toContinuousLinearMap (toLin' A)) = gelfandRadius A := by
  refine tendsto_nhds_unique (tendsto_gelfandRadius _) ((tendsto_gelfandRadius A).congr fun k ↦ ?_)
  rw [← linfty_opNorm_toMatrix, ContinuousLinearMap.toLinearMap_pow,
    LinearMap.coe_toContinuousLinearMap, ← toLin'_pow, LinearMap.toMatrix'_toLin']

/-- The Gelfand radius of a real matrix is the spectral radius of the same matrix over `ℂ`. -/
theorem spectralRadius_map_algebraMap_eq_gelfandRadius (A : Matrix n n ℝ) :
    spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) = ENNReal.ofReal (gelfandRadius A) := by
  rw [spectrum.spectralRadius_eq_gelfandRadius]
  congr 1
  refine tendsto_nhds_unique (tendsto_gelfandRadius _) ((tendsto_gelfandRadius A).congr fun k ↦ ?_)
  rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, linfty_opNorm_def,
    linfty_opNorm_def]
  simp

/-- Powers of `x ↦ A *ᵥ x` are `x ↦ A ^ k *ᵥ x`. -/
theorem toContinuousLinearMap_toLin'_pow (A : Matrix n n ℝ) (k : ℕ) :
    LinearMap.toContinuousLinearMap (toLin' A) ^ k =
      LinearMap.toContinuousLinearMap (toLin' (A ^ k)) :=
  ContinuousLinearMap.coe_injective <| by
    rw [ContinuousLinearMap.toLinearMap_pow, LinearMap.coe_toContinuousLinearMap,
      LinearMap.coe_toContinuousLinearMap, toLin'_pow]

end Matrix
