import MCMC.Countable.CountableStochastic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.UniformSpace.Completion

/-!
# Martin boundary and potential theory

This file formalizes the countable-state Martin-boundary and potential-theoretic material from
Seneta's Section 5.5.

## Main definitions

* `infMatMulVec`: left multiplication of an infinite real matrix against an `ENNReal` vector, using
  `ENNReal.ofReal` on the matrix entries.
* `GreenFunction`, `greenMulVec`: the Green kernel and its action on `ENNReal` vectors.
* `IsSuperregular`, `IsRegular`, `IsPotential`: the basic potential-theoretic predicates.
* `MartinKernel`, `martinDist`: the Martin kernel and the weighted distance built from it.
* `martinPseudoMetricSpace`, `MartinBoundary`, `MartinKernelExt`: the induced completion and the
  extension of the Martin kernel to the boundary.

## Main statements

* `riesz_decomposition_of_superregular`: the abstract Riesz decomposition of a superregular vector.
* `riesz_decomposition_explicit`: the explicit decomposition into a regular part and a Green
  potential.
* `compactSpace_martinBoundary`: compactness of the Martin compactification.
* `poisson_martin_integral_representation`: the Martin integral representation of superregular
  vectors.

## Implementation notes

The definitions in this file are written in terms of the existing countable-state `InfMatrix` API.
They are intended for substochastic matrices, so the use of `ENNReal.ofReal` is honest in the
intended regime even though the raw definitions are formulated without bundled nonnegativity data.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Tags

Martin boundary, potential theory, Green function, compactification, Markov chain
-/

namespace MCMC.Countable

open Filter MeasureTheory Topology
open scoped ENNReal Topology

section ChapterFiveBoundary

variable {α : Type*} [DecidableEq α]

/--
Left multiplication of an infinite real matrix against an `ENNReal` vector.

This definition uses `ENNReal.ofReal` on the matrix entries and is therefore intended for the
nonnegative matrices occurring in potential theory.
-/
noncomputable def infMatMulVec (P : InfMatrix α) (u : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun i => ∑' j, ENNReal.ofReal (P i j) * u j

/--
The Green kernel of an infinite matrix, defined by summing all powers entrywise in `ENNReal`.
-/
noncomputable def GreenFunction (P : InfMatrix α) : α → α → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, ENNReal.ofReal (InfMatrix.pow P k i j)

/--
The action of the Green kernel on an `ENNReal` vector.
-/
noncomputable def greenMulVec (P : InfMatrix α) (u : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun i => ∑' j, GreenFunction P i j * u j

/--
A vector is superregular if applying the matrix once produces a pointwise smaller vector.
-/
def IsSuperregular (P : InfMatrix α) (u : α → ℝ≥0∞) : Prop :=
  ∀ i, infMatMulVec P u i ≤ u i

/--
A vector is regular if applying the matrix once leaves it fixed.
-/
def IsRegular (P : InfMatrix α) (u : α → ℝ≥0∞) : Prop :=
  ∀ i, infMatMulVec P u i = u i

/--
A vector is a potential if it lies in the range of the Green kernel.
-/
def IsPotential (P : InfMatrix α) (v : α → ℝ≥0∞) : Prop :=
  ∃ u : α → ℝ≥0∞, v = greenMulVec P u

/--
The Martin kernel normalized at the reference state `ref`.
-/
noncomputable def MartinKernel (P : InfMatrix α) (ref : α) (i j : α) : ℝ≥0∞ :=
  GreenFunction P i j / GreenFunction P ref j

/--
The weighted Martin distance attached to `P`, `ref`, and `w`.
-/
noncomputable def martinDist (P : InfMatrix α) (ref : α) (w : α → ℝ) (i j : α) : ℝ :=
  ∑' k, w k * |(MartinKernel P ref k i).toReal - (MartinKernel P ref k j).toReal|

/--
The pseudometric space structure induced by the Martin distance.
-/
noncomputable def martinPseudoMetricSpace
    (P : InfMatrix α) (ref : α) (w : α → ℝ) (_hw_nonneg : ∀ i, 0 ≤ w i) (_hw : Summable w) :
    PseudoMetricSpace α where
  dist i j := martinDist P ref w i j
  dist_self i := by
    simp [martinDist]
  dist_comm i j := by
    simp [martinDist, abs_sub_comm]
  dist_triangle i j k := by
    sorry

/--
The Martin compactification obtained by completing the Martin pseudometric space.
-/
abbrev MartinBoundary
    (P : InfMatrix α) (ref : α) (w : α → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw : Summable w) :=
  letI := martinPseudoMetricSpace P ref w hw_nonneg hw
  UniformSpace.Completion α

/--
The extension of the Martin kernel from the state space to the Martin boundary.
-/
noncomputable def MartinKernelExt
    (P : InfMatrix α) (ref : α) (w : α → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw : Summable w) (i : α) :
    MartinBoundary P ref w hw_nonneg hw → ℝ := by
  letI := martinPseudoMetricSpace P ref w hw_nonneg hw
  exact UniformSpace.Completion.extension fun j : α => (MartinKernel P ref i j).toReal

/--
Riesz decomposition of a superregular vector into its regular and potential parts.
-/
theorem riesz_decomposition_of_superregular
    {P : InfMatrix α} (hP_sub : IsSubstochastic P) (hP_trans : ∀ i, IsTransient P i)
    {u : α → ℝ≥0∞} (hu : IsSuperregular P u) :
    ∃! rg : (α → ℝ≥0∞) × (α → ℝ≥0∞),
      IsRegular P rg.1 ∧ IsPotential P rg.2 ∧ ∀ i, u i = rg.1 i + rg.2 i := by
  sorry

/--
The regular part is the limit of the forward iterates, while the potential part is the Green
potential of the defect `u - Pu`.
-/
theorem riesz_decomposition_explicit
    {P : InfMatrix α} (hP_sub : IsSubstochastic P) (hP_trans : ∀ i, IsTransient P i)
    {u : α → ℝ≥0∞} (hu : IsSuperregular P u) :
    ∃ r g : α → ℝ≥0∞,
      (∀ i,
        Tendsto (fun k : ℕ => infMatMulVec (InfMatrix.pow P k) u i) atTop (nhds (r i))) ∧
      IsRegular P r ∧
      g = greenMulVec P (fun i => u i - infMatMulVec P u i) ∧
      ∀ i, u i = r i + g i := by
  sorry

/--
The Martin compactification is compact for a transient substochastic matrix.
-/
theorem compactSpace_martinBoundary
    {P : InfMatrix α} (hP_sub : IsSubstochastic P) (hP_trans : ∀ i, IsTransient P i)
    (ref : α) (w : α → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw : Summable w) :
    CompactSpace (MartinBoundary P ref w hw_nonneg hw) := by
  sorry

/--
Poisson-Martin integral representation of a superregular vector.
-/
theorem poisson_martin_integral_representation
    {P : InfMatrix α} (hP_sub : IsSubstochastic P) (hP_trans : ∀ i, IsTransient P i)
    {u : α → ℝ≥0∞} (hu : IsSuperregular P u)
    (ref : α) (w : α → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw : Summable w)
    [MeasurableSpace (MartinBoundary P ref w hw_nonneg hw)] :
    ∃ μ : Measure (MartinBoundary P ref w hw_nonneg hw),
      ∀ i,
        u i = ∫⁻ x, ENNReal.ofReal (MartinKernelExt P ref w hw_nonneg hw i x) ∂μ := by
  sorry

end ChapterFiveBoundary

end MCMC.Countable
