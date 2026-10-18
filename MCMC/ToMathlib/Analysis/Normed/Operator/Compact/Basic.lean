/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rank-one operators are compact

`ContinuousLinearMap.isCompactOperator_smulRight`: `y ↦ f y • x` is a compact operator over a
proper field, being the compact `c ↦ c • x` on the locally compact `𝕜` composed with `f`.

Staged for `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean`. Searched on 2026-10-17: the
pinned tree has compactness of maps into or out of locally compact spaces
(`isCompactOperator_of_locallyCompactSpace_dom`, `…_rng`) but no rank-one or finite-rank statement.
AxiomaticX QuantumlibCore (branch `minlos`, `QuantumlibCore/ToMathlib/Analysis/Normed/Operator/
Compact/FiniteRank.lean`) has the finite-rank generalization
`isCompactOperator_of_finiteDimensional_range`, staged for the same Mathlib file; upstream the
two together.
-/

/-- A rank-one operator `y ↦ f y • x` is compact. -/
theorem ContinuousLinearMap.isCompactOperator_smulRight {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [ProperSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : StrongDual 𝕜 E) (x : F) :
    IsCompactOperator (f.smulRight x) := by
  convert (isCompactOperator_of_locallyCompactSpace_rng
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight x)).comp_clm f using 1
  ext
  simp
