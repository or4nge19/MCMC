/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import MCMC.ToMathlib.Analysis.Normed.Algebra.GelfandRadius

/-!
# Gelfand's formula in terms of the Gelfand radius

In a complex Banach algebra, `spectralRadius ℂ a = ENNReal.ofReal (gelfandRadius a)`.

Port of `spectrum.spectralRadius_eq_gelfandRadius` from
`Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean` at mathlib4 `56307dd73d68` (#42607,
2026-10-13), verbatim. Delete at a pin containing that commit.
-/

open Filter ENNReal

namespace spectrum

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖ ^ (1 / n)`. -/
theorem spectralRadius_eq_gelfandRadius (a : A) :
    spectralRadius ℂ a = ENNReal.ofReal (gelfandRadius a) :=
  tendsto_nhds_unique (by simpa using pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
    (tendsto_ofReal (tendsto_gelfandRadius a))

end spectrum
