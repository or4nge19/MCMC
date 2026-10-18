/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Nonnegative scalars preserve the order on `Lp`

Staged for `Mathlib/MeasureTheory/Function/LpOrder.lean`. Searched on 2026-10-17: the pinned tree
makes `Lp E p μ` an ordered group and a normed lattice but has no `PosSMulMono` instance.
-/

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ENNReal}
  [NormedAddCommGroup E] [PartialOrder E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [PartialOrder 𝕜] [PosSMulMono 𝕜 E]

instance : PosSMulMono 𝕜 (Lp E p μ) where
  smul_le_smul_of_nonneg_left c hc f g hfg := by
    rw [← coeFn_le] at hfg ⊢
    filter_upwards [hfg, coeFn_smul c f, coeFn_smul c g] with x hx hfx hgx
    rw [hfx, hgx]
    exact smul_le_smul_of_nonneg_left hx hc

end MeasureTheory.Lp
