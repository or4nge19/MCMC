/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.ContinuousMap.Compact
import MCMC.ToMathlib.Topology.ContinuousMap.Ordered

/-!
# The sup norm on `C(α, β)` is solid

For compact `α` and a normed lattice `β`, the sup norm on `C(α, β)` is solid, so `C(α, β)` is a
normed lattice; in particular its order is closed (`OrderClosedTopology`).

Staged for `Mathlib/Topology/ContinuousMap/Compact.lean`. Searched on 2026-10-17: the pinned tree
proves `HasSolidNorm (α →ᵇ β)` but not `HasSolidNorm C(α, β)`.
-/

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [CompactSpace α] [NormedAddCommGroup β] [Lattice β]
  [HasSolidNorm β] [IsOrderedAddMonoid β]

instance : HasSolidNorm C(α, β) where
  solid _ g h := (norm_le _ (norm_nonneg g)).2 fun t ↦
    (HasSolidNorm.solid (h t)).trans (norm_coe_le_norm g t)

end ContinuousMap
