/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Nonnegative scalars preserve the order on bounded continuous functions

Staged for `Mathlib/Topology/ContinuousMap/Bounded/Normed.lean`. Searched on 2026-10-17: the
pinned tree orders `α →ᵇ β` for normed lattices `β` (`IsOrderedAddMonoid`, `HasSolidNorm`)
but has no `PosSMulMono` instance.
-/

namespace BoundedContinuousFunction

variable {α β 𝕜 : Type*} [TopologicalSpace α] [NormedAddCommGroup β] [Lattice β]
  [HasSolidNorm β] [IsOrderedAddMonoid β] [PseudoMetricSpace 𝕜] [Zero 𝕜] [Preorder 𝕜] [SMul 𝕜 β]
  [IsBoundedSMul 𝕜 β] [PosSMulMono 𝕜 β]

instance : PosSMulMono 𝕜 (α →ᵇ β) :=
  PosSMulMono.lift (fun f : α →ᵇ β ↦ (f : α → β)) Iff.rfl fun _ _ ↦ rfl

end BoundedContinuousFunction
