/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Ordered algebraic structure on continuous maps

The pointwise order on `C(α, β)` is compatible with addition (`IsOrderedAddMonoid`) and with
nonnegative scalars (`PosSMulMono`).

Staged for `Mathlib/Topology/ContinuousMap/Ordered.lean`. Searched on 2026-10-17: the pinned tree
has these instances for `C_c(α, β)` and `α →ᵇ β` (`IsOrderedAddMonoid` only) but not for
`C(α, β)`.
-/

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

instance [AddCommMonoid β] [ContinuousAdd β] [PartialOrder β] [IsOrderedAddMonoid β] :
    IsOrderedAddMonoid C(α, β) where
  add_le_add_left _ _ hfg c x := add_le_add_left (hfg x) (c x)

instance {𝕜 : Type*} [Zero 𝕜] [Preorder 𝕜] [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] [PartialOrder β]
    [PosSMulMono 𝕜 β] : PosSMulMono 𝕜 C(α, β) :=
  PosSMulMono.lift (fun f : C(α, β) ↦ (f : α → β)) Iff.rfl coe_smul

end ContinuousMap
