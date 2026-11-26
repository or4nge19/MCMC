/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Probability.Kernel.Reversible

/-!
# Accept–reject kernels

The accept–reject kernel of a proposal `Q` and an acceptance `a : X → X → ℝ≥0∞` proposes `y ∼ Q x`,
accepts it with probability `a x y` and otherwise stays at `x`:
`acceptReject Q a x = (Q x).withDensity (a x) + (1 - ∫⁻ y, a x y ∂Q x) • δ_x`.
Every Metropolis–Hastings kernel is of this form.

Staged for `Mathlib/Probability/Kernel/AcceptReject.lean` (new file). Searched on 2026-11-26 in
the pinned Mathlib: `grep -rni "acceptReject\|accept_reject\|metropolis\|hastings" Mathlib` has no
hit.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {Q : Kernel X X} {a : X → X → ℝ≥0∞}

/-- The accept–reject kernel of the proposal `Q` and the acceptance `a`: propose `y ∼ Q x`,
accept it with probability `a x y`, otherwise stay at `x`. When `Function.uncurry a` is not
measurable, `Q.withDensity a` is `0` by convention. -/
noncomputable def acceptReject (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞) :
    Kernel X X :=
  Q.withDensity a + Kernel.id.withDensity fun x _ ↦ 1 - ∫⁻ y, a x y ∂Q x

instance isSFiniteKernel_acceptReject [IsSFiniteKernel Q] :
    IsSFiniteKernel (acceptReject Q a) := by
  rw [acceptReject]
  infer_instance

/-- The accept–reject kernel at `x` is the accepted part of the proposal plus the rejected mass
at `x`. -/
theorem acceptReject_apply [IsSFiniteKernel Q] (ha : Measurable (Function.uncurry a)) (x : X) :
    acceptReject Q a x = (Q x).withDensity (a x) + (1 - ∫⁻ y, a x y ∂Q x) • Measure.dirac x := by
  have hr : Measurable (Function.uncurry fun x (_ : X) ↦ 1 - ∫⁻ y, a x y ∂Q x) :=
    (measurable_const.sub ha.lintegral_kernel_prod_right).comp measurable_fst
  rw [acceptReject, add_apply, Kernel.withDensity_apply _ ha, Kernel.withDensity_apply _ hr,
    id_apply, withDensity_const]

/-- The accept–reject kernel is Markov iff the accepted mass `∫⁻ y, a x y ∂Q x` is at most `1` at
every point. -/
theorem isMarkovKernel_acceptReject_iff [IsSFiniteKernel Q]
    (ha : Measurable (Function.uncurry a)) :
    IsMarkovKernel (acceptReject Q a) ↔ ∀ x, ∫⁻ y, a x y ∂Q x ≤ 1 := by
  have h : ∀ x, acceptReject Q a x univ = ∫⁻ y, a x y ∂Q x + (1 - ∫⁻ y, a x y ∂Q x) := fun x ↦ by
    rw [acceptReject_apply ha, Measure.add_apply, withDensity_apply _ .univ,
      Measure.restrict_univ, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  refine ⟨fun hP x ↦ ?_, fun h1 ↦ ⟨fun x ↦ ⟨by rw [h, add_tsub_cancel_of_le (h1 x)]⟩⟩⟩
  calc ∫⁻ y, a x y ∂Q x ≤ ∫⁻ y, a x y ∂Q x + (1 - ∫⁻ y, a x y ∂Q x) := le_self_add
    _ = 1 := by rw [← h, measure_univ]

end ProbabilityTheory.Kernel
