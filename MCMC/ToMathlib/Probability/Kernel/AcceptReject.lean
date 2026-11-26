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

variable {X : Type*} {mX : MeasurableSpace X} {Q : Kernel X X} {π μ : Measure X}
  {a : X → X → ℝ≥0∞}

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

/-- An accept–reject kernel is `π`-reversible iff its accepted part `Q.withDensity a` is: the
rejected mass stays at its point and never moves between disjoint sets. No finiteness is assumed
on `π`, `Q` or `a`. -/
theorem isReversible_acceptReject_iff [IsSFiniteKernel Q] (ha : Measurable (Function.uncurry a)) :
    (acceptReject Q a).IsReversible π ↔ (Q.withDensity a).IsReversible π := by
  have h : ∀ ⦃s t : Set X⦄, MeasurableSet s → MeasurableSet t → Disjoint s t →
      ∫⁻ x in s, acceptReject Q a x t ∂π = ∫⁻ x in s, Q.withDensity a x t ∂π :=
    fun s t hs ht hst ↦ setLIntegral_congr_fun hs fun x hx ↦ by
      rw [acceptReject_apply ha, Measure.add_apply, Kernel.withDensity_apply _ ha,
        Measure.smul_apply, Measure.dirac_apply' _ ht,
        indicator_of_notMem (disjoint_left.1 hst hx), smul_zero, add_zero]
  rw [isReversible_iff_forall_disjoint, isReversible_iff_forall_disjoint]
  refine ⟨fun H s t hs ht hst ↦ ?_, fun H s t hs ht hst ↦ ?_⟩
  · rw [← h hs ht hst, ← h ht hs hst.symm]
    exact H hs ht hst
  · rw [h hs ht hst, h ht hs hst.symm]
    exact H hs ht hst

/-- **Tierney's criterion.** For σ-finite `π` and an acceptance whose accepted mass is finite
`π`-almost everywhere, the accept–reject kernel is `π`-reversible iff the accepted flow
`(π ⊗ₘ Q).withDensity (Function.uncurry a)` is invariant under the swap. -/
theorem isReversible_acceptReject_iff_map_swap [IsSFiniteKernel Q] [SigmaFinite π]
    (ha : Measurable (Function.uncurry a)) (ha_fin : ∀ᵐ x ∂π, ∫⁻ y, a x y ∂Q x ≠ ∞) :
    (acceptReject Q a).IsReversible π ↔
      ((π ⊗ₘ Q).withDensity (Function.uncurry a)).map Prod.swap =
        (π ⊗ₘ Q).withDensity (Function.uncurry a) := by
  have hκ : ∀ᵐ x ∂π, Q.withDensity a x univ ≠ ∞ := by
    filter_upwards [ha_fin] with x hx
    rwa [Kernel.withDensity_apply' _ ha, Measure.restrict_univ]
  exact (isReversible_acceptReject_iff ha).trans
    ((isReversible_iff_map_swap_compProd hκ).trans
      (by rw [Measure.compProd_withDensity ha]; exact Iff.rfl))

/-- σ-finiteness of `π` is needed in `isReversible_acceptReject_iff_map_swap`, already for a
Markov proposal and the acceptance `1`. -/
theorem exists_isReversible_acceptReject_and_map_swap_ne :
    ∃ (π : Measure ℝ) (Q : Kernel ℝ ℝ) (_ : IsMarkovKernel Q), SFinite π ∧
      (acceptReject Q fun _ _ ↦ 1).IsReversible π ∧
      ((π ⊗ₘ Q).withDensity fun _ ↦ 1).map Prod.swap ≠ (π ⊗ₘ Q).withDensity fun _ ↦ 1 := by
  obtain ⟨ν, Q, hν, hQ, hrev, hne⟩ := exists_isReversible_smul_top_and_map_swap_compProd_ne
  refine ⟨∞ • ν, Q, hQ, inferInstance, ?_, ?_⟩
  · rw [isReversible_acceptReject_iff measurable_const, withDensity_one']
    exact hrev
  · rw [withDensity_const, one_smul]
    exact hne

/-- Finiteness of the accepted mass is needed in `isReversible_acceptReject_iff_map_swap`: the
acceptance `∞` of a Markov proposal, for a probability measure `π`. -/
theorem exists_isReversible_acceptReject_top_and_map_swap_ne :
    ∃ (π : Measure ℝ) (Q : Kernel ℝ ℝ) (_ : IsMarkovKernel Q), IsProbabilityMeasure π ∧
      (acceptReject Q fun _ _ ↦ ∞).IsReversible π ∧
      ((π ⊗ₘ Q).withDensity fun _ ↦ ∞).map Prod.swap ≠ (π ⊗ₘ Q).withDensity fun _ ↦ ∞ := by
  obtain ⟨π, Q, hQ, hπ, hrev, hne⟩ := exists_isReversible_withDensity_top_and_map_swap_compProd_ne
  rw [Measure.compProd_withDensity measurable_const] at hne
  exact ⟨π, Q, hQ, hπ, (isReversible_acceptReject_iff measurable_const).2 hrev, hne⟩

end ProbabilityTheory.Kernel
