/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.MeasureTheory.Measure.CompleteLattice
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

/-- **The accepted-flow criterion.** For σ-finite `π` and an acceptance whose accepted mass is
finite `π`-almost everywhere, the accept–reject kernel is `π`-reversible iff the accepted flow
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

/-- The Metropolis–Hastings acceptance of the proposal `Q` for the target `π`: the density of the
symmetric part `(π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap` of the flow with respect to `π ⊗ₘ Q`,
truncated at `1`. No density of `π` or `Q` and no positivity is involved. -/
noncomputable def _root_.MeasureTheory.Measure.mhAcceptance (π : Measure X) (Q : Kernel X X)
    (x y : X) : ℝ≥0∞ :=
  min 1 (((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).rnDeriv (π ⊗ₘ Q) (x, y))

theorem _root_.MeasureTheory.Measure.mhAcceptance_le_one (π : Measure X) (Q : Kernel X X)
    (x y : X) : π.mhAcceptance Q x y ≤ 1 :=
  min_le_left _ _

theorem _root_.MeasureTheory.Measure.measurable_mhAcceptance (π : Measure X) (Q : Kernel X X) :
    Measurable (Function.uncurry (π.mhAcceptance Q)) :=
  measurable_const.min (Measure.measurable_rnDeriv _ _)

/-- The Metropolis–Hastings kernel of a Markov proposal is Markov. -/
instance isMarkovKernel_acceptReject_mhAcceptance [IsMarkovKernel Q] :
    IsMarkovKernel (acceptReject Q (π.mhAcceptance Q)) :=
  (isMarkovKernel_acceptReject_iff (π.measurable_mhAcceptance Q)).2 fun x ↦
    (lintegral_mono fun y ↦ π.mhAcceptance_le_one Q x y).trans (by simp)

/-- The flow accepted by the Metropolis–Hastings acceptance is the symmetric part
`(π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap` of the proposed flow. -/
theorem withDensity_mhAcceptance [SigmaFinite (π ⊗ₘ Q)] :
    (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q)) =
      (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap := by
  have hle : (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap ≤ π ⊗ₘ Q := inf_le_left
  have := Measure.sigmaFinite_of_le _ hle
  calc (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q))
      = (π ⊗ₘ Q).withDensity (((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).rnDeriv (π ⊗ₘ Q)) := by
        refine MeasureTheory.withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_le_one_of_le hle] with p hp
        exact min_eq_right hp
    _ = (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap :=
        Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hle)

/-- σ-finiteness of `π ⊗ₘ Q` is needed in `withDensity_mhAcceptance`: on `Bool`, with the flip
proposal and `π = ∞ • δ_true + δ_false`, the symmetric part of the flow has mass `1` at
`(true, false)`, where `π ⊗ₘ Q` has mass `∞`, so it has no density with respect to `π ⊗ₘ Q`. -/
theorem exists_withDensity_mhAcceptance_ne :
    ∃ (π : Measure Bool) (Q : Kernel Bool Bool) (_ : IsMarkovKernel Q), SFinite π ∧
      (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q)) ≠
        (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap := by
  refine ⟨∞ • Measure.dirac true + Measure.dirac false,
    Kernel.deterministic (!·) (measurable_of_countable _), inferInstance, inferInstance,
    fun h ↦ ?_⟩
  have h1 := congrArg (· {(true, false)}) h
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    Measure.inf_apply_singleton, Measure.map_apply measurable_swap (measurableSet_singleton _),
    ← singleton_prod_singleton, preimage_swap_prod, singleton_prod_singleton,
    singleton_prod_singleton,
    Measure.compProd_apply_singleton, Measure.compProd_apply_singleton,
    Function.uncurry_apply_pair] at h1
  rcases eq_or_ne ((∞ • Measure.dirac true + Measure.dirac false).mhAcceptance
    (Kernel.deterministic (!·) (measurable_of_countable _)) true false) 0 with h0 | h0
  · simp [h0, Kernel.deterministic_apply] at h1
  · simp [ENNReal.mul_top h0, Kernel.deterministic_apply] at h1

/-- An accept–reject kernel whose acceptance agrees `π ⊗ₘ Q`-almost everywhere with the
Metropolis–Hastings acceptance is `π`-reversible. -/
theorem isReversible_acceptReject_of_ae_eq_mhAcceptance [SFinite π] [IsSFiniteKernel Q]
    [SigmaFinite (π ⊗ₘ Q)] (ha : Measurable (Function.uncurry a))
    (h : Function.uncurry a =ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q)) :
    (acceptReject Q a).IsReversible π := by
  refine (isReversible_acceptReject_iff ha).2 (IsReversible.of_map_swap_compProd ?_)
  rw [Measure.compProd_withDensity ha]
  change ((π ⊗ₘ Q).withDensity (Function.uncurry a)).map Prod.swap =
    (π ⊗ₘ Q).withDensity (Function.uncurry a)
  have hswap := MeasurableEquiv.prodComm.map_inf (π ⊗ₘ Q) ((π ⊗ₘ Q).map Prod.swap)
  rw [show ⇑(MeasurableEquiv.prodComm : X × X ≃ᵐ X × X) = Prod.swap from rfl,
    Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id] at hswap
  rw [MeasureTheory.withDensity_congr_ae h, withDensity_mhAcceptance, hswap, inf_comm]

/-- **Metropolis–Hastings.** The accept–reject kernel of the Metropolis–Hastings acceptance is
`π`-reversible, for every proposal with `π ⊗ₘ Q` σ-finite. -/
theorem isReversible_acceptReject_mhAcceptance [SFinite π] [IsSFiniteKernel Q]
    [SigmaFinite (π ⊗ₘ Q)] : (acceptReject Q (π.mhAcceptance Q)).IsReversible π :=
  isReversible_acceptReject_of_ae_eq_mhAcceptance (π.measurable_mhAcceptance Q)
    Filter.EventuallyEq.rfl

end ProbabilityTheory.Kernel
