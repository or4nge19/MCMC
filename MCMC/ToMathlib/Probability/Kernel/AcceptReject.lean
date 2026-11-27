/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import MCMC.ToMathlib.MeasureTheory.Measure.CompleteLattice
public import MCMC.ToMathlib.MeasureTheory.Measure.WithDensity
public import MCMC.ToMathlib.Probability.Kernel.Reversible

/-!
# Accept–reject kernels and the Metropolis–Hastings acceptance

The accept–reject kernel of a proposal `Q` and an acceptance `a : X → X → ℝ≥0∞` proposes `y ∼ Q x`,
accepts it with probability `a x y` and otherwise stays at `x`:
`acceptReject Q a x = (Q x).withDensity (a x) + (1 - ∫⁻ y, a x y ∂Q x) • δ_x`.
Every Metropolis–Hastings kernel is of this form. The Metropolis–Hastings acceptance
`π.mhAcceptance Q` is the density of the symmetric part `(π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap` of
the proposed flow with respect to `π ⊗ₘ Q`, truncated at `1`: no density of `π` or of `Q` and no
positivity is involved.

## Main statements

* `isMarkovKernel_acceptReject_iff`: the kernel is Markov iff the accepted mass is at most `1`;
  `acceptReject_of_not_measurable`: for a non-measurable acceptance it is `Kernel.id`.
* `isReversible_acceptReject_iff`: for every measure `π`, the kernel is `π`-reversible iff its
  accepted part `Q.withDensity a` is.
* `isReversible_acceptReject_iff_map_swap`: for σ-finite `π` and accepted mass finite
  `π`-almost everywhere, the kernel is `π`-reversible iff the accepted flow is invariant under the
  swap.
* `withDensity_mhAcceptance`: the flow accepted by `π.mhAcceptance Q` is the symmetric part of the
  proposed flow; `isReversible_acceptReject_mhAcceptance`,
  `isReversible_acceptReject_of_ae_eq_mhAcceptance`: the Metropolis–Hastings kernel is
  `π`-reversible.
* `ae_le_mhAcceptance_of_isReversible_acceptReject`: every acceptance `a ≤ 1` with a
  `π`-reversible accept–reject kernel is at most `π.mhAcceptance Q`, `π ⊗ₘ Q`-almost everywhere.
* `IsReversible.withDensity_min`, `isReversible_acceptReject_min_one_div`: for a proposal
  reversible for a reference measure `μ`, the acceptance `min 1 (f y / f x)` gives a kernel
  reversible for `μ.withDensity f`; `μ` and `Q` need not be finite.
* `mhAcceptance_eq_min_one_div` (on atoms) and `mhAcceptance_withDensity_ae_eq` (with densities):
  `π.mhAcceptance Q` is the classical ratio `min 1 (π(y) q(y, x) / (π(x) q(x, y)))`.
* For each hypothesis that cannot be dropped, a counterexample (`exists_…`).

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
accept it with probability `a x y`, otherwise stay at `x`. The rejected mass is read off the
accepted part `Q.withDensity a`; when `Function.uncurry a` is not measurable, `Q.withDensity a` is
`0` by convention and the kernel is `Kernel.id` (`acceptReject_of_not_measurable`). -/
noncomputable def acceptReject (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞) :
    Kernel X X :=
  Q.withDensity a + Kernel.id.withDensity fun x _ ↦ 1 - Q.withDensity a x univ

instance isSFiniteKernel_acceptReject [IsSFiniteKernel Q] :
    IsSFiniteKernel (acceptReject Q a) := by
  rw [acceptReject]
  infer_instance

/-- The accept–reject kernel at `x` is the accepted part plus the rejected mass at `x`. -/
theorem acceptReject_apply' [IsSFiniteKernel Q] (x : X) :
    acceptReject Q a x =
      Q.withDensity a x + (1 - Q.withDensity a x univ) • Measure.dirac x := by
  have hr : Measurable (Function.uncurry fun x (_ : X) ↦ 1 - Q.withDensity a x univ) :=
    (measurable_const.sub ((Q.withDensity a).measurable_coe .univ)).comp measurable_fst
  rw [acceptReject, add_apply, Kernel.withDensity_apply _ hr, Kernel.id_apply,
    withDensity_const]

/-- For a measurable acceptance, the accept–reject kernel at `x` is the accepted part of the
proposal plus the rejected mass at `x`. -/
theorem acceptReject_apply [IsSFiniteKernel Q] (ha : Measurable (Function.uncurry a)) (x : X) :
    acceptReject Q a x = (Q x).withDensity (a x) + (1 - ∫⁻ y, a x y ∂Q x) • Measure.dirac x := by
  rw [acceptReject_apply', Kernel.withDensity_apply _ ha, withDensity_apply _ .univ,
    Measure.restrict_univ]

/-- For a non-measurable acceptance, the accept–reject kernel is the identity. -/
theorem acceptReject_of_not_measurable [IsSFiniteKernel Q]
    (ha : ¬ Measurable (Function.uncurry a)) : acceptReject Q a = Kernel.id := by
  ext x : 1
  rw [acceptReject_apply', Kernel.withDensity_of_not_measurable _ ha]
  simp [Kernel.id_apply]

/-- The accept–reject kernel is Markov iff the accepted mass is at most `1` at every point. -/
theorem isMarkovKernel_acceptReject_iff [IsSFiniteKernel Q] :
    IsMarkovKernel (acceptReject Q a) ↔ ∀ x, Q.withDensity a x univ ≤ 1 := by
  have h : ∀ x, acceptReject Q a x univ =
      Q.withDensity a x univ + (1 - Q.withDensity a x univ) := fun x ↦ by
    rw [acceptReject_apply', Measure.add_apply, Measure.smul_apply,
      (measure_univ : Measure.dirac x univ = 1), smul_eq_mul, mul_one]
  refine ⟨fun hP x ↦ ?_, fun h1 ↦ ⟨fun x ↦ ⟨by rw [h, add_tsub_cancel_of_le (h1 x)]⟩⟩⟩
  calc Q.withDensity a x univ ≤ Q.withDensity a x univ + (1 - Q.withDensity a x univ) :=
        le_self_add
    _ = 1 := by rw [← h, measure_univ]

/-- An accept–reject kernel is `π`-reversible iff its accepted part `Q.withDensity a` is: the
rejected mass stays at its point and never moves between disjoint sets. No finiteness and no
measurability is assumed. -/
theorem isReversible_acceptReject_iff [IsSFiniteKernel Q] :
    (acceptReject Q a).IsReversible π ↔ (Q.withDensity a).IsReversible π := by
  have h : ∀ ⦃s t : Set X⦄, MeasurableSet s → MeasurableSet t → Disjoint s t →
      ∫⁻ x in s, acceptReject Q a x t ∂π = ∫⁻ x in s, Q.withDensity a x t ∂π :=
    fun s t hs ht hst ↦ setLIntegral_congr_fun hs fun x hx ↦ by
      rw [acceptReject_apply', Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _ ht, indicator_of_notMem (disjoint_left.1 hst hx), smul_zero,
        add_zero]
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
  have := Measure.sigmaFinite_fst_compProd hκ
  exact isReversible_acceptReject_iff.trans
    (isReversible_iff_map_swap_compProd.trans
      (by rw [Measure.compProd_withDensity ha]; exact Iff.rfl))

/-- σ-finiteness of `π` is needed in `isReversible_acceptReject_iff_map_swap`, already for a
Markov proposal and the acceptance `1`. -/
theorem exists_isReversible_acceptReject_and_map_swap_ne :
    ∃ (π : Measure ℝ) (Q : Kernel ℝ ℝ) (_ : IsMarkovKernel Q), SFinite π ∧
      (acceptReject Q fun _ _ ↦ 1).IsReversible π ∧
      ((π ⊗ₘ Q).withDensity fun _ ↦ 1).map Prod.swap ≠ (π ⊗ₘ Q).withDensity fun _ ↦ 1 := by
  obtain ⟨ν, Q, hν, hQ, hrev, hne⟩ := exists_isReversible_smul_top_and_map_swap_compProd_ne
  refine ⟨∞ • ν, Q, hQ, inferInstance, ?_, ?_⟩
  · rw [isReversible_acceptReject_iff, withDensity_one']
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
  exact ⟨π, Q, hQ, hπ, (isReversible_acceptReject_iff).2 hrev, hne⟩

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
  isMarkovKernel_acceptReject_iff.2 fun x ↦ by
    rw [Kernel.withDensity_apply' _ (π.measurable_mhAcceptance Q), Measure.restrict_univ]
    exact (lintegral_mono fun y ↦ π.mhAcceptance_le_one Q x y).trans (by simp)

/-- The symmetric part of a σ-finite flow has a Lebesgue decomposition with respect to it. -/
instance haveLebesgueDecomposition_inf_map_swap_compProd [SigmaFinite (π ⊗ₘ Q)] :
    ((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q) :=
  have := Measure.sigmaFinite_of_le (π ⊗ₘ Q)
    (inf_le_left : (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap ≤ π ⊗ₘ Q)
  inferInstance

/-- The flow accepted by the Metropolis–Hastings acceptance is the symmetric part
`(π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap` of the proposed flow, when the symmetric part has a Lebesgue
decomposition with respect to the flow; in particular when `π ⊗ₘ Q` is σ-finite. -/
theorem withDensity_mhAcceptance
    [((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q)] :
    (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q)) =
      (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap := by
  have hle : (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap ≤ π ⊗ₘ Q := inf_le_left
  have h := Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hle)
  calc (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q))
      = (π ⊗ₘ Q).withDensity (((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).rnDeriv (π ⊗ₘ Q)) :=
        withDensity_min_one_of_le (Measure.measurable_rnDeriv _ _) (h.trans_le hle)
    _ = (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap := h

/-- The identity of `withDensity_mhAcceptance` holds exactly when the symmetric part of the flow
has a Lebesgue decomposition with respect to the flow. -/
theorem withDensity_mhAcceptance_eq_iff :
    (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q)) =
        (π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap ↔
      ((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q) :=
  ⟨fun h ↦ ⟨⟨(0, Function.uncurry (π.mhAcceptance Q)), π.measurable_mhAcceptance Q,
    Measure.MutuallySingular.zero_left, by simp [h]⟩⟩, fun _ ↦ withDensity_mhAcceptance⟩

/-- Without a Lebesgue decomposition of the symmetric part, the Metropolis–Hastings acceptance
is `0` (the convention of `Measure.rnDeriv`): every proposal is rejected. -/
theorem _root_.MeasureTheory.Measure.mhAcceptance_of_not_haveLebesgueDecomposition
    (h : ¬ ((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q)) (x y : X) :
    π.mhAcceptance Q x y = 0 := by
  simp [Measure.mhAcceptance, Measure.rnDeriv_of_not_haveLebesgueDecomposition h]

/-- A Lebesgue decomposition of the symmetric part is needed in `withDensity_mhAcceptance`: on
`Bool`, with the flip proposal and `π = ∞ • δ_true + δ_false`, the symmetric part of the flow has
mass `1` at `(true, false)`, where `π ⊗ₘ Q` has mass `∞`, so it has no density with respect to
`π ⊗ₘ Q`. -/
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
Metropolis–Hastings acceptance is `π`-reversible. No σ-finiteness is assumed. -/
theorem isReversible_acceptReject_of_ae_eq_mhAcceptance [SFinite π] [IsSFiniteKernel Q]
    (ha : Measurable (Function.uncurry a))
    (h : Function.uncurry a =ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q)) :
    (acceptReject Q a).IsReversible π := by
  refine isReversible_acceptReject_iff.2 (IsReversible.of_map_swap_compProd ?_)
  rw [Measure.compProd_withDensity ha]
  change ((π ⊗ₘ Q).withDensity (Function.uncurry a)).map Prod.swap =
    (π ⊗ₘ Q).withDensity (Function.uncurry a)
  rw [MeasureTheory.withDensity_congr_ae h]
  by_cases hL : ((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q)
  · have hswap := (MeasurableEquiv.prodComm : X × X ≃ᵐ X × X).measurableEmbedding.map_inf (π ⊗ₘ Q)
      ((π ⊗ₘ Q).map Prod.swap)
    rw [show ⇑(MeasurableEquiv.prodComm : X × X ≃ᵐ X × X) = Prod.swap from rfl,
      Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id] at hswap
    rw [withDensity_mhAcceptance, hswap, inf_comm]
  · rw [show Function.uncurry (π.mhAcceptance Q) = 0 from
      funext fun p ↦ π.mhAcceptance_of_not_haveLebesgueDecomposition hL p.1 p.2,
      MeasureTheory.withDensity_zero, Measure.map_zero]

/-- **Metropolis–Hastings.** The accept–reject kernel of the Metropolis–Hastings acceptance is
`π`-reversible, for every s-finite `π` and every s-finite proposal. -/
theorem isReversible_acceptReject_mhAcceptance [SFinite π] [IsSFiniteKernel Q] :
    (acceptReject Q (π.mhAcceptance Q)).IsReversible π :=
  isReversible_acceptReject_of_ae_eq_mhAcceptance (π.measurable_mhAcceptance Q)
    Filter.EventuallyEq.rfl

/-- **Maximality of the Metropolis–Hastings acceptance.** Among the acceptances `a ≤ 1` whose
accept–reject kernel is `π`-reversible, the Metropolis–Hastings acceptance is the largest,
`π ⊗ₘ Q`-almost everywhere. -/
theorem ae_le_mhAcceptance_of_isReversible_acceptReject [IsSFiniteKernel Q] [SigmaFinite π]
    (hQ : ∀ᵐ x ∂π, Q x univ ≠ ∞) (ha : Measurable (Function.uncurry a))
    (ha1 : ∀ᵐ p ∂(π ⊗ₘ Q), Function.uncurry a p ≤ 1) (h : (acceptReject Q a).IsReversible π) :
    Function.uncurry a ≤ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q) := by
  have := Measure.sigmaFinite_compProd hQ
  have ha_fin : ∀ᵐ x ∂π, ∫⁻ y, a x y ∂Q x ≠ ∞ := by
    filter_upwards [hQ, Measure.ae_ae_of_ae_compProd ha1] with x hx h1
    exact ((lintegral_mono_ae h1).trans_eq lintegral_one).trans_lt hx.lt_top |>.ne
  have hα : (π ⊗ₘ Q).withDensity (Function.uncurry a) ≤ π ⊗ₘ Q :=
    (withDensity_mono ha1).trans_eq MeasureTheory.withDensity_one
  have hsymm := (isReversible_acceptReject_iff_map_swap ha ha_fin).1 h
  have hle : (π ⊗ₘ Q).withDensity (Function.uncurry a) ≤
      (π ⊗ₘ Q).withDensity (Function.uncurry (π.mhAcceptance Q)) := by
    rw [withDensity_mhAcceptance]
    exact le_inf hα (hsymm ▸ Measure.map_mono hα measurable_swap)
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite ha fun s hs _ ↦ ?_
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
  exact Measure.le_iff'.1 hle s

/-- The bound `a ≤ 1` is needed in `ae_le_mhAcceptance_of_isReversible_acceptReject`: on `Unit`
every kernel is reversible, and the acceptance `2` exceeds the Metropolis–Hastings acceptance. -/
theorem exists_isReversible_acceptReject_not_ae_le_mhAcceptance :
    ∃ (π : Measure Unit) (Q : Kernel Unit Unit) (_ : IsMarkovKernel Q), IsProbabilityMeasure π ∧
      (acceptReject Q fun _ _ ↦ 2).IsReversible π ∧
      ¬ (fun _ ↦ 2) ≤ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q) := by
  refine ⟨Measure.dirac (), Kernel.id, inferInstance, inferInstance, ?_, fun h ↦ ?_⟩
  · intro s t _ _
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simp
    rw [hs.eq_univ, ht.eq_univ]
  rw [Measure.compProd_id, Measure.map_dirac] at h
  have h2 := (ae_dirac_iff (measurableSet_le measurable_const
    (Measure.measurable_mhAcceptance _ _))).1 h
  exact absurd (h2.trans (Measure.mhAcceptance_le_one _ _ _ _)) (by norm_num)

/-- On `Fin 3`, for every flow `π ⊗ₘ Q = ∞ • δ_(0,1) + δ_(1,0) + δ_(2,2)`, the symmetric part has
no Lebesgue decomposition with respect to the flow, so the Metropolis–Hastings acceptance is `0`;
the acceptance of the move from `2` to `2` alone has a `π`-reversible accept–reject kernel. -/
theorem mhAcceptance_eq_zero_and_isReversible_acceptReject_of_compProd_eq {π : Measure (Fin 3)}
    {Q : Kernel (Fin 3) (Fin 3)} [SFinite π] [IsSFiniteKernel Q]
    (hρ : π ⊗ₘ Q = ∞ • Measure.dirac (0, 1) + Measure.dirac (1, 0) + Measure.dirac (2, 2)) :
    (∀ x y, π.mhAcceptance Q x y = 0) ∧
      (acceptReject Q fun x y ↦ if x = 2 ∧ y = 2 then 1 else 0).IsReversible π := by
  have hρ01 : (π ⊗ₘ Q) {((0 : Fin 3), (1 : Fin 3))} = ∞ := by simp [hρ]
  have hρ10 : (π ⊗ₘ Q) {((1 : Fin 3), (0 : Fin 3))} = 1 := by simp [hρ]
  have hρ22 : (π ⊗ₘ Q) {((2 : Fin 3), (2 : Fin 3))} = 1 := by simp [hρ]
  refine ⟨fun x y ↦ π.mhAcceptance_of_not_haveLebesgueDecomposition (fun hL ↦ ?_) x y, ?_⟩
  · have h01 := congrArg (· {((0 : Fin 3), (1 : Fin 3))})
      (withDensity_mhAcceptance (π := π) (Q := Q))
    rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
      Measure.inf_apply_singleton, Measure.map_apply measurable_swap (measurableSet_singleton _),
      ← singleton_prod_singleton, preimage_swap_prod, singleton_prod_singleton,
      singleton_prod_singleton, hρ01, hρ10, Function.uncurry_apply_pair] at h01
    rcases eq_or_ne (π.mhAcceptance Q 0 1) 0 with h0 | h0
    · simp [h0] at h01
    · rw [ENNReal.mul_top h0] at h01
      simp at h01
  have ha : Measurable (Function.uncurry fun x y : Fin 3 ↦
      if x = 2 ∧ y = 2 then (1 : ℝ≥0∞) else 0) := measurable_of_countable _
  refine isReversible_acceptReject_iff.2 (IsReversible.of_map_swap_compProd ?_)
  rw [Measure.compProd_withDensity ha,
    show (fun p : Fin 3 × Fin 3 ↦ if p.1 = 2 ∧ p.2 = 2 then (1 : ℝ≥0∞) else 0) =
      ({(2, 2)} : Set (Fin 3 × Fin 3)).indicator 1 by
        funext p; rcases p with ⟨x, y⟩; simp [Set.indicator_apply],
    withDensity_indicator_one (measurableSet_singleton _), Measure.restrict_singleton, hρ22,
    one_smul, Measure.map_dirac' measurable_swap]
  rfl

/-- σ-finiteness of `π` is needed in `ae_le_mhAcceptance_of_isReversible_acceptReject`: on `Fin 3`,
`π = ∞ • δ_0 + δ_1 + δ_2` (s-finite) and the deterministic Markov proposal `0 ↦ 1, 1 ↦ 0, 2 ↦ 2`;
the acceptance of the move from `2` to `2` alone is not below the Metropolis–Hastings
acceptance, which is `0`. -/
theorem exists_isReversible_acceptReject_not_ae_le_mhAcceptance_sFinite :
    ∃ (π : Measure (Fin 3)) (Q : Kernel (Fin 3) (Fin 3)) (_ : IsMarkovKernel Q)
      (a : Fin 3 → Fin 3 → ℝ≥0∞), SFinite π ∧ (∀ᵐ x ∂π, Q x univ ≠ ∞) ∧
        Measurable (Function.uncurry a) ∧ (∀ᵐ p ∂(π ⊗ₘ Q), Function.uncurry a p ≤ 1) ∧
        (acceptReject Q a).IsReversible π ∧
        ¬ Function.uncurry a ≤ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q) := by
  have hg : Measurable fun x : Fin 3 ↦ (x, (![1, 0, 2] : Fin 3 → Fin 3) x) :=
    measurable_of_countable _
  have hρ : (∞ • Measure.dirac (0 : Fin 3) + Measure.dirac 1 + Measure.dirac 2) ⊗ₘ
      Kernel.deterministic (![1, 0, 2] : Fin 3 → Fin 3) (measurable_of_countable _) =
        ∞ • Measure.dirac (0, 1) + Measure.dirac (1, 0) + Measure.dirac (2, 2) := by
    rw [Measure.compProd_deterministic, Measure.map_add _ _ hg, Measure.map_add _ _ hg,
      Measure.map_smul _ hg.aemeasurable, Measure.map_dirac' hg, Measure.map_dirac' hg,
      Measure.map_dirac' hg]
    rfl
  obtain ⟨h0, hrev⟩ := mhAcceptance_eq_zero_and_isReversible_acceptReject_of_compProd_eq hρ
  refine ⟨_, _, inferInstance, fun x y ↦ if x = 2 ∧ y = 2 then 1 else 0, inferInstance,
    ae_of_all _ fun _ ↦ measure_ne_top _ _, measurable_of_countable _,
    ae_of_all _ fun p ↦ by
      rcases p with ⟨x, y⟩; simp only [Function.uncurry_apply_pair]; split_ifs <;> simp, hrev,
    fun h ↦ ?_⟩
  have h22 := ae_iff_of_countable.1 h (2, 2) (by rw [hρ]; simp)
  simp [h0] at h22

/-- Finiteness of the proposal is needed in `ae_le_mhAcceptance_of_isReversible_acceptReject`:
the same flow on `Fin 3`, from the finite `π = δ_0 + δ_1 + δ_2` and the proposal with
`Q 0 = ∞ • δ_1`. -/
theorem exists_isReversible_acceptReject_not_ae_le_mhAcceptance_isFiniteMeasure :
    ∃ (π : Measure (Fin 3)) (Q : Kernel (Fin 3) (Fin 3)) (_ : IsSFiniteKernel Q)
      (a : Fin 3 → Fin 3 → ℝ≥0∞), IsFiniteMeasure π ∧
        Measurable (Function.uncurry a) ∧ (∀ᵐ p ∂(π ⊗ₘ Q), Function.uncurry a p ≤ 1) ∧
        (acceptReject Q a).IsReversible π ∧
        ¬ Function.uncurry a ≤ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q) := by
  have hg : Measurable fun x : Fin 3 ↦ (x, (![1, 0, 2] : Fin 3 → Fin 3) x) :=
    measurable_of_countable _
  have hρ : (Measure.dirac (0 : Fin 3) + Measure.dirac 1 + Measure.dirac 2) ⊗ₘ
      (Kernel.deterministic (![1, 0, 2] : Fin 3 → Fin 3) (measurable_of_countable _)).withDensity
        (fun x _ ↦ if x = 0 then ∞ else 1) =
        ∞ • Measure.dirac (0, 1) + Measure.dirac (1, 0) + Measure.dirac (2, 2) := by
    rw [Measure.compProd_withDensity (measurable_of_countable _), Measure.compProd_deterministic,
      Measure.map_add _ _ hg, Measure.map_add _ _ hg, Measure.map_dirac' hg,
      Measure.map_dirac' hg, Measure.map_dirac' hg, withDensity_add_measure,
      withDensity_add_measure, dirac_withDensity, dirac_withDensity, dirac_withDensity]
    simp
  obtain ⟨h0, hrev⟩ := mhAcceptance_eq_zero_and_isReversible_acceptReject_of_compProd_eq hρ
  refine ⟨_, _, inferInstance, fun x y ↦ if x = 2 ∧ y = 2 then 1 else 0, inferInstance,
    measurable_of_countable _,
    ae_of_all _ fun p ↦ by
      rcases p with ⟨x, y⟩; simp only [Function.uncurry_apply_pair]; split_ifs <;> simp, hrev,
    fun h ↦ ?_⟩
  have h22 := ae_iff_of_countable.1 h (2, 2) (by rw [hρ]; simp)
  simp [h0] at h22

/-- If `Q` is `μ`-reversible, so is `Q` with density `min (f x) (f y)`, for every measurable `f`.
The proof is the layer-cake formula `min (f x) (f y) = ∫⁻ r in Ioi 0, 1[r < f x] 1[r < f y]`,
which turns the flow into an integral of flows between rectangles; no finiteness is assumed. -/
theorem IsReversible.withDensity_min [SFinite μ] [IsSFiniteKernel Q] (hQ : Q.IsReversible μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (Q.withDensity fun x y ↦ min (f x) (f y)).IsReversible μ := by
  have hm : Measurable (Function.uncurry fun x y ↦ min (f x) (f y)) :=
    (hf.comp measurable_fst).min (hf.comp measurable_snd)
  have hF : ∀ r : ℝ, MeasurableSet {x | ENNReal.ofReal r < f x} := fun r ↦
    measurableSet_lt measurable_const hf
  have hvol : ∀ c : ℝ≥0∞, ∫⁻ r in Ioi (0 : ℝ), {r : ℝ | ENNReal.ofReal r < c}.indicator 1 r = c :=
    fun c ↦ by
      rw [lintegral_indicator_one (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
        Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
      rcases eq_or_ne c ∞ with rfl | hc
      · simp
      rw [show {r : ℝ | ENNReal.ofReal r < c} ∩ Ioi 0 = Ioo 0 c.toReal by
        ext r; exact ⟨fun h ↦ ⟨h.2, (ENNReal.ofReal_lt_iff_lt_toReal h.2.le hc).1 h.1⟩,
          fun h ↦ ⟨(ENNReal.ofReal_lt_iff_lt_toReal h.1.le hc).2 h.2, h.1⟩⟩,
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]
  have hS : Measurable (Function.uncurry fun (p : X × X) (r : ℝ) ↦
      {r : ℝ | ENNReal.ofReal r < min (f p.1) (f p.2)}.indicator (1 : ℝ → ℝ≥0∞) r) :=
    measurable_one.indicator (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      (hm.comp measurable_fst))
  have key : ∀ ⦃u v : Set X⦄, MeasurableSet u → MeasurableSet v →
      ∫⁻ x in u, (Q.withDensity fun x y ↦ min (f x) (f y)) x v ∂μ = ∫⁻ r in Ioi (0 : ℝ),
        (μ ⊗ₘ Q) ((u ∩ {x | ENNReal.ofReal r < f x}) ×ˢ (v ∩ {x | ENNReal.ofReal r < f x})) :=
    fun u v hu hv ↦ by
      rw [← Measure.compProd_apply_prod hu hv, Measure.compProd_withDensity hm,
        withDensity_apply _ (hu.prod hv),
        setLIntegral_congr_fun (hu.prod hv) fun p _ ↦ (hvol (min (f p.1) (f p.2))).symm,
        lintegral_lintegral_swap hS.aemeasurable]
      refine setLIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
      rw [← prod_inter_prod, inter_comm, ← Measure.restrict_apply ((hF r).prod (hF r)),
        ← lintegral_indicator_one ((hF r).prod (hF r))]
      exact lintegral_congr fun p ↦ by simp [indicator, lt_min_iff]
  intro s t hs ht
  rw [key hs ht, key ht hs]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
  rw [Measure.compProd_apply_prod (hs.inter (hF r)) (ht.inter (hF r)),
    Measure.compProd_apply_prod (ht.inter (hF r)) (hs.inter (hF r))]
  exact hQ (hs.inter (hF r)) (ht.inter (hF r))

/-- **The Metropolis acceptance.** If the proposal `Q` is reversible for a reference measure `μ`,
the accept–reject kernel with acceptance `min 1 (f y / f x)` is reversible for `μ.withDensity f`.
Neither `μ` nor `Q` needs to be finite: `μ` may be Lebesgue measure and `Q` a random walk, or `μ`
a Gaussian measure and `Q` the preconditioned Crank–Nicolson proposal. -/
theorem isReversible_acceptReject_min_one_div [SFinite μ] [IsSFiniteKernel Q]
    (hQ : Q.IsReversible μ) {f : X → ℝ≥0∞} (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (acceptReject Q fun x y ↦ min 1 (f y / f x)).IsReversible (μ.withDensity f) := by
  have ha : Measurable (Function.uncurry fun x y ↦ min 1 (f y / f x)) :=
    measurable_const.min ((hf.comp measurable_snd).div (hf.comp measurable_fst))
  have hm : Measurable (Function.uncurry fun x y ↦ min (f x) (f y)) :=
    (hf.comp measurable_fst).min (hf.comp measurable_snd)
  have hmul : ∀ x y, f x ≠ ∞ → f x * min 1 (f y / f x) = min (f x) (f y) := fun x y hx ↦ by
    rcases eq_or_ne (f x) 0 with h0 | h0
    · simp [h0]
    · rw [mul_min_of_nonneg _ _ zero_le, mul_one, ENNReal.mul_div_cancel h0 hx]
  have h : ∀ ⦃u v : Set X⦄, MeasurableSet u → MeasurableSet v →
      ∫⁻ x in u, Q.withDensity (fun x y ↦ min 1 (f y / f x)) x v ∂(μ.withDensity f) =
        ∫⁻ x in u, (Q.withDensity fun x y ↦ min (f x) (f y)) x v ∂μ := fun u v hu hv ↦ by
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hf (Kernel.measurable_coe _ hv) hu]
    refine setLIntegral_congr_fun_ae hu ?_
    filter_upwards [hf_top] with x hx _
    rw [Pi.mul_apply, Kernel.withDensity_apply' _ ha, Kernel.withDensity_apply' _ hm,
      ← lintegral_const_mul' _ _ hx]
    simp_rw [hmul x _ hx]
  refine isReversible_acceptReject_iff.2 fun s t hs ht ↦ ?_
  rw [h hs ht, h ht hs]
  exact hQ.withDensity_min hf hs ht

/-- Finiteness of `f` is needed in `isReversible_acceptReject_min_one_div`: on `Bool`, with the
flip proposal, the reference measure `δ_true + δ_false`, and `f true = ∞`, `f false = 1`, the
move from `false` to `true` is always accepted and the move back never. -/
theorem exists_not_isReversible_acceptReject_min_one_div :
    ∃ (μ : Measure Bool) (Q : Kernel Bool Bool) (_ : IsMarkovKernel Q) (f : Bool → ℝ≥0∞),
      IsFiniteMeasure μ ∧ Q.IsReversible μ ∧ Measurable f ∧
        ¬ (acceptReject Q fun x y ↦ min 1 (f y / f x)).IsReversible (μ.withDensity f) := by
  have hg : Measurable fun b : Bool ↦ (b, !b) := measurable_of_countable _
  refine ⟨Measure.dirac true + Measure.dirac false, Kernel.deterministic (!·)
    (measurable_of_countable _), inferInstance, fun b ↦ if b then ∞ else 1, inferInstance,
    IsReversible.of_map_swap_compProd ?_, measurable_of_countable _, fun h ↦ ?_⟩
  · rw [Measure.compProd_deterministic, Measure.map_add _ _ hg, Measure.map_dirac' hg,
      Measure.map_dirac' hg, Measure.map_add _ _ measurable_swap,
      Measure.map_dirac' measurable_swap, Measure.map_dirac' measurable_swap, add_comm]
    rfl
  have h1 := h (measurableSet_singleton false) (measurableSet_singleton true)
  simp only [acceptReject_apply (measurable_of_countable _), Measure.add_apply,
    withDensity_apply _ (measurableSet_singleton _), Measure.smul_apply, Kernel.deterministic_apply,
    Measure.restrict_singleton] at h1
  simp at h1

/-- Reversibility of the proposal is needed in `isReversible_acceptReject_min_one_div`: with
`f = 1` the accept–reject kernel of the constant proposal `δ_false` on `Bool` moves `δ_true`. -/
theorem exists_not_isReversible_acceptReject_min_one_div_one :
    ∃ (μ : Measure Bool) (Q : Kernel Bool Bool) (_ : IsMarkovKernel Q), IsFiniteMeasure μ ∧
      ¬ (acceptReject Q fun x y ↦ min 1 ((fun _ ↦ 1 : Bool → ℝ≥0∞) y / (fun _ ↦ 1) x)).IsReversible
        (μ.withDensity fun _ ↦ 1) := by
  refine ⟨Measure.dirac true, Kernel.const Bool (Measure.dirac false), inferInstance,
    inferInstance, fun h ↦ ?_⟩
  have h1 := h (measurableSet_singleton true) (measurableSet_singleton false)
  simp only [acceptReject_apply (measurable_of_countable _), Measure.add_apply,
    withDensity_apply _ (measurableSet_singleton _), Measure.smul_apply, Kernel.const_apply,
    Measure.restrict_singleton] at h1
  simp at h1

/-- **The Metropolis–Hastings ratio on atoms.** At a point `(x, y)` charged by a σ-finite
`π ⊗ₘ Q`, the Metropolis–Hastings acceptance is `min 1 (π {y} * Q y {x} / (π {x} * Q x {y}))`.
On a countable space this determines the acceptance `π ⊗ₘ Q`-almost everywhere. -/
theorem mhAcceptance_eq_min_one_div [MeasurableSingletonClass X] [SFinite π] [IsSFiniteKernel Q]
    [SigmaFinite (π ⊗ₘ Q)] {x y : X} (h0 : π {x} * Q x {y} ≠ 0) :
    π.mhAcceptance Q x y = min 1 (π {y} * Q y {x} / (π {x} * Q x {y})) := by
  have htop : π {x} * Q x {y} ≠ ∞ := by
    rw [← Measure.compProd_apply_singleton]
    exact measure_singleton_lt_top.ne
  have h := congrArg (· {(x, y)}) (withDensity_mhAcceptance (π := π) (Q := Q))
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    Measure.inf_apply_singleton, Measure.map_apply measurable_swap (measurableSet_singleton _),
    ← singleton_prod_singleton, preimage_swap_prod, singleton_prod_singleton,
    singleton_prod_singleton,
    Measure.compProd_apply_singleton,
    Measure.compProd_apply_singleton] at h
  rw [Function.uncurry_apply_pair] at h
  calc π.mhAcceptance Q x y = min (π {x} * Q x {y}) (π {y} * Q y {x}) / (π {x} * Q x {y}) :=
        (ENNReal.eq_div_iff h0 htop).2 (by rw [mul_comm]; exact h)
    _ = min 1 (π {y} * Q y {x} / (π {x} * Q x {y})) := by
        rw [(show Monotone fun t : ℝ≥0∞ ↦ t / (π {x} * Q x {y}) from
          fun _ _ hst ↦ ENNReal.div_le_div_right hst _).map_min, ENNReal.div_self h0 htop]

/-- σ-finiteness of `π ⊗ₘ Q` is needed in `mhAcceptance_eq_min_one_div`: on `Fin 3`, with
`π = ∞ • δ_0 + δ_1 + δ_2` and the deterministic Markov proposal `0 ↦ 1, 1 ↦ 0, 2 ↦ 2`, the atom
`(1, 0)` has mass `1`, the acceptance there is `0` and the ratio formula gives `1`. -/
theorem exists_mhAcceptance_ne_min_one_div :
    ∃ (π : Measure (Fin 3)) (Q : Kernel (Fin 3) (Fin 3)) (_ : IsMarkovKernel Q) (x y : Fin 3),
      SFinite π ∧ π {x} * Q x {y} ≠ 0 ∧ π {x} * Q x {y} ≠ ∞ ∧
        π.mhAcceptance Q x y ≠ min 1 (π {y} * Q y {x} / (π {x} * Q x {y})) := by
  have hg : Measurable fun x : Fin 3 ↦ (x, (![1, 0, 2] : Fin 3 → Fin 3) x) :=
    measurable_of_countable _
  have hρ : (∞ • Measure.dirac (0 : Fin 3) + Measure.dirac 1 + Measure.dirac 2) ⊗ₘ
      Kernel.deterministic (![1, 0, 2] : Fin 3 → Fin 3) (measurable_of_countable _) =
        ∞ • Measure.dirac (0, 1) + Measure.dirac (1, 0) + Measure.dirac (2, 2) := by
    rw [Measure.compProd_deterministic, Measure.map_add _ _ hg, Measure.map_add _ _ hg,
      Measure.map_smul _ hg.aemeasurable, Measure.map_dirac' hg, Measure.map_dirac' hg,
      Measure.map_dirac' hg]
    rfl
  have h10 : (∞ • Measure.dirac (0 : Fin 3) + Measure.dirac 1 + Measure.dirac 2 :
      Measure (Fin 3)) {1} *
      (Kernel.deterministic (![1, 0, 2] : Fin 3 → Fin 3) (measurable_of_countable _)) 1 {0} =
        1 := by
    rw [← Measure.compProd_apply_singleton, hρ]
    simp
  refine ⟨_, _, inferInstance, 1, 0, inferInstance, by rw [h10]; exact one_ne_zero,
    by rw [h10]; exact ENNReal.one_ne_top, ?_⟩
  rw [(mhAcceptance_eq_zero_and_isReversible_acceptReject_of_compProd_eq hρ).1, h10,
    ← Measure.compProd_apply_singleton, hρ]
  simp

/-- **The Metropolis–Hastings ratio.** For a target `π = ν.withDensity p` and a proposal with
densities `Q x = ν.withDensity (q x)` with respect to a σ-finite `ν`, the Metropolis–Hastings
acceptance is `min 1 (p y * q y x / (p x * q x y))`, `π ⊗ₘ Q`-almost everywhere. -/
theorem mhAcceptance_withDensity_ae_eq {ν : Measure X} [SigmaFinite ν] {p : X → ℝ≥0∞}
    {q : X → X → ℝ≥0∞} (hp : Measurable p) (hq : Measurable (Function.uncurry q))
    (hpq : ∀ᵐ z ∂(ν.prod ν), p z.1 * q z.1 z.2 ≠ ∞) :
    Function.uncurry ((ν.withDensity p).mhAcceptance ((Kernel.const X ν).withDensity q))
      =ᵐ[(ν.withDensity p) ⊗ₘ (Kernel.const X ν).withDensity q]
        fun z ↦ min 1 (p z.2 * q z.2 z.1 / (p z.1 * q z.1 z.2)) := by
  set g : X × X → ℝ≥0∞ := fun z ↦ p z.1 * q z.1 z.2 with hg_def
  have hg : Measurable g := (hp.comp measurable_fst).mul hq
  have hgs : Measurable fun z : X × X ↦ g z.swap := hg.comp measurable_swap
  have hh : Measurable fun z ↦ min (g z) (g z.swap) / g z := (hg.min hgs).div hg
  have hρ : (ν.withDensity p) ⊗ₘ (Kernel.const X ν).withDensity q = (ν.prod ν).withDensity g := by
    rw [Measure.withDensity_compProd_withDensity hp hq, Measure.compProd_const]
  have := SigmaFinite.withDensity_of_ne_top hpq
  have hmap : ((ν.prod ν).withDensity g).map Prod.swap =
      (ν.prod ν).withDensity fun z ↦ g z.swap :=
    (map_withDensity_comp measurable_swap hgs).trans (by rw [Measure.prod_swap])
  have hinf : (ν.prod ν).withDensity g ⊓ ((ν.prod ν).withDensity g).map Prod.swap =
      ((ν.prod ν).withDensity g).withDensity fun z ↦ min (g z) (g z.swap) / g z := by
    rw [hmap, withDensity_inf_withDensity hg hgs, ← MeasureTheory.withDensity_mul _ hg hh]
    refine MeasureTheory.withDensity_congr_ae ?_
    filter_upwards [hpq] with z hz
    change min (g z) (g z.swap) = g z * (min (g z) (g z.swap) / g z)
    rcases eq_or_ne (g z) 0 with h0 | h0
    · rw [h0, zero_mul]
      exact min_eq_left zero_le
    · exact (ENNReal.mul_div_cancel h0 hz).symm
  have hmh : ∀ z, Function.uncurry ((ν.withDensity p).mhAcceptance
      ((Kernel.const X ν).withDensity q)) z = min 1 ((((ν.prod ν).withDensity g) ⊓
        ((ν.prod ν).withDensity g).map Prod.swap).rnDeriv ((ν.prod ν).withDensity g) z) :=
    fun z ↦ by simp only [Function.uncurry_def, Measure.mhAcceptance, hρ, Prod.mk.eta]
  rw [hρ]
  filter_upwards [Measure.rnDeriv_withDensity ((ν.prod ν).withDensity g) hh,
    (ae_withDensity_iff hg).2 (ae_of_all _ fun z hz ↦ hz),
    (ae_withDensity_iff hg).2 (hpq.mono fun z hz _ ↦ hz)] with z hz h0 htop
  rw [hmh z, hinf, hz]
  rw [(show Monotone fun t : ℝ≥0∞ ↦ t / g z from
    fun _ _ hst ↦ ENNReal.div_le_div_right hst _).map_min, ENNReal.div_self h0 htop, ← min_assoc,
    min_self]
  rfl

/-- The hypotheses of `mhAcceptance_withDensity_ae_eq` hold together, for instance for densities
of a finite target and of a proposal with respect to Lebesgue measure. -/
example {p : ℝ → ℝ≥0∞} {q : ℝ → ℝ → ℝ≥0∞} (hp : Measurable p) (hq : Measurable (Function.uncurry q))
    (hp_top : ∀ x, p x ≠ ∞) (hq_top : ∀ x y, q x y ≠ ∞) :
    Function.uncurry ((volume.withDensity p).mhAcceptance ((Kernel.const ℝ volume).withDensity q))
      =ᵐ[(volume.withDensity p) ⊗ₘ (Kernel.const ℝ volume).withDensity q]
        fun z ↦ min 1 (p z.2 * q z.2 z.1 / (p z.1 * q z.1 z.2)) :=
  mhAcceptance_withDensity_ae_eq hp hq
    (ae_of_all _ fun z ↦ ENNReal.mul_ne_top (hp_top z.1) (hq_top z.1 z.2))

/-- Finiteness of `p * q` is needed in `mhAcceptance_withDensity_ae_eq`: on `Unit` with `ν = δ`,
`p = ∞` and `q = 1`, the ratio formula gives `0` while the flow, invariant under the swap, is
accepted with probability `1`. -/
theorem not_mhAcceptance_withDensity_ae_eq_top :
    ¬ Function.uncurry (((Measure.dirac ()).withDensity fun _ ↦ ∞).mhAcceptance
        ((Kernel.const Unit (Measure.dirac ())).withDensity fun _ _ ↦ 1))
      =ᵐ[((Measure.dirac ()).withDensity fun _ ↦ ∞) ⊗ₘ
          (Kernel.const Unit (Measure.dirac ())).withDensity fun _ _ ↦ 1]
        fun z ↦ min 1 ((fun _ : Unit ↦ (∞ : ℝ≥0∞)) z.2 * (fun _ _ : Unit ↦ (1 : ℝ≥0∞)) z.2 z.1 /
          ((fun _ : Unit ↦ (∞ : ℝ≥0∞)) z.1 * (fun _ _ : Unit ↦ (1 : ℝ≥0∞)) z.1 z.2)) := by
  set π : Measure Unit := (Measure.dirac ()).withDensity fun _ ↦ ∞
  set Q : Kernel Unit Unit := (Kernel.const Unit (Measure.dirac ())).withDensity fun _ _ ↦ 1
  intro h
  have hswap : (π ⊗ₘ Q).map Prod.swap = π ⊗ₘ Q := by
    rw [show (Prod.swap : Unit × Unit → Unit × Unit) = id from
      funext fun _ ↦ Subsingleton.elim _ _, Measure.map_id]
  have hL : ((π ⊗ₘ Q) ⊓ (π ⊗ₘ Q).map Prod.swap).HaveLebesgueDecomposition (π ⊗ₘ Q) := by
    rw [hswap, inf_idem]
    exact ⟨⟨(0, 1), measurable_one, Measure.MutuallySingular.zero_left, by simp⟩⟩
  have h1 := withDensity_mhAcceptance (π := π) (Q := Q)
  rw [hswap, inf_idem, MeasureTheory.withDensity_congr_ae h] at h1
  have h2 := congrArg (fun m : Measure (Unit × Unit) ↦ m univ) h1
  simp [π, Q, withDensity_const] at h2
  rw [← univ_prod_univ, Measure.prod_prod] at h2
  simp at h2

end ProbabilityTheory.Kernel
