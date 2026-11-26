/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Proper

/-!
# Gibbs updates: proper kernels leaving a measure invariant are reversible

A Gibbs update of `π` relative to a sub-σ-algebra `𝓑 ≤ 𝓧` resamples the state from `π` given its
`𝓑`-information. In Mathlib's terms it is a kernel `γ : Kernel[𝓑, 𝓧] X X` that is proper
(`ProbabilityTheory.Kernel.IsProper`: `γ x (A ∩ B) = B.indicator 1 x * γ x A` for `B ∈ 𝓑`, the
`𝓑`-information is kept) and leaves `π` invariant. Read as a kernel on `(X, 𝓧)` through
`Kernel.comap γ id (measurable_id'' h𝓑𝓧)`, such a kernel is `π`-reversible: the flow from `A` to
`B` is `∫⁻ x, γ x B * γ x A ∂π`. For a Markov kernel, reversibility is equivalent to invariance and
the kernel is idempotent. Random-scan Gibbs samplers are mixtures and systematic-scan samplers are
compositions of such updates.

## Main statements

* `IsProper.setLIntegral_eq_lintegral_mul`, `IsProper.isReversible_comap_id`.
* `IsProper.isReversible_comap_id_iff_invariant` (Markov).
* `IsProper.comap_id_comp_comap_id` (Markov): the update is idempotent.
* `isProper_const_bot`: independent resampling is the update for the trivial σ-algebra.
* `exists_invariant_not_isReversible`: properness cannot be dropped;
  `exists_isProper_isReversible_not_invariant`, `exists_isProper_comp_ne`: the Markov hypotheses
  cannot be dropped.

Staged for `Mathlib/Probability/Kernel/Proper.lean`. Searched on 2026-11-26 in the pinned Mathlib:
`grep -rn "IsProper" Mathlib` finds the definition, its characterizations and the integral lemmas
of `Probability/Kernel/Proper.lean` and no statement about invariant measures, reversibility or
composition.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {γ : Kernel[𝓑, 𝓧] X X} {π : Measure[𝓧] X}

/-- The flow of a proper kernel leaving `π` invariant from `A` to `B` is the integral of
`γ x B * γ x A`. -/
theorem IsProper.setLIntegral_eq_lintegral_mul (hγ : γ.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hπ : (γ.comap id (measurable_id'' h𝓑𝓧)).Invariant π) {A B : Set X}
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓧] B) :
    ∫⁻ x in A, γ x B ∂π = ∫⁻ x, γ x B * γ x A ∂π := by
  have hgB : Measurable[𝓑] fun x ↦ γ x B := γ.measurable_coe hB
  calc ∫⁻ x in A, γ x B ∂π = ∫⁻ x, A.indicator (fun x ↦ γ x B) x ∂π :=
        (lintegral_indicator hA _).symm
    _ = ∫⁻ x, A.indicator (fun x ↦ γ x B) x ∂(π.bind (γ.comap id (measurable_id'' h𝓑𝓧))) := by
        rw [hπ.def]
    _ = ∫⁻ x, ∫⁻ y, A.indicator (fun x ↦ γ x B) y ∂(γ x) ∂π :=
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable
          ((hgB.mono h𝓑𝓧 le_rfl).indicator hA).aemeasurable
    _ = ∫⁻ x, γ x B * γ x A ∂π := lintegral_congr fun x ↦ by
        rw [← lintegral_indicator_one hA, ← hγ.lintegral_mul h𝓑𝓧 (measurable_one.indicator hA)
          hgB x]
        exact lintegral_congr fun y ↦ by by_cases hy : y ∈ A <;> simp [hy]

/-- **A Gibbs update is reversible.** A proper kernel leaving `π` invariant is `π`-reversible. -/
theorem IsProper.isReversible_comap_id (hγ : γ.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hπ : (γ.comap id (measurable_id'' h𝓑𝓧)).Invariant π) :
    (γ.comap id (measurable_id'' h𝓑𝓧)).IsReversible π := fun A B hA hB ↦ by
  simp only [comap_apply, id_eq]
  rw [hγ.setLIntegral_eq_lintegral_mul h𝓑𝓧 hπ hA hB,
    hγ.setLIntegral_eq_lintegral_mul h𝓑𝓧 hπ hB hA]
  simp_rw [mul_comm]

/-- A proper Markov kernel is `π`-reversible iff it leaves `π` invariant. -/
theorem IsProper.isReversible_comap_id_iff_invariant [IsMarkovKernel γ] (hγ : γ.IsProper)
    (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    (γ.comap id (measurable_id'' h𝓑𝓧)).IsReversible π ↔
      (γ.comap id (measurable_id'' h𝓑𝓧)).Invariant π :=
  ⟨IsReversible.invariant, hγ.isReversible_comap_id h𝓑𝓧⟩

/-- A proper Markov kernel is idempotent: a Gibbs update repeated is the same update. -/
theorem IsProper.comap_id_comp_comap_id [IsMarkovKernel γ] (hγ : γ.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) :
    γ.comap id (measurable_id'' h𝓑𝓧) ∘ₖ γ.comap id (measurable_id'' h𝓑𝓧) =
      γ.comap id (measurable_id'' h𝓑𝓧) := by
  ext x A hA
  rw [comp_apply' _ _ _ hA]
  simp only [comap_apply, id_eq]
  calc ∫⁻ y, γ y A ∂γ x = ∫⁻ y, γ y A * 1 ∂γ x := by simp
    _ = γ x A := by
        rw [hγ.lintegral_mul h𝓑𝓧 measurable_const (γ.measurable_coe hA), lintegral_one,
          measure_univ, mul_one]

/-- A constant kernel is proper for the trivial σ-algebra. -/
theorem isProper_const_bot (ν : Measure[𝓧] X) : (@Kernel.const X X ⊥ 𝓧 ν).IsProper :=
  ⟨fun B hB x ↦ by
    rw [bot_inf_eq, MeasurableSpace.measurableSet_bot_iff] at hB
    rcases hB with rfl | rfl <;> simp [Kernel.restrict_apply]⟩

/-- The hypotheses of `IsProper.isReversible_comap_id` hold together: resampling from a
probability measure `π` independently of the current state is the Gibbs update of `π` for the
trivial σ-algebra. -/
example [IsProbabilityMeasure π] :
    ((@Kernel.const X X ⊥ 𝓧 π).comap id (measurable_id'' bot_le)).IsReversible π := by
  refine (isProper_const_bot π).isReversible_comap_id bot_le (Measure.ext fun s hs ↦ ?_)
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp

/-- The hypotheses of `IsProper.comap_id_comp_comap_id` hold together. -/
example [IsProbabilityMeasure π] :
    (@Kernel.const X X ⊥ 𝓧 π).comap id (measurable_id'' (bot_le : ⊥ ≤ 𝓧)) ∘ₖ
        (@Kernel.const X X ⊥ 𝓧 π).comap id (measurable_id'' (bot_le : ⊥ ≤ 𝓧)) =
      (@Kernel.const X X ⊥ 𝓧 π).comap id (measurable_id'' (bot_le : ⊥ ≤ 𝓧)) :=
  (isProper_const_bot π).comap_id_comp_comap_id bot_le

/-- Properness is needed in `IsProper.isReversible_comap_id` (take `𝓑 = 𝓧`): the rotation
`x ↦ x + 1` of `Fin 3` leaves the counting measure invariant and is not reversible for it. -/
theorem exists_invariant_not_isReversible :
    ∃ κ : Kernel (Fin 3) (Fin 3), IsMarkovKernel κ ∧ κ.Invariant Measure.count ∧
      ¬ κ.IsReversible Measure.count := by
  refine ⟨Kernel.deterministic (· + 1) (measurable_of_countable _), inferInstance, ?_, fun h ↦ ?_⟩
  · refine Measure.ext_iff_singleton.2 fun y ↦ ?_
    rw [Measure.deterministic_comp_eq_map, Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton y), show (· + 1 : Fin 3 → Fin 3) ⁻¹' {y} = {y - 1} by
        ext x; simp only [mem_preimage, mem_singleton_iff]; exact eq_sub_iff_add_eq.symm]
    simp
  have h1 := h (measurableSet_singleton 0) (measurableSet_singleton 1)
  simp [Kernel.deterministic_apply] at h1

/-- The Markov hypothesis is needed in `IsProper.isReversible_comap_id_iff_invariant`: the zero
kernel is proper and reversible for every measure and leaves no nonzero measure invariant. -/
theorem exists_isProper_isReversible_not_invariant :
    ∃ γ : Kernel Unit Unit, γ.IsProper ∧
      (γ.comap id measurable_id).IsReversible (Measure.dirac ()) ∧
      ¬ (γ.comap id measurable_id).Invariant (Measure.dirac ()) := by
  refine ⟨0, ⟨fun B _ x ↦ by simp [Kernel.restrict_apply]⟩, fun A B _ _ ↦ by simp, fun h ↦ ?_⟩
  have h1 := congrArg (· univ) h.def
  rw [Measure.bind_apply .univ (Kernel.aemeasurable _)] at h1
  simp at h1

/-- The Markov hypothesis is needed in `IsProper.comap_id_comp_comap_id`: the kernel
`Kernel.id + Kernel.id` on `Unit` is proper and not idempotent. -/
theorem exists_isProper_comp_ne :
    ∃ γ : Kernel Unit Unit, γ.IsProper ∧ γ.comap id measurable_id ∘ₖ γ.comap id measurable_id ≠
      γ.comap id measurable_id := by
  refine ⟨Kernel.id + Kernel.id, ⟨fun B hB x ↦ ?_⟩, fun h ↦ ?_⟩
  · rcases B.eq_empty_or_nonempty with rfl | hne
    · simp [Kernel.restrict_apply]
    · rw [hne.eq_univ]
      simp
  · have h1 := congrArg (fun κ ↦ κ () univ) h
    simp only [comp_apply' _ _ _ MeasurableSet.univ, comap_apply, id_eq, add_apply, id_apply,
      Measure.add_apply, measure_univ, lintegral_add_measure, lintegral_dirac] at h1
    norm_num at h1
