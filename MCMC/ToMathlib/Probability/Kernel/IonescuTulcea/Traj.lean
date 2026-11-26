/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import MCMC.ToMathlib.Probability.Kernel.Composition.Comp

/-!
# The law of a Markov chain

Mathlib builds the law of a Markov chain from an initial law `μ₀` and kernels
`κ n : Kernel (Π i : Iic n, X i) (X (n + 1))` by the Ionescu-Tulcea theorem:
`Kernel.trajMeasure μ₀ κ`, a probability measure on trajectories `Π n, X n`. A measure `ν` on
trajectories is this law iff its initial point has law `μ₀` and, at every time `a`, the trajectory
up to `a` and the point at `a + 1` have the joint law `ν.map (frestrictLe a) ⊗ₘ κ a`
(`eq_trajMeasure_iff`; the direction `→` is Mathlib's
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`).

The chain of a kernel `P : Kernel X X` is `trajMeasure μ κ` with `κ n = P.comap (· ⟨n, _⟩)`: the
next point has law `P` at the current one. Its point at time `n` has law `(P ^ n) ∘ₘ μ`
(`trajMeasure_map_eval`) and the pair `(X k, X (k + m))` has law `((P ^ k) ∘ₘ μ) ⊗ₘ (P ^ m)`
(`trajMeasure_map_eval_eval_add`). The Ionescu-Tulcea theorem needs no assumption on the spaces:
`P` is a Markov kernel and `μ` a probability measure, as `trajMeasure` asks.

## Search

`grep -rn "trajMeasure" Mathlib` finds the definition, its `IsProbabilityMeasure` instance,
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` and `condDistrib_trajMeasure`
(`Probability/Kernel/IonescuTulcea/Traj.lean`); `grep -rln "traj κ\|partialTraj" Mathlib` finds in
addition only `Probability/ProductMeasure.lean` (product measures). No characterisation of
`trajMeasure`, no chain of a single kernel, no law of the point at time `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Preorder

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Pushing `ν ⊗ₘ η.comap g` forward by `Prod.map f id` composes the law of `(f, g)` with
`Kernel.id ∥ₖ η`. -/
theorem map_prodMap_compProd_comap (ν : Measure α) [SFinite ν] (η : Kernel γ δ)
    [IsSFiniteKernel η] {f : α → β} {g : α → γ} (hf : Measurable f) (hg : Measurable g) :
    (ν ⊗ₘ η.comap g hg).map (Prod.map f id) = (Kernel.id ∥ₖ η) ∘ₘ ν.map (fun a ↦ (f a, g a)) := by
  ext s hs
  rw [map_apply (hf.prodMap measurable_id) hs, compProd_apply (hf.prodMap measurable_id hs),
    bind_apply hs (Kernel.aemeasurable _), lintegral_map (Kernel.measurable_coe _ hs)
      (hf.prodMk hg)]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.comap_apply, Kernel.parallelComp_apply, Kernel.id_apply, dirac_prod,
    map_apply measurable_prodMk_left hs]
  rfl

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

section General

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)}

/-- The initial point of the trajectory has the initial law. -/
theorem trajMeasure_map_eval_zero : (trajMeasure μ₀ κ).map (fun ω ↦ ω 0) = μ₀ := by
  have h : (fun ω : Π n, X n ↦ ω 0) =
      MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i) ∘ frestrictLe 0 := rfl
  rw [h, ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_frestrictLe 0), trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0), traj_map_frestrictLe, partialTraj_self,
    Measure.id_comp, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    MeasurableEquiv.self_comp_symm, Measure.map_id]

/-- **The law of a Markov chain is determined by its initial law and its transitions**: a measure
`ν` on trajectories is `trajMeasure μ₀ κ` iff its initial point has law `μ₀` and, at every time
`a`, the trajectory up to `a` and the point at `a + 1` have the joint law
`ν.map (frestrictLe a) ⊗ₘ κ a`. -/
theorem eq_trajMeasure_iff [IsProbabilityMeasure μ₀] {ν : Measure (Π n, X n)} :
    ν = trajMeasure μ₀ κ ↔ ν.map (fun ω ↦ ω 0) = μ₀ ∧
      ∀ a, ν.map (fun ω ↦ (frestrictLe a ω, ω (a + 1))) = ν.map (frestrictLe a) ⊗ₘ κ a := by
  refine ⟨fun h ↦ h ▸ ⟨trajMeasure_map_eval_zero,
    fun a ↦ map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm⟩, fun ⟨h0, h⟩ ↦ ?_⟩
  have hT : IsProjectiveMeasureFamily fun I : Finset ℕ ↦ (trajMeasure μ₀ κ).map I.restrict :=
    isProjectiveMeasureFamily_map_restrict (X := fun n (ω : Π n, X n) ↦ ω n)
      fun n ↦ (measurable_pi_apply n).aemeasurable
  suffices hb : ∀ b, ν.map (frestrictLe b) = (trajMeasure μ₀ κ).map (frestrictLe b) by
    exact ((isProjectiveLimit_nat_iff hT ν).2 hb).unique fun I ↦ rfl
  intro b
  induction b with
  | zero =>
    apply (MeasurableEquiv.piUnique _).map_measurableEquiv_injective
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    exact h0.trans trajMeasure_map_eval_zero.symm
  | succ b ih =>
    have hg : Measurable fun p : (Π i : Iic b, X i) × X (b + 1) ↦
        IicProdIoc b (b + 1) (p.1, MeasurableEquiv.piSingleton b p.2) := by fun_prop
    have hf : frestrictLe (b + 1) = (fun p : (Π i : Iic b, X i) × X (b + 1) ↦
        IicProdIoc b (b + 1) (p.1, MeasurableEquiv.piSingleton b p.2)) ∘
          fun ω ↦ (frestrictLe b ω, ω (b + 1)) := by
      ext ω ⟨j, hj⟩
      by_cases hjb : j ≤ b
      · simp [IicProdIoc, hjb]
      · obtain rfl : j = b + 1 := by simp only [mem_Iic] at hj; omega
        simp [IicProdIoc, MeasurableEquiv.piSingleton]
    rw [hf, ← Measure.map_map hg (by fun_prop), h b, ih,
      map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure, Measure.map_map hg (by fun_prop)]

end General

section Homogeneous

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X} [IsMarkovKernel P]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The law of the chain at time `n`**: under the law of the chain of `P` started at `μ`, the
point at time `n` has law `(P ^ n) ∘ₘ μ`. -/
theorem trajMeasure_map_eval (n : ℕ) :
    (trajMeasure (X := fun _ ↦ X) μ fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)).map (fun ω ↦ ω n) =
        (P ^ n) ∘ₘ μ := by
  induction n with
  | zero => exact trajMeasure_map_eval_zero.trans Measure.id_comp.symm
  | succ n ih =>
    have h := congrArg Measure.snd
      (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ ↦ X) (μ₀ := μ)
        (κ := fun n ↦ P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
        (a := n))
    beta_reduce at h
    rw [Measure.snd_compProd, Measure.snd, Measure.map_map measurable_snd (by fun_prop),
      ← comp_deterministic_eq_comap, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
      Measure.map_map (by fun_prop) (by fun_prop)] at h
    rw [(by exact pow_succ' P n : P ^ (n + 1) = P ∘ₖ (P ^ n)), ← Measure.comp_assoc, ← ih]
    exact h.symm

/-- **The Markov property of the chain, for pairs**: under the law of the chain of `P` started at
`μ`, the pair `(X k, X (k + m))` has law `((P ^ k) ∘ₘ μ) ⊗ₘ (P ^ m)`. -/
theorem trajMeasure_map_eval_eval_add (k m : ℕ) :
    (trajMeasure (X := fun _ ↦ X) μ fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)).map
        (fun ω ↦ (ω k, ω (k + m))) = ((P ^ k) ∘ₘ μ) ⊗ₘ (P ^ m) := by
  rw [← trajMeasure_map_eval k]
  induction m with
  | zero =>
    rw [pow_zero]
    refine Eq.trans ?_ Measure.compProd_id.symm
    exact (Measure.map_map (measurable_id.prodMk measurable_id) (measurable_pi_apply k)).symm
  | succ m ih =>
    have h := congrArg (Measure.map (Prod.map
      (fun y : Π i : Iic (k + m), X ↦ y ⟨k, mem_Iic.2 (Nat.le_add_right k m)⟩) id))
      (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ ↦ X) (μ₀ := μ)
        (κ := fun n ↦ P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))
        (a := k + m))
    beta_reduce at h
    rw [Measure.map_prodMap_compProd_comap _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
    rw [(by exact pow_succ' P m : P ^ (m + 1) = P ∘ₖ (P ^ m)),
      ← Measure.parallelComp_comp_compProd, ← ih]
    exact h.symm

end Homogeneous

end ProbabilityTheory.Kernel
