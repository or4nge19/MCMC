/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Composition.Comp
public import MCMC.ToMathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Invariance
public import MCMC.ToMathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Invariant measures of a Markov kernel: powers and differences

The powers `κ ^ n` of a kernel on one space are Mathlib's (`Kernel.instMonoid`, multiplication
`∘ₖ`); the `n`-step law from an initial law `μ` is `(κ ^ n) ∘ₘ μ`. This file adds:

* `ProbabilityTheory.Kernel.Invariant.pow`: a measure invariant under `κ` is invariant under every
  power;
* `ProbabilityTheory.Kernel.existsUnique_invariant_of_existsUnique_invariant_pow`: a unique
  invariant law of a power `κ ^ m` is the unique invariant law of the Markov kernel `κ`;
* `ProbabilityTheory.Kernel.Invariant.sub`: for a Markov kernel and finite invariant measures `μ`,
  `ν`, Mathlib's truncated difference `μ - ν` is invariant; for a finite kernel it need not be
  (`ProbabilityTheory.Kernel.exists_not_invariant_sub_fin_three`).

Searched on 2026-11-25 (Mathlib `d13f23b`): `Probability/Kernel/Invariance.lean` has
`Invariant.comp` and no statement on powers or differences; `grep -rn "Invariant.*sub\|
Invariant.pow" Probability` finds nothing.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-- A measure invariant under a kernel is invariant under each of its powers. -/
theorem Invariant.pow {κ : Kernel α α} {μ : Measure α} (hκ : Invariant κ μ) (n : ℕ) :
    Invariant (κ ^ n) μ := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Measure.id_comp
  | succ n ih =>
    rw [pow_succ]
    exact ih.comp hκ

/-- If a power `κ ^ m` of a Markov kernel has exactly one invariant probability measure, so does
`κ`. -/
theorem existsUnique_invariant_of_existsUnique_invariant_pow {κ : Kernel α α} [IsMarkovKernel κ]
    {m : ℕ} (h : ∃! π : Measure α, IsProbabilityMeasure π ∧ Invariant (κ ^ m) π) :
    ∃! π : Measure α, IsProbabilityMeasure π ∧ Invariant κ π := by
  obtain ⟨π, ⟨hπ, hinv⟩, huniq⟩ := h
  have hcomm : (κ ^ m) ∘ₖ κ = κ ∘ₖ (κ ^ m) := (pow_succ κ m).symm.trans (pow_succ' κ m)
  refine ⟨π, ⟨hπ, ?_⟩, fun π₁ ⟨h₁, h₁P⟩ ↦ huniq π₁ ⟨h₁, h₁P.pow m⟩⟩
  exact huniq (κ ∘ₘ π) ⟨inferInstance, by
    rw [Invariant, Measure.comp_assoc, hcomm, ← Measure.comp_assoc, hinv.def]⟩

/-- **The difference of two invariant measures is invariant**: for a Markov kernel `κ` and finite
measures `μ`, `ν` invariant under `κ`, Mathlib's truncated difference `μ - ν` is invariant. -/
theorem Invariant.sub {κ : Kernel α α} [IsMarkovKernel κ] {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : Invariant κ μ) (hν : Invariant κ ν) : Invariant κ (μ - ν) := by
  set θ := μ ⊓ ν
  have h₁ : θ + (μ - ν) = μ := Measure.inf_add_sub μ ν
  have h₂ : θ + (ν - μ) = ν := (congrArg (· + (ν - μ)) (inf_comm μ ν)).trans
    (Measure.inf_add_sub ν μ)
  have : IsFiniteMeasure θ := isFiniteMeasure_of_le μ inf_le_left
  have hs := Measure.mutually_singular_measure_sub (μ := μ) (ν := ν)
  have e₁ : κ ∘ₘ θ + κ ∘ₘ (μ - ν) = θ + (μ - ν) := by rw [← Measure.comp_add, h₁, hμ.def]
  have e₂ : κ ∘ₘ θ + κ ∘ₘ (ν - μ) = θ + (ν - μ) := by rw [← Measure.comp_add, h₂, hν.def]
  have hb : ∀ A, (ν - μ) (A \ hs.nullSet) = 0 := fun A ↦
    measure_mono_null (fun x hx ↦ hx.2) hs.measure_compl_nullSet
  have hθ : ∀ A, (κ ∘ₘ θ) (A \ hs.nullSet) ≤ θ (A \ hs.nullSet) := fun A ↦
    le_self_add.trans_eq (by simpa [hb A] using congrArg (· (A \ hs.nullSet)) e₂)
  have e₁' : ∀ B, (κ ∘ₘ θ) B + (κ ∘ₘ (μ - ν)) B = θ B + (μ - ν) B := fun B ↦ by
    simpa using congrArg (· B) e₁
  have ha : ∀ A, (μ - ν) A = (μ - ν) (A \ hs.nullSet) := fun A ↦ by
    rw [← measure_inter_add_sdiff A hs.measurableSet_nullSet,
      measure_mono_null inter_subset_right hs.measure_nullSet, zero_add]
  have hle : μ - ν ≤ κ ∘ₘ (μ - ν) := Measure.le_iff.2 fun A _ ↦ by
    rw [ha A]
    refine le_trans ((ENNReal.add_le_add_iff_left (measure_ne_top θ (A \ hs.nullSet))).1 ?_)
      (measure_mono (sdiff_subset : A \ hs.nullSet ⊆ A))
    rw [← e₁']
    exact add_le_add (hθ A) le_rfl
  refine (Measure.eq_of_le_of_measure_univ_eq hle ?_).symm
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  simp

/-- **The Markov hypothesis is forced in `Invariant.sub`**: on `Fin 3` the finite kernel
`κ 0 = δ₀ + ½ δ₁`, `κ 1 = ½ δ₁`, `κ 2 = ½ δ₁ + δ₂` leaves `δ₀ + δ₁` and `δ₁ + δ₂` invariant but
not their truncated difference `D`: `δ₁ ≤ (δ₀ + δ₁) ⊓ (δ₁ + δ₂)` gives `D {1} = 0`, while
`D {0} = 1` and `(κ ∘ₘ D) {1} = ½ D {0} + ½ D {1} + ½ D {2} = ½`. -/
theorem exists_not_invariant_sub_fin_three :
    ∃ κ : Kernel (Fin 3) (Fin 3), IsFiniteKernel κ ∧
      Invariant κ (Measure.dirac 0 + Measure.dirac 1) ∧
      Invariant κ (Measure.dirac 1 + Measure.dirac 2) ∧
      ¬ Invariant κ (Measure.dirac 0 + Measure.dirac 1 - (Measure.dirac 1 + Measure.dirac 2)) := by
  set κ : Kernel (Fin 3) (Fin 3) := Kernel.ofFunOfCountable
    ![Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1, (2⁻¹ : ℝ≥0∞) • Measure.dirac 1,
      (2⁻¹ : ℝ≥0∞) • Measure.dirac 1 + Measure.dirac 2] with hκ
  have hb (μ : Measure (Fin 3)) (a : Fin 3) : (μ.bind κ) {a} = ∑ x, κ x {a} * μ {x} := by
    rw [Measure.bind_apply (measurableSet_singleton a) (Kernel.aemeasurable _), lintegral_fintype]
  have h2 : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.2 one_le_two
  have hfin : IsFiniteKernel κ := ⟨⟨2, by simp, fun x ↦ by
    fin_cases x <;> simp [hκ, Kernel.ofFunOfCountable]
    · exact (add_le_add le_rfl h2).trans one_add_one_eq_two.le
    · exact h2.trans one_le_two
    · exact (add_le_add h2 le_rfl).trans one_add_one_eq_two.le⟩⟩
  have hinv2 : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  refine ⟨κ, hfin, Measure.ext_of_singleton fun a ↦ ?_, Measure.ext_of_singleton fun a ↦ ?_, ?_⟩
  · rw [hb]
    fin_cases a <;> simp [Fin.sum_univ_three, hκ, Kernel.ofFunOfCountable, hinv2]
  · rw [hb]
    fin_cases a <;> simp [Fin.sum_univ_three, hκ, Kernel.ofFunOfCountable, hinv2]
  · intro hinv
    have h := Measure.inf_add_sub (Measure.dirac (0 : Fin 3) + Measure.dirac 1)
      (Measure.dirac 1 + Measure.dirac 2)
    have hθ : Measure.dirac (1 : Fin 3) ≤ (Measure.dirac (0 : Fin 3) + Measure.dirac 1) ⊓
        (Measure.dirac 1 + Measure.dirac 2) := le_inf (Measure.le_add_left le_rfl)
      (Measure.le_add_right le_rfl)
    have hθ0 := Measure.le_iff'.1 (inf_le_right : (Measure.dirac (0 : Fin 3) +
      Measure.dirac 1) ⊓ (Measure.dirac 1 + Measure.dirac 2) ≤ _) {0}
    set θ := (Measure.dirac (0 : Fin 3) + Measure.dirac 1) ⊓ (Measure.dirac 1 + Measure.dirac 2)
    set D := Measure.dirac (0 : Fin 3) + Measure.dirac 1 - (Measure.dirac 1 + Measure.dirac 2)
    have h0 := congrArg (· {0}) h
    have h1 := congrArg (· {1}) h
    have h2 := congrArg (· {2}) h
    have hi := congrArg (· {1}) hinv.def
    have hθ1 := Measure.le_iff'.1 hθ {1}
    rw [hb] at hi
    simp [Fin.sum_univ_three, hκ, Kernel.ofFunOfCountable] at hi
    simp at h0 h1 h2 hθ0 hθ1
    rw [hθ0, zero_add] at h0
    have hD1 : D {1} = 0 := nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left
      ENNReal.one_ne_top).1 (((add_le_add_left hθ1 _).trans_eq h1).trans_eq (add_zero 1).symm))
    rw [h0, hD1, h2.2] at hi
    simp at hi

end Kernel

end ProbabilityTheory
