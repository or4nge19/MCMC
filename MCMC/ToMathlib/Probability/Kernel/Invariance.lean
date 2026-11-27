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
public import MCMC.ToMathlib.MeasureTheory.Integral.Lebesgue.Basic
public import MCMC.ToMathlib.MeasureTheory.Measure.Prod
public import MCMC.ToMathlib.Probability.Kernel.Composition.MeasureCompProd
public import MCMC.ToMathlib.Probability.Kernel.WithDensity

/-!
# Invariant measures and reversible kernels: powers, differences, swaps and mixtures

The powers `κ ^ n` of a kernel on one space are Mathlib's (`Kernel.instMonoid`, multiplication
`∘ₖ`); the `n`-step law from an initial law `μ` is `(κ ^ n) ∘ₘ μ`. This file adds:

* `ProbabilityTheory.Kernel.Invariant.pow`: a measure invariant under `κ` is invariant under every
  power;
* `ProbabilityTheory.Kernel.existsUnique_invariant_of_existsUnique_invariant_pow`: a unique
  invariant law of a power `κ ^ m` is the unique invariant law of the Markov kernel `κ`;
* `ProbabilityTheory.Kernel.Invariant.sub`: for a Markov kernel and finite invariant measures `μ`,
  `ν`, Mathlib's truncated difference `μ - ν` is invariant; for a finite kernel it need not be
  (`ProbabilityTheory.Kernel.exists_not_invariant_sub_fin_three`);
* `ProbabilityTheory.Kernel.isReversible_iff_forall_disjoint`: detailed balance on disjoint pairs
  of sets suffices for reversibility;
* `ProbabilityTheory.Kernel.IsReversible.of_map_swap_compProd`,
  `ProbabilityTheory.Kernel.isReversible_iff_map_swap_compProd`: reversibility is the invariance
  of `π ⊗ₘ κ` under `Prod.swap` when the first marginal `(π ⊗ₘ κ).fst` is σ-finite; the
  counterexamples for the σ-finiteness are in `MCMC/ToMathlib/Probability/Kernel/Reversible.lean`;
* `ProbabilityTheory.Kernel.IsReversible.add`, `ProbabilityTheory.Kernel.IsReversible.sum`,
  `ProbabilityTheory.Kernel.IsReversible.withDensity_const`,
  `ProbabilityTheory.Kernel.isReversible_sum_withDensity_const`: mixtures of `π`-reversible kernels
  (random-scan samplers) are `π`-reversible, as are `0` and `Kernel.id`.
* `ProbabilityTheory.Kernel.IsReversible.withDensity_simpleFunc`,
  `ProbabilityTheory.Kernel.IsReversible.withDensity_iSup`: a `π`-reversible kernel stays
  `π`-reversible with a density that is a symmetric function of a simple function of the two
  states, and under monotone limits of densities; no hypothesis on `π`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `Probability/Kernel/Invariance.lean` has
`Invariant.comp` and no statement on powers or differences; `grep -rn "Invariant.*sub\|
Invariant.pow" Probability` finds nothing. Searched on 2026-11-26: `grep -rn "IsReversible"
Mathlib` finds only the definition and `IsReversible.invariant`; `grep -rn "Prod.swap"
Mathlib/Probability/Kernel` finds no statement about reversibility.
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

/-! ### Reversible kernels

Mathlib's `ProbabilityTheory.Kernel.IsReversible κ π` is detailed balance on measurable sets. -/

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {κ : Kernel X X} {π : Measure X}

/-- Detailed balance on pairs of disjoint measurable sets implies detailed balance. -/
theorem isReversible_iff_forall_disjoint :
    κ.IsReversible π ↔ ∀ ⦃s t : Set X⦄, MeasurableSet s → MeasurableSet t → Disjoint s t →
      ∫⁻ x in s, κ x t ∂π = ∫⁻ x in t, κ x s ∂π := by
  refine ⟨fun h s t hs ht _ ↦ h hs ht, fun h s t hs ht ↦ ?_⟩
  have split : ∀ ⦃A B : Set X⦄, MeasurableSet A → MeasurableSet B → ∫⁻ x in A, κ x B ∂π =
      ∫⁻ x in A ∩ B, κ x (B ∩ A) ∂π + ∫⁻ x in A ∩ B, κ x (B \ A) ∂π +
        (∫⁻ x in A \ B, κ x (B ∩ A) ∂π + ∫⁻ x in A \ B, κ x (B \ A) ∂π) := fun A B hA hB ↦ by
    rw [← lintegral_add_left (κ.measurable_coe (hB.inter hA)),
      ← lintegral_add_left (κ.measurable_coe (hB.inter hA)), lintegral_inter_add_sdiff _ _ hB]
    simp_rw [measure_inter_add_sdiff _ hA]
  rw [split hs ht, split ht hs, inter_comm t s,
    h (hs.inter ht) (ht.diff hs) (disjoint_sdiff_right.mono_left inter_subset_left),
    h (hs.diff ht) (hs.inter ht) (disjoint_sdiff_left.mono_right inter_subset_right),
    h (hs.diff ht) (ht.diff hs) disjoint_sdiff_sdiff]
  ring

/-- A kernel whose composition-product with `π` is invariant under the swap is `π`-reversible. -/
theorem IsReversible.of_map_swap_compProd [SFinite π] [IsSFiniteKernel κ]
    (h : (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ) : κ.IsReversible π := fun s t hs ht ↦ by
  rw [← Measure.compProd_apply_prod hs ht, ← h, Measure.map_apply measurable_swap (hs.prod ht),
    preimage_swap_prod, Measure.compProd_apply_prod ht hs]

/-- If the first marginal of `π ⊗ₘ κ` is σ-finite, `κ` is `π`-reversible iff `π ⊗ₘ κ` is
invariant under the swap. The marginal is σ-finite if `π` is and `κ x` is finite for `π`-almost
every `x` (`MeasureTheory.Measure.sigmaFinite_fst_compProd`). -/
theorem isReversible_iff_map_swap_compProd [SFinite π] [IsSFiniteKernel κ]
    [SigmaFinite (π ⊗ₘ κ).fst] :
    κ.IsReversible π ↔ (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ := by
  refine ⟨fun h ↦ ?_, IsReversible.of_map_swap_compProd⟩
  refine (Measure.ext_prod_of_sigmaFinite_fst fun s t hs ht ↦ ?_).symm
  rw [Measure.map_apply measurable_swap (hs.prod ht), preimage_swap_prod,
    Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod ht hs, h hs ht]

/-- The zero kernel is reversible for every measure. -/
theorem isReversible_zero : (0 : Kernel X X).IsReversible π := fun s t _ _ ↦ by simp

/-- The identity kernel is reversible for every measure. -/
theorem isReversible_id : (Kernel.id : Kernel X X).IsReversible π := fun s t hs ht ↦ by
  simp only [Kernel.id_apply, Measure.dirac_apply' _ ht, Measure.dirac_apply' _ hs]
  rw [← lintegral_indicator hs, ← lintegral_indicator ht]
  refine lintegral_congr fun x ↦ ?_
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]

/-- The sum of two `π`-reversible kernels is `π`-reversible. -/
theorem IsReversible.add {η : Kernel X X} (hκ : κ.IsReversible π) (hη : η.IsReversible π) :
    (κ + η).IsReversible π := fun s t hs ht ↦ by
  simp only [add_apply, Measure.add_apply]
  rw [lintegral_add_left (κ.measurable_coe ht), lintegral_add_left (κ.measurable_coe hs),
    hκ hs ht, hη hs ht]

/-- A countable sum of `π`-reversible kernels is `π`-reversible. -/
theorem IsReversible.sum {ι : Type*} [Countable ι] {κ : ι → Kernel X X}
    (h : ∀ i, (κ i).IsReversible π) : (Kernel.sum κ).IsReversible π := fun s t hs ht ↦ by
  simp only [Kernel.sum_apply' _ _ ht, Kernel.sum_apply' _ _ hs]
  rw [lintegral_tsum fun i ↦ ((κ i).measurable_coe ht).aemeasurable,
    lintegral_tsum fun i ↦ ((κ i).measurable_coe hs).aemeasurable]
  exact tsum_congr fun i ↦ h i hs ht

/-- A constant multiple `κ.withDensity fun _ _ ↦ c` of a `π`-reversible kernel is
`π`-reversible. -/
theorem IsReversible.withDensity_const [IsSFiniteKernel κ] (hκ : κ.IsReversible π) (c : ℝ≥0∞) :
    (κ.withDensity fun _ _ ↦ c).IsReversible π := fun s t hs ht ↦ by
  have hc : Measurable (Function.uncurry fun (_ : X) (_ : X) ↦ c) := measurable_const
  simp only [Kernel.withDensity_apply _ hc, MeasureTheory.withDensity_const, Measure.smul_apply,
    smul_eq_mul]
  rw [lintegral_const_mul _ (κ.measurable_coe ht), lintegral_const_mul _ (κ.measurable_coe hs),
    hκ hs ht]

/-- The monotone limit of densities with `π`-reversible kernels gives a `π`-reversible kernel. -/
theorem IsReversible.withDensity_iSup [IsSFiniteKernel κ] {h : ℕ → X → X → ℝ≥0∞}
    (hh : ∀ n, Measurable (Function.uncurry (h n))) (hmono : ∀ x y, Monotone fun n ↦ h n x y)
    (hrev : ∀ n, (κ.withDensity (h n)).IsReversible π) :
    (κ.withDensity fun x y ↦ ⨆ n, h n x y).IsReversible π := by
  have hsm : Measurable (Function.uncurry fun x y ↦ ⨆ n, h n x y) := Measurable.iSup hh
  have key : ∀ ⦃u v : Set X⦄, MeasurableSet u → MeasurableSet v →
      ∫⁻ x in u, (κ.withDensity fun x y ↦ ⨆ n, h n x y) x v ∂π =
        ⨆ n, ∫⁻ x in u, κ.withDensity (h n) x v ∂π := fun u v hu hv ↦ by
    refine Eq.trans ?_ (lintegral_iSup (μ := π.restrict u)
      (f := fun n x ↦ κ.withDensity (h n) x v) (fun n ↦ Kernel.measurable_coe _ hv)
      fun n m hnm x ↦ ?_)
    · exact lintegral_congr fun x ↦ (Kernel.withDensity_apply' _ hsm x v).trans
        ((lintegral_iSup (f := fun n y ↦ h n x y) (fun n ↦ (hh n).comp measurable_prodMk_left)
          fun n m hnm y ↦ hmono x y hnm).trans
            (iSup_congr fun n ↦ (Kernel.withDensity_apply' _ (hh n) x v).symm))
    · change κ.withDensity (h n) x v ≤ κ.withDensity (h m) x v
      rw [Kernel.withDensity_apply' _ (hh n), Kernel.withDensity_apply' _ (hh m)]
      exact lintegral_mono fun y ↦ hmono x y hnm
  intro s t hs ht
  rw [key hs ht, key ht hs]
  exact iSup_congr fun n ↦ hrev n hs ht

/-- A `π`-reversible kernel with a density that is a symmetric function `w` of a simple function
`g` of the two states is `π`-reversible, for every measure `π`: the flow from `s` to `t` is
`∑ c, ∑ d, w c d * ∫⁻ x in s ∩ g ⁻¹' {c}, κ x (t ∩ g ⁻¹' {d}) ∂π`. -/
theorem IsReversible.withDensity_simpleFunc [IsSFiniteKernel κ] (hκ : κ.IsReversible π)
    {β : Type*} (g : SimpleFunc X β) {w : β → β → ℝ≥0∞} (hw : ∀ c d, w c d = w d c) :
    (κ.withDensity fun x y ↦ w (g x) (g y)).IsReversible π := by
  have hm : Measurable (Function.uncurry fun x y ↦ w (g x) (g y)) :=
    (((g.comp Prod.fst measurable_fst).pair (g.comp Prod.snd measurable_snd)).map
      (Function.uncurry w)).measurable
  have hA : ∀ c, MeasurableSet (g ⁻¹' {c}) := g.measurableSet_fiber
  have hpt : ∀ x ⦃v : Set X⦄, MeasurableSet v → (κ.withDensity fun x y ↦ w (g x) (g y)) x v =
      ∑ d ∈ g.range, w (g x) d * κ x (v ∩ g ⁻¹' {d}) := fun x v hv ↦ by
    rw [Kernel.withDensity_apply' _ hm, g.setLIntegral_eq_sum_fiber _ hv]
    exact Finset.sum_congr rfl fun d _ ↦ (setLIntegral_congr_fun (hv.inter (hA d)) fun y hy ↦ by
      rw [show g y = d from hy.2]).trans (MeasureTheory.setLIntegral_const _ _)
  have key : ∀ ⦃u v : Set X⦄, MeasurableSet u → MeasurableSet v →
      ∫⁻ x in u, (κ.withDensity fun x y ↦ w (g x) (g y)) x v ∂π = ∑ c ∈ g.range,
        ∑ d ∈ g.range, w c d * ∫⁻ x in u ∩ g ⁻¹' {c}, κ x (v ∩ g ⁻¹' {d}) ∂π :=
    fun u v hu hv ↦ by
      rw [g.setLIntegral_eq_sum_fiber _ hu]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [setLIntegral_congr_fun (hu.inter (hA c)) fun x hx ↦ by
        rw [hpt x hv, show g x = c from hx.2], lintegral_finsetSum _ fun d _ ↦
          (Kernel.measurable_coe κ (hv.inter (hA d))).const_mul _]
      exact Finset.sum_congr rfl fun d _ ↦
        lintegral_const_mul _ (Kernel.measurable_coe κ (hv.inter (hA d)))
  intro s t hs ht
  rw [key hs ht, key ht hs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  rw [hw, hκ (hs.inter (hA d)) (ht.inter (hA c))]

/-- **Random-scan mixtures are reversible**: the mixture `∑ i, w i • κ i` of `π`-reversible
kernels, written with Mathlib's `Kernel.sum` and constant densities, is `π`-reversible. -/
theorem isReversible_sum_withDensity_const {ι : Type*} [Countable ι] {κ : ι → Kernel X X}
    [∀ i, IsSFiniteKernel (κ i)] (h : ∀ i, (κ i).IsReversible π) (w : ι → ℝ≥0∞) :
    (Kernel.sum fun i ↦ (κ i).withDensity fun _ _ ↦ w i).IsReversible π :=
  IsReversible.sum fun i ↦ (h i).withDensity_const (w i)

end ProbabilityTheory.Kernel
