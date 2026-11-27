/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Dynamics.Ergodic.AddCircleAdd
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import MCMC.ToMathlib.Dynamics.Ergodic.Ergodic
public import MCMC.ToMathlib.Probability.Kernel.AcceptReject

/-!
# Counterexamples on reversibility, σ-finiteness and the Metropolis–Hastings acceptance

`ProbabilityTheory.Kernel.isReversible_iff_map_swap_compProd` (in
`MCMC/ToMathlib/Probability/Kernel/Invariance.lean`) identifies reversibility with the invariance
of `π ⊗ₘ κ` under `Prod.swap` when the first marginal `(π ⊗ₘ κ).fst` is σ-finite. The
counterexamples below show that this hypothesis cannot be dropped, whether it fails through `π`
(an infinite multiple of a probability measure) or through `κ` (a kernel of infinite mass). They
rest on one probability measure on `ℝ`, the Gaussian `N(0, 1)`, with a Markov kernel for which
`ν ⊗ₘ κ` and its swap have the same null rectangles but are not mutually absolutely continuous.
A third counterexample, the orbit-counting kernel of an irrational rotation of the circle, has a
σ-finite flow `π ⊗ₘ κ` and a first marginal that is not σ-finite.

## Main statements

* `exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous`.
* `exists_isReversible_smul_top_and_map_swap_compProd_ne`,
  `exists_isReversible_withDensity_top_and_map_swap_compProd_ne`.
* `exists_isReversible_acceptReject_and_map_swap_ne`,
  `exists_isReversible_acceptReject_top_and_map_swap_ne`: the same two failures for the
  accepted-flow criterion `isReversible_acceptReject_iff_map_swap` of accept–reject kernels.
* `isReversible_sum_deterministic_iterate`, `sigmaFinite_compProd_sum_deterministic_iterate`,
  `not_ae_le_mhAcceptance_sum_deterministic_iterate`: for an ergodic map `T` of a finite measure
  space with no periodic point, the kernel `x ↦ ∑ n, δ_{T^[n] x}` is reversible, its flow is
  σ-finite and not invariant under the swap (every flow between two sets is `0` or `∞`).
* `exists_isReversible_acceptReject_not_ae_le_mhAcceptance_lintegral_eq_top`: on the circle, with
  an irrational rotation, this kernel shows that finiteness of the accepted mass is needed in the
  maximality of the Metropolis–Hastings acceptance
  (`ae_le_mhAcceptance_of_isReversible_acceptReject`); the two `example`s after it show that
  σ-finiteness of the first marginal is needed in `mhAcceptance_withDensity_ae_eq_min_one_div` and
  cannot be weakened to that of `π ⊗ₘ κ` in `isReversible_iff_map_swap_compProd`.

Staged for Mathlib's `Counterexamples/` (new file): the Gaussian measure is the only reason for the
import of `Mathlib.Probability.Distributions.Gaussian.Real`, and the rotation of the circle for
that of `Mathlib.Dynamics.Ergodic.AddCircleAdd`, which the files of the theorems
(`Invariance.lean`, `AcceptReject.lean`) do not import.

## References

* C. P. Robert, G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer (2004), §6.5.3:
  Definitions 6.44–6.45, Theorem 6.46 and its footnote 3 (p. 230).
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer (2021): the
  composition `ν ⊗ μ` (Chapter 3, (2), Lemma 3.3) and Theorem 3.4 (ii); reversible kernels are not
  treated there.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {κ : Kernel X X} {π : Measure X}

/-- With `ν = N(0, 1)` on `ℝ` and the Markov kernel `κ x = (N(0, 1) + δ_{x + 1}) / 2`, the
measure `ν ⊗ₘ κ` and its image under the swap have the same null rectangles, but the graph
`{p | p.2 - 1 = p.1}` is null for the image and not for `ν ⊗ₘ κ`. -/
theorem exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous :
    ∃ (ν : Measure ℝ) (κ : Kernel ℝ ℝ), IsProbabilityMeasure ν ∧ IsMarkovKernel κ ∧
      (∀ ⦃s t : Set ℝ⦄, MeasurableSet s → MeasurableSet t →
        ((ν ⊗ₘ κ) (s ×ˢ t) = 0 ↔ (ν ⊗ₘ κ) (t ×ˢ s) = 0)) ∧
      ¬ ν ⊗ₘ κ ≪ (ν ⊗ₘ κ).map Prod.swap := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  set γ := gaussianReal 0 1
  set κ₀ : Kernel ℝ ℝ := Kernel.const ℝ γ + Kernel.deterministic (· + 1) (measurable_add_const 1)
  have hκ₀ : γ ⊗ₘ κ₀.withDensity (fun _ _ ↦ 2⁻¹) =
      (2⁻¹ : ℝ≥0∞) • (γ.prod γ + γ.map fun x ↦ (x, x + 1)) := by
    rw [Measure.compProd_withDensity measurable_const, withDensity_const,
      Measure.compProd_add_right, Measure.compProd_const, Measure.compProd_deterministic]
  have hM : IsMarkovKernel (κ₀.withDensity fun _ _ ↦ 2⁻¹) := ⟨fun x ↦ ⟨by
    rw [Kernel.withDensity_apply _ measurable_const, withDensity_const, Measure.smul_apply,
      add_apply, Measure.add_apply, const_apply, deterministic_apply, measure_univ,
      measure_univ, smul_eq_mul, one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero
      ENNReal.ofNat_ne_top]⟩⟩
  have hgm : Measurable fun x : ℝ ↦ (x, x + 1) := measurable_id'.prodMk (measurable_add_const 1)
  have htr : ∀ t, γ t = 0 → γ ((· + 1) ⁻¹' t) = 0 := fun t ht ↦
    gaussianReal_absolutelyContinuous 0 one_ne_zero (by
      rw [measure_preimage_add_right]; exact gaussianReal_absolutelyContinuous' 0 one_ne_zero ht)
  have hrect : ∀ ⦃s t : Set ℝ⦄, MeasurableSet s → MeasurableSet t →
      ((γ.prod γ + γ.map fun x ↦ (x, x + 1) : Measure (ℝ × ℝ)) (s ×ˢ t) = 0 ↔
        γ s = 0 ∨ γ t = 0) := by
    intro s t hs ht
    rw [Measure.add_apply, Measure.prod_prod,
      Measure.map_apply hgm (hs.prod ht),
      mk_preimage_prod, preimage_id', add_eq_zero, mul_eq_zero]
    refine ⟨And.left, fun h ↦ ⟨h, h.elim (measure_mono_null inter_subset_left)
      fun h' ↦ measure_mono_null inter_subset_right (htr t h')⟩⟩
  have hG : MeasurableSet {p : ℝ × ℝ | p.2 - 1 = p.1} :=
    measurableSet_eq_fun (measurable_snd.sub_const 1) measurable_fst
  refine ⟨γ, _, inferInstance, hM, fun s t hs ht ↦ ?_, fun hac ↦ ?_⟩
  · rw [hκ₀, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_eq_zero,
      mul_eq_zero, hrect hs ht, hrect ht hs]
    exact or_congr_right or_comm
  have h0 := @hac {p : ℝ × ℝ | p.2 - 1 = p.1} (by
    rw [hκ₀, Measure.map_smul _ measurable_swap.aemeasurable, Measure.smul_apply,
      Measure.map_apply measurable_swap hG, Measure.add_apply,
      Measure.prod_apply (measurable_swap hG), Measure.map_apply hgm (measurable_swap hG)]
    simp [show ∀ a : ℝ, a - 1 ≠ a + 1 from fun a h ↦ by linarith])
  rw [hκ₀, Measure.smul_apply, Measure.add_apply, Measure.map_apply hgm hG] at h0
  simp at h0

/-- σ-finiteness of the first marginal is needed in `isReversible_iff_map_swap_compProd`, even
for a Markov kernel: a Markov kernel on `ℝ` is reversible for the s-finite measure `∞ • ν` with
`ν` a probability measure (the first marginal is `∞ • ν`), and `(∞ • ν) ⊗ₘ κ` is not invariant
under the swap. -/
theorem exists_isReversible_smul_top_and_map_swap_compProd_ne :
    ∃ (ν : Measure ℝ) (κ : Kernel ℝ ℝ), IsProbabilityMeasure ν ∧ IsMarkovKernel κ ∧
      κ.IsReversible (∞ • ν) ∧ ((∞ • ν) ⊗ₘ κ).map Prod.swap ≠ (∞ • ν) ⊗ₘ κ := by
  obtain ⟨ν, κ, hν, hκ, hnull, hac⟩ := exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous
  refine ⟨ν, κ, hν, hκ, fun s t hs ht ↦ ?_, fun h ↦ hac fun s hs ↦ ?_⟩
  · rw [← Measure.compProd_apply_prod hs ht, ← Measure.compProd_apply_prod ht hs,
      Measure.compProd_smul_left, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases h0 : (ν ⊗ₘ κ) (s ×ˢ t) = 0
    · rw [h0, (hnull hs ht).1 h0]
    · rw [ENNReal.top_mul h0, ENNReal.top_mul (mt (hnull hs ht).2 h0)]
  · rw [Measure.compProd_smul_left, Measure.map_smul _ measurable_swap.aemeasurable] at h
    have h's := congrArg (· s) h
    simp only [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h's
    exact (mul_eq_zero.1 h's.symm).resolve_left ENNReal.top_ne_zero

/-- σ-finiteness of the first marginal is needed in `isReversible_iff_map_swap_compProd` for a
probability measure `π`: for a Markov kernel `Q` on `ℝ`, the kernel `Q.withDensity fun _ _ ↦ ∞`,
of infinite mass at every point (the first marginal is `∞ • π`), is `π`-reversible and its
composition-product with `π` is not invariant under the swap. -/
theorem exists_isReversible_withDensity_top_and_map_swap_compProd_ne :
    ∃ (π : Measure ℝ) (Q : Kernel ℝ ℝ) (_ : IsMarkovKernel Q), IsProbabilityMeasure π ∧
      (Q.withDensity fun _ _ ↦ ∞).IsReversible π ∧
      (π ⊗ₘ Q.withDensity fun _ _ ↦ ∞).map Prod.swap ≠ π ⊗ₘ Q.withDensity fun _ _ ↦ ∞ := by
  obtain ⟨ν, κ, hν, hκ, hrev, hne⟩ := exists_isReversible_smul_top_and_map_swap_compProd_ne
  have heq : ν ⊗ₘ κ.withDensity (fun _ _ ↦ ∞) = (∞ • ν) ⊗ₘ κ := by
    rw [Measure.compProd_withDensity measurable_const, withDensity_const,
      Measure.compProd_smul_left]
  refine ⟨ν, κ, hκ, hν, fun s t hs ht ↦ ?_, by rw [heq]; exact hne⟩
  rw [← Measure.compProd_apply_prod hs ht, ← Measure.compProd_apply_prod ht hs, heq,
    Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod ht hs, hrev hs ht]

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

/-! ### The orbit-counting kernel of an ergodic map -/

section Iterate

open Filter
open scoped Topology

variable {μ : Measure X} {T : X → X}

/-- The kernel `x ↦ ∑ n, δ_{T^[n] x}` on a measurable set counts the visits of the orbit of `x`. -/
theorem sum_deterministic_iterate_apply (hT : Measurable T) (x : X) {B : Set X}
    (hB : MeasurableSet B) :
    (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)) x B =
      ∑' n : ℕ, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) (T^[n] x) :=
  (Kernel.sum_apply' _ _ hB).trans (tsum_congr fun _ ↦ Kernel.deterministic_apply' _ _ hB)

/-- For an ergodic map `T` of a finite measure space, the kernel `x ↦ ∑ n, δ_{T^[n] x}` gives
mass `∞` to every set of positive measure, from almost every point. -/
theorem ae_sum_deterministic_iterate_eq_top [IsFiniteMeasure μ] (hT : Ergodic T μ) {t : Set X}
    (ht : MeasurableSet t) (h0 : μ t ≠ 0) :
    ∀ᵐ x ∂μ, (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.measurable.iterate n)) x t =
      ∞ := by
  filter_upwards [hT.ae_frequently_iterate_mem ht h0] with x hx
  rw [sum_deterministic_iterate_apply hT.measurable x ht]
  by_contra hne
  obtain ⟨n, hn, hlt⟩ := (hx.and_eventually ((ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    hne).eventually (gt_mem_nhds zero_lt_one))).exists
  exact lt_irrefl (1 : ℝ≥0∞) (by simpa only [indicator_of_mem hn] using hlt)

/-- For a measure-preserving map `T`, the kernel `x ↦ ∑ n, δ_{T^[n] x}` gives mass `0` to every
null set, from almost every point. -/
theorem ae_sum_deterministic_iterate_eq_zero (hT : MeasurePreserving T μ μ) {t : Set X}
    (ht : MeasurableSet t) (h0 : μ t = 0) :
    ∀ᵐ x ∂μ, (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.measurable.iterate n)) x t =
      0 := by
  filter_upwards [ae_all_iff.2 fun n : ℕ ↦ measure_eq_zero_iff_ae_notMem.1
    (((hT.iterate n).measure_preimage ht.nullMeasurableSet).trans h0)] with x hx
  rw [sum_deterministic_iterate_apply hT.measurable x ht]
  exact ENNReal.tsum_eq_zero.2 fun n ↦ indicator_of_notMem (show T^[n] x ∉ t from hx n) _

/-- **A reversible kernel whose flow is σ-finite and not invariant under the swap.** For an
ergodic map `T` of a finite measure space, the kernel `x ↦ ∑ n, δ_{T^[n] x}` is `μ`-reversible:
the flow from `s` to `t` is `∞` if both sets have positive measure and `0` otherwise. -/
theorem isReversible_sum_deterministic_iterate [IsFiniteMeasure μ] (hT : Ergodic T μ) :
    (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.measurable.iterate n)).IsReversible
      μ := by
  have hzero : ∀ (s : Set X) ⦃t : Set X⦄, MeasurableSet t → μ s = 0 ∨ μ t = 0 →
      ∫⁻ x in s, (Kernel.sum fun n : ℕ ↦
        Kernel.deterministic T^[n] (hT.measurable.iterate n)) x t ∂μ = 0 := fun s t ht h ↦
    h.elim (fun h ↦ by rw [Measure.restrict_eq_zero.2 h, lintegral_zero_measure])
      fun h ↦ (lintegral_congr_ae (ae_restrict_of_ae
        (ae_sum_deterministic_iterate_eq_zero hT.toMeasurePreserving ht h))).trans lintegral_zero
  have htop : ∀ ⦃s t : Set X⦄, MeasurableSet t → μ s ≠ 0 → μ t ≠ 0 →
      ∫⁻ x in s, (Kernel.sum fun n : ℕ ↦
        Kernel.deterministic T^[n] (hT.measurable.iterate n)) x t ∂μ = ∞ := fun s t ht hs h ↦
    (lintegral_congr_ae (ae_restrict_of_ae (ae_sum_deterministic_iterate_eq_top hT ht h))).trans
      (by rw [MeasureTheory.setLIntegral_const, ENNReal.top_mul hs])
  intro s t hs ht
  by_cases h : μ s = 0 ∨ μ t = 0
  · rw [hzero s ht h, hzero t hs h.symm]
  · rw [htop ht (not_or.1 h).1 (not_or.1 h).2, htop hs (not_or.1 h).2 (not_or.1 h).1]

/-- For a map `T` with no periodic point, the flow of `x ↦ ∑ n, δ_{T^[n] x}` through the graph of
`T^[m]` is `μ univ`. -/
theorem compProd_sum_deterministic_iterate_graph [MeasurableEq X] [SFinite μ] (hT : Measurable T)
    (hinj : ∀ x, Function.Injective fun n : ℕ ↦ T^[n] x) (m : ℕ) :
    (μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n))
      {p | p.2 = T^[m] p.1} = μ univ := by
  have hG : MeasurableSet {p : X × X | p.2 = T^[m] p.1} :=
    measurableSet_eq_fun measurable_snd ((hT.iterate m).comp measurable_fst)
  have hterm : ∀ x n, n ≠ m → (Prod.mk x ⁻¹' {p : X × X | p.2 = T^[m] p.1}).indicator
      (fun _ ↦ (1 : ℝ≥0∞)) (T^[n] x) = 0 := fun x n hn ↦
    indicator_of_notMem (show T^[n] x ∉ Prod.mk x ⁻¹' {p : X × X | p.2 = T^[m] p.1} from
      fun h ↦ hn (@hinj x n m h)) _
  rw [Measure.compProd_apply hG]
  refine (lintegral_congr fun x ↦ ?_).trans lintegral_one
  rw [sum_deterministic_iterate_apply hT x (measurable_prodMk_left hG),
    tsum_eq_single m fun n hn ↦ hterm x n hn]
  exact indicator_of_mem (show T^[m] x ∈ Prod.mk x ⁻¹' {p : X × X | p.2 = T^[m] p.1} from rfl) _

/-- For a map `T` with no periodic point and a finite measure `μ`, the flow of the kernel
`x ↦ ∑ n, δ_{T^[n] x}` is σ-finite: it is carried by the graphs of the iterates, each of mass
`μ univ`. -/
theorem sigmaFinite_compProd_sum_deterministic_iterate [MeasurableEq X] [IsFiniteMeasure μ]
    (hT : Measurable T) (hinj : ∀ x, Function.Injective fun n : ℕ ↦ T^[n] x) :
    SigmaFinite (μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)) := by
  have hG : ∀ m, MeasurableSet {p : X × X | p.2 = T^[m] p.1} := fun m ↦
    measurableSet_eq_fun measurable_snd ((hT.iterate m).comp measurable_fst)
  have hc : (μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n))
      (⋃ m, {p : X × X | p.2 = T^[m] p.1})ᶜ = 0 := by
    rw [Measure.compProd_apply (MeasurableSet.iUnion hG).compl]
    refine (lintegral_congr fun x ↦ ?_).trans lintegral_zero
    rw [sum_deterministic_iterate_apply hT x
      (measurable_prodMk_left (MeasurableSet.iUnion hG).compl)]
    exact ENNReal.tsum_eq_zero.2 fun n ↦ indicator_of_notMem
      (show T^[n] x ∉ Prod.mk x ⁻¹' (⋃ m, {p : X × X | p.2 = T^[m] p.1})ᶜ from fun h ↦
        absurd (mem_iUnion.2 ⟨n, rfl⟩ : (x, T^[n] x) ∈ ⋃ m, {p : X × X | p.2 = T^[m] p.1}) h) _
  refine Measure.sigmaFinite_of_countable (S := insert (⋃ m, {p : X × X | p.2 = T^[m] p.1})ᶜ
    (range fun m ↦ {p : X × X | p.2 = T^[m] p.1})) ((countable_range _).insert _) ?_ ?_
  · rintro s (rfl | ⟨m, rfl⟩)
    · rw [hc]
      exact ENNReal.zero_lt_top
    · rw [compProd_sum_deterministic_iterate_graph hT hinj m]
      exact measure_lt_top μ univ
  · rw [sUnion_insert, sUnion_range, compl_union_self]

/-- For a map `T` with no periodic point and a finite measure `μ ≠ 0`, the acceptance `1` is not
below the Metropolis–Hastings acceptance of the kernel `x ↦ ∑ n, δ_{T^[n] x}`: the graph of `T`
carries the flow `μ univ` and its image under the swap carries none. -/
theorem not_ae_le_mhAcceptance_sum_deterministic_iterate [MeasurableEq X] [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (hT : Measurable T) (hinj : ∀ x, Function.Injective fun n : ℕ ↦ T^[n] x) :
    ¬ (fun _ ↦ 1) ≤ᵐ[μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)]
      Function.uncurry (μ.mhAcceptance
        (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n))) := by
  intro h
  have := sigmaFinite_compProd_sum_deterministic_iterate (μ := μ) hT hinj
  have hG : MeasurableSet {p : X × X | p.2 = T^[1] p.1} :=
    measurableSet_eq_fun measurable_snd ((hT.iterate 1).comp measurable_fst)
  have h1 : (μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)).withDensity
      (Function.uncurry (μ.mhAcceptance
        (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)))) =
      μ ⊗ₘ Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n) :=
    (MeasureTheory.withDensity_congr_ae (g := 1) (h.mono fun p hp ↦
      le_antisymm (μ.mhAcceptance_le_one _ p.1 p.2) hp)).trans MeasureTheory.withDensity_one
  rw [withDensity_mhAcceptance] at h1
  have h2 := Measure.le_iff'.1 (inf_eq_left.1 h1) {p : X × X | p.2 = T^[1] p.1}
  have h3 : ∀ x, (Kernel.sum fun n : ℕ ↦ Kernel.deterministic T^[n] (hT.iterate n)) x
      (Prod.mk x ⁻¹' (Prod.swap ⁻¹' {p : X × X | p.2 = T^[1] p.1})) = 0 := fun x ↦ by
    rw [sum_deterministic_iterate_apply hT x (measurable_prodMk_left (measurable_swap hG))]
    exact ENNReal.tsum_eq_zero.2 fun n ↦ indicator_of_notMem
      (show T^[n] x ∉ Prod.mk x ⁻¹' (Prod.swap ⁻¹' {p : X × X | p.2 = T^[1] p.1}) from fun h ↦
        (by omega : (0 : ℕ) ≠ 1 + n) (@hinj x 0 (1 + n) ((show x = T^[1] (T^[n] x) from h).trans
          (Function.iterate_add_apply T 1 n x).symm))) _
  rw [compProd_sum_deterministic_iterate_graph hT hinj 1, Measure.map_apply measurable_swap hG,
    Measure.compProd_apply (measurable_swap hG), lintegral_congr h3, lintegral_zero] at h2
  exact hμ (Measure.measure_univ_eq_zero.1 (nonpos_iff_eq_zero.1 h2))

/-- Finiteness of the accepted mass is needed in
`ae_le_mhAcceptance_of_isReversible_acceptReject`: on the circle `ℝ / ℤ` with Lebesgue measure,
for the rotation by an irrational angle `α` and the proposal `Q x = ∑ n, δ_{x + n • α}`, the flow
`π ⊗ₘ Q` is σ-finite, the acceptance `1` has a `π`-reversible accept–reject kernel (every flow
between two sets is `0` or `∞`), and it is not below the Metropolis–Hastings acceptance, which
vanishes on the graph of the rotation. -/
theorem exists_isReversible_acceptReject_not_ae_le_mhAcceptance_lintegral_eq_top :
    ∃ (π : Measure (AddCircle (1 : ℝ))) (Q : Kernel (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)))
      (_ : IsSFiniteKernel Q), IsFiniteMeasure π ∧ SigmaFinite (π ⊗ₘ Q) ∧
        (acceptReject Q fun _ _ ↦ 1).IsReversible π ∧
        ¬ (fun _ ↦ 1) ≤ᵐ[π ⊗ₘ Q] Function.uncurry (π.mhAcceptance Q) := by
  have hα : addOrderOf ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    AddCircle.denseRange_zsmul_iff.1 (AddCircle.denseRange_zsmul_coe_iff.2
      (by simpa using irrational_sqrt_two))
  have hT : Ergodic (· + ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.ergodic_add_right.2 hα
  have hinj : ∀ x : AddCircle (1 : ℝ), Function.Injective
      fun n : ℕ ↦ (· + ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))^[n] x := fun x n m h ↦
    injective_nsmul_iff_not_isOfFinAddOrder.2 (addOrderOf_eq_zero_iff.1 hα)
      (by simpa [add_right_iterate] using h)
  refine ⟨volume, Kernel.sum fun n : ℕ ↦ Kernel.deterministic _ (hT.measurable.iterate n),
    inferInstance, inferInstance, sigmaFinite_compProd_sum_deterministic_iterate hT.measurable hinj,
    ?_, not_ae_le_mhAcceptance_sum_deterministic_iterate (fun h0 ↦ ?_) hT.measurable hinj⟩
  · rw [isReversible_acceptReject_iff, Kernel.withDensity_one']
    exact isReversible_sum_deterministic_iterate hT
  · simpa [h0] using AddCircle.measure_univ (T := (1 : ℝ))

/-- Mechanical check: the counterexample meets every hypothesis of
`ae_le_mhAcceptance_of_isReversible_acceptReject` but `ha_fin`. -/
example : ∃ (π : Measure (AddCircle (1 : ℝ))) (Q : Kernel (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)))
    (_ : IsSFiniteKernel Q), ¬ ∀ᵐ x ∂π, ∫⁻ _, (1 : ℝ≥0∞) ∂Q x ≠ ∞ := by
  obtain ⟨π, Q, hQ, _, hσ, hrev, hn⟩ :=
    exists_isReversible_acceptReject_not_ae_le_mhAcceptance_lintegral_eq_top
  exact ⟨π, Q, hQ, fun hfin ↦ hn (ae_le_mhAcceptance_of_isReversible_acceptReject
    measurable_const hfin (ae_of_all _ fun _ ↦ le_rfl) hrev)⟩

/-- The same data show that σ-finiteness of the first marginal is needed in
`mhAcceptance_withDensity_ae_eq_min_one_div` (with `f = 1`), and that in
`isReversible_iff_map_swap_compProd` it cannot be weakened to σ-finiteness of `π ⊗ₘ κ`, even for
a finite `π`. -/
example : ∃ (μ : Measure (AddCircle (1 : ℝ))) (Q : Kernel (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)))
    (_ : IsSFiniteKernel Q), IsFiniteMeasure μ ∧ Q.IsReversible μ ∧ SigmaFinite (μ ⊗ₘ Q) ∧
      ¬ SigmaFinite (μ ⊗ₘ Q).fst := by
  obtain ⟨μ, Q, hQ, hμ, hσ, hrev, hn⟩ :=
    exists_isReversible_acceptReject_not_ae_le_mhAcceptance_lintegral_eq_top
  rw [isReversible_acceptReject_iff, Kernel.withDensity_one'] at hrev
  refine ⟨μ, Q, hQ, hμ, hrev, hσ, fun _ ↦ hn ?_⟩
  have h := mhAcceptance_withDensity_ae_eq_min_one_div hrev (f := fun _ ↦ 1) measurable_const
    (ae_of_all _ fun _ ↦ ENNReal.one_ne_top)
  rw [show μ.withDensity (fun _ ↦ 1) = μ from MeasureTheory.withDensity_one] at h
  filter_upwards [h] with z hz
  rw [hz]
  simp

end Iterate

end ProbabilityTheory.Kernel
