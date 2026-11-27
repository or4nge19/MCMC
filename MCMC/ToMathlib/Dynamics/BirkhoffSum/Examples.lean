/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.LpConvergence
public import MCMC.ToMathlib.Dynamics.BirkhoffSum.Stationary
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Dynamics.Ergodic.AddCircle
public import Mathlib.Dynamics.Ergodic.AddCircleAdd
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The ergodic theorems: instances and the hypotheses that cannot be dropped

Instances in which every hypothesis holds: rotations of a circle (any rotation for the maximal
lemma and for the limit as a conditional expectation; a rotation of infinite order for the limit
as a mean), the doubling map of a circle, and the shift of a space of sequences with a
stationary law.

Hypotheses that cannot be dropped:

* measure preservation, in the maximal ergodic lemma and in
  `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_zero`: on two points with the
  counting measure, the map sending both points to one of them;
* integrability, in `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp`: the
  identity map of `(0, 1]` and `x ↦ x⁻¹` (Mathlib's conditional expectation of a function that is
  not integrable is `0`);
* σ-finiteness on the invariant sets, in the same theorem: the identity map of two points, one of
  mass `1` and one of mass `∞` (Mathlib's conditional expectation is then `0`);
* `0 ≤ c` in `MeasureTheory.MeasurePreserving.ofReal_mul_measure_add_setLIntegral_le`: for the
  identity map of a point of mass `1`, `g = -1` and `c = -2` the left side is `1` and the right
  side is `0`.
-/

@[expose] public section

open Filter MeasureTheory Set MeasurableSpace
open scoped ENNReal Topology

section Instances

variable {p : ℝ} [Fact (0 < p)] {φ : AddCircle p → ℝ}

/-- Hopf's maximal ergodic lemma for a rotation of a circle. -/
example (a : AddCircle p) (hφ : Integrable φ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum (a + ·) φ (n + 1) x}, φ x :=
  (measurePreserving_add_left volume a).setIntegral_exists_birkhoffSum_pos_nonneg hφ

/-- Birkhoff's theorem for a rotation of a circle. -/
example (a : AddCircle p) (hφ : Integrable φ) :
    ∀ᵐ x, Tendsto (fun n ↦ birkhoffAverage ℝ (a + ·) φ n x) atTop
      (𝓝 ((volume : Measure (AddCircle p))[φ | invariants (a + ·)] x)) :=
  (measurePreserving_add_left volume a).ae_tendsto_birkhoffAverage_condExp hφ

/-- Birkhoff's theorem for a rotation of infinite order: the limit is the mean. -/
example {a : AddCircle p} (ha : addOrderOf a = 0) (hφ : Integrable φ) :
    ∀ᵐ x, Tendsto (fun n ↦ birkhoffAverage ℝ (a + ·) φ n x) atTop (𝓝 (⨍ x, φ x)) :=
  (AddCircle.ergodic_add_left.2 ha).ae_tendsto_birkhoffAverage_average hφ

/-- Birkhoff's theorem for the doubling map of a circle. -/
example (hφ : Integrable φ) :
    ∀ᵐ x, Tendsto (fun n ↦ birkhoffAverage ℝ (fun y : AddCircle p ↦ 2 • y) φ n x) atTop
      (𝓝 (⨍ x, φ x)) :=
  (AddCircle.ergodic_nsmul one_lt_two).ae_tendsto_birkhoffAverage_average hφ

/-- Convergence in `Lᵖ` for the doubling map of a circle. -/
example {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ∞) (hφ : MemLp φ q) :
    Tendsto (fun n ↦ eLpNorm (birkhoffAverage ℝ (fun y : AddCircle p ↦ 2 • y) φ n -
      (volume : Measure (AddCircle p))[φ | invariants fun y : AddCircle p ↦ 2 • y]) q) atTop
      (𝓝 0) :=
  (AddCircle.ergodic_nsmul
    one_lt_two).toMeasurePreserving.tendsto_eLpNorm_birkhoffAverage_sub_condExp hq hq' hφ

/-- The law of large numbers for a functional of a stationary sequence: if the shift of the space
of sequences preserves a finite measure `P`, the averages of an integrable `Φ` along the shifted
paths converge `P`-almost everywhere. -/
example {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {P : Measure (ℕ → X)} [IsFiniteMeasure P] {Φ : (ℕ → X) → E}
    (hP : MeasurePreserving (fun ω : ℕ → X ↦ fun n ↦ ω (n + 1)) P P) (hΦ : Integrable Φ P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ birkhoffAverage ℝ (fun ω : ℕ → X ↦ fun n ↦ ω (n + 1)) Φ n ω) atTop
      (𝓝 (P[Φ | invariants fun ω : ℕ → X ↦ fun n ↦ ω (n + 1)] ω)) :=
  hP.ae_tendsto_birkhoffAverage_condExp hΦ

end Instances

section MeasurePreservation

/-- The map of two points sending both to `false` does not preserve the counting measure, and the
maximal ergodic lemma fails for it. -/
example : ∃ (f : Bool → Bool) (g : Bool → ℝ), Measurable f ∧ Integrable g Measure.count ∧
    ∫ x in {x | ∃ n, 0 < birkhoffSum f g (n + 1) x}, g x ∂Measure.count < 0 := by
  refine ⟨fun _ ↦ false, fun b ↦ if b then -3 else 1, measurable_const, .of_finite, ?_⟩
  have hk : ∀ k, (fun _ : Bool ↦ false)^[k + 1] true = false := fun k ↦ by
    rw [Function.iterate_succ_apply']
  have hA : {x : Bool | ∃ n, 0 < birkhoffSum (fun _ ↦ false)
      (fun b : Bool ↦ if b then (-3 : ℝ) else 1) (n + 1) x} = univ := by
    ext x
    cases x
    · simpa using ⟨0, by simp⟩
    · simpa using ⟨4, by norm_num [birkhoffSum, Finset.sum_range_succ', hk]⟩
  rw [hA, Measure.restrict_univ, integral_fintype Integrable.of_finite]
  norm_num [Fintype.sum_bool]

/-- For the same map, a function whose integral vanishes on the invariant sets (`∅` and the whole
space) has Birkhoff averages that do not tend to `0`. -/
example : ∃ (f : Bool → Bool) (ψ : Bool → ℝ), Measurable f ∧ Integrable ψ Measure.count ∧
    (∀ s, MeasurableSet[invariants f] s → Measure.count s < ∞ →
      ∫ x in s, ψ x ∂Measure.count = 0) ∧
    ¬ ∀ᵐ x ∂Measure.count, Tendsto (fun n ↦ birkhoffAverage ℝ f ψ n x) atTop (𝓝 0) := by
  refine ⟨fun _ ↦ false, fun b ↦ if b then 1 else -1, measurable_const, .of_finite,
    fun s hs _ ↦ ?_, fun h ↦ ?_⟩
  · by_cases hF : false ∈ s
    · have hs' : s = univ := by rw [← hs.2]; ext x; simp [hF]
      rw [hs', Measure.restrict_univ, integral_fintype Integrable.of_finite]
      norm_num [Fintype.sum_bool]
    · have hs' : s = ∅ := by rw [← hs.2]; ext x; simp [hF]
      rw [hs', Measure.restrict_empty, integral_zero_measure]
  · have h1 := tendsto_nhds_unique (Measure.ae_count_iff.1 h false)
      (tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun n hn ↦
        ((Function.IsFixedPt.birkhoffAverage_eq ℝ (f := fun _ : Bool ↦ false) (x := false) rfl
          (fun b : Bool ↦ if b then (1 : ℝ) else -1) (Nat.cast_ne_zero.2 hn)).symm)))
    norm_num at h1

end MeasurePreservation

section Integrability

/-- For the identity map of `(0, 1]` and the function `x ↦ x⁻¹`, which is not integrable, the
Birkhoff averages do not tend to the conditional expectation. -/
example : ¬ ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
    Tendsto (fun n ↦ birkhoffAverage ℝ id (fun x : ℝ ↦ x⁻¹) n x) atTop
      (𝓝 ((volume.restrict (Ioc (0 : ℝ) 1))[fun x : ℝ ↦ x⁻¹ | invariants id] x)) := by
  have hni : ¬ Integrable (fun x : ℝ ↦ x⁻¹) (volume.restrict (Ioc (0 : ℝ) 1)) := fun h ↦
    (intervalIntegrable_inv_iff.1 ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      h)).elim zero_ne_one fun h0 ↦ h0 left_mem_uIcc
  intro h
  rw [condExp_of_not_integrable hni] at h
  have h2 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x⁻¹ = 0 := h.mono fun x hx ↦
    tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun n hn ↦
      (birkhoffAverage_apply_of_comp_eq ℝ (f := id) (g := fun x : ℝ ↦ x⁻¹) rfl
        (Nat.cast_ne_zero.2 hn) x).symm)) hx
  have h4 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), False := by
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioc] with x hx hx'
    exact hx'.1.ne' (inv_eq_zero.1 hx)
  have h5 := Measure.restrict_eq_zero.1 (ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h4))
  simp at h5

end Integrability

section SigmaFinite

/-- For the identity map of two points of masses `1` and `∞`, the measure is not σ-finite on the
invariant sets, Mathlib's conditional expectation is `0`, and the Birkhoff averages of the
indicator of the point of mass `1` do not tend to it. -/
example : ∃ (μ : Measure Bool) (φ : Bool → ℝ), MeasurePreserving id μ μ ∧ Integrable φ μ ∧
    ¬ ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ id φ n x) atTop
      (𝓝 (μ[φ | invariants id] x)) := by
  set μ : Measure Bool := Measure.dirac true + (∞ : ℝ≥0∞) • Measure.dirac false with hμ
  have hT : μ {true} = 1 := by simp [hμ]
  have hF : μ {false} = ∞ := by simp [hμ]
  have hns : ¬ SigmaFinite (μ.trim (invariants_le id)) := fun _ ↦
    (mem_iUnion.1 ((iUnion_spanningSets (μ.trim (invariants_le id))).symm ▸
      mem_univ false)).elim fun i hi ↦ absurd hF
        (((measure_mono (singleton_subset_iff.2 hi)).trans (le_trim _)).trans_lt
          (measure_spanningSets_lt_top (μ.trim (invariants_le id)) i)).ne
  refine ⟨μ, ({true} : Set Bool).indicator 1, MeasurePreserving.id μ,
    (integrable_indicator_iff (measurableSet_singleton true)).2
      (integrableOn_const (hs := by simp [hT]) (hC := by simp)), fun h ↦ ?_⟩
  rw [condExp_of_not_sigmaFinite (invariants_le id) hns] at h
  have hlim : Tendsto (fun n ↦ birkhoffAverage ℝ id (({true} : Set Bool).indicator 1) n true)
      atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun n hn ↦
      ((birkhoffAverage_apply_of_comp_eq ℝ (f := id)
        (g := ({true} : Set Bool).indicator (1 : Bool → ℝ)) rfl (Nat.cast_ne_zero.2 hn)
        true).trans (by simp)).symm)
  have hsub : ({true} : Set Bool) ⊆ {x | ¬ Tendsto (fun n ↦ birkhoffAverage ℝ id
      (({true} : Set Bool).indicator 1) n x) atTop (𝓝 ((0 : Bool → ℝ) x))} := fun x hx hx' ↦ by
    rw [mem_singleton_iff.1 hx] at hx'
    exact one_ne_zero (tendsto_nhds_unique hlim hx')
  have h1 : μ {true} = 0 := measure_mono_null hsub (ae_iff.1 h)
  simp [hT] at h1

end SigmaFinite

section Level

/-- The maximal ergodic lemma at a level `c` fails for `c = -2`: the identity map of a point of
mass `1` and the function `-1`. -/
example : ¬ (ENNReal.ofReal (-2) * Measure.dirac ()
      {x | ∃ n, (-2 : ℝ) < birkhoffAverage ℝ id (fun _ : Unit ↦ (-1 : ℝ)) (n + 1) x} +
      ∫⁻ _ in {x | ∃ n, (-2 : ℝ) < birkhoffAverage ℝ id (fun _ : Unit ↦ (-1 : ℝ)) (n + 1) x},
        ENNReal.ofReal (-(-1 : ℝ)) ∂Measure.dirac () ≤
    ∫⁻ _ in {x | ∃ n, (-2 : ℝ) < birkhoffAverage ℝ id (fun _ : Unit ↦ (-1 : ℝ)) (n + 1) x},
      ENNReal.ofReal (-1 : ℝ) ∂Measure.dirac ()) := by
  have hA : {x : Unit | ∃ n, (-2 : ℝ) <
      birkhoffAverage ℝ id (fun _ : Unit ↦ (-1 : ℝ)) (n + 1) x} = univ :=
    eq_univ_of_forall fun x ↦ ⟨0, by norm_num [birkhoffAverage_one_apply]⟩
  rw [hA]
  simp only [Measure.restrict_univ, lintegral_const, measure_univ, mul_one, neg_neg,
    ENNReal.ofReal_one, ENNReal.ofReal_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num),
    ENNReal.ofReal_of_nonpos (show (-2 : ℝ) ≤ 0 by norm_num), zero_add, not_le]
  exact zero_lt_one

end Level
