/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.MaximalErgodic
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# Birkhoff's pointwise ergodic theorem

Let `f` preserve a measure `μ` and let `φ : α → ℝ` be integrable.

* `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp`: if `μ` is σ-finite on the
  σ-algebra `MeasurableSpace.invariants f` of invariant sets (in particular if `μ` is finite), then
  for `μ`-almost every `x` the averages `birkhoffAverage ℝ f φ n x` tend to
  `μ[φ | MeasurableSpace.invariants f] x`.
* `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_zero`, for any measure: if the
  integral of `φ` vanishes on every invariant set of finite measure, the averages tend to `0`
  almost everywhere. The one-sided form is
  `MeasureTheory.MeasurePreserving.ae_eventually_birkhoffAverage_lt`.

When `μ` is not σ-finite on the invariant sets, `μ[φ | MeasurableSpace.invariants f]` is `0` by
definition and the first statement is false: see
`MCMC/ToMathlib/Dynamics/BirkhoffSum/Examples.lean`.

The proof is the one of Yosida and Kakutani. The upper limit of the Birkhoff averages, taken in
`EReal`, is invariant under `f` (`limsup_birkhoffAverage_apply`), so the set where it exceeds
`ε > 0` is an invariant set `D` inside the set where some average exceeds `ε`; the maximal ergodic
lemma on `D` gives `ε * μ D ≤ ∫ x in D, φ x ∂μ`, and `D` has finite measure.

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 25.6 (ergodic
theorem, Birkhoff) and its proof (Yosida and Kakutani), read from an extracted text of the 3rd
edition; there `μ` is a probability measure.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rln "birkhoffAverage" Mathlib` finds
`Dynamics/BirkhoffSum/{Average, NormedSpace, QuasiMeasurePreserving}.lean` and
`Analysis/InnerProductSpace/MeanErgodic.lean`, none with an almost everywhere limit;
`grep -rni "pointwise ergodic" Mathlib` finds nothing. Mathlib's
`tendsto_birkhoffAverage_apply_sub_birkhoffAverage` compares the averages at `x` and `f x` when
`g (f^[n] x) - g x` is bounded; `limsup_birkhoffAverage_apply` has no hypothesis.
-/

@[expose] public section

open Filter MeasureTheory Set MeasurableSpace
open scoped ENNReal Topology

section Limsup

variable {α : Type*} {f : α → α} {g : α → ℝ} {x : α} {a b : ℝ}

theorem frequently_lt_birkhoffAverage_of_frequently_lt_apply (hab : b < a)
    (h : ∃ᶠ n in atTop, a < birkhoffAverage ℝ f g n (f x)) :
    ∃ᶠ n in atTop, b < birkhoffAverage ℝ f g n x := by
  have hev : ∀ᶠ n : ℕ in atTop, b - g x ≤ n * (a - b) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab)).eventually_ge_atTop _
  refine (tendsto_add_atTop_nat 1).frequently
    ((h.and_eventually (hev.and (eventually_gt_atTop 0))).mono ?_)
  rintro n ⟨han, hn, hn0⟩
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [birkhoffAverage, smul_eq_mul, lt_inv_mul_iff₀ hn0'] at han
  show b < birkhoffAverage ℝ f g (n + 1) x
  rw [birkhoffAverage, smul_eq_mul, Nat.cast_add_one, lt_inv_mul_iff₀ (by positivity),
    birkhoffSum_succ_apply']
  nlinarith

theorem frequently_lt_birkhoffAverage_apply_of_frequently_lt (hab : b < a)
    (h : ∃ᶠ n in atTop, a < birkhoffAverage ℝ f g n x) :
    ∃ᶠ n in atTop, b < birkhoffAverage ℝ f g n (f x) := by
  have hev : ∀ᶠ n : ℕ in atTop, g x - a ≤ n * (a - b) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab)).eventually_ge_atTop _
  have h' : ∃ᶠ n in atTop, a < birkhoffAverage ℝ f g (n + 1) x :=
    (frequently_map (m := fun n : ℕ ↦ n + 1) (P := fun n ↦ a < birkhoffAverage ℝ f g n x)).1
      (by rw [map_add_atTop_eq_nat 1]; exact h)
  refine (h'.and_eventually (hev.and (eventually_gt_atTop 0))).mono ?_
  rintro n ⟨han, hn, hn0⟩
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [birkhoffAverage, smul_eq_mul, Nat.cast_add_one, lt_inv_mul_iff₀ (by positivity),
    birkhoffSum_succ_apply'] at han
  rw [birkhoffAverage, smul_eq_mul, lt_inv_mul_iff₀ hn0']
  nlinarith

/-- The upper limit of the Birkhoff averages, in `EReal`, is the same at `x` and at `f x`. -/
theorem limsup_birkhoffAverage_apply (f : α → α) (g : α → ℝ) (x : α) :
    limsup (fun n ↦ ((birkhoffAverage ℝ f g n (f x) : ℝ) : EReal)) atTop =
      limsup (fun n ↦ ((birkhoffAverage ℝ f g n x : ℝ) : EReal)) atTop := by
  refine le_antisymm (EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_)
    (EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_)
  · obtain ⟨a, hza, ha⟩ := EReal.lt_iff_exists_real_btwn.1 hz
    exact le_limsup_of_frequently_le ((frequently_lt_birkhoffAverage_of_frequently_lt_apply
      (EReal.coe_lt_coe_iff.1 hza) ((frequently_lt_of_lt_limsup (h := ha)).mono
        fun n hn ↦ EReal.coe_lt_coe_iff.1 hn)).mono fun n hn ↦ (EReal.coe_lt_coe_iff.2 hn).le)
  · obtain ⟨a, hza, ha⟩ := EReal.lt_iff_exists_real_btwn.1 hz
    exact le_limsup_of_frequently_le ((frequently_lt_birkhoffAverage_apply_of_frequently_lt
      (EReal.coe_lt_coe_iff.1 hza) ((frequently_lt_of_lt_limsup (h := ha)).mono
        fun n hn ↦ EReal.coe_lt_coe_iff.1 hn)).mono fun n hn ↦ (EReal.coe_lt_coe_iff.2 hn).le)

end Limsup

namespace MeasureTheory.MeasurePreserving

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {φ ψ : α → ℝ}

/-- If the integral of a measurable integrable `ψ` is nonpositive on every invariant set of finite
measure, the set where the upper limit of its Birkhoff averages exceeds `ε > 0` is null. -/
theorem measure_lt_limsup_birkhoffAverage_eq_zero (hf : MeasurePreserving f μ μ)
    (hψm : Measurable ψ) (hψ : Integrable ψ μ)
    (h0 : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ → ∫ x in s, ψ x ∂μ ≤ 0) {ε : ℝ}
    (hε : 0 < ε) :
    μ {x | (ε : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ f ψ n x : ℝ) : EReal)) atTop} = 0 := by
  have hD : MeasurableSet[invariants f]
      {x | (ε : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ f ψ n x : ℝ) : EReal)) atTop} :=
    ⟨measurableSet_lt measurable_const (.limsup fun n ↦
      (measurable_birkhoffAverage ℝ hf.measurable hψm n).coe_real_ereal), by
      ext x; simp only [mem_preimage, mem_ofPred_eq, limsup_birkhoffAverage_apply]⟩
  have hsub : {x | (ε : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ f ψ n x : ℝ) : EReal)) atTop} ⊆
      {x | ∃ n, ε < birkhoffAverage ℝ f ψ (n + 1) x} := fun x
      (hx : (ε : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ f ψ n x : ℝ) : EReal)) atTop) ↦ by
    obtain ⟨n, hn, hn0⟩ := ((frequently_lt_of_lt_limsup (h := hx)).and_eventually
      (eventually_gt_atTop 0)).exists
    exact ⟨n - 1, by rw [Nat.sub_add_cancel hn0]; exact EReal.coe_lt_coe_iff.1 hn⟩
  have hfin := (measure_mono hsub).trans_lt (hf.measure_exists_lt_birkhoffAverage_lt_top hψ hε)
  have h := hf.mul_measureReal_inter_le_setIntegral hψ hε.le hD
  rw [inter_eq_left.2 hsub] at h
  have h' := le_of_mul_le_mul_left ((h.trans (h0 _ hD hfin)).trans_eq (mul_zero ε).symm) hε
  exact (measureReal_eq_zero_iff hfin.ne).1 (le_antisymm h' measureReal_nonneg)

/-- For any measure: if the integral of `ψ` is nonpositive on every invariant set of finite
measure, then almost everywhere the Birkhoff averages of `ψ` are eventually below every
`ε > 0`. -/
theorem ae_eventually_birkhoffAverage_lt (hf : MeasurePreserving f μ μ) (hψ : Integrable ψ μ)
    (h0 : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ → ∫ x in s, ψ x ∂μ ≤ 0) :
    ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, birkhoffAverage ℝ f ψ n x < ε := by
  have hae : ψ =ᵐ[μ] hψ.1.mk ψ := hψ.1.ae_eq_mk
  have h0' : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ → ∫ x in s, hψ.1.mk ψ x ∂μ ≤ 0 :=
    fun s hs hμs ↦ (integral_congr_ae (ae_restrict_of_ae hae.symm)).trans_le (h0 s hs hμs)
  have hU : ∀ k : ℕ, ∀ᵐ x ∂μ, ¬ ((1 / ((k : ℝ) + 1) : ℝ) : EReal) <
      limsup (fun n ↦ ((birkhoffAverage ℝ f (hψ.1.mk ψ) n x : ℝ) : EReal)) atTop := fun k ↦
    measure_eq_zero_iff_ae_notMem.1 (hf.measure_lt_limsup_birkhoffAverage_eq_zero
      hψ.1.stronglyMeasurable_mk.measurable (hψ.congr hae) h0' (by positivity))
  have hS : ∀ᵐ x ∂μ, ∀ n, birkhoffAverage ℝ f ψ n x = birkhoffAverage ℝ f (hψ.1.mk ψ) n x :=
    ae_all_iff.2 fun n ↦ hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hae n
  filter_upwards [ae_all_iff.2 hU, hS] with x hx hSx ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  simp only [hSx]
  exact (eventually_lt_of_limsup_lt ((not_lt.1 (hx k)).trans_lt
    (EReal.coe_lt_coe_iff.2 hk))).mono fun n hn ↦ EReal.coe_lt_coe_iff.1 hn

/-- For any measure: if the integral of an integrable `ψ` vanishes on every invariant set of
finite measure, its Birkhoff averages tend to `0` almost everywhere. -/
theorem ae_tendsto_birkhoffAverage_zero (hf : MeasurePreserving f μ μ) (hψ : Integrable ψ μ)
    (h0 : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ → ∫ x in s, ψ x ∂μ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f ψ n x) atTop (𝓝 0) := by
  have h1 := hf.ae_eventually_birkhoffAverage_lt hψ fun s hs hμs ↦ (h0 s hs hμs).le
  have h2 := hf.ae_eventually_birkhoffAverage_lt hψ.neg fun s hs hμs ↦ by
    simp [integral_neg, h0 s hs hμs]
  filter_upwards [h1, h2] with x hx1 hx2
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ hx1 a ha⟩
  refine (hx2 (-a) (neg_pos.2 ha)).mono fun n hn ↦ ?_
  rw [birkhoffAverage_neg_apply] at hn
  exact neg_lt_neg_iff.1 hn

/-- **Birkhoff's pointwise ergodic theorem**: for a map `f` preserving a measure `μ` that is
σ-finite on the invariant sets (for instance a finite measure) and an integrable `φ`, the Birkhoff
averages of `φ` tend almost everywhere to the conditional expectation of `φ` given the invariant
σ-algebra. -/
theorem ae_tendsto_birkhoffAverage_condExp (hf : MeasurePreserving f μ μ)
    [SigmaFinite (μ.trim (invariants_le f))] (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop
      (𝓝 (μ[φ | invariants f] x)) := by
  have hinv : (μ[φ | invariants f]) ∘ f = μ[φ | invariants f] :=
    comp_eq_of_measurable_invariants stronglyMeasurable_condExp.measurable
  have h0 : ∀ s, MeasurableSet[invariants f] s → μ s < ∞ →
      ∫ x in s, (φ - μ[φ | invariants f]) x ∂μ = 0 := fun s hs _ ↦ by
    simp only [Pi.sub_apply]
    rw [integral_sub hφ.integrableOn integrable_condExp.integrableOn,
      setIntegral_condExp (invariants_le f) hφ hs, sub_self]
  filter_upwards [hf.ae_tendsto_birkhoffAverage_zero (hφ.sub integrable_condExp) h0] with x hx
  have h := hx.add_const (μ[φ | invariants f] x)
  rw [zero_add] at h
  refine h.congr' ((eventually_ne_atTop 0).mono fun n hn ↦ ?_)
  rw [birkhoffAverage_sub_apply, birkhoffAverage_apply_of_comp_eq ℝ hinv (Nat.cast_ne_zero.2 hn),
    sub_add_cancel]

end MeasureTheory.MeasurePreserving
