/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Dynamics.BirkhoffSum.MaximalErgodic
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# Birkhoff's pointwise ergodic theorem

Let `f` preserve a measure `μ` and let `φ : α → ℝ` be integrable.

* `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp`: if `μ` is σ-finite on the
  σ-algebra `MeasurableSpace.invariants f` of invariant sets (in particular if `μ` is finite), then
  for `μ`-almost every `x` the averages `birkhoffAverage ℝ f φ n x` tend to
  `μ[φ | MeasurableSpace.invariants f] x`. This holds for `φ` with values in a Banach space.
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

For values in a Banach space the theorem follows from the real case by density: it holds for
`s.indicator fun _ ↦ e`, and the functions for which it holds are closed in `L¹` by the maximal
ergodic inequality and the weak `L¹` bound for the conditional expectation
(`MeasureTheory.ofReal_mul_measure_le_norm_condExp_le`).

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Theorem 25.6 (ergodic
theorem, Birkhoff) and its proof (Yosida and Kakutani), read from an extracted text of the 3rd
edition; there `μ` is a probability measure and `φ` is real. The extension to a Banach space by
density is the standard argument; no source was read for it.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rln "birkhoffAverage" Mathlib` finds
`Dynamics/BirkhoffSum/{Average, NormedSpace, QuasiMeasurePreserving}.lean` and
`Analysis/InnerProductSpace/MeanErgodic.lean`, none with an almost everywhere limit;
`grep -rni "pointwise ergodic" Mathlib` finds nothing. Mathlib's
`tendsto_birkhoffAverage_apply_sub_birkhoffAverage` compares the averages at `x` and `f x` when
`g (f^[n] x) - g x` is bounded; `limsup_birkhoffAverage_apply` has no hypothesis.
Outside Mathlib: the repository `or4nge19/GibbsMeasure` has the maximal inequality and the
pointwise theorem for actions of abelian groups along regular sequences of finite sets
(`GibbsMeasure/Mathlib/Dynamics/Ergodic/{MaximalInequality, Pointwise}.lean`, a covering argument),
which does not cover a single map that is not invertible; nothing is ported from it. A web search
found two public Lean 4 projects on Birkhoff's theorem (`mseri/BET` and
`lua-vr/BirkhoffErgodicThm` on Reservoir); they were not read and nothing is taken from them.
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
      (hx : (ε : EReal) < limsup (fun n ↦ ((birkhoffAverage ℝ f ψ n x : ℝ) : EReal)) atTop) ↦
    ((frequently_lt_of_lt_limsup (h := hx)).and_eventually (eventually_gt_atTop 0)).exists.elim
      fun n hn ↦ ⟨n - 1, by rw [Nat.sub_add_cancel hn.2]; exact EReal.coe_lt_coe_iff.1 hn.1⟩
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

/-- Birkhoff's pointwise ergodic theorem for a real function; the statement for functions with
values in a Banach space is `MeasureTheory.MeasurePreserving.ae_tendsto_birkhoffAverage_condExp`. -/
theorem ae_tendsto_birkhoffAverage_condExp_real (hf : MeasurePreserving f μ μ)
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

theorem eventually_norm_sub_lt_of_tendsto_of_norm_sub_le {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {a b : ι → E} {L L' : E} {c : ℝ} (hb : Tendsto b l (𝓝 L'))
    (hab : ∀ n, ‖a n - b n‖ ≤ c) (hL : ‖L - L'‖ < c) : ∀ᶠ n in l, ‖a n - L‖ < 3 * c := by
  filter_upwards [hb.eventually (Metric.ball_mem_nhds L' ((norm_nonneg _).trans_lt hL))] with n hn
  have h1 : a n - L = a n - b n + (b n - L') - (L - L') := by abel
  have h2 := norm_sub_le (a n - b n + (b n - L')) (L - L')
  have h3 := norm_add_le (a n - b n) (b n - L')
  have h4 : ‖b n - L'‖ < c := mem_ball_iff_norm.1 hn
  rw [h1]
  linarith [hab n]

/-- The weak `L¹` bound for the conditional expectation. -/
theorem MeasureTheory.ofReal_mul_measure_le_norm_condExp_le {α E : Type*} {m m0 : MeasurableSpace α}
    {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {g : α → E}
    (hg : Integrable g μ) (c : ℝ) :
    ENNReal.ofReal c * μ {x | c ≤ ‖μ[g | m] x‖} ≤ ∫⁻ x, ‖g x‖ₑ ∂μ :=
  calc ENNReal.ofReal c * μ {x | c ≤ ‖μ[g | m] x‖}
      ≤ ENNReal.ofReal c * μ {x | ENNReal.ofReal c ≤ ‖μ[g | m] x‖ₑ} :=
        mul_le_mul' le_rfl (measure_mono fun x (hx : c ≤ ‖μ[g | m] x‖) ↦
          (ENNReal.ofReal_le_ofReal hx).trans_eq (ofReal_norm _))
    _ ≤ ∫⁻ x, ‖μ[g | m] x‖ₑ ∂μ := mul_meas_ge_le_lintegral₀ integrable_condExp.1.enorm _
    _ = eLpNorm (μ[g | m]) 1 μ := (eLpNorm_one_eq_lintegral_enorm integrable_condExp.1).symm
    _ ≤ eLpNorm g 1 μ := eLpNorm_condExp_le_eLpNorm _ le_rfl
    _ = ∫⁻ x, ‖g x‖ₑ ∂μ := eLpNorm_one_eq_lintegral_enorm hg.1

namespace MeasureTheory.MeasurePreserving

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {φ ψ : α → E}

/-- If the Birkhoff averages of `ψ` tend almost everywhere to its conditional expectation, the set
where those of `φ` are frequently `3 * c` away from the conditional expectation of `φ` has measure
at most `2 * c⁻¹ * ∫⁻ ‖φ - ψ‖ₑ`. -/
theorem ofReal_mul_measure_frequently_lt_norm_birkhoffAverage_sub_condExp_le
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ) (hψ : Integrable ψ μ)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f ψ n x) atTop
      (𝓝 (μ[ψ | invariants f] x))) (c : ℝ) :
    ENNReal.ofReal c * μ {x | ∃ᶠ n in atTop,
        3 * c < ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖} ≤
      2 * ∫⁻ x, ‖φ x - ψ x‖ₑ ∂μ := by
  have hsub : ∀ᵐ x ∂μ, x ∈ {x | ∃ᶠ n in atTop,
        3 * c < ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖} →
      x ∈ {x | ∃ n, c < ‖birkhoffAverage ℝ f (φ - ψ) n x‖} ∪
        {x | c ≤ ‖μ[φ - ψ | invariants f] x‖} := by
    filter_upwards [h, condExp_sub hφ hψ (invariants f)] with x hx hsx hfreq
    by_contra hcon
    rw [mem_union, not_or] at hcon
    refine hfreq ((eventually_norm_sub_lt_of_tendsto_of_norm_sub_le hx (fun n ↦ ?_)
      ((congrArg norm hsx).symm.trans_lt (not_le.1 hcon.2))).mono fun n hn ↦ not_lt.2 hn.le)
    rw [← birkhoffAverage_sub_apply]
    exact not_lt.1 fun hlt ↦ hcon.1 ⟨n, hlt⟩
  calc ENNReal.ofReal c * μ {x | ∃ᶠ n in atTop,
        3 * c < ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖}
      ≤ ENNReal.ofReal c * (μ {x | ∃ n, c < ‖birkhoffAverage ℝ f (φ - ψ) n x‖} +
          μ {x | c ≤ ‖μ[φ - ψ | invariants f] x‖}) :=
        mul_le_mul' le_rfl ((measure_mono_ae hsub).trans (measure_union_le _ _))
    _ = ENNReal.ofReal c * μ {x | ∃ n, c < ‖birkhoffAverage ℝ f (φ - ψ) n x‖} +
          ENNReal.ofReal c * μ {x | c ≤ ‖μ[φ - ψ | invariants f] x‖} := mul_add _ _ _
    _ ≤ ∫⁻ x, ‖(φ - ψ) x‖ₑ ∂μ + ∫⁻ x, ‖(φ - ψ) x‖ₑ ∂μ :=
        add_le_add (hf.ofReal_mul_measure_exists_lt_norm_birkhoffAverage_le ℝ (hφ.sub hψ).1 c)
          (ofReal_mul_measure_le_norm_condExp_le (hφ.sub hψ) c)
    _ = 2 * ∫⁻ x, ‖φ x - ψ x‖ₑ ∂μ := (two_mul _).symm

theorem measure_frequently_lt_norm_birkhoffAverage_sub_condExp_eq_zero
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ψ : α → E, Integrable ψ μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f ψ n x) atTop
        (𝓝 (μ[ψ | invariants f] x))) ∧ ∫⁻ x, ‖φ x - ψ x‖ₑ ∂μ < ε) {c : ℝ} (hc : 0 < c) :
    μ {x | ∃ᶠ n in atTop,
      3 * c < ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖} = 0 := by
  refine (mul_eq_zero.1 (le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
    zero_le)).resolve_left (ENNReal.ofReal_pos.2 hc).ne'
  obtain ⟨ψ, hψ, hP, hlt⟩ := happrox (ε / 2) (ENNReal.half_pos (ENNReal.coe_ne_zero.2 hε.ne'))
  calc ENNReal.ofReal c * μ {x | ∃ᶠ n in atTop,
        3 * c < ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖}
      ≤ 2 * ∫⁻ x, ‖φ x - ψ x‖ₑ ∂μ :=
        hf.ofReal_mul_measure_frequently_lt_norm_birkhoffAverage_sub_condExp_le hφ hψ hP c
    _ ≤ 2 * (ε / 2) := mul_le_mul' le_rfl hlt.le
    _ = 0 + ε := by rw [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top, zero_add]

/-- The integrable functions whose Birkhoff averages tend almost everywhere to the conditional
expectation given the invariant σ-algebra are closed under limits in `L¹`. -/
theorem ae_tendsto_birkhoffAverage_condExp_of_forall_exists_lintegral_lt
    (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ψ : α → E, Integrable ψ μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f ψ n x) atTop
        (𝓝 (μ[ψ | invariants f] x))) ∧ ∫⁻ x, ‖φ x - ψ x‖ₑ ∂μ < ε) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop
      (𝓝 (μ[φ | invariants f] x)) := by
  have hnull : ∀ k : ℕ, ∀ᵐ x ∂μ, ¬ ∃ᶠ n in atTop, 3 * (1 / ((k : ℝ) + 1)) <
      ‖birkhoffAverage ℝ f φ n x - μ[φ | invariants f] x‖ := fun k ↦
    measure_eq_zero_iff_ae_notMem.1
      (hf.measure_frequently_lt_norm_birkhoffAverage_sub_condExp_eq_zero hφ happrox
        (by positivity))
  filter_upwards [ae_all_iff.2 hnull] with x hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε three_pos)
  refine (not_frequently.1 (hx k)).mono fun n hn ↦ ?_
  rw [dist_eq_norm]
  linarith [not_lt.1 hn]

/-- **Birkhoff's pointwise ergodic theorem**: for a map `f` preserving a measure `μ` that is
σ-finite on the invariant sets (for instance a finite measure) and an integrable `φ` with values
in a Banach space, the Birkhoff averages of `φ` tend almost everywhere to the conditional
expectation of `φ` given the invariant σ-algebra. -/
theorem ae_tendsto_birkhoffAverage_condExp (hf : MeasurePreserving f μ μ)
    [SigmaFinite (μ.trim (invariants_le f))] (hφ : Integrable φ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop
      (𝓝 (μ[φ | invariants f] x)) := by
  refine Integrable.induction (P := fun φ : α → E ↦ ∀ᵐ x ∂μ,
    Tendsto (fun n ↦ birkhoffAverage ℝ f φ n x) atTop (𝓝 (μ[φ | invariants f] x)))
    (fun e s hs hμs ↦ ?_) (fun φ₁ φ₂ _ h₁ h₂ hP₁ hP₂ ↦ ?_) ?_ (fun φ₁ φ₂ h12 _ hP ↦ ?_) hφ
  · have hint : Integrable (s.indicator (1 : α → ℝ)) μ :=
      (integrable_indicator_iff hs).2 (integrableOn_const hμs.ne)
    have heq : (s.indicator fun _ ↦ e) =
        ContinuousLinearMap.toSpanSingleton ℝ e ∘ s.indicator (1 : α → ℝ) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    filter_upwards [hf.ae_tendsto_birkhoffAverage_condExp_real hint,
      (ContinuousLinearMap.toSpanSingleton ℝ e).comp_condExp_comm hint (m := invariants f)]
      with x hx hT
    rw [heq, ← hT]
    exact (((ContinuousLinearMap.toSpanSingleton ℝ e).continuous.tendsto _).comp hx).congr
      fun n ↦ map_birkhoffAverage ℝ ℝ (ContinuousLinearMap.toSpanSingleton ℝ e) f _ n x
  · filter_upwards [hP₁, hP₂, condExp_add h₁ h₂ (invariants f)] with x h1 h2 hadd
    rw [hadd]
    exact (h1.add h2).congr fun n ↦ (birkhoffAverage_add_apply ℝ n x).symm
  · refine isClosed_of_closure_subset fun g hg ↦
      hf.ae_tendsto_birkhoffAverage_condExp_of_forall_exists_lintegral_lt (L1.integrable_coeFn g)
        fun ε hε ↦ ?_
    obtain ⟨g', hg', hlt⟩ := EMetric.mem_closure_iff.1 hg ε hε
    exact ⟨g', L1.integrable_coeFn g', hg', (lintegral_congr fun x ↦
      (edist_eq_enorm_sub _ _).symm).trans_lt ((L1.edist_def g g').symm.trans_lt hlt)⟩
  · filter_upwards [hP, condExp_congr_ae h12 (m := invariants f), ae_all_iff.2 fun n ↦
      hf.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ h12 n] with x hx hc hn
    rw [← hc]
    exact hx.congr hn

end MeasureTheory.MeasurePreserving
