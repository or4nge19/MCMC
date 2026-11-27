/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Limits of finite measures, uniformly on measurable sets

Finite measures on a measurable space are complete for uniform convergence on measurable sets
(the setwise reading of the total variation distance): if `(μ n).real s` is uniformly Cauchy over
the measurable sets `s`, it converges uniformly to `ν.real s` for a finite measure `ν`
(`MeasureTheory.Measure.exists_tendstoUniformlyOn_of_uniformCauchySeqOn`). The limit is countably
additive because the convergence is uniform (`MeasureTheory.Measure.hasSum_of_tendstoUniformlyOn`).

Along such a sequence the integral of every bounded measurable function converges
(`MeasureTheory.tendsto_lintegral_of_tendstoUniformlyOn`), by the layer-cake bound: if
`μ s ≤ ν s + ε` on measurable sets, then `∫⁻ f ∂μ ≤ ∫⁻ f ∂ν + c ε` for measurable `f ≤ c`
(`MeasureTheory.lintegral_le_lintegral_add_mul_of_forall_le_add`).

No topology on the space is used: this is the step that builds the invariant law of a Markov
kernel on a general measurable space as a limit of its iterates
(`MCMC/ToMathlib/Probability/Kernel/Contraction.lean`).

Searched on 2026-11-24 (Mathlib `d13f23b`): `grep -rln "TendstoUniformly\|UniformCauchySeqOn\|
CauchySeq" MeasureTheory/Measure MeasureTheory/VectorMeasure` finds no file; `grep -rln
"setwise"` finds only `Topology/CantorBendixson.lean`; `grep -rn "Nikodym\|VitaliHahnSaks"` finds
nothing. Mathlib's total variation (`SignedMeasure.totalVariation`, equal to
`VectorMeasure.variation` by `SignedMeasure.totalVariation_eq_variation`) has no completeness
statement; integrals against a signed measure (`∫ᵛ`, `MeasureTheory/VectorMeasure/Integral.lean`)
are bounded by the variation (`VectorMeasure.norm_integral_le_integral_norm`).
-/

@[expose] public section

open Filter Function Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

namespace Measure

/-- A limit of finite measures, uniformly on measurable sets, is countably additive. -/
theorem hasSum_of_tendstoUniformlyOn {μ : ℕ → Measure α} [∀ n, IsFiniteMeasure (μ n)]
    {m : Set α → ℝ}
    (hm : TendstoUniformlyOn (fun n s ↦ (μ n).real s) m atTop {s | MeasurableSet s})
    {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i ↦ m (f i)) (m (⋃ i, f i)) := by
  have hA : ∀ N, MeasurableSet (⋃ i ∈ Finset.range N, f i) :=
    fun N ↦ Finset.measurableSet_biUnion _ fun i _ ↦ hf i
  have hfin : ∀ n N, (μ n).real (⋃ i ∈ Finset.range N, f i) =
      ∑ i ∈ Finset.range N, (μ n).real (f i) :=
    fun n N ↦ measureReal_biUnion_finset (fun i _ j _ hij ↦ hd hij) fun i _ ↦ hf i
  have hpart : ∀ N, ∑ i ∈ Finset.range N, m (f i) = m (⋃ i ∈ Finset.range N, f i) := fun N ↦
    tendsto_nhds_unique (tendsto_finsetSum _ fun i _ ↦ hm.tendsto_at (hf i))
      (by simpa only [hfin] using hm.tendsto_at (hA N))
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ ge_of_tendsto' (hm.tendsto_at (hf i))
    fun n ↦ measureReal_nonneg) _).2 ?_
  simp_rw [hpart]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hm (ε / 3) (by positivity)).exists
  have hU : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, (μ n).real (f i)) atTop
      (𝓝 ((μ n).real (⋃ i, f i))) := by
    rw [measureReal_def, measure_iUnion hd hf]
    refine ((ENNReal.tendsto_toReal ?_).comp (ENNReal.tendsto_nat_tsum _)).congr fun N ↦ ?_
    · rw [← measure_iUnion hd hf]
      exact measure_ne_top _ _
    · rw [Function.comp_apply, ENNReal.toReal_sum fun i _ ↦ measure_ne_top _ _]
      rfl
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hU (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have h₃ := hN₀ N hN
  rw [← hfin] at h₃
  calc dist (m (⋃ i ∈ Finset.range N, f i)) (m (⋃ i, f i))
      ≤ dist (m (⋃ i ∈ Finset.range N, f i)) ((μ n).real (⋃ i ∈ Finset.range N, f i)) +
          dist ((μ n).real (⋃ i ∈ Finset.range N, f i)) ((μ n).real (⋃ i, f i)) +
          dist ((μ n).real (⋃ i, f i)) (m (⋃ i, f i)) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add (add_lt_add (hn _ (hA N)) h₃) (by rw [dist_comm]; exact hn _ (.iUnion hf))
    _ = ε := by ring

/-- A limit of finite measures, uniformly on measurable sets, is a finite measure. -/
theorem exists_measureReal_eq_of_tendstoUniformlyOn {μ : ℕ → Measure α}
    [∀ n, IsFiniteMeasure (μ n)] {m : Set α → ℝ}
    (hm : TendstoUniformlyOn (fun n s ↦ (μ n).real s) m atTop {s | MeasurableSet s}) :
    ∃ ν : Measure α, IsFiniteMeasure ν ∧ ∀ s, MeasurableSet s → ν.real s = m s := by
  have h0 : ∀ s, MeasurableSet s → 0 ≤ m s := fun s hs ↦
    ge_of_tendsto' (hm.tendsto_at hs) fun n ↦ measureReal_nonneg
  have he : m ∅ = 0 :=
    tendsto_nhds_unique (hm.tendsto_at MeasurableSet.empty) (by simp)
  refine ⟨ofMeasurable (fun s _ ↦ ENNReal.ofReal (m s)) (by simp [he]) fun f hf hd ↦ ?_, ⟨?_⟩,
    fun s hs ↦ ?_⟩
  · rw [← (hasSum_of_tendstoUniformlyOn hm hf hd).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i ↦ h0 _ (hf i))
      (hasSum_of_tendstoUniformlyOn hm hf hd).summable
  · rw [ofMeasurable_apply _ MeasurableSet.univ]
    exact ENNReal.ofReal_lt_top
  · rw [measureReal_def, ofMeasurable_apply _ hs, ENNReal.toReal_ofReal (h0 s hs)]

/-- **Completeness of finite measures** for uniform convergence on measurable sets: a sequence
of finite measures that is uniformly Cauchy on measurable sets converges uniformly on them to a
finite measure. -/
theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn {μ : ℕ → Measure α}
    [∀ n, IsFiniteMeasure (μ n)]
    (h : UniformCauchySeqOn (fun n s ↦ (μ n).real s) atTop {s | MeasurableSet s}) :
    ∃ ν : Measure α, IsFiniteMeasure ν ∧
      TendstoUniformlyOn (fun n s ↦ (μ n).real s) (fun s ↦ ν.real s) atTop
        {s | MeasurableSet s} := by
  have hm := h.tendstoUniformlyOn_of_tendsto (f := fun s ↦ limUnder atTop fun n ↦ (μ n).real s)
    fun s hs ↦ (h.cauchySeq hs).tendsto_limUnder
  obtain ⟨ν, hν, hνm⟩ := exists_measureReal_eq_of_tendstoUniformlyOn hm
  exact ⟨ν, hν, hm.congr_right fun s hs ↦ (hνm s hs).symm⟩

end Measure

/-- **Layer cake bound**: if `μ s ≤ ν s + ε` on every measurable set, then
`∫⁻ f ∂μ ≤ ∫⁻ f ∂ν + c ε` for every measurable `f ≤ c`. -/
theorem lintegral_le_lintegral_add_mul_of_forall_le_add {μ ν : Measure α} {ε : ℝ≥0∞}
    (h : ∀ s, MeasurableSet s → μ s ≤ ν s + ε) {f : α → ℝ≥0∞} (hf : Measurable f) {c : ℝ≥0}
    (hfc : ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν + c * ε := by
  have hfr : ∀ x, ENNReal.ofReal (f x).toReal = f x := fun x ↦
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hfc x))
  have hg : Measurable fun x ↦ (f x).toReal := hf.ennreal_toReal
  have hempty : ∀ t : ℝ, (c : ℝ) < t → {a | t < (f a).toReal} = ∅ := fun t ht ↦ by
    ext a
    simpa using (ENNReal.toReal_le_coe_of_le_coe (hfc a)).trans ht.le
  have hpt : ∀ t : ℝ, μ {a | t < (f a).toReal} ≤
      ν {a | t < (f a).toReal} + (Iic (c : ℝ)).indicator (fun _ ↦ ε) t := by
    intro t
    by_cases ht : t ≤ c
    · rw [indicator_of_mem (mem_Iic.2 ht)]
      exact h _ (measurableSet_lt measurable_const hg)
    · simp [hempty t (not_le.1 ht)]
  have h0 : ∀ ρ : Measure α, 0 ≤ᵐ[ρ] fun x ↦ (f x).toReal :=
    fun ρ ↦ ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg
  calc ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi 0, μ {a | t < (f a).toReal} := by
        rw [← lintegral_eq_lintegral_meas_lt μ (h0 μ) hg.aemeasurable, lintegral_congr hfr]
    _ ≤ ∫⁻ t in Ioi 0, (ν {a | t < (f a).toReal} + (Iic (c : ℝ)).indicator (fun _ ↦ ε) t) :=
        lintegral_mono hpt
    _ = ∫⁻ x, f x ∂ν + c * ε := by
        rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Iic),
          ← lintegral_eq_lintegral_meas_lt ν (h0 ν) hg.aemeasurable, lintegral_congr hfr,
          lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
          Iic_inter_Ioi, Real.volume_Ioc, sub_zero, ENNReal.ofReal_coe_nnreal, mul_comm]

/-- Along finite measures converging uniformly on measurable sets, the integral of every bounded
measurable function converges. -/
theorem tendsto_lintegral_of_tendstoUniformlyOn {μ : ℕ → Measure α} [∀ n, IsFiniteMeasure (μ n)]
    {ν : Measure α} [IsFiniteMeasure ν]
    (h : TendstoUniformlyOn (fun n s ↦ (μ n).real s) (fun s ↦ ν.real s) atTop
      {s | MeasurableSet s})
    {f : α → ℝ≥0∞} (hf : Measurable f) {c : ℝ≥0} (hfc : ∀ x, f x ≤ c) :
    Tendsto (fun n ↦ ∫⁻ x, f x ∂(μ n)) atTop (𝓝 (∫⁻ x, f x ∂ν)) := by
  have hfin : ∫⁻ x, f x ∂ν ≠ ∞ :=
    ((lintegral_mono hfc).trans_lt (by simp [ENNReal.mul_lt_top])).ne
  refine (ENNReal.tendsto_nhds hfin).2 fun ε hε ↦ ?_
  have hc : Tendsto (fun δ : ℝ ↦ (c : ℝ≥0∞) * ENNReal.ofReal δ) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.tendsto 0).mono_left
      nhdsWithin_le_nhds) (Or.inr ENNReal.coe_ne_top)
  obtain ⟨δ, hδε, hδ⟩ := ((hc.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h δ hδ] with n hn
  have hb : ∀ s, MeasurableSet s → |ν.real s - (μ n).real s| < δ :=
    fun s hs ↦ (Real.dist_eq _ _).symm.trans_lt (hn s hs)
  have h₁ : ∀ s, MeasurableSet s → μ n s ≤ ν s + ENNReal.ofReal δ := fun s hs ↦ by
    rw [← ofReal_measureReal (μ := μ n), ← ofReal_measureReal (μ := ν)]
    exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.1 (hb s hs)])).trans
      ENNReal.ofReal_add_le
  have h₂ : ∀ s, MeasurableSet s → ν s ≤ μ n s + ENNReal.ofReal δ := fun s hs ↦ by
    rw [← ofReal_measureReal (μ := μ n), ← ofReal_measureReal (μ := ν)]
    exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.1 (hb s hs)])).trans
      ENNReal.ofReal_add_le
  refine ⟨tsub_le_iff_right.2 ((lintegral_le_lintegral_add_mul_of_forall_le_add h₂ hf hfc).trans
    (by gcongr)), (lintegral_le_lintegral_add_mul_of_forall_le_add h₁ hf hfc).trans (by gcongr)⟩

end MeasureTheory
