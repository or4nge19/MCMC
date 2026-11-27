/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Order.PartialSups

/-!
# The maximal ergodic lemma

Let `f` preserve a measure `μ` (any measure: no finiteness) and let `g : α → ℝ` be a.e. measurable
(no integrability). On the set `A = {x | ∃ n, 0 < birkhoffSum f g (n + 1) x}` where some Birkhoff
sum is positive, the negative part of `g` has at most the integral of the positive part:
`∫⁻ x in A, ENNReal.ofReal (-g x) ∂μ ≤ ∫⁻ x in A, ENNReal.ofReal (g x) ∂μ`
(`MeasureTheory.MeasurePreserving.setLIntegral_exists_birkhoffSum_pos_le`). For integrable `φ` this
is Hopf's maximal ergodic lemma `0 ≤ ∫ x in A, φ x ∂μ`
(`MeasureTheory.MeasurePreserving.setIntegral_exists_birkhoffSum_pos_nonneg`).

At a level `0 ≤ c`, with `A = {x | ∃ n, c < birkhoffAverage ℝ f g (n + 1) x}`,
`ENNReal.ofReal c * μ A + ∫⁻ x in A, ENNReal.ofReal (-g x) ∂μ ≤ ∫⁻ x in A, ENNReal.ofReal (g x) ∂μ`
(`MeasureTheory.MeasurePreserving.ofReal_mul_measure_add_setLIntegral_le`), so for integrable `φ`
the set `A` has finite measure when `0 < c` and `c * μ.real A ≤ ∫ x in A, φ x ∂μ`
(`MeasureTheory.MeasurePreserving.mul_measureReal_le_setIntegral`). The maximal inequality for
a function with values in a normed space is
`ENNReal.ofReal c * μ {x | ∃ n, c < ‖birkhoffAverage 𝕜 f φ n x‖} ≤ ∫⁻ x, ‖φ x‖ₑ ∂μ`
(`MeasureTheory.MeasurePreserving.ofReal_mul_measure_exists_lt_norm_birkhoffAverage_le`), for every
real `c`.

The proof is Garsia's: the partial maxima `M = partialSups (birkhoffSum f g) N` satisfy
`M x ≤ g x + M (f x)` where `0 < M x` (`partialSups_birkhoffSum_le_add`), and `∫⁻ M ∘ f = ∫⁻ M`.
It is carried out with lower integrals, which is why no integrability is assumed: if the positive
part of `g` is not integrable the statement is trivial, and otherwise `M` is integrable
(`ofReal_partialSups_birkhoffSum_le`, `MeasureTheory.MeasurePreserving.lintegral_birkhoffSum`).

Source: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 25.7 (maximal ergodic
lemma, Hopf; proof after Garsia), read from an extracted text of the 3rd edition. Kallenberg
states it for a stationary sequence of integrable random variables.

Searched on 2026-11-27 (Mathlib `v4.34.1`): `grep -rln "birkhoffAverage\|birkhoffSum" Mathlib`
finds `Dynamics/BirkhoffSum/{Basic, Average, NormedSpace, QuasiMeasurePreserving}.lean` and
`Analysis/InnerProductSpace/MeanErgodic.lean` (algebra, equicontinuity, a.e. congruence, von
Neumann's theorem); `grep -rni "maximal ergodic\|pointwise ergodic\|Hopf" Mathlib` finds only Hopf
algebras; `grep -rn "measurable_birkhoff\|norm_birkhoff" Mathlib` finds nothing;
`MeasureTheory.MeasurePreserving.lintegral_comp` asks for a measurable integrand.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

section Measurable

variable {α M : Type*} [MeasurableSpace α] [AddCommMonoid M] [MeasurableSpace M]
  [MeasurableAdd₂ M] {f : α → α} {g : α → M}

theorem measurable_birkhoffSum (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffSum f g n) :=
  Finset.measurable_sum _ fun k _ ↦ hg.comp (hf.iterate k)

theorem aemeasurable_birkhoffSum {μ : Measure α} (hf : Measure.QuasiMeasurePreserving f μ μ)
    (hg : AEMeasurable g μ) (n : ℕ) : AEMeasurable (birkhoffSum f g n) μ := by
  refine (Finset.aemeasurable_sum (Finset.range n) fun k _ ↦
    hg.comp_quasiMeasurePreserving (hf.iterate k)).congr (.of_forall fun x ↦ ?_)
  simp [birkhoffSum]

theorem measurable_birkhoffAverage (R : Type*) [DivisionSemiring R] [Module R M]
    [MeasurableConstSMul R M] (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffAverage R f g n) :=
  (measurable_birkhoffSum hf hg n).const_smul _

end Measurable

theorem aemeasurable_partialSups {α β : Type*} [MeasurableSpace α] [SemilatticeSup β]
    [MeasurableSpace β] [MeasurableSup₂ β] {μ : Measure α} {F : ℕ → α → β}
    (hF : ∀ n, AEMeasurable (F n) μ) (N : ℕ) : AEMeasurable (partialSups F N) μ := by
  induction N with
  | zero => simpa using hF 0
  | succ N ih => exact partialSups_succ F N ▸ ih.sup (hF _)

section Pointwise

variable {α : Type*}

/-- Where the partial maximum `M` of the Birkhoff sums `0, g, g + g ∘ f, …` is positive,
`M x ≤ g x + M (f x)`. -/
theorem partialSups_birkhoffSum_le_add {M : Type*} [AddCommMonoid M] [LinearOrder M]
    [IsOrderedAddMonoid M] (f : α → α) (g : α → M) (N : ℕ) {x : α}
    (hx : 0 < partialSups (birkhoffSum f g) N x) :
    partialSups (birkhoffSum f g) N x ≤ g x + partialSups (birkhoffSum f g) N (f x) := by
  obtain ⟨k, hk, hkx⟩ := exists_partialSups_eq (fun n ↦ birkhoffSum f g n x) N
  have hkx' : partialSups (birkhoffSum f g) N x = birkhoffSum f g k x :=
    (Pi.partialSups_apply _ N x).trans hkx
  rw [hkx'] at hx ⊢
  cases k with
  | zero => exact absurd hx (by simp)
  | succ k =>
    rw [birkhoffSum_succ_apply']
    gcongr
    exact le_partialSups_of_le (birkhoffSum f g) (Nat.le_of_succ_le hk) (f x)

theorem exists_partialSups_birkhoffSum_pos_iff {M : Type*} [AddCommMonoid M] [LinearOrder M]
    {f : α → α} {g : α → M} {x : α} :
    (∃ N, 0 < partialSups (birkhoffSum f g) N x) ↔ ∃ n, 0 < birkhoffSum f g (n + 1) x := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨k, -, hk⟩ := exists_partialSups_eq (fun n ↦ birkhoffSum f g n x) N
    rw [(Pi.partialSups_apply _ N x).trans hk] at hN
    cases k with
    | zero => exact absurd hN (by simp)
    | succ k => exact ⟨k, hN⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn.trans_le (le_partialSups (birkhoffSum f g) (n + 1) x)⟩

/-- The positive part of a partial maximum of Birkhoff sums of `g` is at most the Birkhoff sum of
the positive part of `g`. -/
theorem ofReal_partialSups_birkhoffSum_le (f : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    ENNReal.ofReal (partialSups (birkhoffSum f g) N x) ≤
      birkhoffSum f (fun x ↦ ENNReal.ofReal (g x)) N x := by
  have h : ∀ k, ENNReal.ofReal (birkhoffSum f g k x) ≤
      birkhoffSum f (fun x ↦ ENNReal.ofReal (g x)) k x := fun k ↦ by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [birkhoffSum_succ_apply, birkhoffSum_succ_apply]
      exact ENNReal.ofReal_add_le.trans (add_le_add ih le_rfl)
  obtain ⟨k, hk, hkx⟩ := exists_partialSups_eq (fun n ↦ birkhoffSum f g n x) N
  rw [(Pi.partialSups_apply _ N x).trans hkx]
  exact (h k).trans (Finset.sum_le_sum_of_subset (Finset.range_mono hk))

theorem lt_birkhoffAverage_iff_birkhoffSum_sub_pos (f : α → α) (g : α → ℝ) (c : ℝ) (n : ℕ)
    (x : α) :
    c < birkhoffAverage ℝ f g (n + 1) x ↔ 0 < birkhoffSum f (fun x ↦ g x - c) (n + 1) x := by
  have h : birkhoffSum f (fun x ↦ g x - c) (n + 1) x =
      birkhoffSum f g (n + 1) x - (n + 1) * c := by
    simp [birkhoffSum, Finset.sum_sub_distrib]
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [h, sub_pos, birkhoffAverage, smul_eq_mul, Nat.cast_add_one, lt_inv_mul_iff₀ hn]

theorem birkhoffSum_indicator_of_preimage_eq {M : Type*} [AddCommMonoid M] {f : α → α}
    {s : Set α} (hs : f ⁻¹' s = s) (g : α → M) (n : ℕ) :
    birkhoffSum f (s.indicator g) n = s.indicator (birkhoffSum f g n) := by
  have hk : ∀ k x, f^[k] x ∈ s ↔ x ∈ s := fun k x ↦
    Set.ext_iff.1 (Function.IsFixedPt.preimage_iterate hs k) x
  ext x
  by_cases hx : x ∈ s <;> simp [birkhoffSum, hx, hk]

theorem birkhoffAverage_indicator_of_preimage_eq (R : Type*) {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} {s : Set α} (hs : f ⁻¹' s = s) (g : α → M)
    (n : ℕ) : birkhoffAverage R f (s.indicator g) n = s.indicator (birkhoffAverage R f g n) := by
  ext x
  rw [birkhoffAverage, birkhoffSum_indicator_of_preimage_eq hs]
  by_cases hx : x ∈ s <;> simp [hx, birkhoffAverage]

theorem norm_birkhoffAverage_le (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : α → α) (φ : α → E) (n : ℕ) (x : α) :
    ‖birkhoffAverage 𝕜 f φ n x‖ ≤ birkhoffAverage ℝ f (fun x ↦ ‖φ x‖) n x := by
  simp only [birkhoffAverage, birkhoffSum, norm_smul, norm_inv, RCLike.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_sum_le _ _

end Pointwise

namespace MeasureTheory.MeasurePreserving

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {g φ : α → ℝ} {c : ℝ}

/-- `MeasureTheory.MeasurePreserving.lintegral_comp` for an a.e. measurable integrand. -/
theorem lintegral_comp' {β : Type*} [MeasurableSpace β] {ν : Measure β} {T : α → β}
    (hT : MeasurePreserving T μ ν) {h : β → ℝ≥0∞} (hh : AEMeasurable h ν) :
    ∫⁻ a, h (T a) ∂μ = ∫⁻ b, h b ∂ν := by
  rw [← hT.map_eq] at hh ⊢
  exact (lintegral_map' hh hT.aemeasurable).symm

theorem lintegral_birkhoffSum (hf : MeasurePreserving f μ μ) {h : α → ℝ≥0∞}
    (hh : AEMeasurable h μ) (n : ℕ) : ∫⁻ x, birkhoffSum f h n x ∂μ = n * ∫⁻ x, h x ∂μ := by
  simp only [birkhoffSum]
  have hk : ∀ k ∈ Finset.range n, AEMeasurable (fun x ↦ h (f^[k] x)) μ := fun k _ ↦
    hh.comp_quasiMeasurePreserving (hf.iterate k).quasiMeasurePreserving
  rw [lintegral_finsetSum' _ hk]
  simp [(hf.iterate _).lintegral_comp' hh]

/-- The maximal ergodic lemma at a finite horizon `N`, with lower integrals. -/
theorem setLIntegral_partialSups_birkhoffSum_pos_le (hf : MeasurePreserving f μ μ)
    (hg : AEMeasurable g μ) (N : ℕ) :
    ∫⁻ x in {x | 0 < partialSups (birkhoffSum f g) N x}, ENNReal.ofReal (-g x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ∞ with htop | htop
  · exact htop ▸ le_top
  set M : α → ℝ := partialSups (birkhoffSum f g) N with hM
  have hMm : AEMeasurable M μ :=
    aemeasurable_partialSups (fun n ↦ aemeasurable_birkhoffSum hf.quasiMeasurePreserving hg n) N
  have hM0 : ∀ x, 0 ≤ M x := fun x ↦ (birkhoffSum_zero_apply f g x).symm.le.trans
    (le_partialSups_of_le (birkhoffSum f g) N.zero_le x)
  have hfin : ∫⁻ x, ENNReal.ofReal (M x) ∂μ ≠ ∞ :=
    ((lintegral_mono (ofReal_partialSups_birkhoffSum_le f g N)).trans_lt (by
      rw [hf.lintegral_birkhoffSum hg.ennreal_ofReal]
      exact ENNReal.mul_lt_top (ENNReal.natCast_ne_top N).lt_top htop.lt_top)).ne
  have h1 : ∫⁻ x, ENNReal.ofReal (M (f x)) ∂μ = ∫⁻ x, ENNReal.ofReal (M x) ∂μ :=
    hf.lintegral_comp' hMm.ennreal_ofReal
  rw [← ENNReal.add_le_add_iff_right hfin]
  calc ∫⁻ x in {x | 0 < M x}, ENNReal.ofReal (-g x) ∂μ + ∫⁻ x, ENNReal.ofReal (M x) ∂μ
      = ∫⁻ x, ({x | 0 < M x}.indicator (fun x ↦ ENNReal.ofReal (-g x)) x +
          ENNReal.ofReal (M x)) ∂μ := by
        rw [lintegral_add_right' _ hMm.ennreal_ofReal,
          lintegral_indicator₀ (_root_.nullMeasurableSet_lt aemeasurable_const hMm)]
    _ ≤ ∫⁻ x, (ENNReal.ofReal (g x) + ENNReal.ofReal (M (f x))) ∂μ := lintegral_mono fun x ↦ ?_
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ + ∫⁻ x, ENNReal.ofReal (M x) ∂μ := by
        rw [lintegral_add_left' hg.ennreal_ofReal, h1]
  by_cases hx : 0 < M x
  · rw [indicator_of_mem (show x ∈ {x | 0 < M x} from hx)]
    rcases le_total 0 (g x) with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 h0), zero_add, ← ENNReal.ofReal_add h0 (hM0 _)]
      exact ENNReal.ofReal_le_ofReal (partialSups_birkhoffSum_le_add f g N hx)
    · rw [ENNReal.ofReal_of_nonpos h0, zero_add, ← ENNReal.ofReal_add (neg_nonneg.2 h0) (hM0 _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [partialSups_birkhoffSum_le_add f g N hx])
  · rw [indicator_of_notMem (show x ∉ {x | 0 < M x} from hx), zero_add,
      ENNReal.ofReal_of_nonpos (not_lt.1 hx)]
    positivity

/-- **The maximal ergodic lemma**, with lower integrals: for a measure-preserving map `f` and an
a.e. measurable `g`, on the set where some Birkhoff sum of `g` is positive the integral of the
negative part of `g` is at most the integral of its positive part. No finiteness of the measure
and no integrability are assumed. -/
theorem setLIntegral_exists_birkhoffSum_pos_le (hf : MeasurePreserving f μ μ)
    (hg : AEMeasurable g μ) :
    ∫⁻ x in {x | ∃ n, 0 < birkhoffSum f g (n + 1) x}, ENNReal.ofReal (-g x) ∂μ ≤
      ∫⁻ x in {x | ∃ n, 0 < birkhoffSum f g (n + 1) x}, ENNReal.ofReal (g x) ∂μ := by
  have hA : {x | ∃ n, 0 < birkhoffSum f g (n + 1) x} =
      ⋃ N, {x | 0 < partialSups (birkhoffSum f g) N x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, exists_partialSups_birkhoffSum_pos_iff]
  have hsupp : (fun x ↦ ENNReal.ofReal (g x)).support ⊆
      {x | ∃ n, 0 < birkhoffSum f g (n + 1) x} := fun x hx ↦ ⟨0, by simpa using hx⟩
  have hmono : Monotone fun N ↦ {x | 0 < partialSups (birkhoffSum f g) N x} :=
    fun N N' h x hx ↦ hx.trans_le ((partialSups (birkhoffSum f g)).monotone h x)
  rw [setLIntegral_eq_of_support_subset hsupp, hA,
    setLIntegral_iUnion_of_directed _ hmono.directed_le]
  exact iSup_le fun N ↦ hf.setLIntegral_partialSups_birkhoffSum_pos_le hg N

/-- **Hopf's maximal ergodic lemma**: for a measure-preserving map `f` and an integrable `φ`, the
integral of `φ` over the set where some Birkhoff sum of `φ` is positive is nonnegative. -/
theorem setIntegral_exists_birkhoffSum_pos_nonneg (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) : 0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum f φ (n + 1) x}, φ x ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.integrableOn]
  exact sub_nonneg.2 (ENNReal.toReal_mono hφ.integrableOn.lintegral_lt_top.ne
    (hf.setLIntegral_exists_birkhoffSum_pos_le hφ.aemeasurable))

/-- **The maximal ergodic lemma at a level** `0 ≤ c`, with lower integrals: on the set `A` where
some Birkhoff average of `g` exceeds `c`, `c * μ A` plus the integral of the negative part of `g`
is at most the integral of the positive part of `g`. -/
theorem ofReal_mul_measure_add_setLIntegral_le (hf : MeasurePreserving f μ μ)
    (hg : AEMeasurable g μ) (hc : 0 ≤ c) :
    ENNReal.ofReal c * μ {x | ∃ n, c < birkhoffAverage ℝ f g (n + 1) x} +
        ∫⁻ x in {x | ∃ n, c < birkhoffAverage ℝ f g (n + 1) x}, ENNReal.ofReal (-g x) ∂μ ≤
      ∫⁻ x in {x | ∃ n, c < birkhoffAverage ℝ f g (n + 1) x}, ENNReal.ofReal (g x) ∂μ := by
  set A : Set α := {x | ∃ n, c < birkhoffAverage ℝ f g (n + 1) x} with hAdef
  have hA : A = {x | ∃ n, 0 < birkhoffSum f (fun x ↦ g x - c) (n + 1) x} := by
    ext x
    simp only [hAdef, mem_ofPred_eq, lt_birkhoffAverage_iff_birkhoffSum_sub_pos]
  have hm : AEMeasurable (fun x ↦ min (ENNReal.ofReal (g x)) (ENNReal.ofReal c)) μ :=
    hg.ennreal_ofReal.min aemeasurable_const
  have h : ∫⁻ x in A, (ENNReal.ofReal (-(g x - c)) +
        min (ENNReal.ofReal (g x)) (ENNReal.ofReal c)) ∂μ ≤
      ∫⁻ x in A, (ENNReal.ofReal (g x - c) + min (ENNReal.ofReal (g x)) (ENNReal.ofReal c)) ∂μ := by
    rw [lintegral_add_right' _ hm.restrict, lintegral_add_right' _ hm.restrict, hA]
    exact add_le_add (hf.setLIntegral_exists_birkhoffSum_pos_le (hg.sub_const c)) le_rfl
  calc ENNReal.ofReal c * μ A + ∫⁻ x in A, ENNReal.ofReal (-g x) ∂μ
      = ∫⁻ x in A, (ENNReal.ofReal c + ENNReal.ofReal (-g x)) ∂μ := by
        rw [lintegral_add_left' aemeasurable_const, setLIntegral_const]
    _ ≤ ∫⁻ x in A, (ENNReal.ofReal (-(g x - c)) +
          min (ENNReal.ofReal (g x)) (ENNReal.ofReal c)) ∂μ := lintegral_mono fun x ↦ ?_
    _ ≤ ∫⁻ x in A, (ENNReal.ofReal (g x - c) +
          min (ENNReal.ofReal (g x)) (ENNReal.ofReal c)) ∂μ := h
    _ = ∫⁻ x in A, ENNReal.ofReal (g x) ∂μ :=
        lintegral_congr fun x ↦ by rw [ENNReal.ofReal_sub _ hc, tsub_add_min]
  rcases le_total 0 (g x) with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 h0), add_zero, neg_sub, ENNReal.ofReal_sub _ h0,
      min_comm, tsub_add_min]
  · rw [ENNReal.ofReal_of_nonpos h0, min_eq_left (by positivity), add_zero, neg_sub,
      sub_eq_add_neg, ENNReal.ofReal_add hc (neg_nonneg.2 h0)]

/-- For integrable `φ` and `0 < c`, the set where some Birkhoff average exceeds `c` has finite
measure. -/
theorem measure_exists_lt_birkhoffAverage_lt_top (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hc : 0 < c) :
    μ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x} < ∞ :=
  ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hφ.integrableOn.lintegral_lt_top.ne
    (le_self_add.trans (hf.ofReal_mul_measure_add_setLIntegral_le hφ.aemeasurable hc.le)))
    (ENNReal.ofReal_pos.2 hc).ne'

/-- **The maximal ergodic lemma at a level** `0 ≤ c`: for integrable `φ`, on the set `A` where
some Birkhoff average of `φ` exceeds `c`, `c * μ A ≤ ∫ x in A, φ x ∂μ`. For `0 < c` the set has
finite measure (`MeasureTheory.MeasurePreserving.measure_exists_lt_birkhoffAverage_lt_top`). -/
theorem mul_measureReal_le_setIntegral (hf : MeasurePreserving f μ μ) (hφ : Integrable φ μ)
    (hc : 0 ≤ c) :
    c * μ.real {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x} ≤
      ∫ x in {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x}, φ x ∂μ := by
  have hE := hf.ofReal_mul_measure_add_setLIntegral_le hφ.aemeasurable hc
  have hP := (hφ.integrableOn
    (s := {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x})).lintegral_lt_top.ne
  have h1 := ENNReal.toReal_mono hP hE
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top hP (le_self_add.trans hE))
    (ne_top_of_le_ne_top hP (le_add_self.trans hE)), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] at h1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.integrableOn]
  exact le_sub_iff_add_le.2 h1

/-- The maximal ergodic lemma on an invariant set `s`: with `A` the set where some Birkhoff average
of `φ` exceeds `c`, `c * μ (s ∩ A) ≤ ∫ x in s ∩ A, φ x ∂μ`. -/
theorem mul_measureReal_inter_le_setIntegral (hf : MeasurePreserving f μ μ)
    (hφ : Integrable φ μ) (hc : 0 ≤ c) {s : Set α}
    (hs : MeasurableSet[MeasurableSpace.invariants f] s) :
    c * μ.real (s ∩ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x}) ≤
      ∫ x in s ∩ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x}, φ x ∂μ := by
  have hA : {x | ∃ n, c < birkhoffAverage ℝ f (s.indicator φ) (n + 1) x} =
      s ∩ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x} := by
    ext x
    by_cases hx : x ∈ s
    · simp [birkhoffAverage_indicator_of_preimage_eq ℝ hs.2, hx]
    · simp [birkhoffAverage_indicator_of_preimage_eq ℝ hs.2, hx, not_lt.2 hc]
  have h2 : ∫ x in s ∩ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x}, s.indicator φ x ∂μ =
      ∫ x in s ∩ {x | ∃ n, c < birkhoffAverage ℝ f φ (n + 1) x}, φ x ∂μ := by
    rw [← Measure.restrict_restrict hs.1]
    exact setIntegral_congr_fun hs.1 fun x hx ↦ indicator_of_mem hx φ
  have h := hf.mul_measureReal_le_setIntegral (hφ.indicator hs.1) hc
  rwa [hA, h2] at h

/-- **The maximal ergodic inequality**: for a measure-preserving map `f` and an a.e. strongly
measurable `φ` with values in a normed space, the set where some Birkhoff average has norm above
`c` has measure at most `c⁻¹ ∫⁻ ‖φ‖ₑ`. -/
theorem ofReal_mul_measure_exists_lt_norm_birkhoffAverage_le (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {φ : α → E} (hf : MeasurePreserving f μ μ)
    (hφ : AEStronglyMeasurable φ μ) (c : ℝ) :
    ENNReal.ofReal c * μ {x | ∃ n, c < ‖birkhoffAverage 𝕜 f φ n x‖} ≤ ∫⁻ x, ‖φ x‖ₑ ∂μ := by
  rcases lt_or_ge c 0 with hc | hc
  · simp [ENNReal.ofReal_of_nonpos hc.le]
  have hsub : {x | ∃ n, c < ‖birkhoffAverage 𝕜 f φ n x‖} ⊆
      {x | ∃ n, c < birkhoffAverage ℝ f (fun x ↦ ‖φ x‖) (n + 1) x} := by
    rintro x ⟨n, hn⟩
    cases n with
    | zero => exact absurd (by simpa using hn) (not_lt.2 hc)
    | succ n => exact ⟨n, hn.trans_le (norm_birkhoffAverage_le 𝕜 f φ (n + 1) x)⟩
  calc ENNReal.ofReal c * μ {x | ∃ n, c < ‖birkhoffAverage 𝕜 f φ n x‖}
      ≤ ENNReal.ofReal c * μ {x | ∃ n, c < birkhoffAverage ℝ f (fun x ↦ ‖φ x‖) (n + 1) x} := by
        gcongr
    _ ≤ ∫⁻ x in {x | ∃ n, c < birkhoffAverage ℝ f (fun x ↦ ‖φ x‖) (n + 1) x},
          ENNReal.ofReal ‖φ x‖ ∂μ :=
        le_self_add.trans (hf.ofReal_mul_measure_add_setLIntegral_le hφ.norm.aemeasurable hc)
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖φ x‖ ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ‖φ x‖ₑ ∂μ := by simp only [ofReal_norm]

end MeasureTheory.MeasurePreserving
