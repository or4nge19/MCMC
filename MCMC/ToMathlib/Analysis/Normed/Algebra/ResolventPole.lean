/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Poles of the resolvent from a spectral idempotent

Let `s` be an element of a complete normed `𝕜`-algebra `E`, let `μ : 𝕜` and
`a = s - algebraMap 𝕜 E μ`. Suppose `P` is an idempotent commuting with `s`, `a` is nilpotent on
the range of `P` (`a ^ n * P = 0`) and invertible on the range of `1 - P` (`a * (1 - P) + P` is a
unit): the algebraic shape of the Riesz decomposition at an isolated spectral value. With
`x = algebraMap 𝕜 E (z - μ)` and `T = (a - x) * (1 - P) + P`, for `z ≠ μ` near `μ`,
`(z - μ) ^ n • resolvent s z = (∑ i < n, x ^ i * a ^ (n - 1 - i)) * P - x ^ n * (T⁻¹ʳ * (1 - P))`.
The right side is analytic at `μ`, so `μ` is at worst a pole of order `n` of the resolvent.

## Main statements

* `IsIdempotentElem.sub_mul_geomSum_sub_eq_pow`: the ring identity behind the formula.
* `IsIdempotentElem.exists_unit_algebraMap_sub_eq`: the resulting inverse of `x - a`, `x ≠ 0`.
* `IsIdempotentElem.exists_analyticAt_pow_smul_resolvent_eq`: an analytic numerator `F` with
  `F μ = a ^ n * P` and `(z - μ) ^ (n + 1) • resolvent s z = F z` near `μ`, `z ≠ μ`.
* `IsIdempotentElem.meromorphicAt_resolvent`: the resolvent is meromorphic at `μ`.
* `IsIdempotentElem.eventually_notMem_spectrum`: `μ` is not an accumulation point of the spectrum.
* `IsIdempotentElem.exists_tendsto_pow_smul_resolvent`: if `P ≠ 0`, the resolvent has a pole of
  some order `m > 0` with nonzero leading coefficient `a ^ (m - 1) * P`.

Staged for a new file `Mathlib/Analysis/Normed/Algebra/ResolventPole.lean`
(`Commute.ringInverse_right` for `Mathlib/Algebra/GroupWithZero/Commute.lean`). Searched on
2026-10-17: pinned mathlib (`v4.34.1`) and mathlib master (`gh api` on
`Analysis/Normed/Algebra/Spectrum.lean`, `Algebra/GroupWithZero/Commute.lean`) have
`analyticAt_inverse` and `Commute.ringInverse_ringInverse`, but no meromorphy of the resolvent at
a spectral value and no spectral-idempotent (Drazin) criterion;
`gh pr list -R leanprover-community/mathlib4 --search "resolvent meromorphic"` returns only the
merged Fredholm alternative (#35048).
-/
open Filter Finset Topology
open scoped Ring

section MonoidWithZero

variable {M₀ : Type*} [MonoidWithZero M₀] {a b : M₀}

/-- If `a` commutes with `b`, it commutes with `Ring.inverse b`. -/
theorem Commute.ringInverse_right (h : Commute a b) : Commute a b⁻¹ʳ := by
  by_cases hb : IsUnit b
  · rw [Ring.inverse_of_isUnit hb]
    exact (hb.unit_spec ▸ h).units_inv_right
  · rw [Ring.inverse_non_unit b hb]
    exact Commute.zero_right a

end MonoidWithZero

section Ring

variable {R : Type*} [Ring R] {a P x : R} {n : ℕ}

/-- `x - a` commutes with every term of the pole formula. -/
theorem Commute.sub_geomSum_sub (haP : Commute a P) (hxa : Commute x a) (hxP : Commute x P) :
    Commute (x - a) ((∑ i ∈ range n, x ^ i * a ^ (n - 1 - i)) * P -
      x ^ n * (((a - x) * (1 - P) + P)⁻¹ʳ * (1 - P))) := by
  have hca : Commute (x - a) a := hxa.sub_left (Commute.refl a)
  have hcx : Commute (x - a) x := (Commute.refl x).sub_left hxa.symm
  have hcP : Commute (x - a) P := hxP.sub_left haP
  have hcQ : Commute (x - a) (1 - P) := (Commute.one_right _).sub_right hcP
  have hcT : Commute (x - a) ((a - x) * (1 - P) + P) :=
    ((hca.sub_right hcx).mul_right hcQ).add_right hcP
  refine ((Commute.sum_right _ _ _ fun i _ ↦ ?_).mul_right hcP).sub_right
    ((hcx.pow_right n).mul_right (hcT.ringInverse_right.mul_right hcQ))
  exact (hcx.pow_right i).mul_right (hca.pow_right _)

/-- **Pole identity**: if `P` is idempotent, `a` commutes with `P`, `x` commutes with `a` and
`P`, `a ^ n * P = 0` and `T = (a - x) * (1 - P) + P` is a unit, then
`(x - a) * ((∑ i < n, x ^ i * a ^ (n - 1 - i)) * P - x ^ n * (T⁻¹ʳ * (1 - P))) = x ^ n`. -/
theorem IsIdempotentElem.sub_mul_geomSum_sub_eq_pow (hP : IsIdempotentElem P)
    (haP : Commute a P) (hxa : Commute x a) (hxP : Commute x P) (hn : a ^ n * P = 0)
    (hT : IsUnit ((a - x) * (1 - P) + P)) :
    (x - a) * ((∑ i ∈ range n, x ^ i * a ^ (n - 1 - i)) * P -
      x ^ n * (((a - x) * (1 - P) + P)⁻¹ʳ * (1 - P))) = x ^ n := by
  set T := (a - x) * (1 - P) + P with hTdef
  have hcx : Commute (x - a) x := (Commute.refl x).sub_left hxa.symm
  have hcT : Commute (x - a) T :=
    (((hxa.sub_left (Commute.refl a)).sub_right hcx).mul_right
      ((Commute.one_right _).sub_right (hxP.sub_left haP))).add_right (hxP.sub_left haP)
  have hTQ : T * (1 - P) = (a - x) * (1 - P) := by
    rw [hTdef, add_mul, mul_assoc, hP.one_sub.eq, hP.mul_one_sub_self, add_zero]
  have hQ : (x - a) * (T⁻¹ʳ * (1 - P)) = -(1 - P) := by
    rw [hcT.ringInverse_right.left_comm, ← neg_sub a x, neg_mul, ← hTQ, mul_neg,
      ← mul_assoc, Ring.inverse_mul_cancel T hT, one_mul]
  rw [mul_sub, ← mul_assoc, (hcx.pow_right n).left_comm, hxa.mul_geom_sum₂, hQ, sub_mul, hn]
  noncomm_ring

end Ring

section Algebra

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] {a P : E} {w : 𝕜} {n : ℕ}

/-- **Inverse near a pole**: under the hypotheses of `IsIdempotentElem.sub_mul_geomSum_sub_eq_pow`
with `x = algebraMap 𝕜 E w` and `w ≠ 0`, `x - a` is a unit `u` with
`w ^ n • u⁻¹ = (∑ i < n, x ^ i * a ^ (n - 1 - i)) * P - x ^ n * (T⁻¹ʳ * (1 - P))`. -/
theorem IsIdempotentElem.exists_unit_algebraMap_sub_eq (hP : IsIdempotentElem P)
    (haP : Commute a P) (hn : a ^ n * P = 0) (hw : w ≠ 0)
    (hT : IsUnit ((a - algebraMap 𝕜 E w) * (1 - P) + P)) :
    ∃ u : Eˣ, (u : E) = algebraMap 𝕜 E w - a ∧ w ^ n • (↑u⁻¹ : E) =
      (∑ i ∈ range n, algebraMap 𝕜 E w ^ i * a ^ (n - 1 - i)) * P -
        algebraMap 𝕜 E w ^ n * (((a - algebraMap 𝕜 E w) * (1 - P) + P)⁻¹ʳ * (1 - P)) := by
  have hxa : Commute (algebraMap 𝕜 E w) a := Algebra.commutes w a
  have hxP : Commute (algebraMap 𝕜 E w) P := Algebra.commutes w P
  have hl := hP.sub_mul_geomSum_sub_eq_pow haP hxa hxP hn hT
  have hr := (Commute.sub_geomSum_sub haP hxa hxP (n := n)).eq.symm.trans hl
  have hc : (w ^ n)⁻¹ • algebraMap 𝕜 E w ^ n = 1 := by
    rw [← map_pow, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n hw), map_one]
  exact ⟨⟨_, (w ^ n)⁻¹ • _, by rw [mul_smul_comm, hl, hc], by rw [smul_mul_assoc, hr, hc]⟩, rfl,
    smul_inv_smul₀ (pow_ne_zero n hw) _⟩

end Algebra

section NormedAlgebra

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E] [NormedAlgebra 𝕜 E]
  [CompleteSpace E] {s P : E} {μ : 𝕜} {n : ℕ}

/-- **Analytic numerator of the resolvent**. Let `a = s - algebraMap 𝕜 E μ`, let `P` be an
idempotent commuting with `s` with `a ^ (n + 1) * P = 0` and `a * (1 - P) + P` a unit. Then there
is `F` analytic at `μ` with `F μ = a ^ n * P` such that, for `z ≠ μ` near `μ`, `z` is not in the
spectrum of `s` and `(z - μ) ^ (n + 1) • resolvent s z = F z`. -/
theorem IsIdempotentElem.exists_analyticAt_pow_smul_resolvent_eq (hP : IsIdempotentElem P)
    (hsP : Commute s P) (hn : (s - algebraMap 𝕜 E μ) ^ (n + 1) * P = 0)
    (hu : IsUnit ((s - algebraMap 𝕜 E μ) * (1 - P) + P)) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F μ ∧ F μ = (s - algebraMap 𝕜 E μ) ^ n * P ∧
      ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 s ∧ (z - μ) ^ (n + 1) • resolvent s z = F z := by
  set a := s - algebraMap 𝕜 E μ with ha
  set x : 𝕜 → E := fun z ↦ algebraMap 𝕜 E (z - μ) with hx
  set T : 𝕜 → E := fun z ↦ (a - x z) * (1 - P) + P with hT
  set F : 𝕜 → E := fun z ↦ (∑ i ∈ range (n + 1), x z ^ i * a ^ (n + 1 - 1 - i)) * P -
    x z ^ (n + 1) * ((T z)⁻¹ʳ * (1 - P)) with hF
  have haP : Commute a P := hsP.sub_left (Algebra.commutes μ P)
  have hxan : AnalyticAt 𝕜 x μ := by
    simp only [hx, Algebra.algebraMap_eq_smul_one]
    fun_prop
  have hTan : AnalyticAt 𝕜 T μ := by
    simp only [hT]
    fun_prop
  have hTμ : T μ = a * (1 - P) + P := by simp [hT, hx]
  refine ⟨F, ?_, ?_, ?_⟩
  · have hinv : AnalyticAt 𝕜 (fun z ↦ (T z)⁻¹ʳ) μ :=
      (analyticAt_inverse (𝕜 := 𝕜) hu.unit).comp_of_eq hTan (by rw [hTμ, hu.unit_spec])
    simp only [hF]
    fun_prop
  · simp [hF, hx, sum_range_succ', zero_pow (Nat.succ_ne_zero _)]
  · have hTev : ∀ᶠ z in 𝓝 μ, IsUnit (T z) :=
      hTan.continuousAt.eventually_mem (Units.isOpen.mem_nhds (hTμ ▸ hu))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hTev, self_mem_nhdsWithin]
      with z hz hzμ
    obtain ⟨u, hux, hFu⟩ := hP.exists_unit_algebraMap_sub_eq haP hn (sub_ne_zero.mpr hzμ) hz
    have hsub : algebraMap 𝕜 E z - s = u := by simp [hux, ha]
    refine ⟨spectrum.notMem_iff.mpr (hsub ▸ u.isUnit), ?_⟩
    rw [resolvent, hsub, Ring.inverse_unit]
    exact hFu

/-- **Meromorphy of the resolvent at a spectral idempotent**: if `P` is an idempotent commuting
with `s`, `a = s - algebraMap 𝕜 E μ` satisfies `a ^ n * P = 0`, and `a * (1 - P) + P` is a unit,
then `resolvent s` is meromorphic at `μ`. -/
theorem IsIdempotentElem.meromorphicAt_resolvent (hP : IsIdempotentElem P) (hsP : Commute s P)
    (hn : (s - algebraMap 𝕜 E μ) ^ n * P = 0)
    (hu : IsUnit ((s - algebraMap 𝕜 E μ) * (1 - P) + P)) :
    MeromorphicAt (resolvent s) μ := by
  obtain ⟨F, hF, -, hev⟩ := hP.exists_analyticAt_pow_smul_resolvent_eq hsP
    (by rw [pow_succ', mul_assoc, hn, mul_zero]) hu
  have hFm := hF.meromorphicAt
  have hm : MeromorphicAt (fun z ↦ ((z - μ) ^ (n + 1))⁻¹ • F z) μ := by fun_prop
  refine hm.congr ?_
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzμ
  rw [← hz.2, inv_smul_smul₀ (pow_ne_zero _ (sub_ne_zero.mpr hzμ))]

/-- Under the hypotheses of `IsIdempotentElem.meromorphicAt_resolvent`, the points `z ≠ μ` near
`μ` lie outside the spectrum of `s`. -/
theorem IsIdempotentElem.eventually_notMem_spectrum (hP : IsIdempotentElem P) (hsP : Commute s P)
    (hn : (s - algebraMap 𝕜 E μ) ^ n * P = 0)
    (hu : IsUnit ((s - algebraMap 𝕜 E μ) * (1 - P) + P)) :
    ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 s := by
  obtain ⟨F, -, -, hev⟩ := hP.exists_analyticAt_pow_smul_resolvent_eq hsP
    (by rw [pow_succ', mul_assoc, hn, mul_zero]) hu
  exact hev.mono fun z hz ↦ hz.1

/-- **Leading coefficient of the pole**: under the hypotheses of
`IsIdempotentElem.meromorphicAt_resolvent` with `P ≠ 0`, there are `m > 0` and `Q ≠ 0` with
`(z - μ) ^ m • resolvent s z → Q` as `z → μ`, `z ≠ μ`. Here `m` is the least `m` with
`a ^ m * P = 0` and `Q = a ^ (m - 1) * P`. -/
theorem IsIdempotentElem.exists_tendsto_pow_smul_resolvent (hP : IsIdempotentElem P)
    (hsP : Commute s P) (hn : (s - algebraMap 𝕜 E μ) ^ n * P = 0)
    (hu : IsUnit ((s - algebraMap 𝕜 E μ) * (1 - P) + P)) (hP0 : P ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ Q : E, Q ≠ 0 ∧
      Tendsto (fun z ↦ (z - μ) ^ m • resolvent s z) (𝓝[≠] μ) (𝓝 Q) := by
  classical
  have hex : ∃ k, (s - algebraMap 𝕜 E μ) ^ k * P = 0 := ⟨n, hn⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h ↦ hP0 (by simpa [h] using Nat.find_spec hex)
  obtain ⟨F, hF, hFμ, hev⟩ :=
    hP.exists_analyticAt_pow_smul_resolvent_eq hsP (hk ▸ Nat.find_spec hex) hu
  refine ⟨k + 1, k.succ_pos, F μ, hFμ ▸ Nat.find_min hex (by omega), ?_⟩
  exact (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (hev.mono fun z hz ↦ hz.2.symm)

end NormedAlgebra
