/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Meromorphic resolvents have poles at spectral values

Let `a` be an element of a complete normed algebra `A` over a nontrivially normed field `𝕜`, and
let `μ ∈ spectrum 𝕜 a`. The resolvent blows up at `μ`: `‖resolvent a z‖⁻¹ ≤ ‖z - μ‖ * ‖1‖`,
since otherwise `algebraMap 𝕜 A μ - a` would be a unit close to `algebraMap 𝕜 A z - a`. Hence if
`resolvent a` is meromorphic at `μ` and `μ` is not an interior point of the spectrum, the
resolvent has no limit at `μ`, its meromorphic order there is a negative integer `-m`, and
`(z - μ) ^ m • resolvent a z` tends to a nonzero `Q`. Passing to the limit in
`(a - μ) * resolvent a z = (z - μ) • resolvent a z - 1` gives `(a - μ) * Q = 0 = Q * (a - μ)`.

Meromorphy passes from `a ^ n` to `a` (`n ≠ 0`): `z ^ n - a ^ n = (z - a) * q z` with
`q z = ∑ i < n, z ^ i * a ^ (n - 1 - i)` commuting with `z - a`, so
`resolvent a z = q z * resolvent (a ^ n) (z ^ n)` off the spectrum of `a ^ n`, and `z ^ n ≠ μ ^ n`
for `z ≠ μ` near `μ`.

## Main statements

* `spectrum.inv_norm_resolvent_le`: the lower bound `‖resolvent a z‖⁻¹ ≤ ‖z - μ‖ * ‖1‖`.
* `spectrum.not_tendsto_resolvent`: no limit at a spectral value which is not interior.
* `MeromorphicAt.exists_tendsto_pow_smul_resolvent`: a meromorphic resolvent has a pole of some
  order `m > 0` with nonzero leading coefficient at every non-interior spectral value.
* `spectrum.sub_algebraMap_mul_eq_zero_of_tendsto_pow_smul_resolvent`,
  `spectrum.mul_sub_algebraMap_eq_zero_of_tendsto_pow_smul_resolvent`: the leading coefficient of
  a pole is annihilated by `a - μ` on both sides.
* `spectrum.resolvent_eq_geom_sum_mul_resolvent_pow`, `spectrum.eventually_notMem_of_pow`,
  `MeromorphicAt.resolvent_of_pow`: from `a ^ n` to `a`.
* `spectrum.analyticAt_resolvent`: the resolvent is analytic on the resolvent set.

Staged for `Mathlib/Analysis/Normed/Algebra/Spectrum.lean` (`eventually_pow_ne_pow`,
`tendsto_pow_nhdsNE_pow` for `Mathlib/Analysis/Normed/Field/Lemmas.lean`). Searched on
2026-10-17: the pinned tree (`v4.34.1`) has the meromorphic order
(`Mathlib/Analysis/Meromorphic/Order.lean`), `analyticAt_inverse` and the resolvent at infinity
(`spectrum.resolvent_tendsto_cobounded`), but no lower bound of the resolvent norm by the distance
to a spectral value, no `AnalyticAt` statement for `resolvent` and no statement combining
`MeromorphicAt` with `resolvent` (`grep -rn "MeromorphicAt" Mathlib` lists only
`Analysis/Meromorphic`, `Analysis/Complex` and `SpecialFunctions`). On mathlib master,
`gh api` on `Analysis/Normed/Algebra/Spectrum.lean` and `Analysis/Meromorphic/Basic.lean` finds
neither; `gh pr list -R leanprover-community/mathlib4 --search "resolvent meromorphic"` returns
only the merged Fredholm alternative (#35048), `--search "resolvent pole"` nothing related.
-/

open Filter Topology

section Algebra

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {a : A} {μ z : 𝕜} {n : ℕ}

namespace spectrum

/-- **Resolvent of a root**: if `z ^ n ∉ spectrum 𝕜 (a ^ n)`, then
`resolvent a z = (∑ i < n, z ^ i * a ^ (n - 1 - i)) * resolvent (a ^ n) (z ^ n)`. -/
theorem resolvent_eq_geom_sum_mul_resolvent_pow (h : z ^ n ∉ spectrum 𝕜 (a ^ n)) :
    resolvent a z = (∑ i ∈ Finset.range n, algebraMap 𝕜 A z ^ i * a ^ (n - 1 - i)) *
      resolvent (a ^ n) (z ^ n) := by
  have hu : IsUnit (algebraMap 𝕜 A (z ^ n) - a ^ n) := notMem_iff.mp h
  have hz : IsUnit (algebraMap 𝕜 A z - a) := notMem_iff.mp (mt (pow_mem_pow a n) h)
  have hmul : (algebraMap 𝕜 A z - a) *
      ((∑ i ∈ Finset.range n, algebraMap 𝕜 A z ^ i * a ^ (n - 1 - i)) *
        resolvent (a ^ n) (z ^ n)) = 1 := by
    rw [← mul_assoc, (Algebra.commute_algebraMap_left z a).mul_geom_sum₂, ← map_pow, resolvent,
      Ring.mul_inverse_cancel _ hu]
  rw [← mul_one (resolvent a z), ← hmul, resolvent, Ring.inverse_mul_cancel_left _ _ hz]

/-- Off the spectrum, `(a - μ) * resolvent a z = (z - μ) • resolvent a z - 1`. -/
theorem sub_algebraMap_mul_resolvent (hz : z ∉ spectrum 𝕜 a) :
    (a - algebraMap 𝕜 A μ) * resolvent a z = (z - μ) • resolvent a z - 1 := by
  have h : (algebraMap 𝕜 A z - a) * resolvent a z = 1 :=
    Ring.mul_inverse_cancel _ (notMem_iff.mp hz)
  rw [← h, Algebra.smul_def, ← sub_mul, map_sub]
  congr 1
  abel

/-- Off the spectrum, `resolvent a z * (a - μ) = (z - μ) • resolvent a z - 1`. -/
theorem resolvent_mul_sub_algebraMap (hz : z ∉ spectrum 𝕜 a) :
    resolvent a z * (a - algebraMap 𝕜 A μ) = (z - μ) • resolvent a z - 1 := by
  have h : resolvent a z * (algebraMap 𝕜 A z - a) = 1 :=
    Ring.inverse_mul_cancel _ (notMem_iff.mp hz)
  rw [← h, Algebra.smul_def, Algebra.commutes, ← mul_sub, map_sub]
  congr 1
  abel

end spectrum

end Algebra

section PowNhds

variable {𝕜 : Type*} [NormedField 𝕜] {μ : 𝕜} {n : ℕ}

/-- Near `μ`, `μ` is the only `n`-th root of `μ ^ n` (`n ≠ 0`): there are finitely many. -/
theorem eventually_pow_ne_pow (hn : n ≠ 0) : ∀ᶠ z in 𝓝[≠] μ, z ^ n ≠ μ ^ n := by
  classical
  have hfin : {z : 𝕜 | z ^ n = μ ^ n}.Finite :=
    (Polynomial.nthRoots n (μ ^ n)).toFinset.finite_toSet.subset fun z hz ↦ by
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using hz
  have h : ({z : 𝕜 | z ^ n = μ ^ n} \ {μ})ᶜ ∈ 𝓝 μ :=
    hfin.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hzμ
  exact fun h ↦ hz ⟨h, hzμ⟩

/-- For `n ≠ 0`, `z ↦ z ^ n` maps punctured neighbourhoods of `μ` to punctured neighbourhoods of
`μ ^ n`. -/
theorem tendsto_pow_nhdsNE_pow (hn : n ≠ 0) :
    Tendsto (· ^ n) (𝓝[≠] μ) (𝓝[≠] (μ ^ n)) :=
  tendsto_nhdsWithin_iff.mpr ⟨((continuous_pow n).tendsto μ).mono_left nhdsWithin_le_nhds,
    eventually_pow_ne_pow hn⟩

end PowNhds

namespace spectrum

section NormedField

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] {a : A} {μ : 𝕜}

/-- If the points `w ≠ μ ^ n` near `μ ^ n` are outside the spectrum of `a ^ n` (`n ≠ 0`), then the
points `z ≠ μ` near `μ` are outside the spectrum of `a`. -/
theorem eventually_notMem_of_pow {n : ℕ} (hn : n ≠ 0)
    (h : ∀ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (a ^ n)) :
    ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 a :=
  ((tendsto_pow_nhdsNE_pow hn).eventually h).mono fun _ hz ↦ mt (pow_mem_pow a n) hz

variable [CompleteSpace A]

/-- **The resolvent blows up at the spectrum**: if `μ ∈ spectrum 𝕜 a`, then
`‖resolvent a z‖⁻¹ ≤ ‖z - μ‖ * ‖1‖` for every `z`. -/
theorem inv_norm_resolvent_le (hμ : μ ∈ spectrum 𝕜 a) (z : 𝕜) :
    ‖resolvent a z‖⁻¹ ≤ ‖z - μ‖ * ‖(1 : A)‖ := by
  by_cases hz : z ∈ spectrum 𝕜 a
  · rw [resolvent, Ring.inverse_non_unit _ hz, norm_zero, inv_zero]
    positivity
  obtain ⟨u, hu⟩ := not_not.mp hz
  refine not_lt.mp fun h ↦ hμ ?_
  rw [resolvent, ← hu, Ring.inverse_unit] at h
  have hd : ‖(algebraMap 𝕜 A μ - a) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹ := by
    rwa [hu, sub_sub_sub_cancel_right, ← map_sub, norm_algebraMap, norm_sub_rev]
  exact (u.ofNearby _ hd).isUnit

/-- At a spectral value `μ`, `‖resolvent a z‖⁻¹ → 0` as `z → μ`. -/
theorem tendsto_inv_norm_resolvent (hμ : μ ∈ spectrum 𝕜 a) :
    Tendsto (fun z ↦ ‖resolvent a z‖⁻¹) (𝓝 μ) (𝓝 0) := by
  have h : Tendsto (fun z ↦ ‖z - μ‖ * ‖(1 : A)‖) (𝓝 μ) (𝓝 0) :=
    (by fun_prop : Continuous fun z : 𝕜 ↦ ‖z - μ‖ * ‖(1 : A)‖).tendsto' μ 0 (by simp)
  exact squeeze_zero (fun _ ↦ by positivity) (inv_norm_resolvent_le hμ) h

/-- At a spectral value `μ` which is not an interior point of the spectrum, the resolvent has no
limit. -/
theorem not_tendsto_resolvent (hμ : μ ∈ spectrum 𝕜 a)
    (hfr : ∃ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 a) (c : A) :
    ¬Tendsto (resolvent a) (𝓝[≠] μ) (𝓝 c) := fun hc ↦ by
  have hA : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with hA | hA
    · simp [of_subsingleton] at hμ
    · exact hA
  have hlim : Tendsto (fun z ↦ ‖resolvent a z‖ * ‖resolvent a z‖⁻¹) (𝓝[≠] μ) (𝓝 0) := by
    simpa using hc.norm.mul ((tendsto_inv_norm_resolvent hμ).mono_left nhdsWithin_le_nhds)
  obtain ⟨z, hz, hz1⟩ := (hfr.and_eventually (hlim.eventually (gt_mem_nhds one_pos))).exists
  exact lt_irrefl 1 ((mul_inv_cancel₀
    (norm_ne_zero_iff.mpr (notMem_iff.mp hz).ringInverse.ne_zero)).symm.trans_lt hz1)

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  {a Q : A} {μ : 𝕜} {m : ℕ}

/-- If `(z - μ) ^ m • resolvent a z` has a nonzero limit as `z → μ`, `z ≠ μ`, then the points
`z ≠ μ` near `μ` are outside the spectrum. -/
theorem eventually_notMem_of_tendsto_pow_smul_resolvent
    (h : Tendsto (fun z ↦ (z - μ) ^ m • resolvent a z) (𝓝[≠] μ) (𝓝 Q)) (hQ : Q ≠ 0) :
    ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 a :=
  (h.eventually_ne hQ).mono fun z hz hzσ ↦ hz <| by
    rw [resolvent, Ring.inverse_non_unit _ (mem_iff.mp hzσ), smul_zero]

/-- **The leading coefficient of a pole is annihilated on the left**: if `m > 0` and
`(z - μ) ^ m • resolvent a z → Q` as `z → μ`, `z ≠ μ`, then `(a - μ) * Q = 0`. -/
theorem sub_algebraMap_mul_eq_zero_of_tendsto_pow_smul_resolvent (hm : 0 < m)
    (h : Tendsto (fun z ↦ (z - μ) ^ m • resolvent a z) (𝓝[≠] μ) (𝓝 Q)) :
    (a - algebraMap 𝕜 A μ) * Q = 0 := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · exact mul_zero _
  have h₀ : Tendsto (fun z : 𝕜 ↦ z - μ) (𝓝[≠] μ) (𝓝 0) :=
    ((by fun_prop : Continuous fun z : 𝕜 ↦ z - μ).tendsto' μ 0 (sub_self μ)).mono_left
      nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((h.const_mul (a - algebraMap 𝕜 A μ)).congr' ?_)
    (by simpa [zero_pow hm.ne'] using (h₀.smul h).sub ((h₀.pow m).smul_const (1 : A)))
  filter_upwards [eventually_notMem_of_tendsto_pow_smul_resolvent h hQ] with z hz
  rw [mul_smul_comm, sub_algebraMap_mul_resolvent hz, smul_sub, smul_comm]

/-- **The leading coefficient of a pole is annihilated on the right**: if `m > 0` and
`(z - μ) ^ m • resolvent a z → Q` as `z → μ`, `z ≠ μ`, then `Q * (a - μ) = 0`. -/
theorem mul_sub_algebraMap_eq_zero_of_tendsto_pow_smul_resolvent (hm : 0 < m)
    (h : Tendsto (fun z ↦ (z - μ) ^ m • resolvent a z) (𝓝[≠] μ) (𝓝 Q)) :
    Q * (a - algebraMap 𝕜 A μ) = 0 := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · exact zero_mul _
  have h₀ : Tendsto (fun z : 𝕜 ↦ z - μ) (𝓝[≠] μ) (𝓝 0) :=
    ((by fun_prop : Continuous fun z : 𝕜 ↦ z - μ).tendsto' μ 0 (sub_self μ)).mono_left
      nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((h.mul_const (a - algebraMap 𝕜 A μ)).congr' ?_)
    (by simpa [zero_pow hm.ne'] using (h₀.smul h).sub ((h₀.pow m).smul_const (1 : A)))
  filter_upwards [eventually_notMem_of_tendsto_pow_smul_resolvent h hQ] with z hz
  rw [smul_mul_assoc, resolvent_mul_sub_algebraMap hz, smul_sub, smul_comm]

variable [CompleteSpace A]

/-- The resolvent is analytic on the resolvent set. -/
theorem analyticAt_resolvent {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    AnalyticAt 𝕜 (resolvent a) k :=
  (analyticAt_inverse (𝕜 := 𝕜) (mem_resolventSet_iff.mp hk).unit).comp_of_eq
    (by simp only [Algebra.algebraMap_eq_smul_one]; fun_prop)
    (mem_resolventSet_iff.mp hk).unit_spec

end NontriviallyNormedField

end spectrum

section Meromorphic

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] {a : A}
  {μ : 𝕜}

/-- **Meromorphy of the resolvent at a root**: if `resolvent (a ^ n)` is meromorphic at `μ ^ n`
(`n ≠ 0`) and the points `w ≠ μ ^ n` near `μ ^ n` are outside the spectrum of `a ^ n`, then
`resolvent a` is meromorphic at `μ`. -/
theorem MeromorphicAt.resolvent_of_pow {n : ℕ} (hn : n ≠ 0)
    (hm : MeromorphicAt (resolvent (a ^ n)) (μ ^ n))
    (h : ∀ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (a ^ n)) :
    MeromorphicAt (resolvent a) μ := by
  have hq : AnalyticAt 𝕜
      (fun z ↦ ∑ i ∈ Finset.range n, algebraMap 𝕜 A z ^ i * a ^ (n - 1 - i)) μ := by
    simp only [Algebra.algebraMap_eq_smul_one]
    fun_prop
  have hR : MeromorphicAt (fun z ↦ resolvent (a ^ n) (z ^ n)) μ :=
    hm.comp_analyticAt (g := (· ^ n)) (analyticAt_id.pow n)
  refine (hq.meromorphicAt.smul hR).congr ?_
  filter_upwards [(tendsto_pow_nhdsNE_pow hn).eventually h] with z hz
  exact (spectrum.resolvent_eq_geom_sum_mul_resolvent_pow hz).symm

variable [CompleteSpace A]

/-- **Poles of a meromorphic resolvent**: if `resolvent a` is meromorphic at a spectral value `μ`
and `μ` is not an interior point of the spectrum, the resolvent has a pole of some order `m > 0`
at `μ` with nonzero leading coefficient `Q`. -/
theorem MeromorphicAt.exists_tendsto_pow_smul_resolvent (hm : MeromorphicAt (resolvent a) μ)
    (hμ : μ ∈ spectrum 𝕜 a) (hfr : ∃ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 a) :
    ∃ m : ℕ, 0 < m ∧ ∃ Q : A, Q ≠ 0 ∧
      Tendsto (fun z ↦ (z - μ) ^ m • resolvent a z) (𝓝[≠] μ) (𝓝 Q) := by
  have hA : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with hA | hA
    · simp [spectrum.of_subsingleton] at hμ
    · exact hA
  have ho : meromorphicOrderAt (resolvent a) μ ≠ ⊤ := fun h ↦
    (hfr.and_eventually (meromorphicOrderAt_eq_top_iff.mp h)).exists.elim fun z hz ↦
      (spectrum.notMem_iff.mp hz.1).ringInverse.ne_zero hz.2
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ho
  have hk0 : k < 0 := by
    by_contra! hk0
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm
      (hk ▸ WithTop.coe_nonneg.mpr hk0)
    exact spectrum.not_tendsto_resolvent hμ hfr c hc
  obtain ⟨g, hg, hgμ, hfg⟩ := (meromorphicOrderAt_eq_int_iff hm).mp hk.symm
  have hmk : (k.natAbs : ℤ) = -k := Int.ofNat_natAbs_of_nonpos hk0.le
  refine ⟨k.natAbs, Int.natAbs_pos.mpr hk0.ne, g μ, hgμ,
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hzμ
  rw [hz, smul_smul, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr hzμ), hmk, neg_add_cancel,
    zpow_zero, one_smul]

end Meromorphic
