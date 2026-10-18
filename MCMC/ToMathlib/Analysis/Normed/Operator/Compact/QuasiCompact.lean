/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import MCMC.ToMathlib.Analysis.Normed.Algebra.Resolvent
import MCMC.ToMathlib.Analysis.Normed.Algebra.ResolventMeromorphic
import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.AnalyticFredholm

/-!
# Quasi-compact operators: poles of the resolvent and eigenvectors

An operator `T` on a Banach space is quasi-compact at `μ` if `gelfandRadius (T ^ n - K) < ‖μ‖ ^ n`
for some `n ≠ 0` and some compact `K`: the essential spectral radius of `T` is `< ‖μ‖`. This file
proves the two halves of the Krein–Rutman theorem for such operators that do not involve a cone.

* **Poles.** With `S = T ^ n` and `A = S - K`, `w - S = (1 - K * (w - A)⁻¹) * (w - A)` for
  `‖w‖ > gelfandRadius A`, and `w ↦ K * (w - A)⁻¹` is analytic with compact values, so the analytic
  Fredholm theorem makes `resolvent S` meromorphic at `μ ^ n`, with the spectrum of `S` either
  filling or avoiding a punctured neighbourhood of `μ ^ n`. Since
  `z ^ n - T ^ n = (z - T) * ∑ i < n, z ^ i * T ^ (n - 1 - i)`, `resolvent T` is then meromorphic
  at `μ`; at a spectral value it has a pole, whose leading coefficient `Q ≠ 0` satisfies
  `(T - μ) * Q = 0`, so `μ` is an eigenvalue. Over a general field the spectrum of `T ^ n` is
  assumed to avoid points accumulating at `μ ^ n`; over `ℂ` this is automatic, because the
  dichotomy propagates along the connected set `{w | gelfandRadius A < ‖w‖}`, which contains
  points beyond the Gelfand radius of `S`.
* **Eigenvectors.** Bounded approximate eigenvectors `t k • y k - T (y k) → 0` with `t k → r`,
  `‖r‖ ^ n > gelfandRadius (T ^ n - K)`, have a convergent subsequence, whose limit is an
  eigenvector for `r`: `y k = (s k - A)⁻¹ (K (y k) + (s k • y k - S (y k)))` with `s k = t k ^ n`,
  and `K (y k)` has a convergent subsequence.

The compact case is `n = 1`, `K = T`. If `T ^ n` is compact (`K = T ^ n`), the spectral hypothesis
is supplied by Riesz–Schauder for `T ^ n`, over any field.

## Main statements

* `ContinuousLinearMap.hasEigenvector_of_tendsto_pow_smul_resolvent`,
  `ContinuousLinearMap.hasEigenvalue_of_tendsto_pow_smul_resolvent`: poles are eigenvalues.
* `IsCompactOperator.meromorphicAt_resolvent_of_gelfandRadius_sub_lt`,
  `IsCompactOperator.frequently_notMem_spectrum_iff_of_gelfandRadius_sub_lt`: the resolvent of
  `S` is meromorphic beyond the Gelfand radius of `S - K`, `K` compact, and the spectral dichotomy.
* `IsCompactOperator.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt`,
  `IsCompactOperator.meromorphicAt_resolvent_of_gelfandRadius_pow_sub_lt`,
  `IsCompactOperator.exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt`,
  `IsCompactOperator.hasEigenvalue_of_gelfandRadius_pow_sub_lt`: poles of quasi-compact
  operators.
* `IsCompactOperator.eventually_notMem_spectrum_of_isPreconnected`: the dichotomy along a
  connected set; `IsCompactOperator.eventually_notMem_spectrum_of_gelfandRadius_sub_lt`: its
  complex form, with no spectral hypothesis.
* `IsCompactOperator.meromorphicAt_resolvent_of_pow`,
  `IsCompactOperator.eventually_notMem_spectrum_of_pow`,
  `IsCompactOperator.exists_tendsto_pow_smul_resolvent_of_pow`,
  `IsCompactOperator.hasEigenvalue_of_pow`: the case of `T ^ n` compact.
* `IsCompactOperator.exists_subseq_tendsto_of_gelfandRadius_pow_sub_lt`,
  `IsCompactOperator.exists_subseq_tendsto_of_ne_zero`: approximate eigenvectors.

Staged for a new file `Mathlib/Analysis/Normed/Operator/Compact/QuasiCompact.lean`
(`isPreconnected_compl_closedBall` for `Mathlib/Analysis/Normed/Module/Connected.lean`;
`spectrum.algebraMap_sub_add_eq_mul`, `spectrum.notMem_add_iff_isUnit`,
`spectrum.resolvent_add_eq_mul_ringInverse` for `Mathlib/Algebra/Algebra/Spectrum/Basic.lean`).
Searched on 2026-10-17: the pinned tree (`v4.34.1`) has no essential spectral radius,
quasi-compact or power-compact operator (`grep -rni "essential spectr" Mathlib/Analysis` and
`grep -rni "quasi-compact operator" Mathlib/Analysis` are empty) and no connectedness of the
complement of a ball (only `isPreconnected_sphere`, `isConnected_compl_singleton_of_one_lt_rank`);
mathlib master (`gh api` on the `Mathlib/Analysis` tree) has no such file, and
`gh pr list -R leanprover-community/mathlib4 --search "quasi-compact operator"`,
`"essential spectrum"`, `"Krein Rutman"` return no related PR (only #43906, compact perturbations
of Fredholm operators, closed).
-/

open Filter Metric Topology

/-- In a real normed space of dimension `> 1`, the complement of a closed ball is preconnected:
it is the image of `Ioi r ×ˢ sphere 0 1` under `(s, u) ↦ x + s • u`. -/
theorem isPreconnected_compl_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) : IsPreconnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [closedBall_eq_empty.mpr hr, Set.compl_empty]
    exact isPreconnected_univ
  have he : (closedBall x r)ᶜ =
      (fun p : ℝ × E ↦ x + p.1 • p.2) '' (Set.Ioi r ×ˢ sphere (0 : E) 1) := by
    ext y
    simp only [Set.mem_compl_iff, mem_closedBall, not_le, dist_eq_norm, Set.mem_image,
      Set.mem_prod, Set.mem_Ioi, mem_sphere_zero_iff_norm, Prod.exists]
    refine ⟨fun hy ↦ ⟨‖y - x‖, ‖y - x‖⁻¹ • (y - x), ⟨hy, ?_⟩, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hr.trans_lt hy).ne']
    · rw [smul_inv_smul₀ (hr.trans_lt hy).ne', add_sub_cancel]
    · rintro ⟨s, u, ⟨hs, hu⟩, rfl⟩
      rwa [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg (hr.trans hs.le)]
  rw [he]
  exact (isPreconnected_Ioi.prod (isPreconnected_sphere h 0 1)).image _
    (by fun_prop : Continuous fun p : ℝ × E ↦ x + p.1 • p.2).continuousOn

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {S Q : X →L[𝕜] X} {μ : 𝕜} {m : ℕ}

/-- **The leading coefficient of a pole maps into the eigenspace**: if `m > 0` and
`(z - μ) ^ m • resolvent S z → Q` as `z → μ`, `z ≠ μ`, then every `Q v ≠ 0` is an eigenvector of
`S` for `μ`. -/
theorem hasEigenvector_of_tendsto_pow_smul_resolvent (hm : 0 < m)
    (h : Tendsto (fun z ↦ (z - μ) ^ m • resolvent S z) (𝓝[≠] μ) (𝓝 Q)) {v : X} (hv : Q v ≠ 0) :
    Module.End.HasEigenvector (S : Module.End 𝕜 X) μ (Q v) := by
  have hSQ := DFunLike.congr_fun
    (spectrum.sub_algebraMap_mul_eq_zero_of_tendsto_pow_smul_resolvent hm h) v
  rw [Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp, sub_apply, smul_apply,
    one_apply_eq_self, zero_apply, sub_eq_zero] at hSQ
  exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hSQ, hv⟩

/-- **Poles of the resolvent are eigenvalues**: if `m > 0`, `Q ≠ 0` and
`(z - μ) ^ m • resolvent S z → Q` as `z → μ`, `z ≠ μ`, then `μ` is an eigenvalue of `S`. -/
theorem hasEigenvalue_of_tendsto_pow_smul_resolvent (hm : 0 < m) (hQ : Q ≠ 0)
    (h : Tendsto (fun z ↦ (z - μ) ^ m • resolvent S z) (𝓝[≠] μ) (𝓝 Q)) :
    Module.End.HasEigenvalue (S : Module.End 𝕜 X) μ := by
  obtain ⟨v, hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra! hQv
    exact hQ (ext hQv)
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (hasEigenvector_of_tendsto_pow_smul_resolvent hm h hv)

end ContinuousLinearMap

namespace spectrum

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {a : A} {w : 𝕜}

/-- **Fredholm factorization**: for `w ∈ resolventSet 𝕜 a`,
`w - (a + k) = (1 - k * resolvent a w) * (w - a)`. -/
theorem algebraMap_sub_add_eq_mul (hw : w ∈ resolventSet 𝕜 a) (k : A) :
    algebraMap 𝕜 A w - (a + k) = (1 - k * resolvent a w) * (algebraMap 𝕜 A w - a) := by
  rw [sub_mul, one_mul, mul_assoc, resolvent,
    Ring.inverse_mul_cancel _ (mem_resolventSet_iff.mp hw), mul_one, sub_add_eq_sub_sub]

/-- For `w ∈ resolventSet 𝕜 a`, `w ∉ spectrum 𝕜 (a + k)` iff `1 - k * resolvent a w` is a unit. -/
theorem notMem_add_iff_isUnit (hw : w ∈ resolventSet 𝕜 a) (k : A) :
    w ∉ spectrum 𝕜 (a + k) ↔ IsUnit (1 - k * resolvent a w) := by
  rw [notMem_iff, algebraMap_sub_add_eq_mul hw k]
  exact (mem_resolventSet_iff.mp hw).mul_right_iff

/-- For `w ∈ resolventSet 𝕜 a`,
`resolvent (a + k) w = resolvent a w * Ring.inverse (1 - k * resolvent a w)`. -/
theorem resolvent_add_eq_mul_ringInverse (hw : w ∈ resolventSet 𝕜 a) (k : A) :
    resolvent (a + k) w = resolvent a w * Ring.inverse (1 - k * resolvent a w) := by
  conv_lhs => rw [resolvent, algebraMap_sub_add_eq_mul hw k,
    Ring.inverse_mul (Or.inr (mem_resolventSet_iff.mp hw))]
  rfl

end spectrum

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {S T K : X →L[𝕜] X} {w μ : 𝕜} {n : ℕ}

section EssentialRadius

variable [CompleteSpace 𝕜]

/-- **Meromorphy beyond the essential radius**: if `K` is compact and
`gelfandRadius (S - K) < ‖w‖`, then `resolvent S` is meromorphic at `w`. -/
theorem meromorphicAt_resolvent_of_gelfandRadius_sub_lt (hK : IsCompactOperator K)
    (h : gelfandRadius (S - K) < ‖w‖) : MeromorphicAt (resolvent S) w := by
  have hw : w ∈ resolventSet 𝕜 (S - K) := mem_resolventSet_of_gelfandRadius_lt h
  have hR := spectrum.analyticAt_resolvent hw
  refine (hR.meromorphicAt.clm_comp
    ((analyticAt_const.fun_mul hR).meromorphicAt_ringInverse_one_sub (hK.comp_clm _))).congr ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    ((spectrum.isOpen_resolventSet (S - K)).mem_nhds hw)] with z hz
  have hRz := spectrum.resolvent_add_eq_mul_ringInverse hz K
  rw [sub_add_cancel] at hRz
  exact hRz.symm

/-- **Spectral dichotomy beyond the essential radius**: if `K` is compact and
`gelfandRadius (S - K) < ‖w‖`, the points `z ≠ w` near `w` are outside the spectrum of `S` as
soon as points outside the spectrum accumulate at `w`. -/
theorem frequently_notMem_spectrum_iff_of_gelfandRadius_sub_lt (hK : IsCompactOperator K)
    (h : gelfandRadius (S - K) < ‖w‖) :
    (∃ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S) ↔ ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S := by
  have hw : w ∈ resolventSet 𝕜 (S - K) := mem_resolventSet_of_gelfandRadius_lt h
  have hR := spectrum.analyticAt_resolvent hw
  have hiff : ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S ↔ IsUnit (1 - K * resolvent (S - K) z) :=
    (eventually_nhdsWithin_of_eventually_nhds
      ((spectrum.isOpen_resolventSet (S - K)).mem_nhds hw)).mono fun z hz ↦ by
      simpa using spectrum.notMem_add_iff_isUnit hz K
  rw [frequently_congr hiff, eventually_congr hiff]
  exact (analyticAt_const.fun_mul hR).frequently_isUnit_one_sub_iff (hK.comp_clm _)

/-- **Isolated spectrum of a quasi-compact operator**: if `K` is compact, `n ≠ 0`,
`gelfandRadius (T ^ n - K) < ‖μ‖ ^ n` and points outside the spectrum of `T ^ n` accumulate at
`μ ^ n`, then the points `z ≠ μ` near `μ` are outside the spectrum of `T`. -/
theorem eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt (hK : IsCompactOperator K)
    (hn : n ≠ 0) (h : gelfandRadius (T ^ n - K) < ‖μ‖ ^ n)
    (hfr : ∃ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (T ^ n)) :
    ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 T :=
  spectrum.eventually_notMem_of_pow hn
    ((hK.frequently_notMem_spectrum_iff_of_gelfandRadius_sub_lt (by rwa [norm_pow])).mp hfr)

/-- **Meromorphic resolvent of a quasi-compact operator**: under the hypotheses of
`IsCompactOperator.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt`, `resolvent T` is
meromorphic at `μ`. -/
theorem meromorphicAt_resolvent_of_gelfandRadius_pow_sub_lt (hK : IsCompactOperator K)
    (hn : n ≠ 0) (h : gelfandRadius (T ^ n - K) < ‖μ‖ ^ n)
    (hfr : ∃ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (T ^ n)) :
    MeromorphicAt (resolvent T) μ :=
  (hK.meromorphicAt_resolvent_of_gelfandRadius_sub_lt (by rwa [norm_pow])).resolvent_of_pow hn
    ((hK.frequently_notMem_spectrum_iff_of_gelfandRadius_sub_lt (by rwa [norm_pow])).mp hfr)

/-- **Poles of a quasi-compact operator**: under the hypotheses of
`IsCompactOperator.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt`, if `μ` is a spectral
value of `T`, the resolvent of `T` has a pole of some order `m > 0` at `μ` with nonzero leading
coefficient `Q`. -/
theorem exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt (hK : IsCompactOperator K)
    (hn : n ≠ 0) (h : gelfandRadius (T ^ n - K) < ‖μ‖ ^ n)
    (hfr : ∃ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (T ^ n)) (hμ : μ ∈ spectrum 𝕜 T) :
    ∃ m : ℕ, 0 < m ∧ ∃ Q : X →L[𝕜] X, Q ≠ 0 ∧
      Tendsto (fun z ↦ (z - μ) ^ m • resolvent T z) (𝓝[≠] μ) (𝓝 Q) :=
  MeromorphicAt.exists_tendsto_pow_smul_resolvent
    (hK.meromorphicAt_resolvent_of_gelfandRadius_pow_sub_lt hn h hfr) hμ
    (hK.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt hn h hfr).frequently

/-- **Spectral values of a quasi-compact operator are eigenvalues**: under the hypotheses of
`IsCompactOperator.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt`, every spectral value
`μ` of `T` is an eigenvalue. -/
theorem hasEigenvalue_of_gelfandRadius_pow_sub_lt (hK : IsCompactOperator K) (hn : n ≠ 0)
    (h : gelfandRadius (T ^ n - K) < ‖μ‖ ^ n)
    (hfr : ∃ᶠ w in 𝓝[≠] (μ ^ n), w ∉ spectrum 𝕜 (T ^ n)) (hμ : μ ∈ spectrum 𝕜 T) :
    Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ := by
  obtain ⟨m, hm, Q, hQ, hlim⟩ :=
    hK.exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt hn h hfr hμ
  exact ContinuousLinearMap.hasEigenvalue_of_tendsto_pow_smul_resolvent hm hQ hlim

/-- **Spectral dichotomy on a connected set**: if `K` is compact, `C` is preconnected and lies
beyond the Gelfand radius of `S - K`, and some `w₀ ∈ C` is outside the spectrum of `S`, then
every `w ∈ C` has a punctured neighbourhood outside the spectrum of `S`. -/
theorem eventually_notMem_spectrum_of_isPreconnected (hK : IsCompactOperator K) {C : Set 𝕜}
    (hC : IsPreconnected C) (hCK : ∀ w ∈ C, gelfandRadius (S - K) < ‖w‖) {w₀ : 𝕜}
    (hw₀C : w₀ ∈ C) (hw₀ : w₀ ∉ spectrum 𝕜 S) (hw : w ∈ C) :
    ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S := by
  have hCuv : C ⊆ {w | ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S} ∪
      {w | ∀ᶠ z in 𝓝[≠] w, z ∈ spectrum 𝕜 S} := fun w hw ↦ by
    by_cases h : ∃ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S
    · exact Or.inl ((hK.frequently_notMem_spectrum_iff_of_gelfandRadius_sub_lt (hCK w hw)).mp h)
    · exact Or.inr ((not_frequently.mp h).mono fun _ hz ↦ not_not.mp hz)
  have hdisj : C ∩ ({w | ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum 𝕜 S} ∩
      {w | ∀ᶠ z in 𝓝[≠] w, z ∈ spectrum 𝕜 S}) = ∅ :=
    Set.eq_empty_of_forall_notMem fun w hw ↦ by
      obtain ⟨-, hu, hv⟩ := hw
      simp only [Set.mem_ofPred_eq] at hu hv
      exact (hu.and hv).exists.elim fun z hz ↦ hz.1 hz.2
  rcases isPreconnected_iff_subset_of_disjoint.mp hC _ _ isOpen_setOfPred_eventually_nhdsWithin
    isOpen_setOfPred_eventually_nhdsWithin hCuv hdisj with hCu | hCv
  · exact hCu hw
  · have hw₀' : ∀ᶠ z in 𝓝[≠] w₀, z ∉ spectrum 𝕜 S :=
      eventually_nhdsWithin_of_eventually_nhds
        ((spectrum.isClosed S).isOpen_compl.mem_nhds hw₀)
    exact ((hw₀'.and (hCv hw₀C)).exists.elim fun z hz ↦ (hz.1 hz.2).elim)

end EssentialRadius

section Complex

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  {S K : Y →L[ℂ] Y} {w : ℂ}

/-- **Isolated spectrum beyond the essential radius**, complex form: if `K` is compact and
`gelfandRadius (S - K) < ‖w‖`, then the points `z ≠ w` near `w` are outside the spectrum of `S`:
`{z | gelfandRadius (S - K) < ‖z‖}` is connected and contains points beyond the Gelfand radius of
`S`. Its frequent form discharges the spectral hypothesis of
`IsCompactOperator.meromorphicAt_resolvent_of_gelfandRadius_pow_sub_lt` and its companions. -/
theorem eventually_notMem_spectrum_of_gelfandRadius_sub_lt (hK : IsCompactOperator K)
    (h : gelfandRadius (S - K) < ‖w‖) : ∀ᶠ z in 𝓝[≠] w, z ∉ spectrum ℂ S := by
  set r := max (gelfandRadius (S - K)) (gelfandRadius S) + 1
  have hr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine hK.eventually_notMem_spectrum_of_isPreconnected
    (isPreconnected_compl_closedBall (by simp [Complex.rank_real_complex]) 0
      (gelfandRadius (S - K))) (fun z hz ↦ by simpa using hz) (w₀ := r) ?_
    (spectrum.notMem_iff.mpr (spectrum.mem_resolventSet_iff.mp
      (mem_resolventSet_of_gelfandRadius_lt ?_))) (by simpa using h)
  · simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hr]
    linarith [le_max_left (gelfandRadius (S - K)) (gelfandRadius S)]
  · rw [hr]
    linarith [le_max_right (gelfandRadius (S - K)) (gelfandRadius S)]

end Complex

section PowCompact

/-- **Power-compact operators**: if `T ^ n` is compact (`n ≠ 0`), `resolvent T` is meromorphic at
every `μ ≠ 0`. -/
theorem meromorphicAt_resolvent_of_pow (hT : IsCompactOperator (T ^ n)) (hn : n ≠ 0)
    (hμ : μ ≠ 0) : MeromorphicAt (resolvent T) μ :=
  (hT.meromorphicAt_resolvent (pow_ne_zero n hμ)).resolvent_of_pow hn
    (hT.eventually_notMem_spectrum (pow_ne_zero n hμ))

/-- **Power-compact operators**: if `T ^ n` is compact (`n ≠ 0`), the nonzero spectral values of
`T` are isolated. -/
theorem eventually_notMem_spectrum_of_pow (hT : IsCompactOperator (T ^ n)) (hn : n ≠ 0)
    (hμ : μ ≠ 0) : ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 T :=
  spectrum.eventually_notMem_of_pow hn (hT.eventually_notMem_spectrum (pow_ne_zero n hμ))

/-- **Power-compact operators**: if `T ^ n` is compact (`n ≠ 0`), at every nonzero spectral value
the resolvent of `T` has a pole of some order `m > 0` with nonzero leading coefficient. -/
theorem exists_tendsto_pow_smul_resolvent_of_pow (hT : IsCompactOperator (T ^ n)) (hn : n ≠ 0)
    (hμ0 : μ ≠ 0) (hμ : μ ∈ spectrum 𝕜 T) :
    ∃ m : ℕ, 0 < m ∧ ∃ Q : X →L[𝕜] X, Q ≠ 0 ∧
      Tendsto (fun z ↦ (z - μ) ^ m • resolvent T z) (𝓝[≠] μ) (𝓝 Q) :=
  (hT.meromorphicAt_resolvent_of_pow hn hμ0).exists_tendsto_pow_smul_resolvent hμ
    (hT.eventually_notMem_spectrum_of_pow hn hμ0).frequently

/-- **Power-compact operators**: if `T ^ n` is compact (`n ≠ 0`), every nonzero spectral value of
`T` is an eigenvalue. -/
theorem hasEigenvalue_of_pow (hT : IsCompactOperator (T ^ n)) (hn : n ≠ 0) (hμ0 : μ ≠ 0)
    (hμ : μ ∈ spectrum 𝕜 T) : Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ := by
  obtain ⟨m, hm, Q, hQ, hlim⟩ := hT.exists_tendsto_pow_smul_resolvent_of_pow hn hμ0 hμ
  exact ContinuousLinearMap.hasEigenvalue_of_tendsto_pow_smul_resolvent hm hQ hlim

end PowCompact

section Eigenvector

/-- **Approximate eigenvectors of a quasi-compact operator**: if `K` is compact,
`gelfandRadius (T ^ n - K) < ‖r‖ ^ n`, `t k → r` and `y` is bounded with
`t k • y k - T (y k) → 0`, then a subsequence of `y` converges to some `z` with `T z = r • z`. -/
theorem exists_subseq_tendsto_of_gelfandRadius_pow_sub_lt (hK : IsCompactOperator K)
    {r : 𝕜} (h : gelfandRadius (T ^ n - K) < ‖r‖ ^ n) {t : ℕ → 𝕜}
    (ht : Tendsto t atTop (𝓝 r)) {y : ℕ → X} {R : ℝ} (hy : ∀ k, ‖y k‖ ≤ R)
    (hTy : Tendsto (fun k ↦ t k • y k - T (y k)) atTop (𝓝 0)) :
    ∃ (z : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z) ∧ T z = r • z := by
  have happ {f : ℕ → X →L[𝕜] X} {g : ℕ → X} {F : X →L[𝕜] X} {v : X}
      (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 v)) :
      Tendsto (fun k ↦ f k (g k)) atTop (𝓝 (F v)) :=
    (isBoundedBilinearMap_apply.continuous.tendsto (F, v)).comp (hf.prodMk_nhds hg)
  have hr : r ^ n ∈ resolventSet 𝕜 (T ^ n - K) :=
    mem_resolventSet_of_gelfandRadius_lt (by rwa [norm_pow])
  have hs : Tendsto (fun k ↦ t k ^ n) atTop (𝓝 (r ^ n)) := ht.pow n
  have hgeom (s : 𝕜) (v : X) :
      (∑ i ∈ Finset.range n, algebraMap 𝕜 (X →L[𝕜] X) s ^ i * T ^ (n - 1 - i)) (s • v - T v) =
        s ^ n • v - (T ^ n) v := by
    simpa [Algebra.algebraMap_eq_smul_one, smul_pow] using
      DFunLike.congr_fun ((Algebra.commute_algebraMap_left s T).geom_sum₂_mul n) v
  have hinv (s : 𝕜) (hs : s ∈ resolventSet 𝕜 (T ^ n - K)) (v : X) :
      resolvent (T ^ n - K) s (K v + (s • v - (T ^ n) v)) = v := by
    calc resolvent (T ^ n - K) s (K v + (s • v - (T ^ n) v))
        = (resolvent (T ^ n - K) s * (algebraMap 𝕜 (X →L[𝕜] X) s - (T ^ n - K))) v := by
          rw [mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one, sub_apply, sub_apply,
            smul_apply, one_apply_eq_self]
          congr 1
          abel
      _ = v := by
          rw [resolvent, Ring.inverse_mul_cancel _ (spectrum.mem_resolventSet_iff.mp hs),
            one_apply_eq_self]
  have hq : Continuous fun s : 𝕜 ↦
      ∑ i ∈ Finset.range n, algebraMap 𝕜 (X →L[𝕜] X) s ^ i * T ^ (n - 1 - i) := by
    simp only [Algebra.algebraMap_eq_smul_one]
    fun_prop
  have hd : Tendsto (fun k ↦ t k ^ n • y k - (T ^ n) (y k)) atTop (𝓝 0) := by
    simpa [hgeom] using happ ((hq.tendsto r).comp ht) hTy
  obtain ⟨C, hC, hKC⟩ := hK.image_closedBall_subset_compact R
  obtain ⟨w, -, φ, hφ, hw⟩ := hC.tendsto_subseq (x := fun k ↦ K (y k))
    fun k ↦ hKC ⟨y k, by simpa using hy k, rfl⟩
  have hsφ := hs.comp hφ.tendsto_atTop
  have hRes : Tendsto (fun k ↦ resolvent (T ^ n - K) (t (φ k) ^ n)) atTop
      (𝓝 (resolvent (T ^ n - K) (r ^ n))) :=
    (spectrum.analyticAt_resolvent hr).continuousAt.tendsto.comp hsφ
  have hlim : Tendsto (y ∘ φ) atTop (𝓝 (resolvent (T ^ n - K) (r ^ n) (w + 0))) := by
    refine (happ hRes (hw.add (hd.comp hφ.tendsto_atTop))).congr' ?_
    filter_upwards [hsφ.eventually ((spectrum.isOpen_resolventSet (T ^ n - K)).mem_nhds hr)]
      with k hk
    exact hinv _ hk _
  rw [add_zero] at hlim
  refine ⟨_, φ, hφ, hlim, ?_⟩
  have h₂ : Tendsto (fun k ↦ t (φ k) • y (φ k) - T (y (φ k))) atTop
      (𝓝 (r • resolvent (T ^ n - K) (r ^ n) w - T (resolvent (T ^ n - K) (r ^ n) w))) :=
    ((ht.comp hφ.tendsto_atTop).smul hlim).sub ((T.continuous.tendsto _).comp hlim)
  exact (sub_eq_zero.mp (tendsto_nhds_unique h₂ (hTy.comp hφ.tendsto_atTop))).symm

/-- **Approximate eigenvectors of a compact operator**: if `T` is compact, `r ≠ 0`, `t k → r` and
`y` is bounded with `t k • y k - T (y k) → 0`, then a subsequence of `y` converges to some `z`
with `T z = r • z`. -/
theorem exists_subseq_tendsto_of_ne_zero (hT : IsCompactOperator T) {r : 𝕜}
    (hr : r ≠ 0) {t : ℕ → 𝕜} (ht : Tendsto t atTop (𝓝 r)) {y : ℕ → X} {R : ℝ}
    (hy : ∀ k, ‖y k‖ ≤ R) (hTy : Tendsto (fun k ↦ t k • y k - T (y k)) atTop (𝓝 0)) :
    ∃ (z : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z) ∧ T z = r • z :=
  hT.exists_subseq_tendsto_of_gelfandRadius_pow_sub_lt (n := 1)
    (by simpa using norm_pos_iff.mpr hr) ht hy hTy

end Eigenvector

end IsCompactOperator
