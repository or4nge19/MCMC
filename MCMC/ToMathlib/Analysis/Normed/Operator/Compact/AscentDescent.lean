/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Ascent and descent of compact perturbations of a scalar

Let `S` be a compact operator on a normed space `X` over a nontrivially normed field `𝕜`, and let
`μ ≠ 0`. This file proves the finiteness half of the Riesz theory of `A = S - μ • 1`:

* `ker A` is finite dimensional (if `𝕜` is complete) and `range A` is closed;
* every power `A ^ k` is again of the form `T - ν • 1` with `T` compact and `ν ≠ 0`, so the same
  holds for `ker (A ^ k)` and `range (A ^ k)`;
* the chains `ker (A ^ k)` and `range (A ^ k)` stop (finite ascent and descent).

Closedness of the range needs neither Hahn–Banach nor completeness: every `x` has a
`2`-approximate best approximation in the closed subspace `ker A`, and `A` is bounded below on the
cone of vectors `v` with `‖v‖ ≤ 2 * ‖v - w‖` for all `w ∈ ker A`. The ascent and descent arguments
are Riesz's: a strictly monotone chain of closed subspaces moved by `A` by one step yields, by
Riesz's lemma, a bounded sequence whose images under `S` are `‖μ‖`-separated.

## Main statements

* `riesz_lemma_of_norm_lt_of_lt`: Riesz's lemma inside a larger subspace.
* `IsClosed.exists_mem_forall_dist_le_two_mul`, `Submodule.norm_smul_le_two_mul_norm_smul_sub`:
  `2`-approximate nearest points and the scalar-stable cone they live in.
* `IsCompactOperator.exists_lt_dist_lt`, `IsCompactOperator.exists_subseq_tendsto_of_tendsto`:
  sequential compactness in the form used below.
* `IsCompactOperator.finiteDimensional_ker_sub_smul_one`,
  `IsCompactOperator.exists_pos_mul_norm_le`, `IsCompactOperator.exists_preimage_norm_le`,
  `IsCompactOperator.isClosed_range_sub_smul_one`: kernel and range of `S - μ • 1`.
* `IsCompactOperator.exists_sub_smul_one_pow_eq`, `IsCompactOperator.finiteDimensional_ker_pow`,
  `IsCompactOperator.isClosed_range_pow`.
* `IsCompactOperator.exists_eq_succ_of_monotone`, `IsCompactOperator.exists_eq_succ_of_antitone`:
  Riesz's chain arguments.
* `IsCompactOperator.exists_ker_pow_eq_ker_pow_succ`,
  `IsCompactOperator.exists_range_pow_eq_range_pow_succ`: finite ascent and descent.

Staged for `Mathlib/Analysis/Normed/Operator/Compact/RieszSchauder.lean`. Searched on
2026-10-17: pinned mathlib (`v4.34.1`) and mathlib master (via `gh api`) have the Fredholm
alternative (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`) but no ascent, descent, closed
range or finite-dimensional kernel for `S - μ • 1`; `gh pr list -R leanprover-community/mathlib4`
with `--search "Riesz Schauder"`, `"Fredholm"`, `"compact operator spectrum"` finds only the
closed PR #43906 (closed range and Fredholmness of `1 + c` over `RCLike`, via Hahn–Banach).
Prior art: TauCeti, `TauCeti/Analysis/Normed/Operator/Compact/{RieszTheory,Eigenspace,Basic}.lean`
and `TauCeti/Analysis/Normed/Module/RieszLemma.lean` (commit `a65deaded1ca`, Apache 2.0); the
relative Riesz lemma, the finite-dimensional kernel (`S = μ` on `ker A`, so the identity of
`ker A` is compact) and the chain argument follow it; the closed-range argument here replaces its
Hahn–Banach complement of `ker A` by `2`-approximate nearest points, so works over any `𝕜`.
TauCeti `59a6ba7bd8b5` (2026-10-13) has since replaced its `finiteDimensional_ker_one_sub` and
`isClosed_range_one_sub` by Peetre's compact-error estimate (`Compact/Estimate.lean`:
`finiteDimensional_ker_of_compact_estimate`, `exists_pos_mul_norm_le_of_compact_estimate`,
`isClosed_range_of_compact_estimate`, from `‖x‖ ≤ C * ‖T x‖ + ‖K x‖`); the statements here are
its case `T = S - μ • 1`, `K = μ⁻¹ • S`, and should become corollaries of it upstream.
-/

open Filter Metric Topology

section RieszLemma

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Riesz's lemma** relative to a larger subspace: if `F` is a closed subspace properly contained
in a subspace `G`, then `G` contains a vector of norm at most `R` at distance at least `1`
from `F`. -/
theorem riesz_lemma_of_norm_lt_of_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    {F G : Submodule 𝕜 E} (hFc : IsClosed (F : Set E)) (hFG : F < G) :
    ∃ x₀ ∈ G, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  obtain ⟨x, hxG, hxF⟩ := SetLike.exists_of_lt hFG
  obtain ⟨x₀, hx₀R, hx₀⟩ := riesz_lemma_of_norm_lt hc hR (F := F.comap G.subtype)
    (hFc.preimage continuous_subtype_val) ⟨⟨x, hxG⟩, hxF⟩
  exact ⟨x₀, x₀.2, hx₀R, fun y hy ↦ hx₀ ⟨y, hFG.le hy⟩ hy⟩

end RieszLemma

section Cone

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The cone of vectors `v` with `‖v‖ ≤ 2 * ‖v - w‖` for all `w ∈ K` is stable under scalars. -/
theorem Submodule.norm_smul_le_two_mul_norm_smul_sub {K : Submodule 𝕜 E} {v : E}
    (hv : ∀ w ∈ K, ‖v‖ ≤ 2 * ‖v - w‖) (d : 𝕜) : ∀ w ∈ K, ‖d • v‖ ≤ 2 * ‖d • v - w‖ := by
  intro w hw
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [← smul_inv_smul₀ hd w, ← smul_sub, norm_smul, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hv _ (K.smul_mem _ hw)) (norm_nonneg d)

end Cone

/-- In a closed nonempty set, every point has a `2`-approximate nearest point. -/
theorem IsClosed.exists_mem_forall_dist_le_two_mul {α : Type*} [PseudoMetricSpace α] {s : Set α}
    (hs : IsClosed s) (hne : s.Nonempty) (x : α) :
    ∃ z ∈ s, ∀ w ∈ s, dist x z ≤ 2 * dist x w := by
  by_cases hx : x ∈ s
  · exact ⟨x, hx, fun w _ ↦ by simp [dist_nonneg]⟩
  have hpos := (hs.notMem_iff_infDist_pos hne).mp hx
  obtain ⟨z, hz, hxz⟩ := (infDist_lt_iff hne).mp (by linarith : infDist x s < 2 * infDist x s)
  exact ⟨z, hz, fun w hw ↦ hxz.le.trans (by gcongr; exact infDist_le_dist_of_mem hw)⟩

namespace IsCompactOperator

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {S : X →L[𝕜] X} {μ : 𝕜}

/-- A compact operator cannot keep the images of a bounded sequence pairwise `ε`-separated. -/
theorem exists_lt_dist_lt {T : X →L[𝕜] Y} (hT : IsCompactOperator T) {f : ℕ → X} {R : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ m n, m < n ∧ dist (T (f m)) (T (f n)) < ε := by
  obtain ⟨K, hK, hKsub⟩ := hT.image_closedBall_subset_compact R
  obtain ⟨y, -, ψ, hψ, hψy⟩ := hK.tendsto_subseq fun n ↦ hKsub ⟨f n, by simpa using hf n, rfl⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hψy.cauchySeq ε hε
  refine ⟨ψ N, ψ (N + 1), hψ (Nat.lt_add_one N), ?_⟩
  rw [dist_comm]
  exact hN (N + 1) (Nat.le_add_right N 1)

/-- If `S` is compact, `μ ≠ 0`, `u` is bounded and `(S - μ • 1) (u n) → b`, then a subsequence of
`u` converges to a preimage of `b`. -/
theorem exists_subseq_tendsto_of_tendsto (hS : IsCompactOperator S) (hμ : μ ≠ 0) {u : ℕ → X}
    {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) {b : X}
    (hb : Tendsto (fun n ↦ (S - μ • 1) (u n)) atTop (𝓝 b)) :
    ∃ (y : X) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 y) ∧ (S - μ • 1) y = b := by
  obtain ⟨K, hK, hKsub⟩ := hS.image_closedBall_subset_compact R
  obtain ⟨w, -, ψ, hψ, hψw⟩ := hK.tendsto_subseq fun n ↦ hKsub ⟨u n, by simpa using hu n, rfl⟩
  have hbψ := hb.comp hψ.tendsto_atTop
  have hy : Tendsto (u ∘ ψ) atTop (𝓝 (μ⁻¹ • (w - b))) :=
    ((hψw.sub hbψ).const_smul μ⁻¹).congr fun n ↦ by simp [hμ]
  exact ⟨_, ψ, hψ, hy, tendsto_nhds_unique (((S - μ • 1).continuous.tendsto _).comp hy) hbψ⟩

/-- The kernel of `S - μ • 1` is finite dimensional when `S` is compact and `μ ≠ 0`. -/
theorem finiteDimensional_ker_sub_smul_one [CompleteSpace 𝕜] (hS : IsCompactOperator S)
    (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (S - μ • 1).ker := by
  set N := (S - μ • 1).ker
  have hSx (x : N) : S x = μ • (x : X) := by simpa [sub_eq_zero] using LinearMap.mem_ker.mp x.2
  have hSN (x : N) : μ⁻¹ • S x ∈ N := by simp [hSx x, hμ]
  have hid : Set.codRestrict (fun x : N ↦ μ⁻¹ • S x) N hSN = id := by
    funext x
    ext
    simp [hSx x, hμ]
  have hc : IsCompactOperator (Set.codRestrict (fun x : N ↦ μ⁻¹ • S x) N hSN) :=
    ((hS.comp_clm N.subtypeL).smul μ⁻¹).codRestrict hSN (S - μ • 1).isClosed_ker
  exact FiniteDimensional.of_isCompactOperator_id (hid ▸ hc)

/-- `S - μ • 1` is bounded below on the cone of vectors that are almost orthogonal to its
kernel. -/
theorem exists_pos_mul_norm_le (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∃ c > 0, ∀ v : X, (∀ w ∈ (S - μ • 1).ker, ‖v‖ ≤ 2 * ‖v - w‖) →
      c * ‖v‖ ≤ ‖(S - μ • 1) v‖ := by
  by_contra! h
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm 𝕜
  choose v hv hAv using fun n : ℕ ↦ h (1 / (n + 1)) (by positivity)
  have hv0 (n : ℕ) : v n ≠ 0 := fun h0 ↦ by simpa [h0] using hAv n
  choose d _ hdlt hdge _ using fun n ↦ rescale_to_shell hk one_pos (hv0 n)
  have hAu (n : ℕ) : ‖(S - μ • 1) (d n • v n)‖ ≤ 1 / (n + 1) := by
    rw [map_smul, norm_smul]
    calc ‖d n‖ * ‖(S - μ • 1) (v n)‖ ≤ ‖d n‖ * (1 / (n + 1) * ‖v n‖) := by grw [(hAv n).le]
      _ = 1 / (n + 1) * ‖d n • v n‖ := by rw [norm_smul]; ring
      _ ≤ 1 / (n + 1) := mul_le_of_le_one_right (by positivity) (hdlt n).le
  obtain ⟨y, ψ, -, hy, hAy⟩ := hS.exists_subseq_tendsto_of_tendsto hμ (fun n ↦ (hdlt n).le)
    (squeeze_zero_norm hAu tendsto_one_div_add_atTop_nhds_zero_nat)
  have hlim : Tendsto (fun n ↦ 2 * ‖d (ψ n) • v (ψ n) - y‖) atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hy).const_mul 2)
  have hge (n : ℕ) : ‖k‖⁻¹ ≤ ‖d n • v n‖ := by simpa using hdge n
  have hcone (n : ℕ) : ‖d (ψ n) • v (ψ n)‖ ≤ 2 * ‖d (ψ n) • v (ψ n) - y‖ :=
    Submodule.norm_smul_le_two_mul_norm_smul_sub (hv (ψ n)) _ y (LinearMap.mem_ker.mpr hAy)
  have hbound : ‖k‖⁻¹ ≤ 0 := ge_of_tendsto' hlim fun n ↦ (hge (ψ n)).trans (hcone n)
  exact (not_le.mpr (inv_pos.mpr (one_pos.trans hk))) hbound

/-- **Bounded preimages**: every vector in the range of `S - μ • 1` has a preimage of norm at
most `C` times its own norm. -/
theorem exists_preimage_norm_le (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∃ C > 0, ∀ y ∈ (S - μ • 1).range, ∃ x, (S - μ • 1) x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨c, hc, hcv⟩ := hS.exists_pos_mul_norm_le hμ
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rintro - ⟨x, rfl⟩
  obtain ⟨z, hz, hxz⟩ := (S - μ • 1).isClosed_ker.exists_mem_forall_dist_le_two_mul
    ⟨0, (S - μ • 1).ker.zero_mem⟩ x
  have hAz : (S - μ • 1) z = 0 := LinearMap.mem_ker.mp hz
  have hA : (S - μ • 1) (x - z) = (S - μ • 1) x := by rw [map_sub, hAz, sub_zero]
  refine ⟨x - z, hA, ?_⟩
  rw [le_inv_mul_iff₀ hc]
  refine (hcv _ fun w hw ↦ ?_).trans_eq (congrArg norm hA)
  simpa [dist_eq_norm, sub_sub] using hxz (z + w) ((S - μ • 1).ker.add_mem hz hw)

/-- The range of `S - μ • 1` is closed when `S` is compact and `μ ≠ 0`. -/
theorem isClosed_range_sub_smul_one (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    IsClosed ((S - μ • 1).range : Set X) := by
  obtain ⟨C, hC, hpre⟩ := hS.exists_preimage_norm_le hμ
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (isBounded_range_of_tendsto v hvy)
  choose x hx hxle using fun n ↦ hpre (v n) (hv n)
  obtain ⟨z, -, -, -, hz⟩ := hS.exists_subseq_tendsto_of_tendsto hμ
    (fun n ↦ (hxle n).trans (mul_le_mul_of_nonneg_left (hB _ ⟨n, rfl⟩) hC.le))
    (by simpa [hx] using hvy)
  exact ⟨z, hz⟩

/-- Every power of `S - μ • 1` is a compact operator minus a nonzero multiple of the identity. -/
theorem exists_sub_smul_one_pow_eq (hS : IsCompactOperator S) (hμ : μ ≠ 0) (k : ℕ) :
    ∃ T : X →L[𝕜] X, IsCompactOperator T ∧ ∃ ν : 𝕜, ν ≠ 0 ∧ (S - μ • 1) ^ k = T - ν • 1 := by
  induction k with
  | zero => exact ⟨0, isCompactOperator_zero, -1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, ν, hν, h⟩ := ih
    refine ⟨T * S - μ • T - ν • S, ?_, -(ν * μ), by simp [hν, hμ], ?_⟩
    · exact ((hT.comp_clm S).sub (hT.smul μ)).sub (hS.smul ν)
    · rw [pow_succ, h, sub_mul, mul_sub, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
        mul_one, smul_mul_assoc, one_mul, smul_smul]
      module

/-- Every power of `S - μ • 1` has a finite-dimensional kernel. -/
theorem finiteDimensional_ker_pow [CompleteSpace 𝕜] (hS : IsCompactOperator S) (hμ : μ ≠ 0)
    (k : ℕ) : FiniteDimensional 𝕜 ((S - μ • 1) ^ k).ker := by
  obtain ⟨T, hT, ν, hν, h⟩ := hS.exists_sub_smul_one_pow_eq hμ k
  rw [h]
  exact hT.finiteDimensional_ker_sub_smul_one hν

/-- Every power of `S - μ • 1` has a closed range. -/
theorem isClosed_range_pow (hS : IsCompactOperator S) (hμ : μ ≠ 0) (k : ℕ) :
    IsClosed (((S - μ • 1) ^ k).range : Set X) := by
  obtain ⟨T, hT, ν, hν, h⟩ := hS.exists_sub_smul_one_pow_eq hμ k
  rw [h]
  exact hT.isClosed_range_sub_smul_one hν

/-- **Riesz's argument, increasing chains**: an increasing chain of closed subspaces `V n` with
`(S - μ • 1) (V (n + 1)) ⊆ V n` cannot increase strictly forever. -/
theorem exists_eq_succ_of_monotone (hS : IsCompactOperator S) (hμ : μ ≠ 0)
    {V : ℕ → Submodule 𝕜 X} (hV : Monotone V) (hc : ∀ n, IsClosed (V n : Set X))
    (hA : ∀ n, ∀ x ∈ V (n + 1), (S - μ • 1) x ∈ V n) : ∃ n, V (n + 1) = V n := by
  by_contra! h
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm 𝕜
  choose f hfV hfle hfsep using fun n ↦ riesz_lemma_of_norm_lt_of_lt hk (lt_add_one ‖k‖) (hc n)
    ((hV n.le_succ).lt_of_ne (h n).symm)
  obtain ⟨m, n, hmn, hlt⟩ := hS.exists_lt_dist_lt hfle (norm_pos_iff.mpr hμ)
  set y := μ⁻¹ • ((S - μ • 1) (f m) + μ • f m - (S - μ • 1) (f n)) with hy
  have hyV : y ∈ V n := (V n).smul_mem _ ((V n).sub_mem ((V n).add_mem
    (hV hmn.le (hA m _ (hfV m))) ((V n).smul_mem _ (hV (Nat.succ_le_of_lt hmn) (hfV m))))
    (hA n _ (hfV n)))
  have heq : μ • (f n - y) = S (f n) - S (f m) := by
    rw [hy, smul_sub, smul_inv_smul₀ hμ]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  refine hlt.not_ge ?_
  rw [dist_comm, dist_eq_norm, ← heq, norm_smul]
  exact le_mul_of_one_le_right (norm_nonneg μ) (hfsep n y hyV)

/-- **Riesz's argument, decreasing chains**: a decreasing chain of closed subspaces `V n` with
`(S - μ • 1) (V n) ⊆ V (n + 1)` cannot decrease strictly forever. -/
theorem exists_eq_succ_of_antitone (hS : IsCompactOperator S) (hμ : μ ≠ 0)
    {V : ℕ → Submodule 𝕜 X} (hV : Antitone V) (hc : ∀ n, IsClosed (V n : Set X))
    (hA : ∀ n, ∀ x ∈ V n, (S - μ • 1) x ∈ V (n + 1)) : ∃ n, V (n + 1) = V n := by
  by_contra! h
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm 𝕜
  choose f hfV hfle hfsep using fun n ↦ riesz_lemma_of_norm_lt_of_lt hk (lt_add_one ‖k‖)
    (hc (n + 1)) ((hV n.le_succ).lt_of_ne (h n))
  obtain ⟨m, n, hmn, hlt⟩ := hS.exists_lt_dist_lt hfle (norm_pos_iff.mpr hμ)
  set y := μ⁻¹ • ((S - μ • 1) (f n) + μ • f n - (S - μ • 1) (f m)) with hy
  have hyV : y ∈ V (m + 1) := (V (m + 1)).smul_mem _ ((V (m + 1)).sub_mem ((V (m + 1)).add_mem
    (hV (Nat.succ_le_succ hmn.le) (hA n _ (hfV n)))
    ((V (m + 1)).smul_mem _ (hV (Nat.succ_le_of_lt hmn) (hfV n)))) (hA m _ (hfV m)))
  have heq : μ • (f m - y) = S (f m) - S (f n) := by
    rw [hy, smul_sub, smul_inv_smul₀ hμ]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  refine hlt.not_ge ?_
  rw [dist_eq_norm, ← heq, norm_smul]
  exact le_mul_of_one_le_right (norm_nonneg μ) (hfsep m y hyV)

/-- **Finite ascent**: the kernels of the powers of `S - μ • 1` stop increasing. -/
theorem exists_ker_pow_eq_ker_pow_succ (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∃ p, ((S - μ • 1) ^ p).ker = ((S - μ • 1) ^ (p + 1)).ker := by
  have hmono : Monotone fun n ↦ ((S - μ • 1) ^ n).ker := monotone_nat_of_le_succ fun n x hx ↦ by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [pow_succ', mul_apply_eq_comp, hx, map_zero]
  have hstep (n : ℕ) (x : X) (hx : x ∈ ((S - μ • 1) ^ (n + 1)).ker) :
      (S - μ • 1) x ∈ ((S - μ • 1) ^ n).ker := by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    rwa [← mul_apply_eq_comp, ← pow_succ]
  obtain ⟨p, hp⟩ := hS.exists_eq_succ_of_monotone hμ hmono
    (fun n ↦ ContinuousLinearMap.isClosed_ker _) hstep
  exact ⟨p, hp.symm⟩

/-- **Finite descent**: the ranges of the powers of `S - μ • 1` stop decreasing. -/
theorem exists_range_pow_eq_range_pow_succ (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∃ q, ((S - μ • 1) ^ q).range = ((S - μ • 1) ^ (q + 1)).range := by
  have hanti : Antitone fun n ↦ ((S - μ • 1) ^ n).range := antitone_nat_of_succ_le fun n ↦ by
    rintro - ⟨x, rfl⟩
    exact ⟨(S - μ • 1) x, by simp [pow_succ]⟩
  have hstep (n : ℕ) (x : X) (hx : x ∈ ((S - μ • 1) ^ n).range) :
      (S - μ • 1) x ∈ ((S - μ • 1) ^ (n + 1)).range := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, by simp [pow_succ']⟩
  obtain ⟨q, hq⟩ := hS.exists_eq_succ_of_antitone hμ hanti (hS.isClosed_range_pow hμ) hstep
  exact ⟨q, hq.symm⟩

end IsCompactOperator
