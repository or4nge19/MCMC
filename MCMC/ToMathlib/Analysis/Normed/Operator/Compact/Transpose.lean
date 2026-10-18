/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Schauder's theorem: the transpose of a compact operator is compact

For seminormed spaces `E`, `F` over a locally compact nontrivially normed field `𝕜` (`ℝ`, `ℂ`,
`ℚ_[p]`, …), the transpose of `T : E →L[𝕜] F` is `f ↦ f ∘L T`, written
`(ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`.
It is compact when `T` is.

The proof is Arzelà–Ascoli. `T` maps `closedBall 0 1` into a compact `K`; the restrictions to `K`
of the functionals of norm `≤ 1` form a bounded `1`-Lipschitz family, hence a totally bounded
subset of `K →ᵇ 𝕜`; and `‖f ∘L T - g ∘L T‖ ≤ ‖c‖ * dist (f|_K) (g|_K)` for any `1 < ‖c‖`. So the
transposes of the unit ball are totally bounded, with compact closure as `StrongDual 𝕜 E` is
complete. Neither `E` nor `F` needs to be complete.

## Main statements

* `TotallyBounded.image_of_dist_le_mul`: `f '' s` is totally bounded if `g '' s` is and
  `dist (f x) (f y) ≤ K * dist (g x) (g y)` on `s`.
* `IsCompactOperator.compL_flip`: **Schauder's theorem**.

Staged for `Mathlib/Analysis/Normed/Operator/Compact/Transpose.lean` (the metric lemma for
`Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`, next to `Metric.finite_approx_of_totallyBounded`).
Searched on 2026-10-17: the pinned tree and mathlib master (`Compact/Basic.lean`,
`FiniteDimension.lean`, `FredholmAlternative.lean`) have no `IsCompactOperator` statement about
`compL`, `flip`, `dualMap`, `adjoint` or a transpose, and no `Schauder` theorem on operators.
Mathlib PRs searched for "Schauder", "compact adjoint", "transpose compact", "IsCompactOperator",
"compact operator dual": none (#43906, closed, proves `1 + c` Fredholm without the transpose).

## References

* [W. Rudin, *Functional analysis*][rudin1991], Theorem 4.19.
-/

open Metric Set
open scoped BoundedContinuousFunction NNReal

section TotallyBounded

variable {α β γ : Type*} [PseudoMetricSpace β] [PseudoMetricSpace γ]

/-- If `f` moves points of `s` at most `K` times as far as `g` does, then `f '' s` is totally
bounded as soon as `g '' s` is. -/
theorem TotallyBounded.image_of_dist_le_mul {f : α → β} {g : α → γ} {s : Set α} {K : ℝ≥0}
    (hg : TotallyBounded (g '' s))
    (hfg : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) :
    TotallyBounded (f '' s) := by
  refine totallyBounded_iff.2 fun ε hε ↦ ?_
  obtain ⟨u, hus, hu, hcover⟩ := exists_subset_image_finite_and.1
    (finite_approx_of_totallyBounded hg (ε / (K + 1)) (by positivity))
  refine ⟨f '' u, hu.image f, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hxz⟩ := mem_iUnion₂.1 (hcover (mem_image_of_mem g hx))
  refine mem_iUnion₂.2 ⟨f z, mem_image_of_mem f hz, ?_⟩
  calc dist (f x) (f z) ≤ K * dist (g x) (g z) := hfg x hx z (hus hz)
    _ ≤ K * (ε / (K + 1)) := by gcongr; exact (mem_ball.1 hxz).le
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; linarith

end TotallyBounded

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Schauder's theorem**: the transpose `f ↦ f ∘L T` of a compact operator `T` is compact. -/
theorem IsCompactOperator.compL_flip {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator ((ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T) := by
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set R : StrongDual 𝕜 F → K →ᵇ 𝕜 := fun f ↦ .mkOfCompact ((f : C(F, 𝕜)).restrict K)
  have hR : IsCompact (closure (R '' closedBall 0 1)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 r) (isCompact_closedBall 0 r) _
      ?_ ((LipschitzWith.uniformEquicontinuous _ 1 ?_).equicontinuous)
    · rintro _ x ⟨f, hf, rfl⟩
      exact mem_closedBall_zero_iff.2 ((f.le_of_opNorm_le_of_le (mem_closedBall_zero_iff.1 hf)
        (mem_closedBall_zero_iff.1 (hr x.2))).trans_eq (one_mul r))
    · rintro ⟨_, f, hf, rfl⟩
      exact (f.lipschitzWith_of_opNorm_le (by simpa using hf)).lipschitzOnWith.to_restrict
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hdist : ∀ f g : StrongDual 𝕜 F, dist ((ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T f)
      ((ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T g) ≤ ‖c‖₊ * dist (R f) (R g) := by
    intro f g
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, coe_nnnorm]
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    refine ContinuousLinearMap.opNorm_le_of_shell one_pos (by positivity) hc fun x hx₁ hx₂ ↦ ?_
    rw [div_le_iff₀ (by positivity)] at hx₁
    rw [ContinuousLinearMap.comp_apply, sub_apply, ← dist_eq_norm]
    calc dist (f (T x)) (g (T x)) ≤ dist (R f) (R g) :=
          BoundedContinuousFunction.dist_coe_le_dist (f := R f) (g := R g)
            ⟨T x, hTK (mem_image_of_mem T (mem_closedBall_zero_iff.2 hx₂.le))⟩
      _ ≤ ‖c‖ * dist (R f) (R g) * ‖x‖ := by nlinarith [dist_nonneg (x := R f) (y := R g)]
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).2
    ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, ?_⟩
  exact ((totallyBounded_closure.1 hR.totallyBounded).image_of_dist_le_mul
    fun f _ g _ ↦ hdist f g).closure.isCompact_of_isClosed isClosed_closure
