/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import MCMC.ToMathlib.Analysis.Normed.Algebra.ResolventPole
import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.AscentDescent
import MCMC.ToMathlib.LinearAlgebra.KerRangePow

/-!
# The Riesz–Schauder theorem

Let `S` be a compact operator on a Banach space `X` over a nontrivially normed field `𝕜`, let
`μ ≠ 0` and `A = S - μ • 1`. For all large `n`, `X = ker (A ^ n) ⊕ range (A ^ n)` with both
summands closed and `S`-invariant, and `A` maps `range (A ^ n)` bijectively onto itself (Riesz
decomposition). The continuous projection `P` onto `ker (A ^ n)` along `range (A ^ n)` is then a
spectral idempotent for `S` at `μ`, so the resolvent of `S` has at worst a pole at `μ`
(`IsIdempotentElem.meromorphicAt_resolvent`). If `μ` is in the spectrum, it is an eigenvalue
(Fredholm alternative), so `P ≠ 0` and the pole has a nonzero leading coefficient.

## Main statements

* `IsCompactOperator.eventually_ker_pow_eq_ker_pow_succ`,
  `IsCompactOperator.eventually_range_pow_eq_range_pow_succ`: ascent and descent, eventual form.
* `IsCompactOperator.eventually_isCompl_ker_pow_range_pow`,
  `IsCompactOperator.eventually_bijOn_range_pow`: the Riesz decomposition; the summands are
  closed (`ContinuousLinearMap.isClosed_ker`, `IsCompactOperator.isClosed_range_pow`) and
  `S`-invariant (`ContinuousLinearMap.ker_sub_smul_one_pow_mem_invtSubmodule`,
  `ContinuousLinearMap.range_sub_smul_one_pow_mem_invtSubmodule`).
* `Submodule.IsTopCompl.isUnit_mul_one_sub_projectionL_add`: `A * (1 - P) + P` is invertible
  when `A` is bijective on the kernel of the projection `P`.
* `IsCompactOperator.exists_isIdempotentElem_range_eq_ker_pow`: the Riesz projection.
* `IsCompactOperator.meromorphicAt_resolvent`: the resolvent is meromorphic at `μ ≠ 0`.
* `IsCompactOperator.eventually_notMem_spectrum`: nonzero spectral values are isolated.
* `IsCompactOperator.exists_tendsto_pow_smul_resolvent`: at a nonzero spectral value the resolvent
  has a pole of order `m > 0` with nonzero leading coefficient.

Staged for `Mathlib/Analysis/Normed/Operator/Compact/RieszSchauder.lean`. Searched on
2026-10-17: pinned mathlib (`v4.34.1`) and mathlib master (via `gh api`) contain only the Fredholm
alternative (`Compact/FredholmAlternative.lean`) and Fredholm operators without compact
perturbations (`Operator/Fredholm/`); `gh pr list -R leanprover-community/mathlib4` with
`--search "Riesz Schauder"`, `"Fredholm"`, `"compact operator spectrum"` finds only the closed
PR #43906 (Fredholmness and index of `1 + c` over `RCLike`), which proves neither the
decomposition nor the pole. The pole is obtained algebraically from the Riesz projection
(`MCMC/ToMathlib/Analysis/Normed/Algebra/ResolventPole.lean`), without contour integrals.
-/

open Filter Topology

/-- If the range of `g` lies in the kernel of `f`, then `f * g = 0`. -/
theorem ContinuousLinearMap.mul_eq_zero_of_range_le_ker {R M : Type*} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] {f g : M →L[R] M} (h : g.range ≤ f.ker) :
    f * g = 0 :=
  ContinuousLinearMap.ext fun x ↦ by simpa using h (LinearMap.mem_range_self (g : M →ₗ[R] M) x)

section Invariance

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (S : X →L[𝕜] X) (μ : 𝕜) (n : ℕ)

/-- `ker ((S - μ • 1) ^ n)` is `S`-invariant. -/
theorem ContinuousLinearMap.ker_sub_smul_one_pow_mem_invtSubmodule :
    ((S - μ • 1) ^ n).ker ∈ Module.End.invtSubmodule (S : Module.End 𝕜 X) :=
  ((((Commute.refl S).sub_right ((Commute.one_right S).smul_right μ)).pow_right n).map
    ContinuousLinearMap.toLinearMapRingHom).ker_mem_invtSubmodule

/-- `range ((S - μ • 1) ^ n)` is `S`-invariant. -/
theorem ContinuousLinearMap.range_sub_smul_one_pow_mem_invtSubmodule :
    ((S - μ • 1) ^ n).range ∈ Module.End.invtSubmodule (S : Module.End 𝕜 X) :=
  ((((Commute.refl S).sub_right ((Commute.one_right S).smul_right μ)).pow_right n).map
    ContinuousLinearMap.toLinearMapRingHom).range_mem_invtSubmodule

end Invariance

section Projection

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {N M : Submodule 𝕜 X}

/-- If `N` and `M` are topological complements and `A` maps `M` bijectively onto itself, then
`A * (1 - P) + P` is invertible, where `P` is the projection onto `N` along `M`. -/
theorem Submodule.IsTopCompl.isUnit_mul_one_sub_projectionL_add (h : N.IsTopCompl M)
    {A : X →L[𝕜] X} (hA : Set.BijOn A M M) :
    IsUnit (A * (1 - N.projectionL M h) + N.projectionL M h) := by
  set P := N.projectionL M h
  have hPP (x : X) : P (P x) = P x :=
    Submodule.projectionL_apply_left h ⟨P x, Submodule.projectionL_apply_mem h x⟩
  have hQ (x : X) : x - P x ∈ M :=
    (Submodule.projectionL_apply_eq_zero_iff h).mp (by rw [map_sub, hPP, sub_self])
  have hB (x : X) : (A * (1 - P) + P) x = A (x - P x) + P x := rfl
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · rw [hB] at hx
    have hPxM : P x ∈ M := by
      rw [eq_neg_of_add_eq_zero_right hx]
      exact M.neg_mem (hA.mapsTo (hQ x))
    have hPx : P x = 0 :=
      Submodule.disjoint_def.mp h.isCompl.disjoint _ (Submodule.projectionL_apply_mem h x) hPxM
    have hAx : A (x - P x) = A 0 := by rw [map_zero, ← hx, hPx, add_zero]
    have hx0 : x - P x = 0 := hA.injOn (hQ x) M.zero_mem hAx
    rwa [hPx, sub_zero] at hx0
  · obtain ⟨m, hm, hAm⟩ := hA.surjOn (hQ y)
    have hPm : P m = 0 := (Submodule.projectionL_apply_eq_zero_iff h).mpr hm
    refine ⟨P y + m, ?_⟩
    rw [hB, map_add, hPP, hPm, add_zero, add_sub_cancel_left, hAm, sub_add_cancel]

end Projection

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {S : X →L[𝕜] X} {μ : 𝕜}

/-- **Finite ascent**, eventual form: `ker ((S - μ • 1) ^ n) = ker ((S - μ • 1) ^ (n + 1))` for
all large `n`. -/
theorem eventually_ker_pow_eq_ker_pow_succ (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∀ᶠ n in atTop, ((S - μ • 1) ^ n).ker = ((S - μ • 1) ^ (n + 1)).ker := by
  obtain ⟨p, hp⟩ := hS.exists_ker_pow_eq_ker_pow_succ hμ
  filter_upwards [eventually_ge_atTop p] with n hn
  simpa only [ContinuousLinearMap.toLinearMap_pow] using
    Module.End.ker_pow_eq_ker_pow_succ_of_le (f := ((S - μ • 1 : X →L[𝕜] X) : Module.End 𝕜 X))
      (by simpa only [ContinuousLinearMap.toLinearMap_pow] using hp) hn

/-- **Finite descent**, eventual form: `range ((S - μ • 1) ^ n) = range ((S - μ • 1) ^ (n + 1))`
for all large `n`. -/
theorem eventually_range_pow_eq_range_pow_succ (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∀ᶠ n in atTop, ((S - μ • 1) ^ n).range = ((S - μ • 1) ^ (n + 1)).range := by
  obtain ⟨q, hq⟩ := hS.exists_range_pow_eq_range_pow_succ hμ
  filter_upwards [eventually_ge_atTop q] with n hn
  simpa only [ContinuousLinearMap.toLinearMap_pow] using
    Module.End.range_pow_eq_range_pow_succ_of_le
      (f := ((S - μ • 1 : X →L[𝕜] X) : Module.End 𝕜 X))
      (by simpa only [ContinuousLinearMap.toLinearMap_pow] using hq) hn

/-- **Riesz decomposition**: for all large `n`, `ker ((S - μ • 1) ^ n)` and
`range ((S - μ • 1) ^ n)` are complements. -/
theorem eventually_isCompl_ker_pow_range_pow (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∀ᶠ n in atTop, IsCompl ((S - μ • 1) ^ n).ker ((S - μ • 1) ^ n).range := by
  filter_upwards [hS.eventually_ker_pow_eq_ker_pow_succ hμ,
    hS.eventually_range_pow_eq_range_pow_succ hμ] with n hk hr
  simpa only [ContinuousLinearMap.toLinearMap_pow] using
    Module.End.isCompl_ker_pow_range_pow (f := ((S - μ • 1 : X →L[𝕜] X) : Module.End 𝕜 X))
      (by simpa only [ContinuousLinearMap.toLinearMap_pow] using hk)
      (by simpa only [ContinuousLinearMap.toLinearMap_pow] using hr)

/-- For all large `n`, `S - μ • 1` maps `range ((S - μ • 1) ^ n)` bijectively onto itself. -/
theorem eventually_bijOn_range_pow (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∀ᶠ n in atTop, Set.BijOn ⇑(S - μ • 1 : X →L[𝕜] X) (((S - μ • 1) ^ n).range : Set X)
      (((S - μ • 1) ^ n).range : Set X) := by
  filter_upwards [eventually_ge_atTop 1, hS.eventually_isCompl_ker_pow_range_pow hμ,
    hS.eventually_range_pow_eq_range_pow_succ hμ] with n hn hc hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine ⟨?_, fun x hx y hy hxy ↦ ?_, ?_⟩
  · rintro - ⟨y, rfl⟩
    exact ⟨(S - μ • 1) y,
      DFunLike.congr_fun (Commute.self_pow (S - μ • 1 : X →L[𝕜] X) (k + 1)).eq.symm y⟩
  · have hxy' : (S - μ • 1) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hk : x - y ∈ ((S - μ • 1) ^ (k + 1)).ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_succ, mul_apply_eq_comp, hxy',
        map_zero]
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint _ hk (sub_mem hx hy))
  · rintro - ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : ((S - μ • 1) ^ (k + 1)) y ∈ ((S - μ • 1) ^ (k + 1 + 1)).range :=
      hr ▸ LinearMap.mem_range_self _ y
    exact ⟨((S - μ • 1) ^ (k + 1)) z, LinearMap.mem_range_self _ z,
      (DFunLike.congr_fun (pow_succ' (S - μ • 1) (k + 1)) z).symm.trans hz⟩

variable [CompleteSpace X]

/-- **Riesz projection**: for some `n > 0` there is a continuous idempotent `P` with range
`ker ((S - μ • 1) ^ n)` and kernel `range ((S - μ • 1) ^ n)`; it commutes with `S`, and
`(S - μ • 1) * (1 - P) + P` is invertible. -/
theorem exists_isIdempotentElem_range_eq_ker_pow (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∃ n, 0 < n ∧ ∃ P : X →L[𝕜] X, IsIdempotentElem P ∧ P.range = ((S - μ • 1) ^ n).ker ∧
      P.ker = ((S - μ • 1) ^ n).range ∧ Commute S P ∧ IsUnit ((S - μ • 1) * (1 - P) + P) := by
  obtain ⟨n, hn, hc, hb⟩ := ((eventually_gt_atTop 0).and
    ((hS.eventually_isCompl_ker_pow_range_pow hμ).and (hS.eventually_bijOn_range_pow hμ))).exists
  have htc := Submodule.IsCompl.isTopCompl_of_isClosed hc ((S - μ • 1) ^ n).isClosed_ker
    (hS.isClosed_range_pow hμ n)
  have hP := Submodule.isIdempotentElem_projectionL htc
  refine ⟨n, hn, _, hP, Submodule.range_projectionL htc, Submodule.ker_projectionL htc,
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hP).mpr ⟨?_, ?_⟩).symm,
    htc.isUnit_mul_one_sub_projectionL_add hb⟩
  · rw [Submodule.range_projectionL]
    exact S.ker_sub_smul_one_pow_mem_invtSubmodule μ n
  · rw [Submodule.ker_projectionL]
    exact S.range_sub_smul_one_pow_mem_invtSubmodule μ n

/-- **Riesz–Schauder**: the resolvent of a compact operator is meromorphic at every `μ ≠ 0`. -/
theorem meromorphicAt_resolvent (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    MeromorphicAt (resolvent S) μ := by
  obtain ⟨n, -, P, hP, hr, -, hSP, hu⟩ := hS.exists_isIdempotentElem_range_eq_ker_pow hμ
  rw [← Algebra.algebraMap_eq_smul_one] at hr hu
  exact hP.meromorphicAt_resolvent hSP (ContinuousLinearMap.mul_eq_zero_of_range_le_ker hr.le) hu

/-- **Isolated spectrum**: the nonzero spectral values of a compact operator are isolated. -/
theorem eventually_notMem_spectrum (hS : IsCompactOperator S) (hμ : μ ≠ 0) :
    ∀ᶠ z in 𝓝[≠] μ, z ∉ spectrum 𝕜 S := by
  obtain ⟨n, -, P, hP, hr, -, hSP, hu⟩ := hS.exists_isIdempotentElem_range_eq_ker_pow hμ
  rw [← Algebra.algebraMap_eq_smul_one] at hr hu
  exact hP.eventually_notMem_spectrum hSP (ContinuousLinearMap.mul_eq_zero_of_range_le_ker hr.le) hu

/-- **Riesz–Schauder pole theorem**: at a nonzero spectral value `μ` of a compact operator `S`,
the resolvent has a pole of some order `m > 0` with nonzero leading coefficient `Q`. -/
theorem exists_tendsto_pow_smul_resolvent (hS : IsCompactOperator S) (hμ0 : μ ≠ 0)
    (hμ : μ ∈ spectrum 𝕜 S) :
    ∃ m : ℕ, 0 < m ∧ ∃ Q : X →L[𝕜] X, Q ≠ 0 ∧
      Tendsto (fun z ↦ (z - μ) ^ m • resolvent S z) (𝓝[≠] μ) (𝓝 Q) := by
  obtain ⟨n, hn, P, hP, hr, -, hSP, hu⟩ := hS.exists_isIdempotentElem_range_eq_ker_pow hμ0
  obtain ⟨v, hv⟩ := ((hS.hasEigenvalue_iff_mem_spectrum hμ0).mpr hμ).exists_hasEigenvector
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hSv : S v = μ • v := hv.apply_eq_smul
  have hvN : v ∈ ((S - μ • 1) ^ (k + 1)).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_succ, mul_apply_eq_comp, sub_apply,
      smul_apply, one_apply_eq_self, hSv, sub_self, map_zero]
  have hPv : P v = v := (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).mp (hr ▸ hvN)
  have hP0 : P ≠ 0 := fun h ↦
    (Module.End.hasEigenvector_iff.mp hv).2 (by rw [← hPv, h, zero_apply])
  rw [← Algebra.algebraMap_eq_smul_one] at hr hu
  exact hP.exists_tendsto_pow_smul_resolvent hSP
    (ContinuousLinearMap.mul_eq_zero_of_range_le_ker hr.le) hu hP0

end IsCompactOperator
