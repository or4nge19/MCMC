/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Convex.Cone.Basic
import MCMC.ToMathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import MCMC.ToMathlib.Analysis.Normed.Algebra.Resolvent

/-!
# Operators preserving a proper cone: resolvent and approximate eigenvectors

Let `C` be a proper cone in a real Banach space `E` and `T : E →L[ℝ] E` with `MapsTo T C C`.

* For real `t > gelfandRadius T` the resolvent `(t - T)⁻¹ = ∑ₙ t⁻ⁿ⁻¹ Tⁿ` preserves `C`, and for a
  functional `f` nonnegative on `C` and `x ∈ C`, `t ↦ f ((t - T)⁻¹ x)` is antitone and dominates
  every partial sum of its series.
* If `‖(tₙ - T)⁻¹ x‖ → ∞`, the normalized resolvents are unit approximate eigenvectors in `C`:
  `tₙ yₙ - T yₙ → 0`.
* Approximate eigenvectors in `C` with `tₙ → r` accumulate at an eigenvector of `T` in `C` for `r`
  when `C ∩ sphere 0 1` is compact (finite dimension) or when `T` is compact and `r ≠ 0`.

Every Krein–Rutman theorem is then reduced to producing `x ∈ C` with `‖(tₙ - T)⁻¹ x‖ → ∞` as
`tₙ ↓ gelfandRadius T`.

## Main statements

* `ContinuousLinearMap.hasSum_apply_resolvent`, `ContinuousLinearMap.smul_resolvent_apply_sub`
* `ProperCone.mapsTo_resolvent`
* `ProperCone.apply_resolvent_le_apply_resolvent`, `ProperCone.sum_range_le_apply_resolvent`
* `ProperCone.exists_approx_eigenvector_of_tendsto_norm_resolvent`
* `ProperCone.exists_eigenvector_of_isCompact_sphere_inter`
* `ProperCone.le_gelfandRadius_of_sub_smul_mem`: the Collatz–Wielandt lower bound.
* `ProperCone.exists_mem_hasEigenvector_of_pow_succ`: eigenvectors of `T ^ (k + 1)` in `C` give
  eigenvectors of `T` in `C`.

Staged for a new `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: no
Krein–Rutman or cone-positive resolvent statement in the pinned tree, on mathlib master, or in an
open mathlib PR (`gh pr list --search "Krein"`, `"positive operator"`, `"ProperCone"`).
-/

open Filter Metric Set Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {T : E →L[ℝ] E}
  {t : ℝ}

/-- The Neumann series of `(t - T)⁻¹ x`, read through a functional. -/
theorem hasSum_apply_resolvent (ht : gelfandRadius T < t) (f : StrongDual ℝ E) (x : E) :
    HasSum (fun n : ℕ ↦ (t ^ (n + 1))⁻¹ * f ((T ^ n) x)) (f (resolvent T t x)) := by
  have ht' : gelfandRadius T < ‖t‖ := ht.trans_le (Real.le_norm_self t)
  simpa using ((hasSum_resolvent_of_gelfandRadius_lt ht').mapL
    (ContinuousLinearMap.apply ℝ E x)).mapL f

/-- `(t - T) (t - T)⁻¹ x = x` beyond the Gelfand radius. -/
theorem smul_resolvent_apply_sub (ht : gelfandRadius T < t) (x : E) :
    t • resolvent T t x - T (resolvent T t x) = x := by
  have ht' : gelfandRadius T < ‖t‖ := ht.trans_le (Real.le_norm_self t)
  simpa [Algebra.algebraMap_eq_smul_one, sub_mul] using
    congr($(algebraMap_sub_mul_resolvent_of_gelfandRadius_lt ht') x)

end ContinuousLinearMap

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convergent series of points of a proper cone sums into the cone. -/
theorem hasSum_mem (C : ProperCone ℝ E) {f : ℕ → E} {x : E} (hf : HasSum f x)
    (hfC : ∀ n, f n ∈ C) : x ∈ C :=
  C.isClosed.mem_of_tendsto hf.tendsto_sum_nat (.of_forall fun _ ↦ C.sum_mem fun n _ ↦ hfC n)

section Complete

variable [CompleteSpace E] {T : E →L[ℝ] E} {t s : ℝ}

/-- **Positivity of the resolvent**: for `T` preserving a proper cone `C` and real
`t > gelfandRadius T`, the resolvent `(t - T)⁻¹ = ∑ t⁻ⁿ⁻¹ Tⁿ` preserves `C`. -/
theorem mapsTo_resolvent (C : ProperCone ℝ E) (hT : MapsTo T C C) (ht : gelfandRadius T < t) :
    MapsTo (resolvent T t : E →L[ℝ] E) C C := fun x hx ↦ by
  have ht0 : 0 ≤ t := (gelfandRadius_nonneg T).trans ht.le
  have ht' : gelfandRadius T < ‖t‖ := ht.trans_le (Real.le_norm_self t)
  refine C.hasSum_mem ((hasSum_resolvent_of_gelfandRadius_lt ht').mapL
    (ContinuousLinearMap.apply ℝ E x)) fun n ↦ ?_
  simpa [FunLike.coe_pow_eq_iterate] using
    C.smul_mem (hT.iterate n hx) (inv_nonneg.2 (pow_nonneg ht0 (n + 1)))

variable {C : ProperCone ℝ E} {f : StrongDual ℝ E} {x : E}

/-- Read through a functional nonnegative on `C`, the resolvent on `C` decreases in `t`. -/
theorem apply_resolvent_le_apply_resolvent (hT : MapsTo T C C) (hf : ∀ y ∈ C, 0 ≤ f y)
    (hx : x ∈ C) (ht : gelfandRadius T < t) (hts : t ≤ s) :
    f (resolvent T s x) ≤ f (resolvent T t x) := by
  have ht0 : 0 < t := (gelfandRadius_nonneg T).trans_lt ht
  refine hasSum_le (fun n ↦ mul_le_mul_of_nonneg_right ?_ ?_)
    (T.hasSum_apply_resolvent (ht.trans_le hts) f x) (T.hasSum_apply_resolvent ht f x)
  · exact inv_anti₀ (pow_pos ht0 _) (pow_le_pow_left₀ ht0.le hts _)
  · simpa [FunLike.coe_pow_eq_iterate] using hf _ (hT.iterate n hx)

/-- Read through a functional nonnegative on `C`, the resolvent on `C` dominates every partial
sum of its Neumann series. -/
theorem sum_range_le_apply_resolvent (hT : MapsTo T C C) (hf : ∀ y ∈ C, 0 ≤ f y) (hx : x ∈ C)
    (ht : gelfandRadius T < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, (t ^ (n + 1))⁻¹ * f ((T ^ n) x) ≤ f (resolvent T t x) := by
  have ht0 : 0 ≤ t := (gelfandRadius_nonneg T).trans ht.le
  refine sum_le_hasSum _ (fun n _ ↦ mul_nonneg (by positivity) ?_) (T.hasSum_apply_resolvent ht f x)
  simpa [FunLike.coe_pow_eq_iterate] using hf _ (hT.iterate n hx)

/-- **Resolvent blow-up gives approximate eigenvectors**: if `‖(tₙ - T)⁻¹ x‖ → ∞` with
`x ∈ C`, the normalized resolvents are unit vectors of `C` with `tₙ yₙ - T yₙ → 0`. -/
theorem exists_approx_eigenvector_of_tendsto_norm_resolvent (hT : MapsTo T C C) (hx : x ∈ C)
    {t : ℕ → ℝ} (htr : ∀ n, gelfandRadius T < t n)
    (hR : Tendsto (fun n ↦ ‖resolvent T (t n) x‖) atTop atTop) :
    ∃ y : ℕ → E, (∀ n, y n ∈ C) ∧ (∀ n, ‖y n‖ = 1) ∧
      Tendsto (fun n ↦ t n • y n - T (y n)) atTop (𝓝 0) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact not_tendsto_const_atTop (0 : ℝ) _ (by simpa using hR)
  have hR0 (n : ℕ) : resolvent T (t n) x ≠ 0 := fun h ↦ hx0 <| by
    simpa [h] using (T.smul_resolvent_apply_sub (htr n) x).symm
  refine ⟨fun n ↦ ‖resolvent T (t n) x‖⁻¹ • resolvent T (t n) x,
    fun n ↦ C.smul_mem (C.mapsTo_resolvent hT (htr n) hx) (by positivity),
    fun n ↦ by simp [norm_smul, hR0 n], ?_⟩
  have h₀ : Tendsto (fun n ↦ ‖resolvent T (t n) x‖⁻¹ • x) atTop (𝓝 0) := by
    simpa using hR.inv_tendsto_atTop.smul_const x
  refine h₀.congr fun n ↦ ?_
  rw [map_smul, smul_comm, ← smul_sub, T.smul_resolvent_apply_sub (htr n)]

end Complete

/-- **Approximate eigenvectors, compact section**: if `C ∩ sphere 0 1` is compact (e.g. in finite
dimension), unit approximate eigenvectors `tₙ yₙ - T yₙ → 0` in `C` with `tₙ → r` accumulate at an
eigenvector of `T` in `C` with eigenvalue `r`. -/
theorem exists_eigenvector_of_isCompact_sphere_inter (C : ProperCone ℝ E)
    (hC : IsCompact ((C : Set E) ∩ sphere 0 1)) (T : E →L[ℝ] E) {r : ℝ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 r)) {y : ℕ → E} (hyC : ∀ n, y n ∈ C) (hy : ∀ n, ‖y n‖ = 1)
    (h : Tendsto (fun n ↦ t n • y n - T (y n)) atTop (𝓝 0)) :
    ∃ x ∈ C, ‖x‖ = 1 ∧ T x = r • x := by
  obtain ⟨x, ⟨hxC, hx⟩, φ, hφ, hlim⟩ :=
    hC.tendsto_subseq (x := y) fun n ↦ ⟨hyC n, by simpa using hy n⟩
  refine ⟨x, hxC, by simpa using hx, ?_⟩
  have h₁ : Tendsto (fun n ↦ t (φ n) • y (φ n) - T (y (φ n))) atTop (𝓝 (r • x - T x)) :=
    ((ht.comp hφ.tendsto_atTop).smul hlim).sub ((T.continuous.tendsto x).comp hlim)
  exact (sub_eq_zero.1 (tendsto_nhds_unique h₁ (h.comp hφ.tendsto_atTop))).symm

/-- **Eigenvectors of a power**: if `x ∈ C \ {0}` is an eigenvector of `T ^ (k + 1)` for
`r ^ (k + 1)`, `r > 0`, then `∑_{j ≤ k} r⁻ʲ • Tʲ x` is an eigenvector of `T` for `r` in `C`; it is
nonzero because `C` is salient. -/
theorem exists_mem_hasEigenvector_of_pow_succ {C : ProperCone ℝ E}
    (hC : (C : ConvexCone ℝ E).Salient)
    {T : E →L[ℝ] E} (hT : MapsTo T C C) {r : ℝ} (hr : 0 < r) {k : ℕ} {x : E} (hxC : x ∈ C)
    (hx : Module.End.HasEigenvector ((T ^ (k + 1) : E →L[ℝ] E) : Module.End ℝ E) (r ^ (k + 1))
      x) :
    ∃ y ∈ C, Module.End.HasEigenvector (T : Module.End ℝ E) r y := by
  have hTk : (T ^ (k + 1)) x = r ^ (k + 1) • x := hx.apply_eq_smul
  have hstep (j : ℕ) : T ((T ^ j) x) = (T ^ (j + 1)) x := by
    rw [pow_succ', mul_apply_eq_comp]
  have hmem (j : ℕ) : (r ^ j)⁻¹ • (T ^ j) x ∈ C :=
    C.smul_mem (by simpa [FunLike.coe_pow_eq_iterate] using hT.iterate j hxC) (by positivity)
  set z := ∑ j ∈ Finset.range k, (r ^ (j + 1))⁻¹ • (T ^ (j + 1)) x
  have hz : z ∈ C := C.sum_mem fun j _ ↦ hmem (j + 1)
  have hy : ∑ j ∈ Finset.range (k + 1), (r ^ j)⁻¹ • (T ^ j) x = z + x := by
    rw [Finset.sum_range_succ']
    simp [z]
  have hTy : T (∑ j ∈ Finset.range (k + 1), (r ^ j)⁻¹ • (T ^ j) x) =
      r • ∑ j ∈ Finset.range (k + 1), (r ^ j)⁻¹ • (T ^ j) x := by
    simp only [map_sum, map_smul, hstep]
    rw [Finset.sum_range_succ, Finset.smul_sum, Finset.sum_range_succ', hTk, pow_zero, inv_one,
      one_smul, pow_zero, one_apply_eq_self]
    congr 1
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_smul]
      congr 1
      field_simp
      ring
    · rw [smul_smul]
      congr 1
      field_simp
      ring
  refine ⟨z + x, C.add_mem hz hxC, Module.End.hasEigenvector_iff.2 ⟨?_, fun h0 ↦ ?_⟩⟩
  · rw [Module.End.mem_eigenspace_iff, ← hy]
    exact hTy
  · refine hC x hxC hx.2 ?_
    rw [show -x = z from (neg_eq_of_add_eq_zero_left h0)]
    exact hz

/-- **Collatz–Wielandt lower bound** for cones: a nonzero `y ∈ C` with `T y - c • y ∈ C`, `c ≥ 0`,
forces `c ≤ gelfandRadius T` when `C` is salient and `T C ⊆ C`: `Tⁿ y - cⁿ • y ∈ C`, and a
functional positive at `y` turns this into `cⁿ ≲ ‖Tⁿ‖`. -/
theorem le_gelfandRadius_of_sub_smul_mem {C : ProperCone ℝ E}
    (hC : (C : ConvexCone ℝ E).Salient) {T : E →L[ℝ] E} (hT : MapsTo T C C) {y : E}
    (hyC : y ∈ C) (hy0 : y ≠ 0) {c : ℝ} (hc : 0 ≤ c) (hcy : T y - c • y ∈ C) :
    c ≤ gelfandRadius T := by
  have hn (n : ℕ) : (T ^ n) y - c ^ n • y ∈ C := by
    induction n with
    | zero => simp
    | succ n ih =>
      have heq : (T ^ (n + 1)) y - c ^ (n + 1) • y =
          T ((T ^ n) y - c ^ n • y) + c ^ n • (T y - c • y) := by
        rw [pow_succ', mul_apply_eq_comp, pow_succ]
        simp only [map_sub, map_smul, smul_sub, mul_smul, smul_comm (c ^ n) c]
        abel
      rw [heq]
      exact C.add_mem (hT ih) (C.smul_mem hcy (pow_nonneg hc n))
  obtain ⟨f, hfC, hfy⟩ := exists_strongDual_pos_of_salient hC hyC hy0
  have hf : 0 < ‖f‖ * ‖y‖ := mul_pos (norm_pos_iff.2 fun h ↦ by simp [h] at hfy)
    (norm_pos_iff.2 hy0)
  refine le_gelfandRadius_of_mul_pow_le_norm_pow hc (div_pos hfy hf) fun n ↦ ?_
  have h₁ := hfC _ (hn n)
  rw [map_sub, map_smul, smul_eq_mul, sub_nonneg] at h₁
  rw [div_mul_eq_mul_div, div_le_iff₀ hf, mul_comm, ← mul_assoc]
  calc c ^ n * f y ≤ f ((T ^ n) y) := h₁
    _ ≤ ‖f‖ * ‖(T ^ n) y‖ := (Real.le_norm_self _).trans (f.le_opNorm _)
    _ ≤ ‖f‖ * (‖T ^ n‖ * ‖y‖) := by gcongr; exact (T ^ n).le_opNorm y
    _ = ‖T ^ n‖ * ‖f‖ * ‖y‖ := by ring

end ProperCone
