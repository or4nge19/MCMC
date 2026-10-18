/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.StronglyPositive

/-!
# Krein–Rutman for `u₀`-positive operators: cones with empty interior

The strongly positive theory needs `interior C ≠ ∅`, which fails for the positive cones of `Lᵖ`,
`ℓᵖ` (`p < ∞`) and `C₀`. Krasnosel'skii's `u₀`-positivity replaces interior points by comparison
with a fixed `u₀ ∈ C`. In the uniform form used here, `T` is bounded below on `C` and above on `E`
in the order of `u₀`:

* `ψ x • u₀ ≤ T x` for `x ∈ C`, for a functional `ψ` positive on `C \ {0}` (a Doeblin-type
  minorization);
* `T x ≤ (β * ‖x‖) • u₀` for every `x` (so `T` maps the unit ball into the order interval
  `[-β • u₀, β • u₀]`).

Integral operators `T f = ∫ k(·, t) f(t) dμ(t)` on `Lᵖ(μ)`, `μ` finite, with `0 < c₁ ≤ k ≤ c₂`
satisfy this with `u₀ = 1` and `ψ f = c₁ ∫ f` (Jentzsch); so do transfer operators with
continuous positive kernels on a compact group, and Markov kernels with two-sided Doeblin bounds.

For quasi-compact `T` (`gelfandRadius (T ^ n - K) < gelfandRadius T ^ n`, `K` compact) on a total
salient cone, the conclusions of Bourbaki's Proposition 8 follow: `r = gelfandRadius T > 0`, a
positive eigenvector `x₀ ≥ a • u₀` (`a > 0`), a transpose eigenfunctional `ℓ` positive on
`C \ {0}` with `ℓ x₀ = 1`, and the spectral gap `gelfandRadius (T - r • ℓ.smulRight x₀) < r`.

## Proof of the gap

`ContinuousLinearMap.gelfandRadius_sub_smul_smulRight_lt_of_forall_subset_image` reduces the gap
to the absence of a nonzero compact `K ⊆ ker ℓ` with `K ⊆ r⁻¹ T K`. The upper bound puts `K` in
an order interval `[-c • u₀, c • u₀]`, so `x₀ + s K ⊆ C` for small `s > 0`. At the largest such
`s`, `x₀ + s K = r⁻¹ T (x₀ + s K)` dominates `(r⁻¹ m) • u₀`, `m > 0` the minimum of `ψ` on the
compact `x₀ + s K ⊆ C \ {0}`, so `s` was not the largest
(`subset_singleton_zero_of_subset_image_of_smul_le_apply_le`). This is the interior argument of
`subset_singleton_zero_of_subset_image`, with the order unit `u₀` in place of an open ball.

## Main statements

* `ProperCone.pos_of_comp_eq_smul_of_smul_le_apply_le`: transpose eigenfunctionals are positive on
  `C \ {0}` (Lemme 5).
* `ProperCone.subset_singleton_zero_of_subset_image_of_smul_le_apply_le`: no peripheral orbit.
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le`:
  **Krein–Rutman for quasi-compact `u₀`-positive operators**, with spectral gap.
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_smul_le_apply_le`: the same
  when only `T ^ k` is quasi-compact and `u₀`-positive (primitive kernels, Doeblin on `Pᵏ`).
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le_of_isCompactOperator`:
  the compact case.

## References

* M. A. Krasnosel'skii, *Positive solutions of operator equations*, Noordhoff, 1964, §2.
* R. Jentzsch, *Über Integralgleichungen mit positivem Kern*, J. reine angew. Math. 141 (1912).

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: no
`u₀`-positivity, Jentzsch or Krein–Rutman statement for cones with empty interior in the pinned
tree, on mathlib master, or in an open mathlib PR; lean-pool `SpectralPositivity` proves Jentzsch
on `L²` for self-adjoint operators with a Hilbert-basis eigen-expansion as a hypothesis.
-/

open Filter Metric Set Topology

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ProperCone ℝ E}
  {T : E →L[ℝ] E} {ℓ ψ : StrongDual ℝ E} {x₀ u₀ : E} {r β : ℝ}

/-- The upper bound with `β` holds with `max β 0`. -/
theorem max_mul_norm_smul_sub_mem (hu₀ : u₀ ∈ C) (hup : ∀ x, (β * ‖x‖) • u₀ - T x ∈ C)
    (x : E) : (max β 0 * ‖x‖) • u₀ - T x ∈ C := by
  have heq : ((max β 0 - β) * ‖x‖) • u₀ + ((β * ‖x‖) • u₀ - T x) =
      (max β 0 * ‖x‖) • u₀ - T x := by module
  rw [← heq]
  exact C.add_mem (C.smul_mem hu₀ (mul_nonneg (sub_nonneg.2 (le_max_left β 0))
    (norm_nonneg x))) (hup x)

/-- **Lemme 5 for `u₀`-positive operators**: a nonzero transpose eigenfunctional for `r > 0`,
nonnegative on a total cone `C`, is positive on `C \ {0}`. -/
theorem pos_of_comp_eq_smul_of_smul_le_apply_le
    (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E)) (hu₀ : u₀ ∈ C)
    (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x) (hlow : ∀ x ∈ C, T x - ψ x • u₀ ∈ C)
    (hup : ∀ x, (β * ‖x‖) • u₀ - T x ∈ C) (hr : 0 < r) (hℓ0 : ℓ ≠ 0) (hℓC : ∀ x ∈ C, 0 ≤ ℓ x)
    (hℓT : ℓ.comp T = r • ℓ) {x : E} (hx : x ∈ C) (hx0 : x ≠ 0) : 0 < ℓ x := by
  have hℓT' (y : E) : ℓ (T y) = r * ℓ y := by simpa using congr($hℓT y)
  obtain ⟨z, hzC, hz⟩ := exists_mem_apply_ne_zero hCE hℓ0
  have hz' : 0 < ℓ z := (hℓC z hzC).lt_of_ne' hz
  have hu : 0 < ℓ u₀ := by
    refine (hℓC u₀ hu₀).lt_of_ne' fun h ↦ ?_
    have h₁ := hℓC _ (max_mul_norm_smul_sub_mem hu₀ hup z)
    rw [map_sub, map_smul, h, smul_zero, zero_sub, hℓT', neg_nonneg] at h₁
    exact (mul_pos hr hz').not_ge h₁
  have h₂ := hℓC _ (hlow x hx)
  rw [map_sub, map_smul, smul_eq_mul, hℓT', sub_nonneg] at h₂
  exact pos_of_mul_pos_right ((mul_pos (hψ x hx hx0) hu).trans_le h₂) hr.le

/-- **No peripheral orbit for `u₀`-positive operators**: with `T x₀ = r • x₀`, `x₀ ≥ a • u₀`
(`a > 0`), `ℓ > 0` on `C \ {0}` and `ℓ x₀ = 1`, a compact subset of `ker ℓ` contained in its image
under `r⁻¹ • T` is `⊆ {0}`. -/
theorem subset_singleton_zero_of_subset_image_of_smul_le_apply_le (hu₀ : u₀ ∈ C)
    (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x) (hlow : ∀ x ∈ C, T x - ψ x • u₀ ∈ C)
    (hup : ∀ x, (β * ‖x‖) • u₀ - T x ∈ C) (hr : 0 < r) {a : ℝ} (ha : 0 < a)
    (hx₀u : x₀ - a • u₀ ∈ C) (hTx₀ : T x₀ = r • x₀) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x)
    (hℓx₀ : ℓ x₀ = 1) {K : Set E} (hK : IsCompact K) (hKℓ : ∀ y ∈ K, ℓ y = 0)
    (hKT : K ⊆ (fun y ↦ r⁻¹ • T y) '' K) : K ⊆ {0} := by
  intro y₁ hy₁
  by_contra hy₁0
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  set M := max β 0
  have hM : 0 ≤ M := le_max_right β 0
  set c : ℝ := r⁻¹ * (M * R) + 1
  have hc : 0 < c := by positivity
  have hbound (y : E) (hy : y ∈ K) : c • u₀ + y ∈ C := by
    obtain ⟨y', hy', rfl⟩ := hKT hy
    have hy'R : ‖-y'‖ ≤ R := by rw [norm_neg]; exact hKR y' hy'
    have heq : r⁻¹ • ((M * ‖-y'‖) • u₀ - T (-y')) + (r⁻¹ * (M * (R - ‖-y'‖)) + 1) • u₀ =
        c • u₀ + r⁻¹ • T y' := by
      simp only [map_neg, sub_neg_eq_add, c]
      module
    rw [← heq]
    exact C.add_mem (C.smul_mem (max_mul_norm_smul_sub_mem hu₀ hup (-y')) (inv_pos.2 hr).le)
      (C.smul_mem hu₀ (add_nonneg (mul_nonneg (inv_pos.2 hr).le
        (mul_nonneg hM (sub_nonneg.2 hy'R))) zero_le_one))
  set S : Set ℝ := Ici 0 ∩ ⋂ y ∈ K, (fun s : ℝ ↦ x₀ + s • y) ⁻¹' C
  have hSc : IsClosed S :=
    isClosed_Ici.inter (isClosed_biInter fun y _ ↦ C.isClosed.preimage (by fun_prop))
  have hs₁ : a / c ∈ S := by
    refine ⟨mem_Ici.2 (div_pos ha hc).le, mem_iInter₂.2 fun y hy ↦ ?_⟩
    have heq : x₀ - a • u₀ + (a / c) • (c • u₀ + y) = x₀ + (a / c) • y := by
      rw [smul_add, smul_smul, div_mul_cancel₀ a hc.ne']
      abel
    rw [mem_preimage, ← heq]
    exact C.add_mem hx₀u (C.smul_mem (hbound y hy) (div_pos ha hc).le)
  have hbdd : BddAbove S := by
    refine (bddAbove_setOf_add_smul_mem hℓ (x₀ := x₀) hy₁0 (hKℓ y₁ hy₁)).mono fun s hs ↦ ?_
    exact ⟨hs.1, mem_iInter₂.1 hs.2 y₁ hy₁⟩
  have hs₀ : sSup S ∈ S := hSc.csSup_mem ⟨_, hs₁⟩ hbdd
  set s := sSup S
  have hZC (y' : E) (hy' : y' ∈ K) : x₀ + s • y' ∈ C ∧ x₀ + s • y' ≠ 0 :=
    ⟨mem_iInter₂.1 hs₀.2 y' hy', fun h ↦ by simpa [hKℓ y' hy', hℓx₀] using congr(ℓ $h)⟩
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hmin⟩ := (hK.image (by fun_prop : Continuous fun y' ↦ x₀ + s • y')
    ).exists_isMinOn ⟨_, y₁, hy₁, rfl⟩ ψ.continuous.continuousOn
  set m := ψ (x₀ + s • y₀)
  have hm : 0 < m := hψ _ (hZC y₀ hy₀).1 (hZC y₀ hy₀).2
  set δ := r⁻¹ * m / c
  have hδ : 0 < δ := by positivity
  have hmem : s + δ ∈ S := by
    refine ⟨mem_Ici.2 (add_nonneg hs₀.1 hδ.le), mem_iInter₂.2 fun y hy ↦ ?_⟩
    obtain ⟨y', hy', rfl⟩ := hKT hy
    have hz := hZC y' hy'
    have hψz : m ≤ ψ (x₀ + s • y') := hmin ⟨y', hy', rfl⟩
    have hTz : T (x₀ + s • y') - m • u₀ ∈ C := by
      have heq : T (x₀ + s • y') - ψ (x₀ + s • y') • u₀ + (ψ (x₀ + s • y') - m) • u₀ =
          T (x₀ + s • y') - m • u₀ := by module
      rw [← heq]
      exact C.add_mem (hlow _ hz.1) (C.smul_mem hu₀ (sub_nonneg.2 hψz))
    have hδc : δ * c = r⁻¹ * m := div_mul_cancel₀ _ hc.ne'
    have heq : r⁻¹ • (T (x₀ + s • y') - m • u₀) + δ • (c • u₀ + r⁻¹ • T y') =
        x₀ + (s + δ) • (r⁻¹ • T y') := by
      simp only [map_add, map_smul, hTx₀, smul_add, smul_sub, smul_smul, hδc]
      match_scalars <;> field_simp
      ring
    rw [mem_preimage, ← heq]
    exact C.add_mem (C.smul_mem hTz (inv_pos.2 hr).le) (C.smul_mem (hbound _ hy) hδ.le)
  linarith [le_csSup hbdd hmem]

/-- A lower bound `ψ x • u₀ ≤ T x` on `C` with `ψ ≥ 0` there makes `T` preserve `C`. -/
theorem mapsTo_of_forall_sub_smul_mem (hu₀ : u₀ ∈ C) (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x)
    (hlow : ∀ x ∈ C, T x - ψ x • u₀ ∈ C) : MapsTo T C C := fun x hx ↦ by
  have hψx : 0 ≤ ψ x := by
    obtain rfl | hx0 := eq_or_ne x 0
    · simp
    · exact (hψ x hx hx0).le
  simpa using C.add_mem (hlow x hx) (C.smul_mem hu₀ hψx)

variable [CompleteSpace E] {K : E →L[ℝ] E} {n : ℕ}

/-- **Krein–Rutman theorem for quasi-compact `u₀`-positive operators** (Krasnosel'skii; Jentzsch
for integral operators): let `C` be a total salient proper cone, `u₀ ∈ C`, `ψ` positive on
`C \ {0}`, and let `T` satisfy `ψ x • u₀ ≤ T x` on `C`, `T x ≤ (β * ‖x‖) • u₀` everywhere, and
`gelfandRadius (T ^ n - K) < gelfandRadius T ^ n` for a compact `K`. Then `r = gelfandRadius T > 0`,
`T x₀ = r • x₀` for some `x₀ ∈ C` with `x₀ ≥ a • u₀`, `a > 0`, the transpose has an
eigenfunctional `ℓ` for `r` positive on `C \ {0}` with `ℓ x₀ = 1`, and
`gelfandRadius (T - r • ℓ.smulRight x₀) < r`. No interior point of `C` is needed. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n) (hu₀ : u₀ ∈ C)
    (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x) (hlow : ∀ x ∈ C, T x - ψ x • u₀ ∈ C)
    (hup : ∀ x, (β * ‖x‖) • u₀ - T x ∈ C) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ C, ∃ a : ℝ, 0 < a ∧ x₀ - a • u₀ ∈ C ∧ ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  have hr : 0 < gelfandRadius T := lt_of_pow_lt_pow_left₀ n (gelfandRadius_nonneg T)
    (by rw [zero_pow hn]; exact (gelfandRadius_nonneg _).trans_lt hTK)
  have hT := mapsTo_of_forall_sub_smul_mem hu₀ hψ hlow
  obtain ⟨x₁, hx₁C, hx₁⟩ :=
    exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT
  have hTx₁ : T x₁ = gelfandRadius T • x₁ := hx₁.apply_eq_smul
  obtain ⟨ℓ₁, hℓ₁0, hℓ₁C, hℓ₁T⟩ :=
    exists_dual_comp_eq_gelfandRadius_smul_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT
  have hpos (x) (hx : x ∈ C) (hx0 : x ≠ 0) : 0 < ℓ₁ x :=
    pos_of_comp_eq_smul_of_smul_le_apply_le hCE hu₀ hψ hlow hup hr hℓ₁0 hℓ₁C hℓ₁T hx hx0
  have hc : 0 < ℓ₁ x₁ := hpos x₁ hx₁C hx₁.2
  set ℓ := (ℓ₁ x₁)⁻¹ • ℓ₁
  have hℓx₁ : ℓ x₁ = 1 := by simp [ℓ, inv_mul_cancel₀ hc.ne']
  have hℓT : ℓ.comp T = gelfandRadius T • ℓ := by
    simp [ℓ, ContinuousLinearMap.smul_comp, hℓ₁T, smul_comm (ℓ₁ x₁)⁻¹]
  have hℓ (x) (hx : x ∈ C) (hx0 : x ≠ 0) : 0 < ℓ x := by
    simpa [ℓ] using mul_pos (inv_pos.2 hc) (hpos x hx hx0)
  have ha : 0 < (gelfandRadius T)⁻¹ * ψ x₁ := mul_pos (inv_pos.2 hr) (hψ x₁ hx₁C hx₁.2)
  have hx₁u : x₁ - ((gelfandRadius T)⁻¹ * ψ x₁) • u₀ ∈ C := by
    have heq : (gelfandRadius T)⁻¹ • (T x₁ - ψ x₁ • u₀) =
        x₁ - ((gelfandRadius T)⁻¹ * ψ x₁) • u₀ := by
      rw [hTx₁, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [← heq]
    exact C.smul_mem (hlow x₁ hx₁C) (inv_pos.2 hr).le
  refine ⟨hr, x₁, hx₁C, _, ha, hx₁u, ℓ, hTx₁, hℓT, hℓx₁, hℓ, ?_⟩
  exact ContinuousLinearMap.gelfandRadius_sub_smul_smulRight_lt_of_forall_subset_image hK hn hTK
    le_rfl hTx₁ hℓT hℓx₁ fun _ hK' hKℓ hKT ↦
      subset_singleton_zero_of_subset_image_of_smul_le_apply_le hu₀ hψ hlow hup hr ha hx₁u hTx₁
        hℓ hℓx₁ hK' hKℓ hKT

/-- **Krein–Rutman theorem for primitive quasi-compact `u₀`-positive operators**: if `T` preserves
`C` and some power `T ^ k`, `k ≠ 0`, is quasi-compact and `u₀`-positive (`ψ x • u₀ ≤ T ^ k x` on
`C`, `T ^ k x ≤ (β * ‖x‖) • u₀`), the conclusions of
`exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le` hold for `T` (Doeblin-type
conditions on `Pᵏ`). -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_smul_le_apply_le
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hT : MapsTo T C C) {k : ℕ} (hk : k ≠ 0) (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius ((T ^ k) ^ n - K) < gelfandRadius (T ^ k) ^ n) (hu₀ : u₀ ∈ C)
    (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x) (hlow : ∀ x ∈ C, (T ^ k) x - ψ x • u₀ ∈ C)
    (hup : ∀ x, (β * ‖x‖) • u₀ - (T ^ k) x ∈ C) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ C, ∃ a : ℝ, 0 < a ∧ x₀ - a • u₀ ∈ C ∧ ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  obtain ⟨hrk, x₀, hx₀C, a, ha, hx₀u, ℓ, hTkx₀, hℓTk, hℓx₀, hℓ, hgapk⟩ :=
    exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le hC hCE hK hn hTK hu₀ hψ hlow
      hup
  rw [gelfandRadius_pow_of_ne_zero T hk] at hrk hTkx₀ hℓTk hgapk
  have hr : 0 < gelfandRadius T :=
    lt_of_pow_lt_pow_left₀ k (gelfandRadius_nonneg T) (by rwa [zero_pow hk])
  have hx₀0 : x₀ ≠ 0 := fun h ↦ by simp [h] at hℓx₀
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  obtain ⟨x₁, hx₁C, hx₁⟩ := exists_mem_hasEigenvector_of_pow_succ hC hT hr hx₀C
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hTkx₀, hx₀0⟩)
  obtain ⟨hTx₀, hℓT, hgap⟩ := apply_eq_smul_and_gelfandRadius_sub_smul_smulRight_lt_of_pow hr hk
    hTkx₀ hℓTk hℓx₀ hℓ hgapk hx₁C hx₁
  exact ⟨hr, x₀, hx₀C, a, ha, hx₀u, ℓ, hTx₀, hℓT, hℓx₀, hℓ, hgap⟩

/-- **Krein–Rutman theorem for compact `u₀`-positive operators**: the conclusions of
`exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le` for compact `T` and `u₀ ≠ 0`
(then `gelfandRadius T ≥ ψ u₀ > 0`). -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hTc : IsCompactOperator T) (hu₀ : u₀ ∈ C) (hu₀0 : u₀ ≠ 0)
    (hψ : ∀ x ∈ C, x ≠ 0 → 0 < ψ x) (hlow : ∀ x ∈ C, T x - ψ x • u₀ ∈ C)
    (hup : ∀ x, (β * ‖x‖) • u₀ - T x ∈ C) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ C, ∃ a : ℝ, 0 < a ∧ x₀ - a • u₀ ∈ C ∧ ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  have hr : 0 < gelfandRadius T := (hψ u₀ hu₀ hu₀0).trans_le
    (le_gelfandRadius_of_sub_smul_mem hC (mapsTo_of_forall_sub_smul_mem hu₀ hψ hlow) hu₀ hu₀0
      (hψ u₀ hu₀ hu₀0).le (hlow u₀ hu₀))
  exact exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le hC hCE hTc one_ne_zero
    (by simpa using hr) hu₀ hψ hlow hup

end ProperCone
