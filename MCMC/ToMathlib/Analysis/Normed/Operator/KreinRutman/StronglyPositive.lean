/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Convex.Cone.Basic
import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.Basic
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Compact
import MCMC.ToMathlib.Analysis.Normed.Operator.SpectralGap

/-!
# Krein–Rutman for strongly positive operators

Let `C` be a salient proper cone with nonempty interior in a real Banach space and `T` an operator
with `T (C \ {0}) ⊆ interior C` (*strongly positive*) which is compact, or more generally
quasi-compact: `gelfandRadius (T ^ n - K) < gelfandRadius T ^ n` for a compact `K` and `n ≠ 0`.
Write `r = gelfandRadius T`. Bourbaki, *Théories spectrales*, III §6, Proposition 8 (compact `T`):

* a) `r > 0` and `T x₀ = r • x₀` for some `x₀ ∈ interior C`; the transpose has an eigenfunctional
  `ℓ` for `r`, positive on `C \ {0}`, with `ℓ x₀ = 1`;
* the **spectral gap** `gelfandRadius (T - r • P) < r`, `P = ℓ.smulRight x₀` (the projection
  `y ↦ ℓ y • x₀`). With `SpectralGap.lean` it gives b) `maxGenEigenspace T r = ℝ ∙ x₀`,
  c) `‖μ‖ < r` for every complex spectral value `μ ≠ r`, d) `x₀ ∈ F` for every closed
  `T`-invariant subspace `F` meeting `C \ {0}` (Bourbaki states d) for all subspaces, which fails
  for non-closed ones), uniqueness of eigenvectors in `C`, and `(r⁻¹ T)ⁿ → P`.

The same holds when `T` preserves `C` and only a power `T ^ k` is strongly positive and
(quasi-)compact (Bourbaki's Corollaire; primitive operators).

## Proof of the gap

`S = T - r P` is quasi-compact with the same compact part: `Sⁿ - (K - rⁿ P) = Tⁿ - K`. A spectral
value `μ` of `S_ℂ` with `‖μ‖ ≥ r` is therefore a pole of the resolvent, hence an eigenvalue
(`IsCompactOperator.hasEigenvalue_of_gelfandRadius_pow_sub_lt`; the Fredholm alternative for compact
`T`); `ℓ_ℂ S_ℂ = 0` puts its eigenvector `v` in `ker ℓ_ℂ`, so `T_ℂ v = μ v` and `‖μ‖ = r`.
Then `K = {re (c • v) | ‖c‖ = 1}` is a compact subset of `ker ℓ` which `r⁻¹ T` maps onto itself.
Strong positivity forbids such a set (`subset_singleton_zero_of_subset_image`): at the largest `s`
with `x₀ + s K ⊆ C`, the image `x₀ + s K = r⁻¹ T (x₀ + s K)` lies in the interior of `C`, so `s` was
not the largest. This replaces Bourbaki's Lemme 6, the gauge argument on the finite-dimensional
peripheral subspace.

## Main statements

* `ProperCone.pos_of_comp_eq_smul`: Bourbaki's Lemme 5.
* `ProperCone.gelfandRadius_pos_of_mapsTo_interior`: strong positivity forces `r > 0`.
* `ProperCone.subset_singleton_zero_of_subset_image`: no peripheral orbit in `ker ℓ`.
* `ProperCone.gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt`: the spectral gap.
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt`:
  **Krein–Rutman, strongly positive quasi-compact case** (Proposition 8).
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_gelfandRadius_pow_sub_lt`: the
  same when only `T ^ k` is strongly positive and quasi-compact (Corollaire).
* `…_of_isCompactOperator`, `…_of_pow_of_isCompactOperator`: the compact cases.
* `ProperCone.eq_and_eq_smul_of_mem_of_apply_eq_smul`,
  `ProperCone.mem_of_isClosed_of_mem_invtSubmodule`: eigenvectors in `C` and closed invariant
  subspaces (Proposition 8 d)).
* `ProperCone.apply_eq_smul_and_gelfandRadius_sub_smul_smulRight_lt_of_pow`: the data for `T ^ k`
  descend to `T`.
* `ProperCone.exists_maxGenEigenspace_eq_span_of_one_add_pow_of_isCompactOperator`: **irreducible
  compact operators** (`(1 + T) ^ k` strongly positive): interior eigenvector, positive dual,
  algebraic simplicity, spectral gap of `1 + T`.

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: no
strongly positive Krein–Rutman, spectral-gap or Perron–Frobenius-for-cones statement in the pinned
tree, on mathlib master, or in an open mathlib PR.
-/

open Filter Metric Set Topology TaylorComplexification

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ProperCone ℝ E}
  {T : E →L[ℝ] E} {ℓ : StrongDual ℝ E} {x₀ : E} {r : ℝ}

/-- **Bourbaki's Lemme 5**: a nonzero eigenfunctional of the transpose of a strongly positive
operator, nonnegative on `C`, is positive on `C \ {0}`. -/
theorem pos_of_comp_eq_smul (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) (hℓ0 : ℓ ≠ 0)
    (hℓC : ∀ x ∈ C, 0 ≤ ℓ x) {μ : ℝ} (hℓT : ℓ.comp T = μ • ℓ) {x : E} (hx : x ∈ C) (hx0 : x ≠ 0) :
    0 < ℓ x := by
  refine (hℓC x hx).lt_of_ne fun h ↦ ?_
  have h₁ : 0 < ℓ (T x) := pos_of_mem_interior hℓC hℓ0 (hT ⟨hx, hx0⟩)
  have h₂ : ℓ (T x) = μ * ℓ x := by simpa using congr($hℓT x)
  rw [h₂, ← h, mul_zero] at h₁
  exact lt_irrefl _ h₁

/-- **Strong positivity forces a positive Gelfand radius**: for an interior point `y`, `T y` is
interior, so `T y - c • y ∈ C` for some `c > 0` (`le_gelfandRadius_of_sub_smul_mem`). -/
theorem gelfandRadius_pos_of_mapsTo_interior [Nontrivial E] (hC : (C : ConvexCone ℝ E).Salient)
    (hCi : (interior (C : Set E)).Nonempty) (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T := by
  obtain ⟨y, hy⟩ := hCi
  have hy0 : y ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    exact hC z (mem_of_zero_mem_interior hy z) hz (mem_of_zero_mem_interior hy (-z))
  have hT' : MapsTo T C C := fun x hx ↦ by
    obtain rfl | hx0 := eq_or_ne x 0
    · simp
    · exact interior_subset (hT ⟨hx, hx0⟩)
  obtain ⟨c, hc, -, hcy⟩ := exists_pos_add_smul_mem_of_mem_interior (hT ⟨interior_subset hy, hy0⟩) y
  exact hc.trans_le (le_gelfandRadius_of_sub_smul_mem hC hT' (interior_subset hy) hy0 hc.le hcy)

/-- One step of strong positivity: if `x₀ + s • y ∈ C` with `ℓ y = 0`, then
`x₀ + s • (r⁻¹ • T y)` is an interior point of `C`. -/
theorem add_smul_inv_smul_mem_interior (hT : MapsTo T ((C : Set E) \ {0}) (interior C))
    (hr : 0 < r) (hTx₀ : T x₀ = r • x₀) (hℓx₀ : ℓ x₀ = 1) {y : E} (hℓy : ℓ y = 0) {s : ℝ}
    (hmem : x₀ + s • y ∈ C) : x₀ + s • (r⁻¹ • T y) ∈ interior (C : Set E) := by
  have hne : x₀ + s • y ≠ 0 := fun h ↦ by simpa [hℓy, hℓx₀] using congr(ℓ $h)
  convert smul_mem_interior (inv_pos.2 hr) (hT ⟨hmem, hne⟩) using 1
  simp [smul_add, hTx₀, smul_smul, inv_mul_cancel₀ hr.ne', smul_comm s r⁻¹]

/-- Along a nonzero direction `y` with `ℓ y = 0`, only boundedly many shifts `x₀ + s • y` stay in
`C` when `ℓ` is positive on `C \ {0}`. -/
theorem bddAbove_setOf_add_smul_mem (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x) {y : E} (hy : y ≠ 0)
    (hℓy : ℓ y = 0) : BddAbove {s : ℝ | 0 ≤ s ∧ x₀ + s • y ∈ C} := by
  by_contra hb
  rw [not_bddAbove_iff] at hb
  choose s hs hlt using fun n : ℕ ↦ hb n
  have hs0 (n : ℕ) : 0 < s n := (Nat.cast_nonneg n).trans_lt (hlt n)
  have hlim : Tendsto (fun n ↦ (s n)⁻¹ • x₀ + y) atTop (𝓝 y) := by
    simpa using ((tendsto_atTop_mono (fun n ↦ (hlt n).le)
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop.smul_const x₀).add_const y
  have hmem (n : ℕ) : (s n)⁻¹ • x₀ + y ∈ C := by
    have h := C.smul_mem (hs n).2 (inv_nonneg.2 (hs0 n).le)
    rwa [smul_add, smul_smul, inv_mul_cancel₀ (hs0 n).ne', one_smul] at h
  exact (hℓ y (C.isClosed.mem_of_tendsto hlim (.of_forall hmem)) hy).ne' hℓy

/-- **No peripheral orbit in `ker ℓ`**: for a strongly positive `T` with the Krein–Rutman data,
a compact subset of `ker ℓ` contained in its image under `r⁻¹ • T` is `{0}` (or empty). -/
theorem subset_singleton_zero_of_subset_image (hT : MapsTo T ((C : Set E) \ {0}) (interior C))
    (hr : 0 < r) (hx₀ : x₀ ∈ interior (C : Set E)) (hTx₀ : T x₀ = r • x₀)
    (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x) (hℓx₀ : ℓ x₀ = 1) {K : Set E} (hK : IsCompact K)
    (hKℓ : ∀ y ∈ K, ℓ y = 0) (hKT : K ⊆ (fun y ↦ r⁻¹ • T y) '' K) : K ⊆ {0} := by
  intro y₁ hy₁
  by_contra hy₁0
  set S : Set ℝ := Ici 0 ∩ ⋂ y ∈ K, (fun s : ℝ ↦ x₀ + s • y) ⁻¹' C
  have hSc : IsClosed S :=
    isClosed_Ici.inter (isClosed_biInter fun y _ ↦ C.isClosed.preimage (by fun_prop))
  have h0 : (0 : ℝ) ∈ S :=
    ⟨mem_Ici.2 le_rfl, mem_iInter₂.2 fun y _ ↦ by simpa using interior_subset hx₀⟩
  have hbdd : BddAbove S := by
    refine (bddAbove_setOf_add_smul_mem hℓ (x₀ := x₀) hy₁0 (hKℓ y₁ hy₁)).mono fun s hs ↦ ?_
    exact ⟨hs.1, mem_iInter₂.1 hs.2 y₁ hy₁⟩
  have hs₀ : sSup S ∈ S := hSc.csSup_mem ⟨0, h0⟩ hbdd
  have hint (y : E) (hy : y ∈ K) : x₀ + sSup S • y ∈ interior (C : Set E) := by
    obtain ⟨y', hy', rfl⟩ := hKT hy
    exact add_smul_inv_smul_mem_interior hT hr hTx₀ hℓx₀ (hKℓ y' hy') (mem_iInter₂.1 hs₀.2 y' hy')
  obtain ⟨ε, hε, hεK⟩ := (hK.image (by fun_prop : Continuous fun y ↦ x₀ + sSup S • y)
    ).exists_thickening_subset_open isOpen_interior (by rintro _ ⟨y, hy, rfl⟩; exact hint y hy)
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  have hδ : 0 < ε / (2 * R) := by positivity
  have hdist (y : E) (hy : y ∈ K) :
      dist (x₀ + (sSup S + ε / (2 * R)) • y) (x₀ + sSup S • y) < ε := by
    rw [dist_eq_norm, add_smul, add_sub_add_left_eq_sub, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hδ.le]
    calc ε / (2 * R) * ‖y‖ ≤ ε / (2 * R) * R := by gcongr; exact hKR y hy
      _ < ε := by field_simp; linarith
  have hmem : sSup S + ε / (2 * R) ∈ S := ⟨add_nonneg hs₀.1 hδ.le, mem_iInter₂.2 fun y hy ↦
    interior_subset (s := (C : Set E)) (hεK (mem_thickening_iff.2 ⟨_, ⟨y, hy, rfl⟩, hdist y hy⟩))⟩
  linarith [le_csSup hbdd hmem]

/-- **Closed invariant subspaces** (Bourbaki TS III §6 Prop. 8 d), for closed subspaces): given
Krein–Rutman data with a spectral gap, every closed `T`-invariant subspace meeting `C \ {0}`
contains `x₀`. -/
theorem mem_of_isClosed_of_mem_invtSubmodule (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {F : Submodule ℝ E}
    (hF : IsClosed (F : Set E)) (hTF : F ∈ Module.End.invtSubmodule (T : Module.End ℝ E))
    {y : E} (hyF : y ∈ F) (hyC : y ∈ C) (hy0 : y ≠ 0) : x₀ ∈ F := by
  have h := F.smul_mem (ℓ y)⁻¹
    (ContinuousLinearMap.smul_mem_of_isClosed_of_mem_invtSubmodule hTx₀ hℓT hℓx₀ hgap hF hTF hyF)
  rwa [smul_smul, inv_mul_cancel₀ (hℓ y hyC hy0).ne', one_smul] at h

variable [CompleteSpace E]

/-- **Eigenvectors in the cone** (Bourbaki TS III §6 Prop. 8 d)): given the Krein–Rutman data with
a spectral gap, every eigenvector of `T` in `C` is `ℓ y • x₀`, for the eigenvalue `r`. -/
theorem eq_and_eq_smul_of_mem_of_apply_eq_smul (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x)
    (hgap : gelfandRadius (T - r • ℓ.smulRight x₀) < r) {y : E} (hyC : y ∈ C) (hy0 : y ≠ 0)
    {μ : ℝ} (hTy : T y = μ • y) : μ = r ∧ y = ℓ y • x₀ := by
  have hμ : μ = r := by
    refine mul_right_cancel₀ (hℓ y hyC hy0).ne' ?_
    simpa [hTy] using congr($hℓT y)
  subst hμ
  have hy : y ∈ Module.End.maxGenEigenspace (T : Module.End ℝ E) μ :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hTy)
  rw [ContinuousLinearMap.maxGenEigenspace_eq_span_of_gelfandRadius_sub_lt hTx₀ hℓT hℓx₀ hgap,
    Submodule.mem_span_singleton] at hy
  obtain ⟨c, rfl⟩ := hy
  simp [hℓx₀]

/-- **Descent from a power**: Krein–Rutman data with a spectral gap for `T ^ k`, `k ≠ 0`, and an
eigenvector of `T` in `C` for `r` give Krein–Rutman data with a spectral gap for `T`. -/
theorem apply_eq_smul_and_gelfandRadius_sub_smul_smulRight_lt_of_pow (hr : 0 < r) {k : ℕ}
    (hk : k ≠ 0) (hTkx₀ : (T ^ k) x₀ = r ^ k • x₀) (hℓTk : ℓ.comp (T ^ k) = r ^ k • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x)
    (hgapk : gelfandRadius (T ^ k - r ^ k • ℓ.smulRight x₀) < r ^ k) {x₁ : E} (hx₁C : x₁ ∈ C)
    (hx₁ : Module.End.HasEigenvector (T : Module.End ℝ E) r x₁) :
    T x₀ = r • x₀ ∧ ℓ.comp T = r • ℓ ∧ gelfandRadius (T - r • ℓ.smulRight x₀) < r := by
  have hTkx₁ : (T ^ k) x₁ = r ^ k • x₁ := by
    simpa [← ContinuousLinearMap.toLinearMap_pow] using hx₁.pow_apply k
  obtain ⟨c, hc, hx₁₀⟩ : ∃ c, 0 < c ∧ x₁ = c • x₀ :=
    ⟨ℓ x₁, hℓ x₁ hx₁C hx₁.2,
      (eq_and_eq_smul_of_mem_of_apply_eq_smul hTkx₀ hℓTk hℓx₀ hℓ hgapk hx₁C hx₁.2 hTkx₁).2⟩
  have hTx₀ : T x₀ = r • x₀ := by
    have h : T x₁ = r • x₁ := hx₁.apply_eq_smul
    rw [hx₁₀, map_smul, smul_comm r c] at h
    exact smul_right_injective E hc.ne' h
  have hℓT : ℓ.comp T = r • ℓ := by
    refine sub_eq_zero.1 (ContinuousLinearMap.eq_zero_of_comp_eq_smul_of_gelfandRadius_sub_lt
      hgapk ?_ (by simp [hTx₀, hℓx₀]))
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.mul_def, ← pow_succ', pow_succ, ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.comp_assoc, hℓTk, ContinuousLinearMap.smul_comp, smul_sub,
      smul_comm r (r ^ k)]
  refine ⟨hTx₀, hℓT, lt_of_pow_lt_pow_left₀ k hr.le ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [← gelfandRadius_pow_of_ne_zero _ hk,
    ContinuousLinearMap.sub_smul_smulRight_pow_succ hTx₀ hℓT hℓx₀]
  exact hgapk

/-- **Descent from `1 + T`**: Krein–Rutman data with a spectral gap for `1 + T` and an eigenvector
of `T` in `C` for its Gelfand radius `r` give `T x₀ = r • x₀`, `ℓ ∘ T = r • ℓ`, algebraic
simplicity of `r`, and the spectral gap of `1 + T` at `1 + r`. -/
theorem apply_eq_smul_and_maxGenEigenspace_eq_span_of_one_add
    (hUx₀ : (1 + T) x₀ = gelfandRadius (1 + T) • x₀)
    (hℓU : ℓ.comp (1 + T) = gelfandRadius (1 + T) • ℓ) (hℓx₀ : ℓ x₀ = 1)
    (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x)
    (hgapU : gelfandRadius (1 + T - gelfandRadius (1 + T) • ℓ.smulRight x₀) <
      gelfandRadius (1 + T)) {y : E} (hyC : y ∈ C)
    (hy : Module.End.HasEigenvector (T : Module.End ℝ E) (gelfandRadius T) y) :
    T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧
      Module.End.maxGenEigenspace (T : Module.End ℝ E) (gelfandRadius T) = ℝ ∙ x₀ ∧
      gelfandRadius (1 + T - (1 + gelfandRadius T) • ℓ.smulRight x₀) < 1 + gelfandRadius T := by
  have hTy : T y = gelfandRadius T • y := hy.apply_eq_smul
  have hUy : (1 + T) y = (1 + gelfandRadius T) • y := by
    simp [hTy, add_smul]
  have hρ : 1 + gelfandRadius T = gelfandRadius (1 + T) :=
    (eq_and_eq_smul_of_mem_of_apply_eq_smul hUx₀ hℓU hℓx₀ hℓ hgapU hyC hy.2 hUy).1
  rw [← hρ] at hUx₀ hℓU hgapU
  have hTx₀ : T x₀ = gelfandRadius T • x₀ := by
    simp only [add_apply, one_apply_eq_self, add_smul, one_smul] at hUx₀
    exact add_left_cancel hUx₀
  have hℓT : ℓ.comp T = gelfandRadius T • ℓ := by
    ext x
    have h := congr($hℓU x)
    simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self, map_add,
      _root_.smul_apply, smul_eq_mul, add_mul, one_mul] at h
    simpa using add_left_cancel h
  have hshift : (((1 + T : E →L[ℝ] E) : Module.End ℝ E) - (1 + gelfandRadius T) • 1) =
      (T : Module.End ℝ E) - gelfandRadius T • 1 := by
    ext x
    simp [add_smul]
  have hgen : Module.End.maxGenEigenspace (T : Module.End ℝ E) (gelfandRadius T) =
      Module.End.maxGenEigenspace ((1 + T : E →L[ℝ] E) : Module.End ℝ E)
        (1 + gelfandRadius T) := by
    ext x
    simp only [Module.End.mem_maxGenEigenspace, hshift]
  exact ⟨hTx₀, hℓT, hgen.trans
    (ContinuousLinearMap.maxGenEigenspace_eq_span_of_gelfandRadius_sub_lt hUx₀ hℓU hℓx₀ hgapU),
    hgapU⟩

variable {K : E →L[ℝ] E} {n : ℕ}

/-- **Spectral gap from the absence of peripheral orbits** (data form, no cone): let
`gelfandRadius (T ^ n - K) < r ^ n` for a compact `K`, `gelfandRadius T ≤ r`, `T x₀ = r • x₀`,
`ℓ ∘ T = r • ℓ` and `ℓ x₀ = 1`. If every compact `K ⊆ ker ℓ` contained in its image under
`r⁻¹ • T` is `⊆ {0}`, then `gelfandRadius (T - r • ℓ.smulRight x₀) < r`: a peripheral eigenvector
`v` of `(T - r P)_ℂ` lies in `ker ℓ_ℂ`, and `{re (c • v) | ‖c‖ = 1}` is such a `K`. Cone positivity
enters only through the hypothesis on orbits. -/
theorem _root_.ContinuousLinearMap.gelfandRadius_sub_smul_smulRight_lt_of_forall_subset_image
    (hK : IsCompactOperator K) (hn : n ≠ 0) (hTK : gelfandRadius (T ^ n - K) < r ^ n)
    (hrT : gelfandRadius T ≤ r) (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1)
    (hno : ∀ K : Set E, IsCompact K → (∀ y ∈ K, ℓ y = 0) → K ⊆ (fun y ↦ r⁻¹ • T y) '' K →
      K ⊆ {0}) :
    gelfandRadius (T - r • ℓ.smulRight x₀) < r := by
  have hr : 0 < r := lt_of_pow_lt_pow_left₀ n ((gelfandRadius_nonneg T).trans hrT)
    (by rw [zero_pow hn]; exact (gelfandRadius_nonneg _).trans_lt hTK)
  set S := T - r • ℓ.smulRight x₀
  by_contra! hS
  have : Nontrivial E := ⟨⟨x₀, 0, fun h ↦ by simp [h] at hℓx₀⟩⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  set K' := K - r ^ (j + 1) • ℓ.smulRight x₀
  have hK' : IsCompactOperator K' := hK.sub ((ℓ.isCompactOperator_smulRight x₀).smul _)
  have hSK : S ^ (j + 1) - K' = T ^ (j + 1) - K := by
    simp only [S, K', ContinuousLinearMap.sub_smul_smulRight_pow_succ hTx₀ hℓT hℓx₀]
    abel
  obtain ⟨μ, hμσ, hμn⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (A := TaylorComplexification E →L[ℂ] TaylorComplexification E) (complexify S)
  rw [spectrum.spectralRadius_eq_gelfandRadius, gelfandRadius_complexify]
    at hμn
  have hμ : ‖μ‖ = gelfandRadius S := by
    simpa [ENNReal.toReal_ofReal (gelfandRadius_nonneg S)] using congrArg ENNReal.toReal hμn
  have hμ0 : μ ≠ 0 := fun h ↦ by
    rw [h, norm_zero] at hμ
    linarith
  have hK'c := isCompactOperator_complexify hK'
  have hSKc : gelfandRadius (complexify S ^ (j + 1) - complexify K') < ‖μ‖ ^ (j + 1) := by
    rw [← complexify_pow, ← complexify_sub, gelfandRadius_complexify, hSK, hμ]
    exact hTK.trans_le (pow_le_pow_left₀ hr.le hS _)
  obtain ⟨v, hv⟩ := (hK'c.hasEigenvalue_of_gelfandRadius_pow_sub_lt (Nat.succ_ne_zero j) hSKc
    (hK'c.eventually_notMem_spectrum_of_gelfandRadius_sub_lt
      (by rw [norm_pow]; exact hSKc)).frequently hμσ).exists_hasEigenvector
  have hSv : complexify S v = μ • v := hv.apply_eq_smul
  have hℓS : (complexifyDual ℓ).comp (complexify S) = 0 := ext_ofReal fun x ↦ by
    have h : ℓ (T x) = r * ℓ x := by simpa using congr($hℓT x)
    simp [S, complexify_sub, complexify_smul, hℓx₀, h]
  have hℓv : complexifyDual ℓ v = 0 := by
    have h := congr($hℓS v)
    rw [ContinuousLinearMap.comp_apply, hSv, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hμ0
  have hTv : complexify T v = μ • v := by
    have hTS : T = S + r • ℓ.smulRight x₀ := by simp [S]
    rw [← hSv, hTS, complexify_add]
    simp [complexify_smul, complexify_smulRight, hℓv]
  have hμT : μ ∈ spectrum ℂ (complexify T) := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.2
      ⟨Module.End.mem_eigenspace_iff.2 hTv, hv.2⟩)).mem_spectrum
  have hμle : ‖μ‖ ≤ gelfandRadius T := by
    rw [← gelfandRadius_complexify]
    exact not_lt.1 fun h ↦ hμT (mem_resolventSet_of_gelfandRadius_lt h)
  have hμr : ‖μ‖ = r := le_antisymm (hμle.trans hrT) (hS.trans hμ.ge)
  set K : Set E := (fun c : ℂ ↦ re (c • v)) '' sphere 0 1
  have hK : IsCompact K := (isCompact_sphere 0 1).image (by fun_prop)
  have hℓre : ℓ (re v) = 0 := by simpa [complexifyDual_apply] using congr_arg Complex.re hℓv
  have hℓim : ℓ (im v) = 0 := by simpa [complexifyDual_apply] using congr_arg Complex.im hℓv
  have hKℓ : ∀ y ∈ K, ℓ y = 0 := by
    rintro _ ⟨c, -, rfl⟩
    simp [re_smul, hℓre, hℓim]
  have hKT : K ⊆ (fun y ↦ r⁻¹ • T y) '' K := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨re ((c * r / μ) • v), ⟨c * r / μ, ?_, rfl⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm] at hc ⊢
      rw [norm_div, norm_mul, hc, hμr, Complex.norm_real, Real.norm_of_nonneg hr.le, one_mul,
        div_self hr.ne']
    · dsimp only
      rw [← re_complexify, map_smul, hTv, smul_smul, div_mul_cancel₀ _ hμ0,
        mul_comm c, mul_smul, re_smul (r : ℂ)]
      simp [smul_smul, hr.ne']
  have hK0 := hno _ hK hKℓ hKT
  have hre : re v = 0 := by simpa using hK0 ⟨1, by simp, rfl⟩
  have him : im v = 0 := by simpa [re_smul] using hK0 ⟨-Complex.I, by simp, rfl⟩
  exact hv.2 (TaylorComplexification.ext (by rw [hre, map_zero]) (by rw [him, map_zero]))

/-- **Spectral gap for strongly positive quasi-compact operators** (data form): with
`gelfandRadius (T ^ n - K) < r ^ n` for a compact `K`, `T x₀ = r • x₀`,
`x₀ ∈ interior C`, `ℓ ∘ T = r • ℓ`, `ℓ x₀ = 1`, `ℓ > 0` on `C \ {0}` and `gelfandRadius T ≤ r`,
the operator `T - r • ℓ.smulRight x₀` has Gelfand radius `< r`. -/
theorem gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt
    (hK : IsCompactOperator K) (hn : n ≠ 0) (hTK : gelfandRadius (T ^ n - K) < r ^ n)
    (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) (hrT : gelfandRadius T ≤ r)
    (hx₀ : x₀ ∈ interior (C : Set E)) (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x) :
    gelfandRadius (T - r • ℓ.smulRight x₀) < r :=
  ContinuousLinearMap.gelfandRadius_sub_smul_smulRight_lt_of_forall_subset_image hK hn hTK hrT
    hTx₀ hℓT hℓx₀ fun _ hK' hKℓ hKT ↦ subset_singleton_zero_of_subset_image hT
      (lt_of_pow_lt_pow_left₀ n ((gelfandRadius_nonneg T).trans hrT)
        (by rw [zero_pow hn]; exact (gelfandRadius_nonneg _).trans_lt hTK))
      hx₀ hTx₀ hℓ hℓx₀ hK' hKℓ hKT

/-- **Krein–Rutman theorem for strongly positive quasi-compact operators** (Bourbaki TS III §6,
Proposition 8, for compact `T`): if `gelfandRadius (T ^ n - K) < gelfandRadius T ^ n` for a compact
`K` and `T` maps `C \ {0}` into the interior of a salient proper cone `C` with nonempty interior,
then `r = gelfandRadius T > 0`, `T x₀ = r • x₀` with `x₀ ∈ interior C`, the transpose has an
eigenfunctional `ℓ` for `r` positive on `C \ {0}` with `ℓ x₀ = 1`, and
`gelfandRadius (T - r • ℓ.smulRight x₀) < r`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n)
    (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  have hr : 0 < gelfandRadius T := lt_of_pow_lt_pow_left₀ n (gelfandRadius_nonneg T)
    (by rw [zero_pow hn]; exact (gelfandRadius_nonneg _).trans_lt hTK)
  obtain ⟨y, hy⟩ := hCi
  have hCE : Dense (Submodule.span ℝ (C : Set E) : Set E) := by
    rw [span_eq_top_of_mem_interior hy, Submodule.top_coe]
    exact dense_univ
  have hT' : MapsTo T C C := fun x hx ↦ by
    obtain rfl | hx0 := eq_or_ne x 0
    · simp
    · exact interior_subset (hT ⟨hx, hx0⟩)
  obtain ⟨x₁, hx₁C, hx₁⟩ :=
    exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT'
  have hTx₁ : T x₁ = gelfandRadius T • x₁ := hx₁.apply_eq_smul
  have hint : T x₁ ∈ interior (C : Set E) := hT ⟨hx₁C, hx₁.2⟩
  have hx₁i : x₁ ∈ interior (C : Set E) := by
    simpa [hTx₁, smul_smul, inv_mul_cancel₀ hr.ne'] using smul_mem_interior (inv_pos.2 hr) hint
  obtain ⟨ℓ₁, hℓ₁0, hℓ₁C, hℓ₁T⟩ :=
    exists_dual_comp_eq_gelfandRadius_smul_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT'
  have hpos (x) (hx : x ∈ C) (hx0 : x ≠ 0) : 0 < ℓ₁ x :=
    pos_of_comp_eq_smul hT hℓ₁0 hℓ₁C hℓ₁T hx hx0
  have hc : 0 < ℓ₁ x₁ := hpos x₁ hx₁C hx₁.2
  set ℓ := (ℓ₁ x₁)⁻¹ • ℓ₁
  have hℓx₁ : ℓ x₁ = 1 := by simp [ℓ, inv_mul_cancel₀ hc.ne']
  have hℓT : ℓ.comp T = gelfandRadius T • ℓ := by
    simp [ℓ, ContinuousLinearMap.smul_comp, hℓ₁T, smul_comm (ℓ₁ x₁)⁻¹]
  have hℓ (x) (hx : x ∈ C) (hx0 : x ≠ 0) : 0 < ℓ x := by
    simpa [ℓ] using mul_pos (inv_pos.2 hc) (hpos x hx hx0)
  exact ⟨hr, x₁, hx₁i, ℓ, hTx₁, hℓT, hℓx₁, hℓ,
    gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt hK hn hTK hT le_rfl hx₁i hTx₁
      hℓT hℓx₁ hℓ⟩

/-- **Krein–Rutman theorem for primitive quasi-compact operators** (Bourbaki TS III §6, Corollaire
of Proposition 8, for compact `T`): if `T` preserves a salient proper cone `C` with nonempty
interior and some power `T ^ k`, `k ≠ 0`, is strongly positive and quasi-compact, the conclusions
of `exists_gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt` hold for `T`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hT : MapsTo T C C) {k : ℕ} (hk : k ≠ 0) (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius ((T ^ k) ^ n - K) < gelfandRadius (T ^ k) ^ n)
    (hTk : MapsTo (T ^ k) ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  obtain ⟨hrk, x₀, hx₀, ℓ, hTkx₀, hℓTk, hℓx₀, hℓ, hgapk⟩ :=
    exists_gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt hC hCi hK hn hTK hTk
  rw [gelfandRadius_pow_of_ne_zero T hk] at hrk hTkx₀ hℓTk hgapk
  have hr : 0 < gelfandRadius T :=
    lt_of_pow_lt_pow_left₀ k (gelfandRadius_nonneg T) (by rwa [zero_pow hk])
  have hx₀0 : x₀ ≠ 0 := fun h ↦ by simp [h] at hℓx₀
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  obtain ⟨x₁, hx₁C, hx₁⟩ := exists_mem_hasEigenvector_of_pow_succ hC hT hr (interior_subset hx₀)
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hTkx₀, hx₀0⟩)
  obtain ⟨hTx₀, hℓT, hgap⟩ := apply_eq_smul_and_gelfandRadius_sub_smul_smulRight_lt_of_pow hr hk
    hTkx₀ hℓTk hℓx₀ hℓ hgapk hx₁C hx₁
  exact ⟨hr, x₀, hx₀, ℓ, hTx₀, hℓT, hℓx₀, hℓ, hgap⟩

/-! ### Compact operators

The case `n = 1`, `K = T` of the quasi-compact theorems. -/

/-- **Spectral gap for strongly positive compact operators** (data form). -/
theorem gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator (hTc : IsCompactOperator T)
    (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) (hrT : gelfandRadius T ≤ r) (hr : 0 < r)
    (hx₀ : x₀ ∈ interior (C : Set E)) (hTx₀ : T x₀ = r • x₀) (hℓT : ℓ.comp T = r • ℓ)
    (hℓx₀ : ℓ x₀ = 1) (hℓ : ∀ x ∈ C, x ≠ 0 → 0 < ℓ x) :
    gelfandRadius (T - r • ℓ.smulRight x₀) < r :=
  gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt hTc one_ne_zero
    (by simpa using hr) hT hrT hx₀ hTx₀ hℓT hℓx₀ hℓ

/-- **Krein–Rutman theorem for strongly positive compact operators** (Bourbaki TS III §6,
Proposition 8): if a compact `T` maps `C \ {0}` into the interior of a salient proper cone `C`
with nonempty interior, then `r = gelfandRadius T > 0`, `T x₀ = r • x₀` with `x₀ ∈ interior C`, the
transpose has an eigenfunctional `ℓ` for `r` positive on `C \ {0}` with `ℓ x₀ = 1`, and
`gelfandRadius (T - r • ℓ.smulRight x₀) < r`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator [Nontrivial E]
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hTc : IsCompactOperator T) (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T :=
  exists_gelfandRadius_sub_smul_smulRight_lt_of_gelfandRadius_pow_sub_lt hC hCi hTc one_ne_zero
    (by simpa using gelfandRadius_pos_of_mapsTo_interior hC hCi hT) hT

/-- **Krein–Rutman theorem for power-compact primitive operators** (Bourbaki TS III §6, Corollaire
of Proposition 8): if `T` preserves a salient proper cone `C` with nonempty interior and some power
`T ^ k`, `k ≠ 0`, is compact and strongly positive, the conclusions of
`exists_gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator` hold for `T`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_isCompactOperator [Nontrivial E]
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hT : MapsTo T C C) {k : ℕ} (hk : k ≠ 0) (hTkc : IsCompactOperator (T ^ k))
    (hTk : MapsTo (T ^ k) ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T :=
  exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_gelfandRadius_pow_sub_lt hC hCi hT hk hTkc
    one_ne_zero (by simpa using gelfandRadius_pos_of_mapsTo_interior hC hCi hTk) hTk

/-- **Krein–Rutman theorem for irreducible compact operators**: let a compact `T` with
`gelfandRadius T > 0` preserve a salient proper cone `C` with nonempty interior, with
`(1 + T) ^ k` mapping `C \ {0}` into `interior C`. Then `r = gelfandRadius T` has an eigenvector
`x₀ ∈ interior C`, the transpose has an eigenfunctional `ℓ` for `r` positive on `C \ {0}` with
`ℓ x₀ = 1`, `r` is algebraically simple, and `1 + T` has a spectral gap at `1 + r`. The operator
`(1 + T) ^ k` is quasi-compact: `(1 + T) ^ k - 1 = (∑ᵢ (1 + T) ^ i) * T` is compact. -/
theorem exists_maxGenEigenspace_eq_span_of_one_add_pow_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hTc : IsCompactOperator T) (hT : MapsTo T C C) (hr : 0 < gelfandRadius T) {k : ℕ}
    (hk : k ≠ 0) (hTk : MapsTo ((1 + T) ^ k : E →L[ℝ] E) ((C : Set E) \ {0}) (interior C)) :
    ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      Module.End.maxGenEigenspace (T : Module.End ℝ E) (gelfandRadius T) = ℝ ∙ x₀ ∧
      gelfandRadius (1 + T - (1 + gelfandRadius T) • ℓ.smulRight x₀) < 1 + gelfandRadius T := by
  have : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim T 0, gelfandRadius_zero] at hr
    exact lt_irrefl _ hr
  obtain ⟨z, hz⟩ := hCi
  have hCE : Dense (Submodule.span ℝ (C : Set E) : Set E) := by
    rw [span_eq_top_of_mem_interior hz, Submodule.top_coe]
    exact dense_univ
  obtain ⟨y, hyC, hy⟩ :=
    exists_mem_hasEigenvector_gelfandRadius_of_isCompactOperator hC hCE hTc hT hr
  have hU : MapsTo (1 + T : E →L[ℝ] E) C C := fun x hx ↦ by simpa using C.add_mem hx (hT hx)
  have hTy : T y = gelfandRadius T • y := hy.apply_eq_smul
  have hU1 : 1 < gelfandRadius (1 + T) := (lt_add_of_pos_right 1 hr).trans_le
    (le_gelfandRadius_of_sub_smul_mem hC hU hyC hy.2 (by positivity) (by simp [hTy, add_smul]))
  have hKc : IsCompactOperator ((1 + T) ^ k - 1 : E →L[ℝ] E) := by
    rw [← geom_sum_mul, add_sub_cancel_left, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp]
    exact hTc.clm_comp _
  obtain ⟨-, x₀, hx₀, ℓ, hUx₀, hℓU, hℓx₀, hℓ, hgapU⟩ :=
    exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_gelfandRadius_pow_sub_lt hC ⟨z, hz⟩ hU hk
      hKc one_ne_zero (by
        rw [pow_one, pow_one, sub_sub_cancel, gelfandRadius_one, gelfandRadius_pow_of_ne_zero _ hk]
        exact one_lt_pow₀ hU1 hk) hTk
  obtain ⟨hTx₀, hℓT, hgen, hgap⟩ :=
    apply_eq_smul_and_maxGenEigenspace_eq_span_of_one_add hUx₀ hℓU hℓx₀ hℓ hgapU hyC hy
  exact ⟨x₀, hx₀, ℓ, hTx₀, hℓT, hℓx₀, hℓ, hgen, hgap⟩

end ProperCone
