/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Convex.Cone.FiniteDimensional
import MCMC.ToMathlib.Analysis.Normed.Operator.GelfandRadius
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.StronglyPositive

/-!
# The Krein–Rutman theorem in finite dimension

In a finite-dimensional real normed space every operator is compact, so the Krein–Rutman theorems
for compact operators apply. Let `C` be a salient generating proper cone and `T` preserve `C`.

* **Birkhoff–Vandergraft**: `gelfandRadius T` is an eigenvalue of `T` with an eigenvector in `C`,
  including `gelfandRadius T = 0`, where compactness of `T` gives nothing: there
  `f ((t - T)⁻¹ x) ≥ t⁻¹ f x` blows up as `t ↓ 0`, and the unit sphere of `C` is compact.
* **Dual Krein–Rutman**: the same for the transpose on the dual cone, which is again salient and
  generating.
* **Strongly positive and primitive operators** (Bourbaki TS III §6 Proposition 8 and Corollaire)
  are the compact theorems verbatim.

For `E = ℝⁿ` and the nonnegative orthant this is the Perron–Frobenius theorem (Bourbaki TS III §6
Théorème 5), with the eigenvector in `C` also when `gelfandRadius T = 0`.

## Main statements

* `ProperCone.exists_mem_hasEigenvector_gelfandRadius`: **Krein–Rutman in finite dimension**.
* `ProperCone.spectralRadius_eq_gelfandRadius`: the real spectral radius is the Gelfand radius.
* `ProperCone.exists_dual_comp_eq_gelfandRadius_smul`: **dual Krein–Rutman**.
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt`: strongly positive operators.
* `ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_pow`: primitive operators.
* `ProperCone.exists_maxGenEigenspace_eq_span_of_one_add_pow`: irreducible operators.

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: no
Krein–Rutman, Birkhoff–Vandergraft or cone-preserving Perron–Frobenius statement in the pinned
tree, on mathlib master, or in an open mathlib PR; the open Perron–Frobenius series (#39913–#39927)
is about matrices with the entrywise order.
-/

open Filter Metric Set Topology

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : ProperCone ℝ E} {T : E →L[ℝ] E}

/-- **Krein–Rutman theorem in finite dimension** (Birkhoff–Vandergraft): an operator preserving a
salient generating proper cone `C` has its Gelfand radius as an eigenvalue, with an eigenvector
in `C`. -/
theorem exists_mem_hasEigenvector_gelfandRadius [Nontrivial E] (hC : (C : ConvexCone ℝ E).Salient)
    (hCE : Submodule.span ℝ (C : Set E) = ⊤) (hT : MapsTo T C C) :
    ∃ x ∈ C, Module.End.HasEigenvector (T : Module.End ℝ E) (gelfandRadius T) x := by
  obtain hr | hr := (gelfandRadius_nonneg T).lt_or_eq
  · refine exists_mem_hasEigenvector_gelfandRadius_of_isCompactOperator hC ?_
      (isCompactOperator_of_locallyCompactSpace_rng T) hT hr
    rw [hCE, Submodule.top_coe]
    exact dense_univ
  obtain ⟨x, hxC, hx0⟩ : ∃ x ∈ C, x ≠ 0 := by
    by_contra! h
    exact bot_ne_top ((Submodule.span_eq_bot.2 h).symm.trans hCE)
  obtain ⟨f, hf0, hfx⟩ := exists_strongDual_pos_of_salient hC hxC hx0
  set t : ℕ → ℝ := fun n ↦ gelfandRadius T + 1 / (n + 1)
  have ht : Tendsto t atTop (𝓝 (gelfandRadius T)) := by
    simpa [t] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (gelfandRadius T)
  have htr (n : ℕ) : gelfandRadius T < t n := lt_add_of_pos_right _ Nat.one_div_pos_of_nat
  have ht0 : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr ▸ ht, .of_forall fun n ↦ hr ▸ htr n⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hfx
  have hR : Tendsto (fun n ↦ ‖resolvent T (t n) x‖) atTop atTop := by
    refine (tendsto_atTop_mono (fun n ↦ ?_)
      ((tendsto_inv_nhdsGT_zero.comp ht0).atTop_mul_const hfx)).atTop_of_const_mul₀
      (norm_pos_iff.2 hf)
    exact (by simpa using sum_range_le_apply_resolvent hT hf0 hxC (htr n) 1 :
      (t n)⁻¹ * f x ≤ f (resolvent T (t n) x)).trans ((Real.le_norm_self _).trans (f.le_opNorm _))
  obtain ⟨y, hyC, hy, hlim⟩ := exists_approx_eigenvector_of_tendsto_norm_resolvent hT hxC htr hR
  obtain ⟨z, hzC, hz, hTz⟩ := C.exists_eigenvector_of_isCompact_sphere_inter
    ((isCompact_sphere 0 1).inter_left C.isClosed) T ht hyC hy hlim
  refine ⟨z, hzC, Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hTz, ?_⟩⟩
  rintro rfl
  simp at hz

/-- In finite dimension, for `T` preserving a salient generating proper cone, the **real spectral
radius is the Gelfand radius**: `gelfandRadius T` is a real eigenvalue. -/
theorem spectralRadius_eq_gelfandRadius [Nontrivial E] (hC : (C : ConvexCone ℝ E).Salient)
    (hCE : Submodule.span ℝ (C : Set E) = ⊤) (hT : MapsTo T C C) :
    spectralRadius ℝ T = ENNReal.ofReal (gelfandRadius T) := by
  refine le_antisymm (spectralRadius_le_gelfandRadius T) ?_
  obtain ⟨_, -, hx⟩ := exists_mem_hasEigenvector_gelfandRadius hC hCE hT
  have hσ : gelfandRadius T ∈ spectrum ℝ T := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hx).mem_spectrum
  have hle : (‖gelfandRadius T‖₊ : ENNReal) ≤ spectralRadius ℝ T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℝ T) ↦ (‖k‖₊ : ENNReal)) _ hσ
  rwa [← enorm_eq_nnnorm, ← ofReal_norm, Real.norm_of_nonneg (gelfandRadius_nonneg T)] at hle

/-- **Dual Krein–Rutman in finite dimension** (Bourbaki TS III §6 no. 7, Corollaire): the
transpose of an operator preserving a salient generating proper cone has the Gelfand radius as an
eigenvalue, with an eigenfunctional nonnegative on the cone. -/
theorem exists_dual_comp_eq_gelfandRadius_smul [Nontrivial E] (hC : (C : ConvexCone ℝ E).Salient)
    (hCE : Submodule.span ℝ (C : Set E) = ⊤) (hT : MapsTo T C C) :
    ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ (∀ x ∈ C, 0 ≤ ℓ x) ∧ ℓ.comp T = gelfandRadius T • ℓ := by
  have : Nontrivial (StrongDual ℝ E) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ x (norm_ne_zero_iff.2 hx)
    exact ⟨⟨g, 0, fun h ↦ hx (norm_eq_zero.1 (by simp [h] at hg; exact hg.symm))⟩⟩
  obtain ⟨ℓ, hℓC, hℓ⟩ := exists_mem_hasEigenvector_gelfandRadius
    (salient_dual_of_span_eq_top hCE) (span_dual_eq_top_of_salient hC) (mapsTo_compL_flip_dual hT)
  refine ⟨ℓ, hℓ.2, mem_dual_topDualPairing_flip.1 hℓC, ?_⟩
  simpa [gelfandRadius_compL_flip] using hℓ.apply_eq_smul

/-- **Krein–Rutman theorem for strongly positive operators** in finite dimension (Bourbaki TS III
§6 Proposition 8): the conclusions of
`ProperCone.exists_gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt [Nontrivial E]
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hT : MapsTo T ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T :=
  exists_gelfandRadius_sub_smul_smulRight_lt_of_isCompactOperator hC hCi
    (isCompactOperator_of_locallyCompactSpace_rng T) hT

/-- **Krein–Rutman theorem for primitive operators** in finite dimension (Bourbaki TS III §6,
Corollaire of Proposition 8): if `T` preserves `C` and some power `T ^ k`, `k ≠ 0`, is strongly
positive, the conclusions of `exists_gelfandRadius_sub_smul_smulRight_lt` hold for `T`. -/
theorem exists_gelfandRadius_sub_smul_smulRight_lt_of_pow [Nontrivial E]
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hT : MapsTo T C C) {k : ℕ} (hk : k ≠ 0)
    (hTk : MapsTo (T ^ k) ((C : Set E) \ {0}) (interior C)) :
    0 < gelfandRadius T ∧ ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T :=
  exists_gelfandRadius_sub_smul_smulRight_lt_of_pow_of_isCompactOperator hC hCi hT hk
    (isCompactOperator_of_locallyCompactSpace_rng _) hTk

/-- **Krein–Rutman theorem for irreducible operators** in finite dimension (Vandergraft; for the
nonnegative orthant, Perron–Frobenius for irreducible matrices): let `T` preserve a salient proper
cone `C` with nonempty interior, with `(1 + T) ^ k` mapping `C \ {0}` into `interior C` for some
`k` (for proper cones, equivalent to irreducibility: no nontrivial `T`-invariant face). Then
`r = gelfandRadius T` has an eigenvector `x₀ ∈ interior C`, the transpose has an eigenfunctional
`ℓ` for `r` positive on `C \ {0}` with `ℓ x₀ = 1`, `r` is algebraically simple, and `1 + T` has
the spectral gap `gelfandRadius (1 + T - (1 + r) • ℓ.smulRight x₀) < 1 + r`. Unlike the primitive
case, `T` itself need not have a spectral gap: its peripheral spectrum may be a rotation group. -/
theorem exists_maxGenEigenspace_eq_span_of_one_add_pow [Nontrivial E]
    (hC : (C : ConvexCone ℝ E).Salient) (hCi : (interior (C : Set E)).Nonempty)
    (hT : MapsTo T C C) {k : ℕ} (hk : k ≠ 0)
    (hTk : MapsTo ((1 + T) ^ k : E →L[ℝ] E) ((C : Set E) \ {0}) (interior C)) :
    ∃ x₀ ∈ interior (C : Set E), ∃ ℓ : StrongDual ℝ E,
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x ∈ C, x ≠ 0 → 0 < ℓ x) ∧
      Module.End.maxGenEigenspace (T : Module.End ℝ E) (gelfandRadius T) = ℝ ∙ x₀ ∧
      gelfandRadius (1 + T - (1 + gelfandRadius T) • ℓ.smulRight x₀) < 1 + gelfandRadius T := by
  have hU : MapsTo (1 + T : E →L[ℝ] E) C C := fun x hx ↦ by simpa using C.add_mem hx (hT hx)
  obtain ⟨-, x₀, hx₀, ℓ, hUx₀, hℓU, hℓx₀, hℓ, hgapU⟩ :=
    exists_gelfandRadius_sub_smul_smulRight_lt_of_pow hC hCi hU hk hTk
  obtain ⟨y, hyC, hy⟩ := exists_mem_hasEigenvector_gelfandRadius hC
    (span_eq_top_of_mem_interior hx₀) hT
  obtain ⟨hTx₀, hℓT, hgen, hgap⟩ :=
    apply_eq_smul_and_maxGenEigenspace_eq_span_of_one_add hUx₀ hℓU hℓx₀ hℓ hgapU hyC hy
  exact ⟨x₀, hx₀, ℓ, hTx₀, hℓT, hℓx₀, hℓ, hgen, hgap⟩

end ProperCone
