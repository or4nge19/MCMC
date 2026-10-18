/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Analysis.Convex.Cone.Dual
import MCMC.ToMathlib.Analysis.Normed.Algebra.GelfandFormula
import MCMC.ToMathlib.Analysis.Normed.Module.TaylorComplexification
import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.QuasiCompact
import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Basic

/-!
# The Krein–Rutman theorem for compact and quasi-compact operators

Let `C` be a total (`span C` dense) salient proper cone in a real Banach space `E` and let
`T : E →L[ℝ] E` preserve `C`. Suppose `gelfandRadius (T ^ n - K) < gelfandRadius T ^ n` for some
compact `K` and `n ≠ 0`: the essential spectral radius of `T` is below its spectral radius `r`
(quasi-compactness; for compact `T` take `n = 1`, `K = T`, which needs `r > 0`). Then `r` is an
eigenvalue of `T` with an eigenvector in `C`, an isolated point of the spectrum, and an eigenvalue
of the transpose with an eigenfunctional nonnegative on `C` (Krein–Rutman; Bourbaki, *Théories
spectrales*, III §6, Théorème 4 and Corollaire for compact `T`; Nussbaum for `r_ess < r`).

## Proof

The complexified operator `T_ℂ = TaylorComplexification.complexify T` has spectral radius `r`, so
some `λ₀` of modulus `r` is a spectral value. Since `‖λ₀‖ⁿ > gelfandRadius (T_ℂⁿ - K_ℂ)`, the
resolvent of `T_ℂ` has a pole at `λ₀` (local analytic Fredholm theorem,
`IsCompactOperator.exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt`):
`(z - λ₀)ᵐ R(z) → Q ≠ 0`. Totality gives `x ∈ C` with `Q x ≠ 0`, and salience gives `f ≥ 0` on
`C` with `f_ℂ (Q x) ≠ 0`. Positivity makes the coefficients of `f_ℂ (R(z) x) = ∑ₙ z⁻ⁿ⁻¹ f (Tⁿ x)`
nonnegative, so `‖f_ℂ (R(z) x)‖ ≤ f (R(‖z‖) x)` (`norm_complexify_apply_resolvent_le`). Along
`z = t λ₀ / r`, `t ↓ r`, the left side is `≈ ‖f_ℂ (Q x)‖ (t - r)⁻ᵐ`, so `f (R(t) x) → ∞`;
normalized real resolvents are approximate eigenvectors in `C`, which quasi-compactness turns into
an eigenvector (`exists_approx_eigenvector_of_tendsto_norm_resolvent`,
`exists_eigenvector_of_gelfandRadius_pow_sub_lt`). This needs neither Pringsheim's theorem nor the
pole at `r` itself. The dual eigenfunctional is `φ ∘ q` for the positive leading Laurent
coefficient `q` of the real resolvent at its pole `r`.

## Main statements

* `ProperCone.norm_complexify_apply_resolvent_le`: positivity of the complex resolvent.
* `ProperCone.exists_mem_apply_ofReal_ne_zero`: a nonzero complex operator is seen on a total cone.
* `ProperCone.exists_complexify_ne_zero`: the complexified dual of a salient cone separates points.
* `ProperCone.exists_mem_tendsto_norm_resolvent_of_tendsto`: resolvent blow-up from a peripheral
  pole.
* `ProperCone.exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt`:
  **Krein–Rutman for quasi-compact operators**;
  `ProperCone.exists_mem_hasEigenvector_gelfandRadius_of_isCompactOperator`: **Krein–Rutman**.
* `ProperCone.gelfandRadius_mem_spectrum_of_gelfandRadius_pow_sub_lt` (and
  `…_of_isCompactOperator`): the Gelfand radius is an isolated spectral value.
* `ProperCone.exists_dual_comp_eq_gelfandRadius_smul_of_gelfandRadius_pow_sub_lt` (and
  `…_of_isCompactOperator`): **dual Krein–Rutman**.
* `ProperCone.spectralRadius_eq_gelfandRadius_of_gelfandRadius_pow_sub_lt` (and
  `…_of_isCompactOperator`): `spectralRadius ℝ T` is the Gelfand radius (the formulation of
  `facebookresearch/atlas-lean`'s Krein–Rutman on `C(K, ℝ)`).

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-10-17: no
Krein–Rutman statement in the pinned tree, on mathlib master, or in an open mathlib PR;
`facebookresearch/atlas-lean` (`MathlibExt/Analysis/FunctionalAnalysis/KreinRutman.lean`) proves
the compact case on `C(K, ℝ)` through `spectralRadius ℝ`; no quasi-compact version anywhere.
-/

open Filter Metric Set Topology TaylorComplexification

/-- Real points beyond `gelfandRadius a ^ n` lie outside the spectrum of `a ^ n`. -/
theorem frequently_notMem_spectrum_pow_gelfandRadius {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (a : A) {n : ℕ} (hn : n ≠ 0) :
    ∃ᶠ w in 𝓝[≠] (gelfandRadius a ^ n), w ∉ spectrum ℝ (a ^ n) := by
  have h : ∀ᶠ w in 𝓝[>] (gelfandRadius a ^ n), w ∉ spectrum ℝ (a ^ n) :=
    eventually_nhdsWithin_of_forall fun w hw hw' ↦ hw' <| mem_resolventSet_of_gelfandRadius_lt <| by
      rw [gelfandRadius_pow_of_ne_zero a hn]
      exact (Set.mem_Ioi.1 hw).trans_le (Real.le_norm_self w)
  exact h.frequently.filter_mono (nhdsWithin_mono _ fun w hw ↦ ne_of_gt hw)

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ProperCone ℝ E}

/-- **A total cone sees every nonzero operator**: if `span C` is dense, a nonzero continuous
linear map is nonzero at some point of `C`. -/
theorem exists_mem_apply_ne_zero (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : E →L[ℝ] F} (hL : L ≠ 0) :
    ∃ x ∈ C, L x ≠ 0 := by
  by_contra! h
  refine hL (ContinuousLinearMap.ext fun x ↦ ?_)
  have hker : Submodule.span ℝ (C : Set E) ≤ LinearMap.ker (L : E →ₗ[ℝ] F) :=
    Submodule.span_le.2 fun y hy ↦ by simpa using h y hy
  simpa using (L.isClosed_ker.closure_subset_iff.2 hker) (hCE x)

/-- **A total cone sees every nonzero complex operator**: if `span C` is dense, a nonzero
`Q : E_ℂ →L[ℂ] F` is nonzero at `ofReal x` for some `x ∈ C`. -/
theorem exists_mem_apply_ofReal_ne_zero (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Q : TaylorComplexification E →L[ℂ] F}
    (hQ : Q ≠ 0) : ∃ x ∈ C, Q (ofReal x) ≠ 0 :=
  exists_mem_apply_ne_zero hCE (L := (Q.restrictScalars ℝ).comp ofReal) fun h ↦
    hQ (ext_ofReal fun x ↦ by simpa using congr($h x))

/-- **The complexified dual of a salient cone separates points**: for `ψ ≠ 0` some `f ≥ 0` on `C`
has `f_ℂ ψ ≠ 0`. -/
theorem exists_complexify_ne_zero (hC : (C : ConvexCone ℝ E).Salient)
    {ψ : TaylorComplexification E} (hψ : ψ ≠ 0) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ complexifyDual f ψ ≠ 0 := by
  by_cases hre : re ψ = 0
  · have him : im ψ ≠ 0 := fun h ↦ hψ (TaylorComplexification.ext (by simp [hre]) (by simp [h]))
    obtain ⟨f, hfC, hf⟩ := exists_strongDual_ne_zero_of_salient hC him
    exact ⟨f, hfC, fun h ↦ hf (by
      simpa [complexifyDual_apply, hre] using congr_arg Complex.im h)⟩
  · obtain ⟨f, hfC, hf⟩ := exists_strongDual_ne_zero_of_salient hC hre
    exact ⟨f, hfC, fun h ↦ hf (by
      simpa [complexifyDual_apply] using congr_arg Complex.re h)⟩

variable [CompleteSpace E] {T : E →L[ℝ] E} {f : StrongDual ℝ E} {x : E}

/-- **Positivity of the complex resolvent**: for `x ∈ C`, `f ≥ 0` on `C` and
`‖z‖ > gelfandRadius T`, `‖f_ℂ ((z - T_ℂ)⁻¹ x)‖ ≤ f ((‖z‖ - T)⁻¹ x)`: the Neumann series of the left
side has the nonnegative coefficients `f (Tⁿ x)`. -/
theorem norm_complexify_apply_resolvent_le (hT : MapsTo T C C) (hf : ∀ y ∈ C, 0 ≤ f y)
    (hx : x ∈ C) {z : ℂ} (hz : gelfandRadius T < ‖z‖) :
    ‖complexifyDual f (resolvent (complexify T) z (ofReal x))‖ ≤ f (resolvent T ‖z‖ x) := by
  have hz' : gelfandRadius (complexify T) < ‖z‖ := by
    rwa [gelfandRadius_complexify]
  refine (((hasSum_resolvent_of_gelfandRadius_lt hz').mapL
    (ContinuousLinearMap.apply ℂ _ (ofReal x))).mapL (complexifyDual f)).norm_le_of_bounded
    (T.hasSum_apply_resolvent hz f x) fun n ↦ ?_
  have hn : 0 ≤ f ((⇑T)^[n] x) := hf _ (hT.iterate n hx)
  simp [← complexify_pow, abs_of_nonneg hn]

/-- **Resolvent blow-up from a peripheral pole**: if the complexified resolvent satisfies
`(z - μ) ^ m • R(z) → Q ≠ 0` at some `μ` with `‖μ‖ = gelfandRadius T > 0` and `m ≥ 1`, and `C` is
total and salient, then `‖(t - T)⁻¹ x‖ → ∞` as `t ↓ gelfandRadius T` for some `x ∈ C`. -/
theorem exists_mem_tendsto_norm_resolvent_of_tendsto (hC : (C : ConvexCone ℝ E).Salient)
    (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E)) (hT : MapsTo T C C)
    (hr : 0 < gelfandRadius T) {μ : ℂ} (hμ : ‖μ‖ = gelfandRadius T) {m : ℕ} (hm : m ≠ 0)
    {Q : TaylorComplexification E →L[ℂ] TaylorComplexification E} (hQ : Q ≠ 0)
    (hlim : Tendsto (fun z ↦ (z - μ) ^ m • resolvent (complexify T) z) (𝓝[≠] μ) (𝓝 Q)) :
    ∃ x ∈ C, Tendsto (fun t ↦ ‖resolvent T t x‖) (𝓝[>] gelfandRadius T) atTop := by
  set r := gelfandRadius T
  obtain ⟨x, hxC, hQx⟩ := exists_mem_apply_ofReal_ne_zero hCE hQ
  obtain ⟨f, hfC, hf⟩ := exists_complexify_ne_zero hC hQx
  refine ⟨x, hxC, ?_⟩
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set u : ℂ := μ / r
  have hu : ‖u‖ = 1 := by simp [u, hμ, hr.ne', abs_of_pos hr]
  have hμu : (r : ℂ) * u = μ := mul_div_cancel₀ μ hr0
  set z : ℝ → ℂ := fun t ↦ (t : ℂ) * u
  have hzμ (t : ℝ) : ‖z t - μ‖ = |t - r| := by
    rw [← hμu, ← sub_mul, norm_mul, hu, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hzn (t : ℝ) : ‖z t‖ = |t| := by simp [z, hu]
  have hz : Tendsto z (𝓝[>] r) (𝓝[≠] μ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa [z, hμu] using (((by fun_prop : Continuous z).tendsto r).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t (ht : r < t)
      rw [mem_compl_iff, mem_singleton_iff, ← sub_eq_zero, ← norm_eq_zero, hzμ]
      exact abs_ne_zero.2 (sub_ne_zero.2 ht.ne')
  set Φ : (TaylorComplexification E →L[ℂ] TaylorComplexification E) →L[ℂ] ℂ :=
    (complexifyDual f).comp (ContinuousLinearMap.apply ℂ _ (ofReal x))
  have hc : 0 < ‖Φ Q‖ := norm_pos_iff.2 hf
  have h₁ := ((Φ.continuous.tendsto Q).comp (hlim.comp hz)).norm
  have h₂ : ∀ᶠ t in 𝓝[>] r, ‖Φ Q‖ / 2 < (t - r) ^ m * f (resolvent T t x) := by
    filter_upwards [h₁.eventually (lt_mem_nhds (half_lt_self hc)), self_mem_nhdsWithin]
      with t ht (htr : r < t)
    refine ht.trans_le ?_
    have hle := norm_complexify_apply_resolvent_le hT hfC hxC (z := z t)
      (by rw [hzn, abs_of_pos (hr.trans htr)]; exact htr)
    rw [hzn, abs_of_pos (hr.trans htr)] at hle
    simp only [Function.comp_apply, map_smul, smul_eq_mul, norm_mul, norm_pow, hzμ,
      abs_of_pos (sub_pos.2 htr)]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hsub₀ : Tendsto (fun t ↦ t - r) (𝓝[>] r) (𝓝 0) := by
    simpa using ((continuous_sub_right r).tendsto r).mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun t ↦ t - r) (𝓝[>] r) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hsub₀, eventually_nhdsWithin_of_forall fun t (ht : r < t) ↦
      sub_pos.2 ht⟩
  have h₃ := ((tendsto_pow_atTop hm).comp (tendsto_inv_nhdsGT_zero.comp hsub)).const_mul_atTop
    (half_pos hc)
  have hG : Tendsto (fun t ↦ f (resolvent T t x)) (𝓝[>] r) atTop := by
    refine tendsto_atTop_mono' _ ?_ h₃
    filter_upwards [h₂, self_mem_nhdsWithin] with t ht (htr : r < t)
    have hpos : 0 < (t - r) ^ m := pow_pos (sub_pos.2 htr) m
    rw [Function.comp_apply, Function.comp_apply, inv_pow, ← div_eq_mul_inv, div_le_iff₀ hpos,
      mul_comm]
    exact ht.le
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp [complexifyDual_apply] at hf
  exact (tendsto_atTop_mono (fun t ↦ (Real.le_norm_self _).trans (f.le_opNorm _)) hG
    ).atTop_of_const_mul₀ (norm_pos_iff.2 hf0)

/-- **Approximate eigenvectors, quasi-compact operator**: if `gelfandRadius (T ^ n - K) < ‖r‖ ^ n`
for a compact `K`, unit approximate eigenvectors `tₖ yₖ - T yₖ → 0` in `C` with `tₖ → r` accumulate
at a unit eigenvector of `T` in `C` for `r`. -/
theorem exists_eigenvector_of_gelfandRadius_pow_sub_lt {K : E →L[ℝ] E} {n : ℕ}
    (hK : IsCompactOperator K) {r : ℝ} (h : gelfandRadius (T ^ n - K) < ‖r‖ ^ n) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 r)) {y : ℕ → E} (hyC : ∀ k, y k ∈ C) (hy : ∀ k, ‖y k‖ = 1)
    (hlim : Tendsto (fun k ↦ t k • y k - T (y k)) atTop (𝓝 0)) :
    ∃ x ∈ C, ‖x‖ = 1 ∧ T x = r • x := by
  obtain ⟨z, φ, -, hz, hTz⟩ :=
    hK.exists_subseq_tendsto_of_gelfandRadius_pow_sub_lt h ht (fun k ↦ (hy k).le) hlim
  exact ⟨z, C.isClosed.mem_of_tendsto hz (.of_forall fun k ↦ hyC _),
    tendsto_nhds_unique hz.norm (by simp [hy]), hTz⟩

variable {K : E →L[ℝ] E} {n : ℕ}

/-- **Krein–Rutman theorem for quasi-compact operators** (Bourbaki TS III §6 Théorème 4 for
compact `T`; Nussbaum): if `T` preserves a total salient proper cone and
`gelfandRadius (T ^ n - K) < gelfandRadius T ^ n` for a compact `K` and `n ≠ 0` (the essential
spectral radius is below the Gelfand radius), the Gelfand radius is an eigenvalue of `T` with an
eigenvector in the cone. -/
theorem exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n) (hT : MapsTo T C C) :
    ∃ x ∈ C, Module.End.HasEigenvector (T : Module.End ℝ E) (gelfandRadius T) x := by
  have hr : 0 < gelfandRadius T := lt_of_pow_lt_pow_left₀ n (gelfandRadius_nonneg T)
    (by rw [zero_pow hn]; exact (gelfandRadius_nonneg _).trans_lt hTK)
  have : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim T 0, gelfandRadius_zero] at hr
    exact lt_irrefl _ hr
  obtain ⟨μ, hμσ, hμn⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (A := TaylorComplexification E →L[ℂ] TaylorComplexification E) (complexify T)
  rw [spectrum.spectralRadius_eq_gelfandRadius, gelfandRadius_complexify] at hμn
  have hμ : ‖μ‖ = gelfandRadius T := by
    simpa [ENNReal.toReal_ofReal hr.le] using congrArg ENNReal.toReal hμn
  have hKc := isCompactOperator_complexify hK
  have hTKc : gelfandRadius (complexify T ^ n - complexify K) < ‖μ‖ ^ n := by
    rw [← complexify_pow, ← complexify_sub, gelfandRadius_complexify, hμ]
    exact hTK
  obtain ⟨m, hm, Q, hQ, hlim⟩ := hKc.exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt
    hn hTKc (hKc.eventually_notMem_spectrum_of_gelfandRadius_sub_lt
      (by rw [norm_pow]; exact hTKc)).frequently hμσ
  obtain ⟨x, hxC, hR⟩ :=
    exists_mem_tendsto_norm_resolvent_of_tendsto hC hCE hT hr hμ hm.ne' hQ hlim
  set t : ℕ → ℝ := fun n ↦ gelfandRadius T + 1 / (n + 1)
  have ht₀ : Tendsto t atTop (𝓝 (gelfandRadius T)) := by
    simpa [t] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (gelfandRadius T)
  have htr (n : ℕ) : gelfandRadius T < t n := lt_add_of_pos_right _ Nat.one_div_pos_of_nat
  obtain ⟨y, hyC, hy, hlimy⟩ := exists_approx_eigenvector_of_tendsto_norm_resolvent hT hxC htr
    (hR.comp (tendsto_nhdsWithin_iff.2 ⟨ht₀, .of_forall htr⟩))
  obtain ⟨z, hzC, hz, hTz⟩ := exists_eigenvector_of_gelfandRadius_pow_sub_lt hK
    (r := gelfandRadius T) (by rw [Real.norm_of_nonneg hr.le]; exact hTK) ht₀ hyC hy hlimy
  refine ⟨z, hzC, Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hTz, ?_⟩⟩
  rintro rfl
  simp at hz

/-- In the quasi-compact Krein–Rutman setting the Gelfand radius is an **isolated point of the
spectrum**. -/
theorem gelfandRadius_mem_spectrum_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n) (hT : MapsTo T C C) :
    gelfandRadius T ∈ spectrum ℝ T ∧ ∀ᶠ z in 𝓝[≠] gelfandRadius T, z ∉ spectrum ℝ T := by
  obtain ⟨_, -, hx⟩ :=
    exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT
  refine ⟨?_, hK.eventually_notMem_spectrum_of_gelfandRadius_pow_sub_lt hn
    (by rw [Real.norm_of_nonneg (gelfandRadius_nonneg T)]; exact hTK)
    (frequently_notMem_spectrum_pow_gelfandRadius T hn)⟩
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.hasEigenvalue_of_hasEigenvector hx).mem_spectrum

/-- In the quasi-compact Krein–Rutman setting the **real spectral radius is the Gelfand radius**,
so statements of Krein–Rutman through `spectralRadius ℝ` are corollaries of those through
`gelfandRadius`. -/
theorem spectralRadius_eq_gelfandRadius_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n) (hT : MapsTo T C C) :
    spectralRadius ℝ T = ENNReal.ofReal (gelfandRadius T) := by
  refine le_antisymm (spectralRadius_le_gelfandRadius T) ?_
  have hle : (‖gelfandRadius T‖₊ : ENNReal) ≤ spectralRadius ℝ T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℝ T) ↦ (‖k‖₊ : ENNReal)) _
      (gelfandRadius_mem_spectrum_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT).1
  rwa [← enorm_eq_nnnorm, ← ofReal_norm, Real.norm_of_nonneg (gelfandRadius_nonneg T)] at hle

/-- `(t - T)⁻¹ (T - r) = (t - r) (t - T)⁻¹ - 1` beyond the Gelfand radius. -/
theorem resolvent_mul_sub_smul_one {t : ℝ} (ht : gelfandRadius T < t) (r : ℝ) :
    resolvent T t * (T - r • 1) = (t - r) • resolvent T t - 1 := by
  have h := resolvent_mul_algebraMap_sub_of_gelfandRadius_lt
    (ht.trans_le (Real.le_norm_self t) : gelfandRadius T < ‖t‖)
  rw [Algebra.algebraMap_eq_smul_one, mul_sub, mul_smul_comm, mul_one] at h
  rw [mul_sub, mul_smul_comm, mul_one, sub_smul, ← h]
  abel

/-- **Dual Krein–Rutman theorem** (Bourbaki TS III §6 no. 7, Corollaire, for compact `T`): in the
quasi-compact Krein–Rutman setting the transpose has the Gelfand radius as an eigenvalue, with an
eigenfunctional nonnegative on the cone. It is `φ ∘ q` for the positive leading Laurent coefficient
`q = lim (t - r) ^ m (t - T)⁻¹` of the real resolvent at its pole `r`, which satisfies
`q T = r q`. -/
theorem exists_dual_comp_eq_gelfandRadius_smul_of_gelfandRadius_pow_sub_lt
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hK : IsCompactOperator K) (hn : n ≠ 0)
    (hTK : gelfandRadius (T ^ n - K) < gelfandRadius T ^ n) (hT : MapsTo T C C) :
    ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ (∀ x ∈ C, 0 ≤ ℓ x) ∧ ℓ.comp T = gelfandRadius T • ℓ := by
  set r := gelfandRadius T
  obtain ⟨hrσ, -⟩ := gelfandRadius_mem_spectrum_of_gelfandRadius_pow_sub_lt hC hCE hK hn hTK hT
  obtain ⟨m, hm, q, hq, hlim⟩ := hK.exists_tendsto_pow_smul_resolvent_of_gelfandRadius_pow_sub_lt hn
    (by rw [Real.norm_of_nonneg (gelfandRadius_nonneg T)]; exact hTK)
    (frequently_notMem_spectrum_pow_gelfandRadius T hn) hrσ
  have hlim' : Tendsto (fun t ↦ (t - r) ^ m • resolvent T t) (𝓝[>] r) (𝓝 q) :=
    hlim.mono_left (nhdsWithin_mono _ fun t (ht : r < t) ↦ ne_of_gt ht)
  have hqC : MapsTo q C C := fun x hx ↦ C.isClosed.mem_of_tendsto
    (((ContinuousLinearMap.apply ℝ E x).continuous.tendsto q).comp hlim')
    (eventually_nhdsWithin_of_forall fun t (ht : r < t) ↦ by
      simpa using C.smul_mem (C.mapsTo_resolvent hT ht hx) (pow_nonneg (sub_pos.2 ht).le m))
  have h₀ : Tendsto (fun t ↦ (t - r) • ((t - r) ^ m • resolvent T t) - (t - r) ^ m • 1)
      (𝓝[>] r) (𝓝 0) := by
    have hsub : Tendsto (fun t ↦ t - r) (𝓝[>] r) (𝓝 0) := by
      simpa using ((continuous_sub_right r).tendsto r).mono_left nhdsWithin_le_nhds
    simpa [zero_pow hm.ne'] using (hsub.smul hlim').sub ((hsub.pow m).smul_const 1)
  have hqT : q * (T - r • 1) = 0 := by
    refine tendsto_nhds_unique (hlim'.mul_const (T - r • 1)) (h₀.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t (ht : r < t)
    rw [smul_mul_assoc, resolvent_mul_sub_smul_one ht, smul_sub, smul_smul, smul_smul, mul_comm]
  obtain ⟨x, hxC, hqx⟩ := exists_mem_apply_ne_zero hCE hq
  obtain ⟨φ, hφC, hφ⟩ := exists_strongDual_pos_of_salient hC (hqC hxC) hqx
  refine ⟨φ.comp q, fun h ↦ hφ.ne' (by simpa using congr($h x)), fun y hy ↦ hφC _ (hqC hy), ?_⟩
  have hqT' : q.comp T = r • q := by
    rw [mul_sub, mul_smul_comm, mul_one, sub_eq_zero] at hqT
    exact hqT
  rw [ContinuousLinearMap.comp_assoc, hqT', ContinuousLinearMap.comp_smul]

/-! ### Compact operators

The case `n = 1`, `K = T` of the quasi-compact theorems: `gelfandRadius (T - T) = 0`. -/

/-- **Krein–Rutman theorem** (Bourbaki, *Théories spectrales*, III §6, Théorème 4): a compact
operator preserving a total salient proper cone, with positive Gelfand radius, has its Gelfand
radius as an eigenvalue with an eigenvector in the cone. -/
theorem exists_mem_hasEigenvector_gelfandRadius_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hTc : IsCompactOperator T) (hT : MapsTo T C C) (hr : 0 < gelfandRadius T) :
    ∃ x ∈ C, Module.End.HasEigenvector (T : Module.End ℝ E) (gelfandRadius T) x :=
  exists_mem_hasEigenvector_gelfandRadius_of_gelfandRadius_pow_sub_lt hC hCE hTc one_ne_zero
    (by simpa using hr) hT

/-- In the Krein–Rutman setting the Gelfand radius is an **isolated point of the spectrum**. -/
theorem gelfandRadius_mem_spectrum_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hTc : IsCompactOperator T) (hT : MapsTo T C C) (hr : 0 < gelfandRadius T) :
    gelfandRadius T ∈ spectrum ℝ T ∧ ∀ᶠ z in 𝓝[≠] gelfandRadius T, z ∉ spectrum ℝ T :=
  gelfandRadius_mem_spectrum_of_gelfandRadius_pow_sub_lt hC hCE hTc one_ne_zero
    (by simpa using hr) hT

/-- In the Krein–Rutman setting the **real spectral radius is the Gelfand radius** (the
formulation of `facebookresearch/atlas-lean`'s Krein–Rutman on `C(K, ℝ)`). -/
theorem spectralRadius_eq_gelfandRadius_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hTc : IsCompactOperator T) (hT : MapsTo T C C) (hr : 0 < gelfandRadius T) :
    spectralRadius ℝ T = ENNReal.ofReal (gelfandRadius T) :=
  spectralRadius_eq_gelfandRadius_of_gelfandRadius_pow_sub_lt hC hCE hTc one_ne_zero
    (by simpa using hr) hT

/-- **Dual Krein–Rutman theorem** (Bourbaki TS III §6 no. 7, Corollaire): in the Krein–Rutman
setting the transpose has the Gelfand radius as an eigenvalue with an eigenfunctional nonnegative on
the cone. -/
theorem exists_dual_comp_eq_gelfandRadius_smul_of_isCompactOperator
    (hC : (C : ConvexCone ℝ E).Salient) (hCE : Dense (Submodule.span ℝ (C : Set E) : Set E))
    (hTc : IsCompactOperator T) (hT : MapsTo T C C) (hr : 0 < gelfandRadius T) :
    ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ (∀ x ∈ C, 0 ≤ ℓ x) ∧ ℓ.comp T = gelfandRadius T • ℓ :=
  exists_dual_comp_eq_gelfandRadius_smul_of_gelfandRadius_pow_sub_lt hC hCE hTc one_ne_zero
    (by simpa using hr) hT

end ProperCone
