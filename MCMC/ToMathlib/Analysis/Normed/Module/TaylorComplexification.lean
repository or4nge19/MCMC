/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import MCMC.ToMathlib.Analysis.Normed.Algebra.GelfandRadius

/-!
# The Taylor complexification of a real normed space

For a real normed space `E`, `TaylorComplexification E` is `ℂ →L[ℝ] E` with the operator norm,
made complex through the domain: `(c • ψ) z = ψ (c * z)`. Its real and imaginary parts are
`re ψ = ψ 1` and `im ψ = -ψ I`, with `ψ = ofReal (re ψ) + I • ofReal (im ψ)`, where
`ofReal x = (z ↦ z.re • x)`. Under `ψ ↦ (re ψ, im ψ)` the norm is the Taylor norm
`‖(a, b)‖ = ⨆ θ, ‖cos θ • a + sin θ • b‖`. A real operator `T` extends to `ψ ↦ T ∘L ψ`, a real
functional `f` to `ψ ↦ f (re ψ) + I * f (im ψ)`, both isometrically.

Design. The carrier `ℂ →L[ℝ] E` gives the norm, completeness and topology for free, and the domain
action makes the norm exactly complex-homogeneous, which a product norm on `E × E` in general is not
(the `ℓ²` norm is, on an inner product space). `TaylorComplexification` is a type synonym so that
`ℂ →L[ℝ] E` itself carries no second `ℂ`-action: when `E` is complex, the codomain action would
clash with the domain one. The synonym only inherits `NormedAddCommGroup`, `FunLike`,
`ContinuousLinearMapClass` and `CompleteSpace`; its real structure is restriction of scalars
(`Module.complexToReal`), which is the original pointwise one (`real_smul_apply`).

## Main definitions

* `TaylorComplexification E`, with `NormedSpace ℂ` and `CompleteSpace` instances.
* `TaylorComplexification.ofReal`, `re`, `im`: the real embedding and the real and imaginary
  parts, real-linear and continuous.
* `TaylorComplexification.equivProd`: `ψ ↦ (re ψ, im ψ)`, a real-linear homeomorphism onto `E × E`.
* `TaylorComplexification.complexify`: the complexification `T ∘L ·` of a real operator.
* `TaylorComplexification.complexifyDual`: the complexification of a real functional.

## Main statements

* `TaylorComplexification.norm_eq_iSup`: the norm is the Taylor norm.
* `TaylorComplexification.ofReal_re_add_I_smul_ofReal_im`, `ext_iff_re_im`, `ext_ofReal`.
* `TaylorComplexification.norm_complexify`, `norm_complexifyDual`: isometric extension.
* `TaylorComplexification.gelfandRadius_complexify`, `isCompactOperator_complexify`.
* `TaylorComplexification.isUnit_complexify_iff`, `complexify_resolvent`: at real points the
  complex resolvent is the complexified real one, with no hypothesis on `t`.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces, polynomials
  and multilinear maps*, Studia Math. 134 (1999), 1–33.

Staged for `Mathlib/Analysis/Normed/Module/TaylorComplexification.lean`. Searched on 2026-10-17:
the pinned mathlib (v4.34.1) has no complexification of normed spaces (only TODOs in
`Analysis/InnerProductSpace/Rayleigh.lean` and `Adjoint.lean`); mathlib master has no such file
under `Mathlib/Analysis/Normed/Module` (`gh api repos/leanprover-community/mathlib4/contents/...`);
`gh pr list -R leanprover-community/mathlib4 --search complexification` finds #42744
(`Complexification 𝕜 E := WithLp 2 (E × E)` for inner product spaces, operators
`ContinuousLinearMap.toComplexification`) and its follow-up #42805. TauCeti
(`TauCetiProject/TauCeti`, `Analysis/Normed/Module/Complexification.lean`) has a Taylor-norm
complexification with root-namespace `ContinuousLinearMap.complexify`; our operations live in the
`TaylorComplexification` namespace so that both can be imported. `openai/math`
(`OAI.SeparableQuotient.Complexify X := ℂ →L[ℝ] X`) uses the same carrier. `gelfandRadius` is the
backport of #42607.
-/

open Complex (I)

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Taylor complexification** of a real normed space `E`: real-linear maps `ℂ →L[ℝ] E` with
the operator norm, a complex space through the domain, `(c • ψ) z = ψ (c * z)`. -/
def TaylorComplexification : Type _ := ℂ →L[ℝ] E

namespace TaylorComplexification

noncomputable instance : NormedAddCommGroup (TaylorComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] E))

instance : FunLike (TaylorComplexification E) ℂ E := inferInstanceAs (FunLike (ℂ →L[ℝ] E) ℂ E)

instance : ContinuousLinearMapClass (TaylorComplexification E) ℝ ℂ E :=
  inferInstanceAs (ContinuousLinearMapClass (ℂ →L[ℝ] E) ℝ ℂ E)

instance [CompleteSpace E] : CompleteSpace (TaylorComplexification E) :=
  inferInstanceAs (CompleteSpace (ℂ →L[ℝ] E))

/-- `ℂ` acts through the domain: `(c • ψ) z = ψ (c * z)`. -/
noncomputable instance : Module ℂ (TaylorComplexification E) where
  smul c ψ := ContinuousLinearMap.comp ψ (ContinuousLinearMap.mul ℝ ℂ c)
  one_smul ψ := DFunLike.ext _ _ fun z ↦ congrArg ψ (one_mul z)
  mul_smul c d ψ := DFunLike.ext _ _ fun z ↦
    congrArg ψ ((mul_right_comm c d z).trans (mul_comm _ _))
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul c d ψ := DFunLike.ext _ _ fun z ↦ (congrArg ψ (add_mul c d z)).trans (map_add ψ _ _)
  zero_smul ψ := DFunLike.ext _ _ fun z ↦ (congrArg ψ (zero_mul z)).trans (map_zero ψ)

noncomputable instance : NormedSpace ℂ (TaylorComplexification E) where
  norm_smul_le c ψ := (ContinuousLinearMap.opNorm_comp_le ψ _).trans <|
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ c)
      (norm_nonneg _)).trans_eq (mul_comm _ _)

variable {E}

@[simp]
theorem smul_apply (c : ℂ) (ψ : TaylorComplexification E) (z : ℂ) : (c • ψ) z = ψ (c * z) := rfl

/-- The real structure, restricted from the complex one, is the pointwise one. -/
@[simp]
theorem real_smul_apply (r : ℝ) (ψ : TaylorComplexification E) (z : ℂ) :
    (r • ψ) z = r • ψ z :=
  (congrArg ψ Complex.real_smul.symm).trans (map_smul ψ r z)

/-- The real part `ψ ↦ ψ 1`. -/
noncomputable def re : TaylorComplexification E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun ψ := ψ 1
      map_add' _ _ := rfl
      map_smul' r ψ := real_smul_apply r ψ 1 }
    1 fun ψ ↦ (ContinuousLinearMap.unit_le_opNorm ψ 1 (by simp)).trans_eq (one_mul _).symm

/-- The imaginary part `ψ ↦ ψ (-I) = -ψ I`. -/
noncomputable def im : TaylorComplexification E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun ψ := ψ (-I)
      map_add' _ _ := rfl
      map_smul' r ψ := real_smul_apply r ψ (-I) }
    1 fun ψ ↦ (ContinuousLinearMap.unit_le_opNorm ψ (-I) (by simp)).trans_eq (one_mul _).symm

/-- The real embedding `x ↦ (z ↦ z.re • x)`. -/
noncomputable def ofReal : E →L[ℝ] TaylorComplexification E :=
  LinearMap.mkContinuous
    { toFun x := Complex.reCLM.smulRight x
      map_add' x y := DFunLike.ext _ _ fun z ↦ smul_add z.re x y
      map_smul' r x := DFunLike.ext _ _ fun z ↦
        (smul_comm z.re r x).trans (real_smul_apply r (Complex.reCLM.smulRight x) z).symm }
    1 fun x ↦ (Complex.reCLM.norm_smulRight_apply x).trans_le (by rw [Complex.reCLM_norm])

theorem re_apply (ψ : TaylorComplexification E) : re ψ = ψ 1 := rfl

theorem im_apply (ψ : TaylorComplexification E) : im ψ = -ψ I := map_neg ψ I

@[simp]
theorem ofReal_apply (x : E) (z : ℂ) : ofReal x z = z.re • x := rfl

@[simp]
theorem re_ofReal (x : E) : re (ofReal x) = x := by simp [re_apply]

@[simp]
theorem im_ofReal (x : E) : im (ofReal x) = 0 := by simp [im_apply]

@[simp]
theorem norm_ofReal (x : E) : ‖ofReal x‖ = ‖x‖ :=
  (Complex.reCLM.norm_smulRight_apply x).trans (by rw [Complex.reCLM_norm, one_mul])

theorem norm_re_le (ψ : TaylorComplexification E) : ‖re ψ‖ ≤ ‖ψ‖ :=
  ContinuousLinearMap.unit_le_opNorm ψ 1 (by simp)

theorem norm_im_le (ψ : TaylorComplexification E) : ‖im ψ‖ ≤ ‖ψ‖ :=
  ContinuousLinearMap.unit_le_opNorm ψ (-I) (by simp)

/-- `ψ` is determined by its real and imaginary parts. -/
theorem apply_eq_re_smul_sub_im_smul (ψ : TaylorComplexification E) (z : ℂ) :
    ψ z = z.re • re ψ - z.im • im ψ := by
  rw [re_apply, im_apply, smul_neg, sub_neg_eq_add, ← map_smul, ← map_smul, ← map_add]
  congr 1
  apply Complex.ext <;> simp

@[ext (iff := false)]
theorem ext {ψ ψ' : TaylorComplexification E} (hre : re ψ = re ψ') (him : im ψ = im ψ') :
    ψ = ψ' :=
  DFunLike.ext _ _ fun z ↦ by
    rw [apply_eq_re_smul_sub_im_smul ψ, apply_eq_re_smul_sub_im_smul ψ', hre, him]

theorem ext_iff_re_im {ψ ψ' : TaylorComplexification E} :
    ψ = ψ' ↔ re ψ = re ψ' ∧ im ψ = im ψ' :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun h ↦ ext h.1 h.2⟩

@[simp]
theorem re_smul (c : ℂ) (ψ : TaylorComplexification E) :
    re (c • ψ) = c.re • re ψ - c.im • im ψ := by
  rw [re_apply, smul_apply, mul_one, apply_eq_re_smul_sub_im_smul]

@[simp]
theorem im_smul (c : ℂ) (ψ : TaylorComplexification E) :
    im (c • ψ) = c.re • im ψ + c.im • re ψ := by
  rw [im_apply, smul_apply, apply_eq_re_smul_sub_im_smul]
  simp

@[simp]
theorem ofReal_re_add_I_smul_ofReal_im (ψ : TaylorComplexification E) :
    ofReal (re ψ) + I • ofReal (im ψ) = ψ :=
  ext (by simp) (by simp)

instance [Nontrivial E] : Nontrivial (TaylorComplexification E) :=
  Function.Injective.nontrivial (f := (ofReal : E →L[ℝ] TaylorComplexification E))
    fun x y h ↦ by simpa using congrArg re h

/-- A complex-linear map out of `TaylorComplexification E` is determined on real vectors. -/
theorem ext_ofReal {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℂ F]
    {f g : TaylorComplexification E →L[ℂ] F} (h : ∀ x, f (ofReal x) = g (ofReal x)) : f = g :=
  ContinuousLinearMap.ext fun ψ ↦ by
    rw [← ofReal_re_add_I_smul_ofReal_im ψ, map_add, map_smul, map_add, map_smul, h, h]

/-- `ψ ↦ (re ψ, im ψ)` as a real-linear homeomorphism `TaylorComplexification E ≃L[ℝ] E × E`. -/
noncomputable def equivProd : TaylorComplexification E ≃L[ℝ] E × E :=
  .equivOfInverse (re.prod im) (ofReal.coprod (I • ofReal)) ofReal_re_add_I_smul_ofReal_im
    fun _ ↦ by simp

@[simp]
theorem equivProd_apply (ψ : TaylorComplexification E) : equivProd ψ = (re ψ, im ψ) := rfl

@[simp]
theorem equivProd_symm_apply (p : E × E) : equivProd.symm p = ofReal p.1 + I • ofReal p.2 := rfl

/-- The norm of `ψ` is the **Taylor norm** `⨆ θ, ‖cos θ • re ψ + sin θ • im ψ‖`. -/
theorem norm_eq_iSup (ψ : TaylorComplexification E) :
    ‖ψ‖ = ⨆ θ : ℝ, ‖Real.cos θ • re ψ + Real.sin θ • im ψ‖ := by
  have hle (θ : ℝ) : ‖Real.cos θ • re ψ + Real.sin θ • im ψ‖ ≤ ‖ψ‖ := calc
    _ = ‖ψ (Complex.exp (↑(-θ) * I))‖ := by
      rw [apply_eq_re_smul_sub_im_smul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg, neg_smul, sub_neg_eq_add]
    _ ≤ ‖ψ‖ := ContinuousLinearMap.unit_le_opNorm ψ _ (Complex.norm_exp_ofReal_mul_I _).le
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound ψ
    (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun z ↦ ?_) (ciSup_le hle)
  calc ‖ψ z‖ = ‖z‖ * ‖Real.cos (-Complex.arg z) • re ψ + Real.sin (-Complex.arg z) • im ψ‖ := by
        rw [apply_eq_re_smul_sub_im_smul, Real.cos_neg, Real.sin_neg, neg_smul, ← sub_eq_add_neg,
          ← norm_norm z, ← norm_smul, smul_sub, smul_smul, smul_smul,
          Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
    _ ≤ ‖z‖ * ⨆ θ : ℝ, ‖Real.cos θ • re ψ + Real.sin θ • im ψ‖ := by
        gcongr
        exact le_ciSup ⟨‖ψ‖, Set.forall_mem_range.2 hle⟩ _
    _ = _ := mul_comm _ _

/-! ### Complexification of operators and functionals -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **complexification** `ψ ↦ T ∘L ψ` of a real operator. -/
noncomputable def complexify (T : E →L[ℝ] F) :
    TaylorComplexification E →L[ℂ] TaylorComplexification F :=
  LinearMap.mkContinuous
    { toFun ψ := T.comp ψ
      map_add' := T.comp_add
      map_smul' _ _ := rfl }
    ‖T‖ T.opNorm_comp_le

@[simp]
theorem complexify_apply (T : E →L[ℝ] F) (ψ : TaylorComplexification E) (z : ℂ) :
    complexify T ψ z = T (ψ z) := rfl

@[simp]
theorem re_complexify (T : E →L[ℝ] F) (ψ : TaylorComplexification E) :
    re (complexify T ψ) = T (re ψ) := rfl

@[simp]
theorem im_complexify (T : E →L[ℝ] F) (ψ : TaylorComplexification E) :
    im (complexify T ψ) = T (im ψ) := rfl

@[simp]
theorem complexify_ofReal (T : E →L[ℝ] F) (x : E) : complexify T (ofReal x) = ofReal (T x) := by
  ext <;> simp

@[simp]
theorem complexify_zero : complexify (0 : E →L[ℝ] F) = 0 := by
  ext <;> simp

@[simp]
theorem complexify_add (S T : E →L[ℝ] F) : complexify (S + T) = complexify S + complexify T := by
  ext <;> simp

@[simp]
theorem complexify_sub (S T : E →L[ℝ] F) : complexify (S - T) = complexify S - complexify T := by
  ext <;> simp

@[simp]
theorem complexify_smul (r : ℝ) (T : E →L[ℝ] F) : complexify (r • T) = r • complexify T := by
  ext <;> simp

@[simp]
theorem complexify_id : complexify (ContinuousLinearMap.id ℝ E) = .id ℂ _ := by
  ext <;> simp

@[simp]
theorem complexify_one : complexify (1 : E →L[ℝ] E) = 1 := complexify_id

@[simp]
theorem complexify_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (S : F →L[ℝ] G)
    (T : E →L[ℝ] F) : complexify (S.comp T) = (complexify S).comp (complexify T) := rfl

@[simp]
theorem complexify_mul (S T : E →L[ℝ] E) : complexify (S * T) = complexify S * complexify T :=
  complexify_comp S T

@[simp]
theorem complexify_pow (T : E →L[ℝ] E) (n : ℕ) : complexify (T ^ n) = complexify T ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, complexify_mul, ih, pow_succ]

/-- Real operators extend isometrically. -/
@[simp]
theorem norm_complexify (T : E →L[ℝ] F) : ‖complexify T‖ = ‖T‖ :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) <|
    T.opNorm_le_bound (norm_nonneg _) fun x ↦ by
      simpa using (complexify T).le_opNorm (ofReal x)

theorem gelfandRadius_complexify (T : E →L[ℝ] E) : gelfandRadius (complexify T) = gelfandRadius T :=
  tendsto_nhds_unique (tendsto_gelfandRadius (complexify T)) <| by
    simpa only [← complexify_pow, norm_complexify] using tendsto_gelfandRadius T

theorem isCompactOperator_complexify {T : E →L[ℝ] F} (hT : IsCompactOperator T) :
    IsCompactOperator (complexify T) := by
  obtain ⟨K, hK, hTK⟩ := hT
  have hprod : IsCompactOperator (Prod.map T T) := ⟨K ×ˢ K, hK.prod hK, prod_mem_nhds hTK hTK⟩
  have h : ⇑(complexify T) =
      equivProd.symm ∘ Prod.map T T ∘ (equivProd (E := E) : _ →L[ℝ] E × E) :=
    funext fun ψ ↦ by
      simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, equivProd_apply,
        Prod.map_apply, equivProd_symm_apply]
      exact (ofReal_re_add_I_smul_ofReal_im _).symm
  rw [h]
  exact (hprod.comp_clm _).continuous_comp equivProd.symm.continuous

/-- The inverse of `T` is `re ∘L V ∘L ofReal` for `V` the inverse of `complexify T`. -/
theorem isUnit_complexify_iff {T : E →L[ℝ] E} : IsUnit (complexify T) ↔ IsUnit T := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨V, hTV, hVT⟩ := isUnit_iff_exists.1 h
    refine isUnit_iff_exists.2 ⟨re ∘L V.restrictScalars ℝ ∘L ofReal,
      ContinuousLinearMap.ext fun x ↦ ?_, ContinuousLinearMap.ext fun x ↦ ?_⟩
    · simpa [← re_complexify] using congr(re ($hTV (ofReal x)))
    · simpa using congr(re ($hVT (ofReal x)))
  · obtain ⟨S, hTS, hST⟩ := isUnit_iff_exists.1 h
    exact isUnit_iff_exists.2 ⟨complexify S, by rw [← complexify_mul, hTS, complexify_one],
      by rw [← complexify_mul, hST, complexify_one]⟩

theorem complexify_ringInverse (T : E →L[ℝ] E) :
    complexify (Ring.inverse T) = Ring.inverse (complexify T) := by
  by_cases h : IsUnit T
  · rw [← Ring.inverse_mul_cancel_left _ (complexify (Ring.inverse T))
      (isUnit_complexify_iff.2 h), ← complexify_mul, Ring.mul_inverse_cancel _ h, complexify_one,
      mul_one]
  · rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ (mt isUnit_complexify_iff.1 h),
      complexify_zero]

/-- At real points the complex resolvent is the complexified real one, for every `t`. -/
theorem complexify_resolvent (T : E →L[ℝ] E) (t : ℝ) :
    complexify (resolvent T t) = resolvent (complexify T) (t : ℂ) := by
  simp [resolvent, complexify_ringInverse, Algebra.algebraMap_eq_smul_one]

theorem resolvent_complexify_ofReal (T : E →L[ℝ] E) (t : ℝ) (x : E) :
    resolvent (complexify T) (t : ℂ) (ofReal x) = ofReal (resolvent T t x) := by
  rw [← complexify_resolvent, complexify_ofReal]

/-- The **complexification** `ψ ↦ f (re ψ) + I * f (im ψ)` of a real functional. -/
noncomputable def complexifyDual (f : StrongDual ℝ E) : StrongDual ℂ (TaylorComplexification E) :=
  StrongDual.extendRCLike (f ∘L re)

theorem complexifyDual_apply (f : StrongDual ℝ E) (ψ : TaylorComplexification E) :
    complexifyDual f ψ = f (re ψ) + I * f (im ψ) := by
  simp [complexifyDual, StrongDual.extendRCLike_apply]

@[simp]
theorem complexifyDual_ofReal (f : StrongDual ℝ E) (x : E) : complexifyDual f (ofReal x) = f x := by
  simp [complexifyDual_apply]

/-- Real functionals extend isometrically. -/
@[simp]
theorem norm_complexifyDual (f : StrongDual ℝ E) : ‖complexifyDual f‖ = ‖f‖ :=
  (StrongDual.norm_extendRCLike _).trans <| le_antisymm
    ((f ∘L re).opNorm_le_bound (norm_nonneg f) fun ψ ↦
      (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_re_le ψ) (norm_nonneg f)))
    (f.opNorm_le_bound (norm_nonneg _) fun x ↦ by simpa using (f ∘L re).le_opNorm (ofReal x))

/-- The complexification of a rank-one operator: `(ℓ.smulRight x)_ℂ ψ = ℓ_ℂ ψ • ofReal x`. -/
theorem complexify_smulRight (ℓ : StrongDual ℝ E) (x : F) (ψ : TaylorComplexification E) :
    complexify (ℓ.smulRight x) ψ = complexifyDual ℓ ψ • ofReal x := by
  refine ext ?_ ?_ <;> simp [complexifyDual_apply, re_smul, im_smul]

end TaylorComplexification
