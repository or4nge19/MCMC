/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real and imaginary parts in complex `Lᵖ`; the real form of an operator with a real kernel

Write `Re v`, `Im v` for the real-linear maps `Lᵖ(μ; ℂ) → Lᵖ(μ; ℝ)` of composition with
`Complex.reCLM`, `Complex.imCLM`, and `ι f` for the composition with `Complex.ofRealCLM`
(`ContinuousLinearMap.compLpL`).

* `MeasureTheory.Lp.reCLM_compLpL_ofRealCLM_compLpL` and its three companions:
  `Re (ι f) = f`, `Im (ι f) = 0`, `Re (i • ι f) = 0`, `Im (i • ι f) = f`.
* `MeasureTheory.Lp.ofRealCLM_compLpL_reCLM_compLpL_add_I_smul`: `ι (Re v) + i • ι (Im v) = v`.

Let `Q` be a complex-linear operator on `Lᵖ(μ; ℂ)` with a real kernel `κ`:
`(Q g)(x) = ∫ κ(x, y) g(y) dμ(y)` for `μ`-almost every `x`, for every `g`. Its real form is the
real-linear operator `T f = Re (Q (ι f))` on `Lᵖ(μ; ℝ)`.

* `MeasureTheory.Lp.exists_forall_eq_reCLM_compLpL_apply_ofRealCLM_compLpL`: the real form is a
  continuous real-linear operator.
* `MeasureTheory.Lp.reCLM_compLpL_apply_ofRealCLM_compLpL_ae_eq_integral`: `T` has the kernel `κ`.
* `MeasureTheory.Lp.ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL`: `Q (ι f) = ι (T f)`.
* `MeasureTheory.Lp.reCLM_compLpL_apply_eq_of_real_kernel`,
  `MeasureTheory.Lp.imCLM_compLpL_apply_eq_of_real_kernel`: `Re (Q v) = T (Re v)` and
  `Im (Q v) = T (Im v)`.
* `MeasureTheory.Lp.apply_ofRealCLM_compLpL_add_I_smul_eq_of_real_kernel`:
  `Q (ι f + i • ι g) = ι (T f) + i • ι (T g)`.

These are the identities by which spectral statements on the real `L²` (Jentzsch's theorem)
pass to the complex `L²` of an operator with a real kernel.

Staged for `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`. Searched on 2026-11-23: the
pinned Mathlib has the function-level `MeasureTheory.memLp_re_im_iff` and no composition of an
`Lᵖ` class with `Complex.reCLM`, `Complex.imCLM` or `Complex.ofRealCLM`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real part of a real function, seen as a complex one, is the function. -/
theorem reCLM_compLpL_ofRealCLM_compLpL (f : Lp ℝ p μ) :
    Complex.reCLM.compLpL p μ (Complex.ofRealCLM.compLpL p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [Complex.reCLM.coeFn_compLpL (Complex.ofRealCLM.compLpL p μ f),
    Complex.ofRealCLM.coeFn_compLpL f] with x h₁ h₂
  rw [h₁, h₂, Complex.reCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_re]

/-- The imaginary part of a real function, seen as a complex one, vanishes. -/
theorem imCLM_compLpL_ofRealCLM_compLpL (f : Lp ℝ p μ) :
    Complex.imCLM.compLpL p μ (Complex.ofRealCLM.compLpL p μ f) = 0 := by
  refine Lp.ext ?_
  filter_upwards [Complex.imCLM.coeFn_compLpL (Complex.ofRealCLM.compLpL p μ f),
    Complex.ofRealCLM.coeFn_compLpL f, Lp.coeFn_zero ℝ p μ] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, Complex.imCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_im,
    Pi.zero_apply]

/-- The real part of `i` times a real function vanishes. -/
theorem reCLM_compLpL_I_smul_ofRealCLM_compLpL (f : Lp ℝ p μ) :
    Complex.reCLM.compLpL p μ (Complex.I • Complex.ofRealCLM.compLpL p μ f) = 0 := by
  refine Lp.ext ?_
  filter_upwards [Complex.reCLM.coeFn_compLpL (Complex.I • Complex.ofRealCLM.compLpL p μ f),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL p μ f),
    Complex.ofRealCLM.coeFn_compLpL f, Lp.coeFn_zero ℝ p μ] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply, h₃, h₄, Complex.reCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.I_mul_re, Complex.ofReal_im, neg_zero, Pi.zero_apply]

/-- The imaginary part of `i` times a real function is the function. -/
theorem imCLM_compLpL_I_smul_ofRealCLM_compLpL (f : Lp ℝ p μ) :
    Complex.imCLM.compLpL p μ (Complex.I • Complex.ofRealCLM.compLpL p μ f) = f := by
  refine Lp.ext ?_
  filter_upwards [Complex.imCLM.coeFn_compLpL (Complex.I • Complex.ofRealCLM.compLpL p μ f),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL p μ f),
    Complex.ofRealCLM.coeFn_compLpL f] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.I_mul_im, Complex.ofReal_re]

/-- **A complex `Lᵖ` function is its real part plus `i` times its imaginary part.** -/
theorem ofRealCLM_compLpL_reCLM_compLpL_add_I_smul (v : Lp ℂ p μ) :
    Complex.ofRealCLM.compLpL p μ (Complex.reCLM.compLpL p μ v) +
      Complex.I • Complex.ofRealCLM.compLpL p μ (Complex.imCLM.compLpL p μ v) = v := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLpL p μ (Complex.reCLM.compLpL p μ v))
      (Complex.I • Complex.ofRealCLM.compLpL p μ (Complex.imCLM.compLpL p μ v)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL p μ v),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL p μ (Complex.imCLM.compLpL p μ v)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.imCLM.compLpL p μ v),
    Complex.reCLM.coeFn_compLpL v, Complex.imCLM.coeFn_compLpL v] with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, h₄, h₅, h₆, Complex.ofRealCLM_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, mul_comm]
  exact Complex.re_add_im (v x)

/-- **The real form of a complex operator** `f ↦ Re (Q (ι f))` is a continuous real-linear
operator on `Lᵖ(μ; ℝ)`. -/
theorem exists_forall_eq_reCLM_compLpL_apply_ofRealCLM_compLpL (Q : Lp ℂ p μ →L[ℂ] Lp ℂ p μ) :
    ∃ T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ,
      ∀ f, T f = Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ f)) :=
  ⟨(Complex.reCLM.compLpL p μ).comp ((Q.restrictScalars ℝ).comp (Complex.ofRealCLM.compLpL p μ)),
    fun _ ↦ rfl⟩

section RealKernel

variable {Q : Lp ℂ p μ →L[ℂ] Lp ℂ p μ} {κ : X × X → ℝ}

/-- An operator with a real kernel maps a real function to a real function:
`(Q (ι f))(x) = ∫ κ(x, y) f(y) dμ(y)` almost everywhere. -/
theorem apply_ofRealCLM_compLpL_ae_eq_ofReal_integral
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (f : Lp ℝ p μ) :
    (Q (Complex.ofRealCLM.compLpL p μ f) : X → ℂ) =ᵐ[μ]
      fun x ↦ ((∫ y, κ (x, y) * f y ∂μ : ℝ) : ℂ) := by
  filter_upwards [hQ (Complex.ofRealCLM.compLpL p μ f)] with x hx
  rw [hx, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL f] with y hy
  rw [hy, Complex.ofRealCLM_apply, Complex.ofReal_mul]

/-- **The kernel of the real form**: `Re (Q (ι f))(x) = ∫ κ(x, y) f(y) dμ(y)` almost
everywhere. -/
theorem reCLM_compLpL_apply_ofRealCLM_compLpL_ae_eq_integral
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (f : Lp ℝ p μ) :
    (Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ f)) : X → ℝ) =ᵐ[μ]
      fun x ↦ ∫ y, κ (x, y) * f y ∂μ := by
  filter_upwards [Complex.reCLM.coeFn_compLpL (Q (Complex.ofRealCLM.compLpL p μ f)),
    apply_ofRealCLM_compLpL_ae_eq_ofReal_integral hQ f] with x h₁ h₂
  rw [h₁, Complex.reCLM_apply, h₂, Complex.ofReal_re]

/-- **`Q (ι f) = ι (T f)`** for an operator with a real kernel. -/
theorem ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (f : Lp ℝ p μ) :
    Complex.ofRealCLM.compLpL p μ
        (Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ f))) =
      Q (Complex.ofRealCLM.compLpL p μ f) := by
  refine Lp.ext ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
      (Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ f))),
    reCLM_compLpL_apply_ofRealCLM_compLpL_ae_eq_integral hQ f,
    apply_ofRealCLM_compLpL_ae_eq_ofReal_integral hQ f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, Complex.ofRealCLM_apply]

/-- **`Re (Q v) = T (Re v)`** for an operator with a real kernel. -/
theorem reCLM_compLpL_apply_eq_of_real_kernel
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (v : Lp ℂ p μ) :
    Complex.reCLM.compLpL p μ (Q v) =
      Complex.reCLM.compLpL p μ
        (Q (Complex.ofRealCLM.compLpL p μ (Complex.reCLM.compLpL p μ v))) := by
  conv_lhs => rw [← ofRealCLM_compLpL_reCLM_compLpL_add_I_smul v, map_add, map_smul, map_add,
    ← ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ (Complex.imCLM.compLpL p μ v),
    reCLM_compLpL_I_smul_ofRealCLM_compLpL, add_zero]

/-- **`Im (Q v) = T (Im v)`** for an operator with a real kernel. -/
theorem imCLM_compLpL_apply_eq_of_real_kernel
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (v : Lp ℂ p μ) :
    Complex.imCLM.compLpL p μ (Q v) =
      Complex.reCLM.compLpL p μ
        (Q (Complex.ofRealCLM.compLpL p μ (Complex.imCLM.compLpL p μ v))) := by
  conv_lhs => rw [← ofRealCLM_compLpL_reCLM_compLpL_add_I_smul v, map_add, map_smul, map_add,
    ← ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ (Complex.reCLM.compLpL p μ v),
    ← ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ (Complex.imCLM.compLpL p μ v),
    imCLM_compLpL_ofRealCLM_compLpL, imCLM_compLpL_I_smul_ofRealCLM_compLpL, zero_add]

/-- **`Q (ι f + i • ι g) = ι (T f) + i • ι (T g)`** for an operator with a real kernel. -/
theorem apply_ofRealCLM_compLpL_add_I_smul_eq_of_real_kernel
    (hQ : ∀ g : Lp ℂ p μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (f g : Lp ℝ p μ) :
    Q (Complex.ofRealCLM.compLpL p μ f + Complex.I • Complex.ofRealCLM.compLpL p μ g) =
      Complex.ofRealCLM.compLpL p μ
          (Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ f))) +
        Complex.I • Complex.ofRealCLM.compLpL p μ
          (Complex.reCLM.compLpL p μ (Q (Complex.ofRealCLM.compLpL p μ g))) := by
  rw [map_add, map_smul, ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ f,
    ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ g]

end RealKernel

end MeasureTheory.Lp
