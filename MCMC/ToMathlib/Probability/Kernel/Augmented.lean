/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import MCMC.ToMathlib.Probability.Kernel.Mixing

/-!
# An iterated random map together with its input

For the recursion `ξ (k + 1) = F (ξ k) (w k)` with independent inputs `w k ∼ ρ`, an output that
reads the current input, such as `w k - f (ξ k)`, is a function of the pair `(ξ k, w k)`, not of
`ξ k`. The pair is again an iterated random map,
`(x, w) ↦ (F x w, w')` with a fresh `w' ∼ ρ`, with Mathlib's kernel
`(Kernel.id ×ₖ Kernel.const (X × W) ρ).map fun p ↦ (Function.uncurry F p.1, p.2)`; no new object is
introduced. Here:

* **Its powers** (`ProbabilityTheory.Kernel.pow_succ_map_prod_const_prod_apply`): from `(x, w)`,
  the pair after `n + 1` steps has the law `Pⁿ (F x w) ⊗ ρ`, `P` the kernel of `F`. So a
  minorization `α • ν ≤ Pᵐ y` of the state chain gives `α • (ν ⊗ ρ) ≤ Q^{m+1} (x, w)` wherever
  `F x w = y`.
* **Its law as a process** (`ProbabilityTheory.map_eq_trajMeasure_prodMk_of_iIndepFun`): the
  trajectory of the pairs `(ξ k, w k)` has the law of the chain of the pair kernel, started at
  the law of `(ξ 0, w 0)`, under the hypotheses of
  `ProbabilityTheory.map_eq_trajMeasure_of_iIndepFun` for `ξ`; so do the pairs from time `1`,
  started at the law of `(ξ 1, w 1)`
  (`ProbabilityTheory.map_eq_trajMeasure_prodMk_succ_of_iIndepFun`, through
  `ProbabilityTheory.indepFun_prodMk_shift_of_iIndepFun`), which asks of `ξ 0` only what `ξ 1`
  needs.
* **The drift of a perturbed contraction**: on an additive group, if `√V` is subadditive (`√V` a
  seminorm, e.g. a positive semidefinite quadratic form), the noise-free map contracts,
  `V (F₀ x) ≤ θ V x` with `θ < 1`, and the input enters with `V (F x w - F₀ x) ≤ g w`, then
  `V (F x w) ≤ (1 + θ)/2 · V x + (1 + θ)/(1 - θ) · g w`
  (`NNReal.le_one_add_div_two_mul_add_of_sqrt_le`, from `(p + q)² ≤ (1 + θ)/2 · D +
  (1 + θ)/(1 - θ) · q²` for `p² ≤ θ D`). The kernel of `F` then has the drift
  `((1 + θ)/2, (1 + θ)/(1 - θ) K)` for `∫⁻ g ∂ρ ≤ K`
  (`ProbabilityTheory.Kernel.lintegral_map_prod_const_le_of_sqrt_add_le`), and the pair kernel
  the drift `((1 + θ)/2, 2 K/(1 - θ))` for `V (x, w) = V x + 2 g w/(1 - θ)`
  (`ProbabilityTheory.Kernel.lintegral_map_prod_const_prod_le_of_sqrt_add_le`).
* **Two steps of a random map** are the map of the product noise,
  `P² x = (ρ ⊗ ρ).map (fun w ↦ F (F x w₀) w₁)`
  (`ProbabilityTheory.Kernel.pow_two_map_prod_const_apply`), and a Lebesgue minorization on a
  translated set pushes forward to a fixed one
  (`MeasureTheory.Measure.smul_map_restrict_le_map_of_eq`): the two ingredients of a minorization
  of `P²` when two steps are a fixed map after a translation of the noise.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rln "Foster\|Lyapunov" Probability` finds
nothing; `grep -rn "pow_succ.*\.prod" Probability/Kernel` finds no formula for powers of a kernel
of the form `x ↦ δ_{f x} ⊗ ρ`; the Markov-kernel files of this library have the drift from a
pointwise bound (`ProbabilityTheory.Kernel.lintegral_map_prod_const_le`) and the square root of a
drift (`ProbabilityTheory.Kernel.lintegral_sqrt_le_of_drift`), not the drift of a perturbed
contraction; `grep -rln "smul_map\|map_restrict_le" MeasureTheory/Measure` finds only the Haar
character of a group automorphism (`addEquivAddHaarChar_smul_map`), no pushforward of a
minorization; `grep -rn "\^ 2) x =" Probability` finds no two-step formula.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {X W : Type*} {mX : MeasurableSpace X} {mW : MeasurableSpace W}

/-- **A perturbed contraction of a seminorm square**: if `√a ≤ √b + √c` and `b ≤ θ d` with
`θ < 1`, then `a ≤ (1 + θ)/2 · d + (1 + θ)/(1 - θ) · c`. -/
theorem NNReal.le_one_add_div_two_mul_add_of_sqrt_le {a b c d θ : ℝ≥0} (hθ : θ < 1)
    (h : NNReal.sqrt a ≤ NNReal.sqrt b + NNReal.sqrt c) (hb : b ≤ θ * d) :
    a ≤ (1 + θ) / 2 * d + (1 + θ) / (1 - θ) * c := by
  have hθ' : (θ : ℝ) < 1 := by exact_mod_cast hθ
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hθ.le]
  have ha : (a : ℝ) = (NNReal.sqrt a : ℝ) ^ 2 := by exact_mod_cast (NNReal.sq_sqrt a).symm
  have hb' : (b : ℝ) = (NNReal.sqrt b : ℝ) ^ 2 := by exact_mod_cast (NNReal.sq_sqrt b).symm
  have hc : (c : ℝ) = (NNReal.sqrt c : ℝ) ^ 2 := by exact_mod_cast (NNReal.sq_sqrt c).symm
  have hs : (NNReal.sqrt a : ℝ) ≤ NNReal.sqrt b + NNReal.sqrt c := by exact_mod_cast h
  have hpd : (NNReal.sqrt b : ℝ) ^ 2 ≤ θ * d := hb' ▸ (by exact_mod_cast hb)
  set p : ℝ := (NNReal.sqrt b : ℝ)
  set r : ℝ := (NNReal.sqrt c : ℝ)
  have hp0 : 0 ≤ p := NNReal.coe_nonneg _
  have hp : (θ : ℝ) = 0 → p = 0 := fun h0 ↦ le_antisymm (by nlinarith [h0 ▸ hpd]) hp0
  have key : 2 * (1 - θ) * (p + r) ^ 2 ≤ (1 - θ) * (1 + θ) * d + 2 * (1 + θ) * r ^ 2 := by
    rcases θ.coe_nonneg.eq_or_lt with h0 | h0
    · rw [← h0, hp h0.symm]
      nlinarith [d.coe_nonneg]
    · refine le_of_mul_le_mul_left ?_ h0
      nlinarith [sq_nonneg ((1 - θ) * p - 2 * θ * r), mul_le_mul_of_nonneg_left hpd
        (by nlinarith : (0 : ℝ) ≤ (1 - θ) * (1 + θ))]
  have hsq : (NNReal.sqrt a : ℝ) ^ 2 ≤ (p + r) ^ 2 :=
    pow_le_pow_left₀ (NNReal.coe_nonneg _) hs 2
  have h1 : (1 : ℝ) - θ ≠ 0 := (sub_pos.2 hθ').ne'
  rw [ha, hc, (by field_simp : (1 + (θ : ℝ)) / 2 * d + (1 + θ) / (1 - θ) * r ^ 2 =
    ((1 - θ) * (1 + θ) * d + 2 * (1 + θ) * r ^ 2) / (2 * (1 - θ))),
    le_div_iff₀ (by linarith)]
  nlinarith

/-- **A Lebesgue minorization on a translated set pushes forward to a fixed one**: if
`c • λ|_{(t + ·)⁻¹' B} ≤ μ` for a left-invariant `λ`, and `f d = L (t + d)` whenever `t + d ∈ B`,
then `c • (λ|_B).map L ≤ μ.map f`. -/
theorem MeasureTheory.Measure.smul_map_restrict_le_map_of_eq {G Y : Type*} [AddGroup G]
    [MeasurableSpace G] [MeasurableAdd G] [MeasurableSpace Y] (μ₀ : Measure G)
    [μ₀.IsAddLeftInvariant] {μ : Measure G} {f L : G → Y} (hf : Measurable f) (hL : Measurable L)
    {B : Set G} (hB : MeasurableSet B) {t : G} {c : ℝ≥0∞}
    (hμ : c • μ₀.restrict ((t + ·) ⁻¹' B) ≤ μ) (hfL : ∀ d, t + d ∈ B → f d = L (t + d)) :
    c • (μ₀.restrict B).map L ≤ μ.map f := by
  have ht : Measurable (t + · : G → G) := measurable_const_add t
  calc c • (μ₀.restrict B).map L = c • ((μ₀.restrict ((t + ·) ⁻¹' B)).map (t + ·)).map L := by
        rw [← Measure.restrict_map ht hB, map_add_left_eq_self]
    _ = c • (μ₀.restrict ((t + ·) ⁻¹' B)).map f := by
        rw [Measure.map_map hL ht]
        exact congrArg (c • ·) (Measure.map_congr ((ae_restrict_iff' (ht hB)).2
          (ae_of_all _ fun d hd ↦ (hfL d hd).symm)))
    _ = (c • μ₀.restrict ((t + ·) ⁻¹' B)).map f := (Measure.map_smul c hf.aemeasurable).symm
    _ ≤ μ.map f := Measure.map_mono hμ hf

namespace ProbabilityTheory

namespace Kernel

/-- **The drift of a random map that perturbs a contraction**: on an additive group, let `√V` be
subadditive, `V (F₀ x) ≤ θ V x` with `θ < 1`, and `V (F x w - F₀ x) ≤ g w` with
`∫⁻ g ∂ρ ≤ K`. Then the kernel `x ↦ ρ.map (F x)` has the drift
`∫⁻ V ∂(P x) ≤ (1 + θ)/2 · V x + (1 + θ)/(1 - θ) · K`. -/
theorem lintegral_map_prod_const_le_of_sqrt_add_le [AddGroup X] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) {V : X → ℝ≥0} (hV : Measurable V)
    (hsub : ∀ p q, NNReal.sqrt (V (p + q)) ≤ NNReal.sqrt (V p) + NNReal.sqrt (V q))
    {F₀ : X → X} {θ : ℝ≥0} (hθ : θ < 1) (h₀ : ∀ x, V (F₀ x) ≤ θ * V x) {g : W → ℝ≥0}
    (hg : ∀ x w, V (F x w - F₀ x) ≤ g w) {ρ : Measure W} [IsProbabilityMeasure ρ] {K : ℝ≥0}
    (hK : ∫⁻ w, g w ∂ρ ≤ K) (x : X) :
    ∫⁻ y, V y ∂((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F) x) ≤
      ((1 + θ) / 2 : ℝ≥0) * V x + ((1 + θ) / (1 - θ) * K : ℝ≥0) := by
  refine lintegral_map_prod_const_le hF hV (g := fun w ↦ ((1 + θ) / (1 - θ) * g w : ℝ≥0))
    (fun x w ↦ ?_) ?_ x
  · have h := hsub (F x w - F₀ x) (F₀ x)
    rw [sub_add_cancel] at h
    exact_mod_cast (NNReal.le_one_add_div_two_mul_add_of_sqrt_le hθ (h.trans_eq (add_comm _ _))
      (h₀ x)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hg x w) zero_le))
  · simp_rw [ENNReal.coe_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    gcongr

/-- **The drift of a random map with its input**: under the hypotheses of
`lintegral_map_prod_const_le_of_sqrt_add_le` and `g` measurable, the pair `(ξ, w)`, moving by
`(x, w) ↦ (F x w, w')`, `w' ∼ ρ`, has the drift `((1 + θ)/2, 2 K/(1 - θ))` for
`V (x, w) = V x + 2 g w/(1 - θ)`. -/
theorem lintegral_map_prod_const_prod_le_of_sqrt_add_le [AddGroup X] {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) {V : X → ℝ≥0} (hV : Measurable V)
    (hsub : ∀ p q, NNReal.sqrt (V (p + q)) ≤ NNReal.sqrt (V p) + NNReal.sqrt (V q))
    {F₀ : X → X} {θ : ℝ≥0} (hθ : θ < 1) (h₀ : ∀ x, V (F₀ x) ≤ θ * V x) {g : W → ℝ≥0}
    (hgm : Measurable g) (hg : ∀ x w, V (F x w - F₀ x) ≤ g w) {ρ : Measure W}
    [IsProbabilityMeasure ρ] {K : ℝ≥0} (hK : ∫⁻ w, g w ∂ρ ≤ K) (z : X × W) :
    ∫⁻ y, (V y.1 + 2 / (1 - θ) * g y.2 : ℝ≥0) ∂((Kernel.id ×ₖ Kernel.const (X × W) ρ).map
      (fun p : (X × W) × W ↦ (Function.uncurry F p.1, p.2)) z) ≤
      ((1 + θ) / 2 : ℝ≥0) * (V z.1 + 2 / (1 - θ) * g z.2 : ℝ≥0) + (2 / (1 - θ) * K : ℝ≥0) := by
  have hγβ : (1 + θ) / 2 * (2 / (1 - θ)) = (1 + θ) / (1 - θ) := by
    rw [div_mul_div_comm, mul_comm (1 + θ) 2, mul_div_mul_left _ _ two_ne_zero]
  refine lintegral_map_prod_const_le (F := fun z w ↦ (Function.uncurry F z, w))
    (V := fun y ↦ V y.1 + 2 / (1 - θ) * g y.2) ((hF.comp measurable_fst).prodMk measurable_snd)
    ((hV.comp measurable_fst).add ((hgm.comp measurable_snd).const_mul _))
    (g := fun w ↦ (2 / (1 - θ) * g w : ℝ≥0)) (fun z w ↦ ?_) ?_ z
  · have h := hsub (F z.1 z.2 - F₀ z.1) (F₀ z.1)
    rw [sub_add_cancel] at h
    have h' : V (F z.1 z.2) ≤ (1 + θ) / 2 * V z.1 + (1 + θ) / (1 - θ) * g z.2 :=
      (NNReal.le_one_add_div_two_mul_add_of_sqrt_le hθ (h.trans_eq (add_comm _ _))
        (h₀ z.1)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hg z.1 z.2) zero_le))
    have h'' : V (F z.1 z.2) + 2 / (1 - θ) * g w ≤
        (1 + θ) / 2 * (V z.1 + 2 / (1 - θ) * g z.2) + 2 / (1 - θ) * g w := by
      rw [mul_add, ← mul_assoc, hγβ]
      exact add_le_add h' le_rfl
    exact_mod_cast h''
  · simp_rw [ENNReal.coe_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    gcongr

/-- **Two steps of a random map**: the kernel `x ↦ ρ.map (F x)` moves `x` in two steps to the law
of `F (F x w₀) w₁` for independent `w₀, w₁ ∼ ρ`. -/
theorem pow_two_map_prod_const_apply {F : X → W → X} (hF : Measurable (Function.uncurry F))
    (ρ : Measure W) [IsProbabilityMeasure ρ] (x : X) :
    (((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)) ^ 2) x =
      (ρ.prod ρ).map fun w ↦ F (F x w.1) w.2 := by
  set P := (Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)
  have : IsMarkovKernel P := IsMarkovKernel.map _ hF
  have hFx : Measurable (F x) := hF.comp measurable_prodMk_left
  have h2 : P ^ 2 = P ∘ₖ P := pow_two P
  calc (P ^ 2) x = ((ρ.map (F x)).prod (ρ.map id)).map (Function.uncurry F) := by
        rw [h2, Kernel.comp_apply, map_prod_const_apply hF, Measure.map_id]
        exact comp_map_prod_const hF ρ _
    _ = (ρ.prod ρ).map fun w ↦ F (F x w.1) w.2 := by
        rw [Measure.map_prod_map _ _ hFx measurable_id,
          Measure.map_map hF (hFx.prodMap measurable_id)]
        rfl

/-- **The powers of a random map with its input**: the pair `(ξ, w)`, moving by
`(x, w) ↦ (F x w, w')`, `w' ∼ ρ`, has after `n + 1` steps from `z` the law `Pⁿ (F z) ⊗ ρ`, `P` the
kernel `x ↦ ρ.map (F x)`. -/
theorem pow_succ_map_prod_const_prod_apply {F : X → W → X}
    (hF : Measurable (Function.uncurry F)) (ρ : Measure W) [IsProbabilityMeasure ρ] (n : ℕ)
    (z : X × W) :
    (((Kernel.id ×ₖ Kernel.const (X × W) ρ).map
      fun p : (X × W) × W ↦ (Function.uncurry F p.1, p.2)) ^ (n + 1)) z =
      ((((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)) ^ n)
        (Function.uncurry F z)).prod ρ := by
  set P := (Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)
  set Q := (Kernel.id ×ₖ Kernel.const (X × W) ρ).map
    fun p : (X × W) × W ↦ (Function.uncurry F p.1, p.2)
  have hG : Measurable fun p : (X × W) × W ↦ (Function.uncurry F p.1, p.2) :=
    (hF.comp measurable_fst).prodMk measurable_snd
  have : IsMarkovKernel P := IsMarkovKernel.map _ hF
  have : IsMarkovKernel Q := IsMarkovKernel.map _ hG
  have hpP (n : ℕ) : P ^ (n + 1) = P ∘ₖ (P ^ n) := pow_succ' P n
  have hpQ (n : ℕ) : Q ^ (n + 1) = Q ∘ₖ (Q ^ n) := pow_succ' Q n
  induction n generalizing z with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    show Q z = (Kernel.id (Function.uncurry F z)).prod ρ
    rw [Kernel.id_apply, Measure.dirac_prod]
    exact map_prod_const_apply (F := fun z w ↦ (Function.uncurry F z, w)) hG ρ z
  | succ n ih =>
    calc (Q ^ (n + 1 + 1)) z = Q ∘ₘ ((P ^ n) (Function.uncurry F z)).prod ρ := by
          rw [hpQ, Kernel.comp_apply, ih]
      _ = ((((P ^ n) (Function.uncurry F z)).prod ρ).prod ρ).map
            (Prod.map (Function.uncurry F) id) :=
          comp_map_prod_const (F := fun z w ↦ (Function.uncurry F z, w)) hG ρ _
      _ = ((((P ^ n) (Function.uncurry F z)).prod ρ).map (Function.uncurry F)).prod
            (ρ.map id) := (Measure.map_prod_map _ _ hF measurable_id).symm
      _ = ((P ^ (n + 1)) (Function.uncurry F z)).prod ρ := by
          rw [Measure.map_id, ← comp_map_prod_const hF, hpP, Kernel.comp_apply]

end Kernel

open Finset Preorder in
/-- **A random map with its input is a Markov chain**: under the hypotheses of
`map_eq_trajMeasure_of_iIndepFun` (`ξ (k + 1) = F (ξ k) (w k)`, the `w k` independent with law
`ρ` and independent of `ξ 0`), the trajectory of the pairs `(ξ k, w k)` has the law of the chain of
any kernel `Q` with `Q (x, w) = ρ.map (fun w' ↦ (F x w, w'))`, started at the law of
`(ξ 0, w 0)`. -/
theorem map_eq_trajMeasure_prodMk_of_iIndepFun {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Kernel (X × W) (X × W)} [IsMarkovKernel Q]
    {F : X → W → X} (hF : Measurable (Function.uncurry F)) {ρ : Measure W}
    (hQ : ∀ z, Q z = ρ.map fun w' ↦ (Function.uncurry F z, w'))
    {ξ : ℕ → Ω → X} {w : ℕ → Ω → W} (hξ₀ : Measurable (ξ 0)) (hw : ∀ k, Measurable (w k))
    (hξ : ∀ k ω, ξ (k + 1) ω = F (ξ k ω) (w k ω)) (hind : IndepFun (ξ 0) (fun ω k ↦ w k ω) P)
    (hiid : iIndepFun w P) (hρ : ∀ k, P.map (w k) = ρ) :
    P.map (fun ω k ↦ (ξ k ω, w k ω)) = Kernel.trajMeasure (X := fun _ ↦ X × W)
      (P.map fun ω ↦ (ξ 0 ω, w 0 ω)) fun n ↦
        Q.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  exact map_eq_trajMeasure_of_iIndepFun (Q := Q) (F := fun z w ↦ (Function.uncurry F z, w))
    ((hF.comp measurable_fst).prodMk measurable_snd) hQ (ξ := fun k ω ↦ (ξ k ω, w k ω))
    (w := fun k ω ↦ w (k + 1) ω) (hξ₀.prodMk (hw 0)) (fun k ↦ hw (k + 1))
    (fun k ω ↦ Prod.ext (hξ k ω) rfl) (indepFun_prodMk_shift_of_iIndepFun hξ₀ hw hind hiid)
    (hiid.precomp (g := fun k ↦ k + 1) fun _ _ h ↦ Nat.succ_injective h) fun k ↦ hρ (k + 1)

open Finset Preorder in
/-- **The pair chain from time `1`**: under the hypotheses of
`map_eq_trajMeasure_prodMk_of_iIndepFun`, the trajectory of the pairs `(ξ (k + 1), w (k + 1))` has
the law of the same chain started at the law of `(ξ 1, w 1)`; `ξ 0` enters only through `ξ 1`, so
no integrability of `ξ 0` beyond that of `ξ 1` is needed downstream. -/
theorem map_eq_trajMeasure_prodMk_succ_of_iIndepFun {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Kernel (X × W) (X × W)} [IsMarkovKernel Q]
    {F : X → W → X} (hF : Measurable (Function.uncurry F)) {ρ : Measure W}
    (hQ : ∀ z, Q z = ρ.map fun w' ↦ (Function.uncurry F z, w'))
    {ξ : ℕ → Ω → X} {w : ℕ → Ω → W} (hξ₀ : Measurable (ξ 0)) (hw : ∀ k, Measurable (w k))
    (hξ : ∀ k ω, ξ (k + 1) ω = F (ξ k ω) (w k ω)) (hind : IndepFun (ξ 0) (fun ω k ↦ w k ω) P)
    (hiid : iIndepFun w P) (hρ : ∀ k, P.map (w k) = ρ) :
    P.map (fun ω k ↦ (ξ (k + 1) ω, w (k + 1) ω)) = Kernel.trajMeasure (X := fun _ ↦ X × W)
      (P.map fun ω ↦ (ξ 1 ω, w 1 ω)) fun n ↦
        Q.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  have h₁ : Measurable (ξ 1) := by
    rw [(funext (hξ 0) : ξ 1 = fun ω ↦ F (ξ 0 ω) (w 0 ω))]
    exact hF.comp (hξ₀.prodMk (hw 0))
  exact map_eq_trajMeasure_prodMk_of_iIndepFun hF hQ (ξ := fun k ω ↦ ξ (k + 1) ω)
    (w := fun k ω ↦ w (k + 1) ω) h₁ (fun k ↦ hw (k + 1)) (fun k ↦ hξ (k + 1))
    (((indepFun_prodMk_shift_of_iIndepFun hξ₀ hw hind hiid).comp hF measurable_id).congr
      (ae_of_all _ fun ω ↦ (hξ 0 ω).symm) (ae_of_all _ fun _ ↦ rfl))
    (hiid.precomp (add_left_injective 1)) fun k ↦ hρ (k + 1)

end ProbabilityTheory
