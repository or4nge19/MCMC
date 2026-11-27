/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Probability.Independence.Basic

/-!
# Regrouping independent random variables

If `f` is independent of the pair `(g, h)` and `g` is independent of `h`, then the pair `(f, g)`
is independent of `h` (`ProbabilityTheory.IndepFun.prodMk_of_indepFun_prodMk`): the three are
mutually independent, read through the laws `μ.map (f, (g, h)) = μ.map f ⊗ (μ.map g ⊗ μ.map h)`
and Mathlib's `Measure.prodAssoc_prod`. For an independent sequence `w` independent of `ξ₀`,
`(ξ₀, w 0)` is independent of the shifted sequence `(w (k + 1))_k`
(`ProbabilityTheory.indepFun_prodMk_shift_of_iIndepFun`, through Mathlib's
`indep_iSup_of_disjoint`).

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -n "^lemma IndepFun\.\|^theorem IndepFun\."
Probability/Independence/Basic.lean` finds `meas_inter`, `congr`, `comp`, `comp₀`, `neg_right`,
`neg_left` and the convolution identities; the regrouping lemmas of Mathlib
(`iIndepFun.indepFun_prodMk`, `iIndepFun.indepFun_prodMk_prodMk`) assume an `iIndepFun` family
of one type.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → γ} {h : Ω → δ}

/-- **Regrouping independent variables**: if `f` is independent of `(g, h)` and `g` of `h`, then
`(f, g)` is independent of `h`. -/
theorem IndepFun.prodMk_of_indepFun_prodMk (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (h₁ : IndepFun f (fun ω ↦ (g ω, h ω)) μ) (h₂ : IndepFun g h μ) :
    IndepFun (fun ω ↦ (f ω, g ω)) h μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.prodMk hg).aemeasurable hh.aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).1
      (h₁.comp measurable_id measurable_fst)]
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Measure.prodAssoc_prod, Measure.map_map MeasurableEquiv.prodAssoc.measurable
      ((hf.prodMk hg).prodMk hh),
    ← (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hh.aemeasurable).1 h₂,
    ← (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable (hg.prodMk hh).aemeasurable).1 h₁]
  rfl

/-- **The initial state and the first input are independent of the later inputs**: if the `w k`
are independent and independent of `ξ₀`, then `(ξ₀, w 0)` is independent of `(w (k + 1))_k`. -/
theorem indepFun_prodMk_shift_of_iIndepFun {X W : Type*} {mX : MeasurableSpace X}
    {mW : MeasurableSpace W} [IsProbabilityMeasure μ] {ξ₀ : Ω → X} {w : ℕ → Ω → W}
    (hξ₀ : Measurable ξ₀) (hw : ∀ k, Measurable (w k)) (hind : IndepFun ξ₀ (fun ω k ↦ w k ω) μ)
    (hiid : iIndepFun w μ) : IndepFun (fun ω ↦ (ξ₀ ω, w 0 ω)) (fun ω k ↦ w (k + 1) ω) μ := by
  have h0 := indep_iSup_of_disjoint (fun i ↦ (hw i).comap_le) hiid (S := {0})
    (T := {i | 0 < i}) (by simp)
  have h₂ : IndepFun (w 0) (fun ω k ↦ w (k + 1) ω) μ := by
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h0 ?_) ?_
    · exact le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) ↦
        MeasurableSpace.comap (w i) inferInstance) 0 rfl
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun k ↦ ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | 0 < i}) ↦
        MeasurableSpace.comap (w i) inferInstance) (k + 1) k.succ_pos
  exact (hind.comp measurable_id ((measurable_pi_apply 0).prodMk
    (measurable_pi_iff.2 fun k ↦ measurable_pi_apply (k + 1)))).prodMk_of_indepFun_prodMk hξ₀
      (hw 0) (measurable_pi_iff.2 fun k ↦ hw (k + 1)) h₂

end ProbabilityTheory
