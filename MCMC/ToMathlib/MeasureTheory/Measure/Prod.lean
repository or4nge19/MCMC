/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measures on a product that agree on rectangles

Two measures on `α × β` that agree on measurable rectangles are equal as soon as the first marginal
of one of them is σ-finite: the strips `s ×ˢ univ` over the spanning sets of that marginal are
rectangles of finite measure that cover the product. This generalizes
`MeasureTheory.Measure.ext_prod`, which assumes a finite measure. Some σ-finiteness is needed: the
file `Probability/Kernel/Reversible.lean` of this library exhibits an s-finite measure on `ℝ × ℝ`
that agrees with its image under the swap on every rectangle and differs from it.

Staged for `Mathlib/MeasureTheory/Measure/Prod.lean`. Searched on 2026-11-26 in the pinned Mathlib:
`grep -rn "lemma ext_prod\|theorem ext_prod" Mathlib/MeasureTheory` finds only `ext_prod`,
`ext_prod_iff`, `ext_prod₃`, `ext_prod₃_iff`, `ext_prod₃_iff'`, all for finite measures.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Two measures on a product that agree on measurable rectangles are equal if the first marginal
of one of them is σ-finite. -/
theorem ext_prod_of_sigmaFinite_fst {μ ν : Measure (α × β)} [SigmaFinite μ.fst]
    (h : ∀ ⦃s : Set α⦄ ⦃t : Set β⦄, MeasurableSet s → MeasurableSet t →
      μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  refine ext_of_generateFrom_of_iUnion _ (fun n ↦ spanningSets μ.fst n ×ˢ univ)
    generateFrom_prod.symm isPiSystem_prod ?_
    (fun n ↦ mem_image2_of_mem (measurableSet_spanningSets _ n) MeasurableSet.univ)
    (fun n ↦ ?_) ?_
  · rw [← iUnion_prod_const, iUnion_spanningSets, univ_prod_univ]
  · rw [prod_univ, ← fst_apply (measurableSet_spanningSets _ n)]
    exact (measure_spanningSets_lt_top _ n).ne
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact h hs ht

end MeasureTheory.Measure
