import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Extreme value theorem for upper semicontinuous functions (deprecated)

The extreme value theorem for upper semicontinuous functions is
`UpperSemicontinuousOn.exists_isMaxOn` in mathlib, and boundedness is
`UpperSemicontinuousOn.bddAbove_of_isCompact`. The declarations below are deprecated shims for the
former MCMC names.
-/

open Set Filter Topology

namespace IsCompact

variable {α : Type*} [TopologicalSpace α] {f : α → ℝ} {K : Set α}

@[deprecated upperSemicontinuousOn_iff_restrict (since := "2026-10-17")]
lemma upperSemicontinuousOn_iff_upperSemicontinuous {s : Set α} :
    UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.domRestrict f) :=
  upperSemicontinuousOn_iff_restrict.symm

@[deprecated UpperSemicontinuousOn.bddAbove_of_isCompact (since := "2026-10-17")]
theorem bddAbove_image_of_upperSemicontinuousOn (hK : IsCompact K)
    (hf : UpperSemicontinuousOn f K) : BddAbove (f '' K) :=
  hf.bddAbove_of_isCompact hK

@[deprecated "use `tendsto_one_div_add_atTop_nhds_zero_nat`" (since := "2026-10-17")]
lemma tendsto_const_sub_inv_add_one_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c - 1 / (n + 1)) atTop (𝓝 c) := by
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

@[deprecated UpperSemicontinuousOn.exists_isMaxOn (since := "2026-10-17")]
theorem exists_isMaxOn_of_upperSemicontinuousOn (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ :=
  hf.exists_isMaxOn hK_nonempty hK

@[deprecated upperSemicontinuousOn_iff_restrict (since := "2026-10-17")]
lemma usco_on_iff_usco {s : Set α} :
    UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.domRestrict f) :=
  upperSemicontinuousOn_iff_restrict.symm

@[deprecated UpperSemicontinuousOn.bddAbove_of_isCompact (since := "2026-10-17")]
theorem bdd_above_image_usco_on (hK : IsCompact K)
    (hf : UpperSemicontinuousOn f K) : BddAbove (f '' K) :=
  hf.bddAbove_of_isCompact hK

@[deprecated "use `tendsto_one_div_add_atTop_nhds_zero_nat`" (since := "2026-10-17")]
lemma tendsto_sub_inv_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c - 1 / (n + 1)) atTop (𝓝 c) := by
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

@[deprecated UpperSemicontinuousOn.exists_isMaxOn (since := "2026-10-17")]
theorem exists_max_on_usco (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ :=
  hf.exists_isMaxOn hK_nonempty hK

end IsCompact
