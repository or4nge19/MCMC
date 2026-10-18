/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Bilinear
import MCMC.ToMathlib.Analysis.Normed.Algebra.Resolvent

/-!
# Gelfand radius of the transpose

The transpose `f ↦ f ∘L T` on `StrongDual ℝ E` has the Gelfand radius of `T`: by Hahn–Banach its
powers have the norms of the powers of `T`.

## Main statements

* `norm_compL_flip_pow`, `gelfandRadius_compL_flip`.

Staged for `Mathlib/Analysis/Normed/Algebra/GelfandRadius.lean` (operator section). Searched on
2026-10-17: no Banach transpose with its norm in the pinned tree or on mathlib master (only
`compL`/`flip`).
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compL_flip_pow_apply (T : E →L[ℝ] E) (n : ℕ) (f : StrongDual ℝ E) :
    (((ContinuousLinearMap.compL ℝ E E ℝ).flip T) ^ n) f = f.comp (T ^ n) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, pow_succ]; rfl

/-- The powers of the transpose `f ↦ f ∘L T` have the norms of the powers of `T`. -/
theorem norm_compL_flip_pow (T : E →L[ℝ] E) (n : ℕ) :
    ‖((ContinuousLinearMap.compL ℝ E E ℝ).flip T) ^ n‖ = ‖T ^ n‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · rw [compL_flip_pow_apply, mul_comm]
    exact f.opNorm_comp_le _
  · obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℝ ((T ^ n) x)
    calc ‖(T ^ n) x‖ = (((ContinuousLinearMap.compL ℝ E E ℝ).flip T) ^ n) g x := by
          rw [compL_flip_pow_apply, ContinuousLinearMap.comp_apply, hgx]
          rfl
      _ ≤ ‖(((ContinuousLinearMap.compL ℝ E E ℝ).flip T) ^ n) g‖ * ‖x‖ :=
          (Real.le_norm_self _).trans (ContinuousLinearMap.le_opNorm _ x)
      _ ≤ ‖((ContinuousLinearMap.compL ℝ E E ℝ).flip T) ^ n‖ * ‖x‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ g).trans
            (mul_le_of_le_one_right (norm_nonneg _) hg)

/-- The transpose `f ↦ f ∘L T` has the Gelfand radius of `T`. -/
theorem gelfandRadius_compL_flip (T : E →L[ℝ] E) :
    gelfandRadius ((ContinuousLinearMap.compL ℝ E E ℝ).flip T) = gelfandRadius T :=
  tendsto_nhds_unique (tendsto_gelfandRadius _)
    ((tendsto_gelfandRadius T).congr fun n ↦ by rw [norm_compL_flip_pow])
