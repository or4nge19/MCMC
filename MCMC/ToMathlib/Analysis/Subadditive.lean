/-
Copyright (c) 2026 Sébastien Gouëzel, Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Thomas Browning
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Submultiplicative sequences

`Submultiplicative u` and Fekete's lemma for its nth roots (`Submultiplicative.tendsto_lim`).

Port of the `Submultiplicative` part of `Mathlib/Analysis/Subadditive.lean` at mathlib4
`f58d2cce48bd` (#42605, 2026-09-30). Changes: no module-system header, `Submultiplicative` is not
linked to `Subadditive` by `to_additive`, and `lim` is marked `noncomputable` (the origin is a
`noncomputable section`). Delete at a pin containing that commit.
-/

open Set Filter

open scoped Topology

/-- A sequence is submultiplicative if it satisfies the inequality `u (m + n) ≤ u m * u n`
for all `m, n`. -/
def Submultiplicative {α β : Type*} [Add α] [Mul β] [LE β] (u : α → β) : Prop :=
  ∀ m n, u (m + n) ≤ u m * u n

namespace Submultiplicative

variable {u : ℕ → ℝ} (h : Submultiplicative u)

/-- The limit of the nth roots of a submultiplicative sequence. The fact that the nth roots indeed
converge to this limit is given in `Submultiplicative.tendsto_lim`. -/
protected noncomputable def lim (_h : Submultiplicative u) :=
  sInf ((fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) '' Ici 1)

theorem lim_le_rpow (hbdd : ∀ n, 0 ≤ u n) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n ^ (n : ℝ)⁻¹ := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, hn.pos, rfl⟩
  rintro - ⟨n, hn, rfl⟩
  exact Real.rpow_nonneg (hbdd n) n⁻¹

include h in
theorem apply_mul_add_le (k n r) (hbdd : 0 ≤ u n) : u (k * n + r) ≤ u n ^ k * u r := by
  induction k with
  | zero => simp
  | succ k IH => grw [add_one_mul, add_right_comm, h (k * n + r) n, IH, mul_right_comm, pow_succ]

include h in
theorem eventually_rpow_lt_of_rpow_lt (hbdd : ∀ k, 0 ≤ u k) {L : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hL : u n ^ (n : ℝ)⁻¹ < L) : ∀ᶠ p in atTop, u p ^ (p : ℝ)⁻¹ < L := by
  /- It suffices to prove the statement for each arithmetic progression `(n * · + r)`. -/
  refine .atTop_of_arithmetic hn fun r hrn ↦ ?_
  /- `(u n ^ x * u r) ^ (x * n + r)⁻¹` tends to `u n ^ n⁻¹ < L`, hence
  `(u n ^ x * u r) ^ (x * n + r)⁻¹ < L` for sufficiently large `x`. -/
  by_cases hur : u r = 0
  · replace hur (m : ℕ) (hrm : r ≤ m) : u m = 0 := by grind [le_antisymm, h r (m - r)]
    refine (eventually_ne_atTop 0).mono fun m hm ↦ ?_
    rw [hur n hrn.le, Real.zero_rpow (by simpa)] at hL
    rwa [hur (n * m + r) (r.le_add_left (n * m)), Real.zero_rpow]
    rw [ne_eq, inv_eq_zero, Nat.cast_eq_zero, Nat.add_eq_zero_iff, mul_eq_zero]
    grind
  have A : Tendsto (fun x : ℝ ↦ (u n * u r ^ x⁻¹) ^ (n + r / x)⁻¹) atTop _ :=
    (Real.continuousAt_rpow _ (by simp [hn.pos])).tendsto.comp <|
      (((((Real.continuous_const_rpow hur).tendsto' 0 1 (u r).rpow_zero).comp
        tendsto_inv_atTop_zero).const_mul (u n)).prodMk_nhds
          ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).inv₀ (by simpa)))
  have B : Tendsto (fun x : ℝ ↦ (u n ^ x * u r) ^ (x * n + r)⁻¹) atTop (𝓝 (u n ^ (n : ℝ)⁻¹)) := by
    rw [mul_one, add_zero] at A
    refine A.congr' <| (eventually_ne_atTop 0).mono fun x hx ↦ ?_
    rw [add_div' _ _ _ hx, inv_div, div_eq_mul_inv, Real.rpow_mul (by bound),
      Real.mul_rpow (hbdd n) (by bound), Real.rpow_inv_rpow (hbdd r) hx, mul_comm _ x]
  refine ((B.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hL)).mono fun k hk ↦ ?_
  grw [mul_comm, h.apply_mul_add_le k n r (hbdd n)]
  · simpa using hk
  · exact hbdd (k * n +r)

/-- Fekete's lemma for nonnegative submultiplicative sequences:
The nth roots of a submultiplicative sequence converge. -/
theorem tendsto_lim (hbdd : ∀ n, 0 ≤ u n) : Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 h.lim) := by
  refine tendsto_order.mpr ⟨fun l hl ↦ ?_, fun L hL ↦ ?_⟩
  · exact (eventually_ne_atTop 0).mono fun n hn ↦ hl.trans_le (h.lim_le_rpow hbdd hn)
  · obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n ^ (n : ℝ)⁻¹ < L := by
      obtain ⟨-, ⟨n, hn, rfl⟩, xL⟩ := exists_lt_of_csInf_lt (by simp) hL
      exact ⟨n, hn, xL⟩
    exact h.eventually_rpow_lt_of_rpow_lt hbdd npos.ne' hn

end Submultiplicative
