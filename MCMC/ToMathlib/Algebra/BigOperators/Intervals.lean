/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# The square of a sum over a range, by lags

Staged for `Mathlib/Algebra/BigOperators/Intervals.lean`.

## Search

At Mathlib `d13f23b`: `grep -rn "sq_sum_range\|sum_sq_range\|sum_range_sq" Mathlib` finds nothing;
`grep -rn "sq_sum_le_card_mul_sum_sq" Mathlib` finds the Cauchy–Schwarz inequality for finite sums
(`Algebra/Order/Chebyshev.lean`), and `Algebra/BigOperators/Intervals.lean` has sums over
intervals and their reflection, with no expansion of `(∑_{k < n} a k)²` by lags.
-/

@[expose] public section

open Finset

/-- **The square of a sum, by lags**:
`(∑_{k < n} a k)² = ∑_{k < n} (2 ∑_{l < n - k} a k a (k + l) - (a k)²)`. -/
theorem Finset.sq_sum_range_eq_sum_range_sum_range {R : Type*} [CommRing R] (a : ℕ → R)
    (n : ℕ) : (∑ k ∈ range n, a k) ^ 2 =
      ∑ k ∈ range n, (2 * ∑ l ∈ range (n - k), a k * a (k + l) - a k ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h (k : ℕ) (hk : k ∈ range n) : 2 * ∑ l ∈ range (n + 1 - k), a k * a (k + l) - a k ^ 2 =
        (2 * ∑ l ∈ range (n - k), a k * a (k + l) - a k ^ 2) + 2 * (a k * a n) := by
      rw [Nat.sub_add_comm (mem_range.1 hk).le, sum_range_succ,
        Nat.add_sub_of_le (mem_range.1 hk).le]
      ring
    rw [sum_range_succ, add_sq, ih, sum_range_succ, sum_congr rfl h, sum_add_distrib,
      Nat.add_sub_cancel_left, sum_range_one, add_zero, ← mul_sum, ← sum_mul]
    ring
