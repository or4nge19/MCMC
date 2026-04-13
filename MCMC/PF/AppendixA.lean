import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Seneta Appendix A

This file packages the number-theoretic input from Seneta's Appendix A in a form adapted to the
existing mathlib API.

## Main definitions

* `rootSequence`: the real sequence `((u (n + 1) : ℝ) ^ (1 / (n + 1)))`, indexed by `n + 1` to
  avoid dividing by `0`.

## Main statements

* `exists_bound_of_gcd_one_of_closed_add`: an additively closed set of natural numbers containing a
  finite subset of gcd `1` is eventually cofinal.
* `limit_of_supermultiplicative_sequence`: a supermultiplicative positive sequence has a limiting
  root sequence.
* `iSup_rootSequence_eq_limit_of_supermultiplicative`: the limit agrees with the supremum of the
  root sequence.

## Implementation notes

The first theorem is intended as a thin bridge to mathlib's `Nat.setGcd` and Frobenius-number API.
The limit theorems are designed to be proved by reducing supermultiplicativity to the subadditive
theory in `Mathlib.Analysis.Subadditive`.

-/

namespace MCMC.PF

open Filter Topology

/--
The real root sequence attached to `u`, indexed by `n + 1` to avoid dividing by `0`.
-/
noncomputable def rootSequence (u : ℕ → NNReal) : ℕ → ℝ :=
  fun n => Real.rpow (u (n + 1) : ℝ) (1 / ((n + 1 : ℝ)))

/--
If a set of natural numbers is closed under addition and has set gcd `1`, then it contains all
sufficiently large natural numbers.

 Appendix A bridge from Seneta's formulation to mathlib's Frobenius-number API.
-/
theorem exists_bound_of_gcd_one_of_closed_add
    {V : Set ℕ}
    (h_closed : ∀ {a b}, a ∈ V → b ∈ V → a + b ∈ V)
    (h_gcd : Nat.setGcd V = 1) :
    ∃ N, ∀ q ≥ N, q ∈ V := by
  sorry

/--
Kingman's/Fekete's limit lemma for a positive supermultiplicative sequence, stated for the root
sequence `u (n + 1) ^ (1 / (n + 1))`.
-/
theorem limit_of_supermultiplicative_sequence
    {u : ℕ → NNReal}
    (h_super : ∀ i j, u (i + j) ≥ u i * u j)
    (hu_pos : ∀ n > 0, 0 < u n) :
    ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (rootSequence u) atTop (nhds L) ∧
      ∀ i > 0, (u i : ℝ) ≤ Real.rpow L (i : ℝ) := by
  sorry

/--
For a positive supermultiplicative sequence, the limiting value of the root sequence agrees with
its supremum.
-/
theorem iSup_rootSequence_eq_limit_of_supermultiplicative
    {u : ℕ → NNReal}
    (h_super : ∀ i j, u (i + j) ≥ u i * u j)
    (hu_pos : ∀ n > 0, 0 < u n) :
    ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (rootSequence u) atTop (nhds L) ∧
      sSup (Set.range (rootSequence u)) = L := by
  sorry

end MCMC.PF
