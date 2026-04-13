import MCMC.Countable.CountableStochastic

/-!
# Countable-state nonnegative matrices and `R`-theory

This file formalizes Chapter 6 for irreducible nonnegative matrices on countable state spaces.

## Main definitions

* `convergenceRadius`: the radius of convergence of the matrix power series between two states.
* `rParam`: the convergence parameter based at a specified state.
* `IsRTransient`, `IsRRecurrent`: the `R`-transient and `R`-recurrent regimes.
* `IsRInvariantMeasure`, `IsRInvariantVector`: left and right `R`-invariant data.

## Main statements

* `convergenceRadius_eq_of_irreducible`: irreducibility makes the convergence radius independent of
  the states.
* `rParam_eq_of_irreducible`: the state-based definition `rParam T i` is independent of `i` in the
  irreducible case.
* `exists_unique_rInvariantMeasure_of_rRecurrent`: uniqueness of normalized positive
  `R`-invariant measures in the `R`-recurrent case.
* `limit_of_rRecurrent_of_aperiodic`: Seneta's `R`-limit theorem under irreducibility and
  aperiodicity.
* `rParam_eq_one_of_irreducible_stochastic_recurrent`: recurrence forces `R = 1` in the stochastic
  case.

## Implementation notes

The definition `rParam T i` is based at an explicit state `i`. The theorem
`rParam_eq_of_irreducible` is the API lemma showing that this choice is immaterial in the
irreducible regime.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Tags

nonnegative matrix, convergence parameter, countable state space, Perron-Frobenius
-/

namespace MCMC.Countable

open scoped BigOperators ENNReal
open Filter Topology

section ChapterSix

variable {α : Type*} [DecidableEq α]

/--
The convergence radius attached to the power series `∑ (T^[k] i j) s^k`.
-/
noncomputable def convergenceRadius (T : InfMatrix α) (i j : α) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ |
    ∃ s : NNReal,
      Summable (fun k : ℕ => InfMatrix.pow T k i j * (s : ℝ) ^ k) ∧
        r = (s : ℝ≥0∞)}

/--
The convergence parameter based at the state `i`.

For irreducible matrices, `rParam_eq_of_irreducible` shows that this does not depend on `i`.
-/
noncomputable def rParam (T : InfMatrix α) (i : α) : ℝ≥0∞ :=
  convergenceRadius T i i

/-- `R`-transience, defined by summability at the convergence parameter. -/
def IsRTransient (T : InfMatrix α) (i : α) : Prop :=
  Summable (fun k : ℕ => InfMatrix.pow T k i i * (rParam T i).toReal ^ k)

/-- `R`-recurrence is the negation of `R`-transience. -/
def IsRRecurrent (T : InfMatrix α) (i : α) : Prop :=
  ¬ IsRTransient T i

/--
A strictly positive left `R`-invariant measure based at the state `i`.

This definition is intended for use in the regime where `0 < rParam T i` and `rParam T i < ⊤`.
-/
def IsRInvariantMeasure (T : InfMatrix α) (i : α) (x : α → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧
    ∀ j, (∑' k, x k * T k j) = (rParam T i).toReal⁻¹ * x j

/--
A strictly positive right `R`-invariant vector based at the state `i`.

This definition is intended for use in the regime where `0 < rParam T i` and `rParam T i < ⊤`.
-/
def IsRInvariantVector (T : InfMatrix α) (i : α) (y : α → ℝ) : Prop :=
  (∀ i, 0 < y i) ∧
    ∀ k, (∑' j, T k j * y j) = (rParam T i).toReal⁻¹ * y k

/-- The convergence radius is independent of the pair of states in the irreducible case. -/
theorem convergenceRadius_eq_of_irreducible
    {T : InfMatrix α} (hT_nonneg : ∀ i j, 0 ≤ T i j) (hT_irred : IsIrreducible T)
    (i j u v : α) :
    convergenceRadius T i j = convergenceRadius T u v := by
  sorry

/-- In the irreducible case, `rParam T i` does not depend on the chosen state `i`. -/
theorem rParam_eq_of_irreducible
    {T : InfMatrix α} (hT_nonneg : ∀ i j, 0 ≤ T i j) (hT_irred : IsIrreducible T)
    (i j : α) :
    rParam T i = rParam T j := by
  exact convergenceRadius_eq_of_irreducible hT_nonneg hT_irred i i j j

/--
In the `R`-recurrent case there is a unique normalized positive left `R`-invariant measure.
-/
theorem exists_unique_rInvariantMeasure_of_rRecurrent
    {T : InfMatrix α} (hT_nonneg : ∀ i j, 0 ≤ T i j) (hT_irred : IsIrreducible T)
    (i₀ : α) (hR_pos : 0 < rParam T i₀) (hR_lt_top : rParam T i₀ < ⊤)
    (hRrec : IsRRecurrent T i₀) :
    ∃! x : α → ℝ, x i₀ = 1 ∧ IsRInvariantMeasure T i₀ x := by
  sorry

/--
Asymptotic Perron-Frobenius limit theorem under `R`-recurrence and aperiodicity.
-/
theorem limit_of_rRecurrent_of_aperiodic
    {T : InfMatrix α} (hT_nonneg : ∀ i j, 0 ≤ T i j) (hT_aper : IsAperiodic T)
    {i₀ i j : α} (hR_pos : 0 < rParam T i₀) (hR_lt_top : rParam T i₀ < ⊤)
    {x y : α → ℝ} (hx : IsRInvariantMeasure T i₀ x) (hy : IsRInvariantVector T i₀ y)
    (hxy : Summable (fun k : α => x k * y k))
    (hxy_ne_zero : (∑' k : α, x k * y k) ≠ 0) :
    Tendsto (fun k : ℕ => InfMatrix.pow T k i j * (rParam T i₀).toReal ^ k) atTop
      (nhds (x j * y i / (∑' k : α, x k * y k))) := by
  sorry

/--
For an irreducible recurrent stochastic matrix, the convergence parameter is `1`.
-/
theorem rParam_eq_one_of_irreducible_stochastic_recurrent
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P)
    {i : α} (hi_rec : IsRecurrent P i) :
    rParam P i = 1 := by
  sorry

end ChapterSix

end MCMC.Countable
