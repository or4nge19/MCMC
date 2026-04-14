import MCMC.Countable.CountableNonneg
import MCMC.Finite.Core
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt

/-!
# Truncations of countable matrices

This file formalizes Chapter 7 for finite truncations of countable matrices.

## Main definitions

* `finsetTruncation`: restriction of an infinite matrix to a finite set.
* `extendByZero`: extension of a vector on a truncation by `0` outside the truncation.
* `stochasticAugmentation`: Seneta's column augmentation turning a substochastic truncation into a
  stochastic matrix.
* `IsNormalizedLeftEigenvector`: normalized left eigenvectors of finite truncations, reusing
  `stdSimplex`.

## Main statements

* `truncation_perronRoot_monotone_convergence`: convergence of Perron roots along an exhaustive
  sequence of finite truncations.
* `seneta_probability_algorithm_converges`: convergence of stationary distributions of augmented
  truncations.
* `quasi_stationary_limit_of_truncations`: convergence of finite-truncation quasi-stationary data.

## Implementation notes

The operation called `finsetTruncation` is order-free: it is simply restriction to a finite set.
When the finite sets are initial segments of an enumeration of the state space, this recovers
Seneta's northwest-corner truncations.

-/

namespace MCMC.Countable

open scoped BigOperators
open Filter Topology Matrix.CollatzWielandt

/-! ### Chapter 7: finite truncations -/

section ChapterSeven

variable {α : Type*} [DecidableEq α] [Nonempty α]

/--
The restriction of an infinite matrix to a finite set `s`.

For exhaustions by initial segments of an enumeration, this is Seneta's northwest-corner
truncation.
-/
def finsetTruncation (T : InfMatrix α) (s : Finset α) : Matrix s s ℝ :=
  fun i j => T i.1 j.1

omit [DecidableEq α] [Nonempty α] in
@[simp] theorem finsetTruncation_apply (T : InfMatrix α) (s : Finset α) (i j : s) :
    finsetTruncation T s i j = T i.1 j.1 := by
  rfl

/-- Extend a vector on a finite truncation by `0` outside the truncation. -/
def extendByZero (s : Finset α) (v : s → ℝ) : α → ℝ :=
  fun a => if h : a ∈ s then v ⟨a, h⟩ else 0

omit [Nonempty α] in
@[simp] theorem extendByZero_of_mem (s : Finset α) (v : s → ℝ) {a : α} (ha : a ∈ s) :
    extendByZero s v a = v ⟨a, ha⟩ := by
  simp [extendByZero, ha]

omit [Nonempty α] in
@[simp] theorem extendByZero_of_notMem (s : Finset α) (v : s → ℝ) {a : α} (ha : a ∉ s) :
    extendByZero s v a = 0 := by
  simp [extendByZero, ha]

/--
Stochastic augmentation at a distinguished column `j₀`: the missing row mass is added to that
column.
-/
def stochasticAugmentation {s : Finset α} (j₀ : s) (P : Matrix s s ℝ) : Matrix s s ℝ :=
  fun i j =>
    if j = j₀ then
      P i j + (1 - ∑ k, P i k)
    else
      P i j

omit [Nonempty α] in
@[simp] theorem stochasticAugmentation_apply {s : Finset α} (j₀ : s) (P : Matrix s s ℝ) (i j : s) :
    stochasticAugmentation j₀ P i j =
      if j = j₀ then P i j + (1 - ∑ k, P i k) else P i j := by
  rfl

/--
If every row of a finite matrix has sum at most `1`, then stochastic augmentation forces the row
sums to be exactly `1`.
-/
theorem stochasticAugmentation_row_sum
    {s : Finset α} (j₀ : s) {P : Matrix s s ℝ}
    (hP_row : ∀ i, ∑ j, P i j ≤ 1) :
    ∀ i, ∑ j, stochasticAugmentation j₀ P i j = 1 := by
  sorry

/--
If the truncated matrix is substochastic, its augmentation is stochastic.
-/
theorem stochasticAugmentation_isStochastic
    {s : Finset α} (j₀ : s) {P : Matrix s s ℝ}
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_row : ∀ i, ∑ j, P i j ≤ 1) :
    MCMC.Finite.IsStochastic (stochasticAugmentation j₀ P) := by
  sorry

/--
Normalized left eigenvectors on finite truncations.

This reuses the existing finite simplex type instead of restating nonnegativity and normalization
constraints by hand.
-/
def IsNormalizedLeftEigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (v : stdSimplex ℝ ι) : Prop :=
  ∃ μ : ℝ, 0 < μ ∧ Matrix.vecMul v.val A = μ • v.val

/--
Monotone exhaustive truncations recover the inverse convergence parameter through the Perron roots
of the finite truncations.
-/
theorem truncation_perronRoot_monotone_convergence
    {T : InfMatrix α} (hT_irred : IsIrreducible T)
    (i₀ : α) (hR_pos : 0 < rParam T i₀) (hR_lt_top : rParam T i₀ < ⊤)
    (s : ℕ → Finset α) (hs_mono : Monotone s) (hs_exhaust : ∀ a : α, ∃ n, a ∈ s n) :
    Tendsto (fun n : ℕ => Matrix.CollatzWielandt.perronRoot_alt (finsetTruncation T (s n))) atTop
      (nhds ((rParam T i₀).toReal⁻¹)) := by
  sorry

/--
Seneta's probability algorithm: stationary distributions of augmented finite truncations converge
pointwise to the target invariant distribution.
-/
theorem seneta_probability_algorithm_converges
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P)
    {π : α → ℝ} (hπ : IsInvariantDistribution P π)
    {s : ℕ → Finset α} (hs_mono : Monotone s) (hs_exhaust : ∀ a : α, ∃ n, a ∈ s n)
    (j₀ : ∀ n, s n) (v : ∀ n, stdSimplex ℝ (s n))
    (h_stat : ∀ n,
      MCMC.Finite.IsStationary
        (stochasticAugmentation (j₀ n) (finsetTruncation P (s n))) (v n)) :
    ∀ j : α, Tendsto (fun n : ℕ => extendByZero (s n) (v n).val j) atTop (nhds (π j)) := by
  sorry

/-- Quasi-stationary distributions for substochastic countable kernels. -/
def IsQuasiStationaryDist (Q : InfMatrix α) (v : α → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ Summable v ∧ (∑' i, v i = 1) ∧
    ∃ μ : ℝ, 0 < μ ∧ ∀ j, (∑' i, v i * Q i j) = μ * v j

/--
Finite-truncation normalized left eigenvectors converge to the target quasi-stationary
distribution.
-/
theorem quasi_stationary_limit_of_truncations
    {Q : InfMatrix α} (hQ : IsSubstochastic Q) (hQ_irred : IsIrreducible Q)
    {q : α → ℝ} (hq : IsQuasiStationaryDist Q q)
    {s : ℕ → Finset α} (hs_mono : Monotone s) (hs_exhaust : ∀ a : α, ∃ n, a ∈ s n)
    (v : ∀ n, stdSimplex ℝ (s n))
    (hv : ∀ n, IsNormalizedLeftEigenvector (finsetTruncation Q (s n)) (v n)) :
    Tendsto (fun n : ℕ => extendByZero (s n) (v n).val) atTop (nhds q) := by
  sorry

end ChapterSeven

end MCMC.Countable
