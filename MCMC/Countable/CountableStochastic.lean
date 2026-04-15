import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import MCMC.PF.Combinatorics.Quiver.Cyclic

/-!
# Countable-state stochastic matrices

This file begins the countable-state version of Seneta's Chapter 5.
Since `Matrix` in mathlib is reserved for finitely indexed matrices, we model an infinite matrix
as a function `α → α → ℝ` and define matrix multiplication using `tsum`.

## Main definitions

* `InfMatrix`: real-valued infinite matrices.
* `infMatMul`, `InfMatrix.pow`: `tsum`-based multiplication and powers.
* `IsStochastic`, `IsSubstochastic`: stochasticity and substochasticity for infinite matrices.
* `IsIrreducible`, `IsAperiodic`: irreducibility and aperiodicity via the positive-edge quiver.
* `firstPassageProb`, `meanRecurrenceTime`: first-passage probabilities and mean recurrence times.
* `IsTransient`, `IsRecurrent`, `IsPositiveRecurrent`, `IsNullRecurrent`: recurrence classes.
* `IsInvariantMeasure`, `IsInvariantDistribution`: invariant weights and invariant probability
  distributions.

## Main statements

* `transient_iff_tsum_lt_top`: transience as finiteness of the `ENNReal` return-probability series.
* `recurrence_is_solidarity_property`: recurrence is shared across states in the irreducible case.
* `positive_recurrence_is_solidarity_property`: positive recurrence is shared across states in the
  irreducible case.
* `limit_of_recurrent_of_aperiodic`: Seneta's diagonal limit theorem under irreducibility and
  period-one aperiodicity.

## Implementation notes

The motivating setting is a countable state space, but the basic definitions only require explicit
summability hypotheses and therefore make sense for arbitrary index types.

The aperiodicity notion is expressed through the positive-edge quiver of the matrix, reusing the
periodicity API from `MCMC.PF.Combinatorics.Quiver.Cyclic`.

## References

* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006.

## Tags

Markov chain, stochastic matrix, countable state space, recurrence
-/

namespace MCMC.Countable

open scoped BigOperators ENNReal
open Filter Topology

/-- A real-valued infinite matrix indexed by `α`. -/
abbrev InfMatrix (α : Type*) := α → α → ℝ

/--
Infinite matrix multiplication via `tsum`.

This is the raw `tsum`-based convolution formula; applications should supply whatever summability
hypotheses are needed to identify it with the intended matrix product.
-/
noncomputable def infMatMul {α : Type*} (A B : InfMatrix α) : InfMatrix α :=
  fun i j => ∑' k, A i k * B k j

@[simp] theorem infMatMul_apply {α : Type*} (A B : InfMatrix α) (i j : α) :
    infMatMul A B i j = ∑' k, A i k * B k j := by
  rfl

namespace InfMatrix

variable {α : Type*} [DecidableEq α]

/-- The identity infinite matrix. -/
def one : InfMatrix α :=
  fun i j => if i = j then 1 else 0

/-- Powers of an infinite matrix formed using `infMatMul`. -/
noncomputable def pow (P : InfMatrix α) : ℕ → InfMatrix α
  | 0 => InfMatrix.one
  | k + 1 => infMatMul (pow P k) P

@[simp] theorem pow_zero (P : InfMatrix α) :
    InfMatrix.pow P 0 = InfMatrix.one := by
  rfl

@[simp] theorem pow_succ (P : InfMatrix α) (k : ℕ) :
    InfMatrix.pow P (k + 1) = infMatMul (InfMatrix.pow P k) P := by
  rfl

@[simp] theorem one_apply (i j : α) :
    InfMatrix.one i j = if i = j then 1 else 0 := by
  rfl

omit [DecidableEq α] in
/-- The positive-edge quiver attached to an infinite matrix. -/
def toQuiver (P : InfMatrix α) : Quiver α :=
  ⟨fun i j => 0 < P i j⟩

omit [DecidableEq α] in
@[simp] theorem toQuiver_hom_iff (P : InfMatrix α) {i j : α} :
    @Nonempty (@Quiver.Hom α (toQuiver P) i j) ↔ 0 < P i j := by
  constructor
  · intro h
    exact h.some
  · intro h
    exact ⟨h⟩

end InfMatrix

/-! ### Chapter 5: recurrence and invariant measures -/

section ChapterFive

variable {α : Type*} [DecidableEq α]

/--
A countable-state stochastic matrix is a nonnegative matrix whose rows are summable and have total
mass `1`.
-/
def IsStochastic (P : InfMatrix α) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, Summable (P i) ∧ ∑' j, P i j = 1

/--
A countable-state substochastic matrix is a nonnegative matrix whose rows are summable and have
total mass at most `1`.
-/
def IsSubstochastic (Q : InfMatrix α) : Prop :=
  (∀ i j, 0 ≤ Q i j) ∧ ∀ i, Summable (Q i) ∧ ∑' j, Q i j ≤ 1

/--
Irreducibility of an infinite matrix, following mathlib's finite `Matrix.IsIrreducible` API.

It packages entrywise nonnegativity together with strong connectivity of the positive-edge quiver
`InfMatrix.toQuiver P`.
-/
@[mk_iff] structure IsIrreducible (P : InfMatrix α) : Prop where
  nonneg (i j : α) : 0 ≤ P i j
  connected : @Quiver.IsSStronglyConnected α (InfMatrix.toQuiver P)

omit [DecidableEq α] in
/--
If an irreducible infinite matrix acts on a nontrivial state space, then every row has a positive
entry.
-/
theorem IsIrreducible.exists_pos [Nontrivial α] {P : InfMatrix α} (hP : IsIrreducible P) (i : α) :
    ∃ j, 0 < P i j := by
  obtain ⟨j, hj⟩ := exists_ne i
  letI : Quiver α := InfMatrix.toQuiver P
  obtain ⟨p, hp⟩ := hP.connected i j
  clear hj
  induction p with
  | nil => simp [Quiver.Path.length_nil] at hp
  | cons rest e ih =>
    cases rest with
    | nil => exact ⟨_, e⟩
    | cons rest' e' => exact ih (by simp [Quiver.Path.length_cons])

/--
An infinite matrix is aperiodic if it is irreducible and its positive-edge quiver is aperiodic.
-/
def IsAperiodic (P : InfMatrix α) : Prop :=
  IsIrreducible P ∧ Quiver.IsAperiodic (InfMatrix.toQuiver P)

omit [DecidableEq α] in
/-- Aperiodicity implies irreducibility. -/
theorem IsAperiodic.isIrreducible {P : InfMatrix α} (hP : IsAperiodic P) :
    IsIrreducible P :=
  hP.1

omit [DecidableEq α] in
/-- Aperiodicity of an infinite matrix is aperiodicity of its positive-edge quiver. -/
theorem IsAperiodic.quiver_isAperiodic {P : InfMatrix α} (hP : IsAperiodic P) :
    Quiver.IsAperiodic (InfMatrix.toQuiver P) :=
  hP.2

omit [DecidableEq α] in
/-- An aperiodic infinite matrix has a period-one vertex in its positive-edge quiver. -/
theorem IsAperiodic.exists_period_eq_one {P : InfMatrix α} (hP : IsAperiodic P) :
    letI : Quiver α := InfMatrix.toQuiver P
    ∃ i : α, Quiver.period i = 1 :=
  hP.2

omit [DecidableEq α] in
/--
For an irreducible infinite matrix, aperiodicity is equivalent to the period-one condition at any
chosen vertex of the positive-edge quiver.
-/
theorem isAperiodic_iff_period_eq_one
    {P : InfMatrix α} (hP_irred : IsIrreducible P) (i : α) :
    IsAperiodic P ↔ (letI : Quiver α := InfMatrix.toQuiver P; Quiver.period i = 1) := by
  constructor
  · intro hP
    exact Quiver.isAperiodic_iff_period_eq_one (G := InfMatrix.toQuiver P) hP_irred.connected i
      |>.mp hP.2
  · intro hi
    exact
      ⟨hP_irred,
        Quiver.isAperiodic_iff_period_eq_one (G := InfMatrix.toQuiver P) hP_irred.connected i
          |>.mpr hi⟩

omit [DecidableEq α] in
/--
For an aperiodic infinite matrix, every vertex of the positive-edge quiver has period `1`.
-/
theorem IsAperiodic.period_eq_one {P : InfMatrix α} (hP : IsAperiodic P) (i : α) :
    letI : Quiver α := InfMatrix.toQuiver P
    Quiver.period i = 1 := by
  exact Quiver.IsAperiodic.period_eq_one hP.1.connected hP.2 i

/--
The first-passage probability `fᵢⱼ^(k)`.

The recursion encodes: first hit `j` in one step, or first move to some `ℓ ≠ j` and then hit `j`
for the first time after the remaining number of steps.
-/
noncomputable def firstPassageProb (P : InfMatrix α) (i j : α) : ℕ → ℝ
  | 0 => 0
  | 1 => P i j
  | k + 2 => ∑' ℓ, if ℓ = j then 0 else P i ℓ * firstPassageProb P ℓ j (k + 1)

@[simp] theorem firstPassageProb_zero (P : InfMatrix α) (i j : α) :
    firstPassageProb P i j 0 = 0 := by
  rfl

@[simp] theorem firstPassageProb_one (P : InfMatrix α) (i j : α) :
    firstPassageProb P i j 1 = P i j := by
  rfl

/-- The mean recurrence time `μᵢ`, allowed to be infinite. -/
noncomputable def meanRecurrenceTime (P : InfMatrix α) (i : α) : ℝ≥0∞ :=
  ∑' k : ℕ, (k : ℝ≥0∞) * ENNReal.ofReal (firstPassageProb P i i k)

/-- Transience at a state, expressed through summability of return probabilities. -/
def IsTransient (P : InfMatrix α) (i : α) : Prop :=
  Summable fun k : ℕ => InfMatrix.pow P k i i

/-- Recurrence is the negation of transience. -/
def IsRecurrent (P : InfMatrix α) (i : α) : Prop :=
  ¬ IsTransient P i

/-- Positive recurrence means recurrence with finite mean recurrence time. -/
def IsPositiveRecurrent (P : InfMatrix α) (i : α) : Prop :=
  IsRecurrent P i ∧ meanRecurrenceTime P i < ⊤

/-- Null recurrence means recurrence with infinite mean recurrence time. -/
def IsNullRecurrent (P : InfMatrix α) (i : α) : Prop :=
  IsRecurrent P i ∧ meanRecurrenceTime P i = ⊤

/-- A nonzero nonnegative invariant measure for a countable stochastic matrix. -/
def IsInvariantMeasure (P : InfMatrix α) (v : α → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ ∀ j, (∑' i, v i * P i j) = v j

/-- An invariant probability distribution on a countable state space. -/
def IsInvariantDistribution (P : InfMatrix α) (π : α → ℝ) : Prop :=
  IsInvariantMeasure P π ∧ Summable π ∧ ∑' i, π i = 1

/-- Transience is equivalent to finiteness of the `ENNReal` series of return probabilities. -/
theorem transient_iff_tsum_lt_top
    {P : InfMatrix α} (hP : IsStochastic P) (i : α) :
    IsTransient P i ↔ (∑' k : ℕ, ENNReal.ofReal (InfMatrix.pow P k i i)) < ⊤ := by
  sorry

/-- Recurrence is a class property for irreducible countable stochastic matrices. -/
theorem recurrence_is_solidarity_property
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P)
    (i j : α) :
    IsRecurrent P i ↔ IsRecurrent P j := by
  sorry

/-- Positive recurrence is a class property for irreducible countable stochastic matrices. -/
theorem positive_recurrence_is_solidarity_property
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P)
    (i j : α) :
    IsPositiveRecurrent P i ↔ IsPositiveRecurrent P j := by
  sorry

/-- Aperiodicity implies Seneta's diagonal limit formula in the irreducible recurrent case. -/
theorem limit_of_recurrent_of_aperiodic
    {P : InfMatrix α} (hP : IsStochastic P) (hP_aper : IsAperiodic P) (i : α) :
    Tendsto (fun k : ℕ => InfMatrix.pow P k i i) atTop
      (nhds (((meanRecurrenceTime P i)⁻¹).toReal)) := by
  sorry

/--
An irreducible countable stochastic matrix admits a summable invariant measure exactly in the
positive recurrent case.
-/
theorem exists_summable_invariantMeasure_iff_forall_positiveRecurrent
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P) :
    (∃ v, IsInvariantMeasure P v ∧ Summable v) ↔ ∀ i, IsPositiveRecurrent P i := by
  sorry

/--
For an irreducible recurrent countable stochastic matrix, every nonzero nonnegative subinvariant
measure is automatically invariant.
-/
theorem subinvariant_measure_is_invariant_of_recurrent
    {P : InfMatrix α} (hP : IsStochastic P) (hP_irred : IsIrreducible P)
    (hP_rec : ∀ i, IsRecurrent P i) {v : α → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0)
    (h_sub : ∀ j, (∑' i, v i * P i j) ≤ v j) :
    IsInvariantMeasure P v := by
  sorry

end ChapterFive

end MCMC.Countable
