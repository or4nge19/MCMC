import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt

/-!
# Leontief systems and Hawkins-Simon criteria

This file starts a Chapter 2 style formalization of Seneta's treatment of Leontief systems
`(s • 1 - A) *ᵥ x = c`.

The file deliberately reuses mathlib's global `resolvent` on the matrix algebra rather than
introducing a second matrix-specific definition. The Perron-Frobenius input is
`CollatzWielandt.perronRoot_alt`.
-/

namespace Matrix

open scoped BigOperators
open Filter Topology CollatzWielandt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-
This file uses the existing algebraic `resolvent` from mathlib, specialized to the matrix algebra.
-/

/-- The finite Neumann sums approximating the resolvent. -/
noncomputable def resolventPartialSums (A : Matrix n n ℝ) (s : ℝ) (N : ℕ) :
    Matrix n n ℝ :=
  Finset.sum (Finset.range N) fun k => s⁻¹ • ((s⁻¹ • A) ^ k)

@[simp] theorem resolventPartialSums_zero (A : Matrix n n ℝ) (s : ℝ) :
    Matrix.resolventPartialSums A s 0 = 0 := by
  simp [Matrix.resolventPartialSums]

/-- Principal minors indexed by embeddings of finite initial index types. -/
def principalMinor {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (e : Fin k ↪ Fin m) : ℝ :=
  Matrix.det (A.submatrix e e)

/-- The canonical embedding `Fin k ↪ Fin m` attached to `k ≤ m`. -/
private def leadingPrincipalEmbedding {m k : ℕ} (hk : k ≤ m) : Fin k ↪ Fin m where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 hk⟩
  inj' := by
    intro i j hij
    cases i
    cases j
    cases hij
    rfl

/-- The `k × k` leading principal minor of a matrix indexed by `Fin m`. -/
def leadingPrincipalMinor {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hk : k ≤ m) : ℝ :=
  principalMinor A (leadingPrincipalEmbedding hk)

/--
Leontief-Seneta positivity criterion:
for an irreducible nonnegative matrix, strict productivity is equivalent to solvability of the
Leontief system by a strictly positive vector for every strictly positive demand vector.
-/
theorem exists_unique_pos_solution_iff_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ} :
    (∀ c : n → ℝ, (∀ i, 0 < c i) →
      ∃! x : n → ℝ, (∀ i, 0 < x i) ∧ (s • (1 : Matrix n n ℝ) - A) *ᵥ x = c) ↔
      perronRoot_alt A < s := by
  sorry

/--
If the Perron root lies strictly below `s`, the resolvent is entrywise nonnegative.
This is the matrix-valued Neumann positivity statement.
-/
theorem resolvent_nonneg_of_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot_alt A < s) :
    ∀ i j, 0 ≤ resolvent A s i j := by
  sorry

/--
For an irreducible nonnegative matrix, entrywise positivity of the resolvent exactly detects the
strict inequality `perronRoot_alt A < s`.
-/
theorem resolvent_pos_iff_perronRoot_lt
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible) {s : ℝ} :
    (∀ i j, 0 < resolvent A s i j) ↔ perronRoot_alt A < s := by
  sorry

/--
Neumann-series expansion of the resolvent in the productive regime `perronRoot_alt A < s`.
-/
theorem tendsto_resolventPartialSums
    [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ}
    (hs : perronRoot_alt A < s) :
    Tendsto (fun N : ℕ => Matrix.resolventPartialSums A s N) atTop
      (nhds (resolvent A s)) := by
  sorry

/--
Coordinate-free Hawkins-Simon statement: all principal minors of `s I - A` are positive exactly in
the strictly productive regime.
-/
theorem perronRoot_lt_iff_principalMinors_pos
    {m : ℕ} [Nonempty (Fin m)]
    {A : Matrix (Fin m) (Fin m) ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} :
    perronRoot_alt A < s ↔
      ∀ {k : ℕ} (e : Fin k ↪ Fin m),
        0 < Matrix.principalMinor (s • (1 : Matrix (Fin m) (Fin m) ℝ) - A) e := by
  sorry

/--
Hawkins-Simon in the classical ordered basis on `Fin m`: positivity of all leading principal
minors of `s I - A`.
-/
theorem perronRoot_lt_iff_leadingPrincipalMinors_pos
    {m : ℕ} [Nonempty (Fin m)]
    {A : Matrix (Fin m) (Fin m) ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) {s : ℝ} :
    perronRoot_alt A < s ↔
      ∀ {k : ℕ} (hk : k ≤ m),
        0 < Matrix.leadingPrincipalMinor (s • (1 : Matrix (Fin m) (Fin m) ℝ) - A) hk := by
  sorry

end Matrix
