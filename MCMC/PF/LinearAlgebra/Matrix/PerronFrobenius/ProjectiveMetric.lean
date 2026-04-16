import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Hilbert projective metric and Birkhoff contraction

This file formalizes the projective-metric layer of Seneta's Chapter 3.1.

The basic domain is `Matrix.PositiveVec`, i.e. the interior of the positive cone, so the Hilbert
metric and the Birkhoff coefficient are stated without relying on totalized division-by-zero or
`Real.log` outside its natural domain.
-/

namespace Matrix

open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Positive vectors in `ℝ^n`, i.e. points of the interior of the positive cone. -/
abbrev PositiveVec (n : Type*) :=
  {v : n → ℝ // ∀ i, 0 < v i}

/-- Row-allowability: every row contains a strictly positive entry. -/
def IsRowAllowable (A : Matrix n n ℝ) : Prop :=
  ∀ i, ∃ j, 0 < A i j

/-- Column-allowability: every column contains a strictly positive entry. -/
def IsColAllowable (A : Matrix n n ℝ) : Prop :=
  ∀ j, ∃ i, 0 < A i j

/-- Allowability in the sense of Seneta: both row- and column-allowable. -/
def IsAllowable (A : Matrix n n ℝ) : Prop :=
  A.IsRowAllowable ∧ A.IsColAllowable

/--
The Hilbert projective distance on the positive cone.
It is defined on `PositiveVec n` to avoid partiality issues.
-/
noncomputable def projectiveDist (x y : PositiveVec n) : ℝ :=
  Real.log (Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / y.1 i) -
    Real.log (Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / y.1 i)

/--
If `A` is nonnegative and row-allowable, then it maps positive vectors to positive vectors.

This is the natural action of `A` on the interior of the positive cone.
-/
def mulVecPositive
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_row : A.IsRowAllowable)
    (x : PositiveVec n) : PositiveVec n := by
  refine ⟨A *ᵥ x.1, ?_⟩
  intro i
  rcases hA_row i with ⟨j, hij⟩
  have h_nonneg : ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A i k * x.1 k := by
    intro k hk
    exact mul_nonneg (hA_nonneg i k) (le_of_lt (x.2 k))
  have h_pos_term : 0 < A i j * x.1 j := by
    exact mul_pos hij (x.2 j)
  have h_sum_pos : 0 < ∑ k, A i k * x.1 k := by
    have h_sum_nonneg : 0 ≤ ∑ k, A i k * x.1 k := by
      exact Finset.sum_nonneg (fun k hk => h_nonneg k hk)
    by_contra h_not_pos
    have hsum : ∑ k, A i k * x.1 k = 0 := by
      exact le_antisymm (le_of_not_gt h_not_pos) h_sum_nonneg
    have hzero :
        ∀ k ∈ (Finset.univ : Finset n), A i k * x.1 k = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => h_nonneg k hk)).mp hsum
    exact h_pos_term.ne' (hzero j (Finset.mem_univ j))
  simpa [Matrix.mulVec, dotProduct] using h_sum_pos

omit [DecidableEq n] [Nonempty n] in
@[simp] theorem coe_mulVecPositive
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_row : A.IsRowAllowable)
    (x : PositiveVec n) :
    ((Matrix.mulVecPositive A hA_nonneg hA_row x : PositiveVec n) : n → ℝ) = A *ᵥ x.1 := by
  rfl

/--
Birkhoff's contraction coefficient, defined as the supremum of projective-distance ratios over the
projective cone after discarding the degenerate zero-distance pairs.
-/
noncomputable def birkhoffContraction (A : Matrix n n ℝ) : ℝ :=
  sSup ({0} ∪ { t : ℝ |
    ∃ x y : PositiveVec n,
      ∃ hx : ∀ i, 0 < (A *ᵥ x.1) i,
      ∃ hy : ∀ i, 0 < (A *ᵥ y.1) i,
        Matrix.projectiveDist x y ≠ 0 ∧
          t = Matrix.projectiveDist ⟨A *ᵥ x.1, hx⟩ ⟨A *ᵥ y.1, hy⟩ / Matrix.projectiveDist x y })

/-- Seneta's scrambling condition. -/
def IsScrambling (A : Matrix n n ℝ) : Prop :=
  ∀ i j, ∃ s, 0 < A i s ∧ 0 < A j s

/-- Nonnegativity of the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_nonneg
    (x y : PositiveVec n) :
    0 ≤ Matrix.projectiveDist x y := by
  sorry

/-- Symmetry of the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_symm
    (x y : PositiveVec n) :
    Matrix.projectiveDist x y = Matrix.projectiveDist y x := by
  sorry

/-- Triangle inequality for the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_triangle
    (x y z : PositiveVec n) :
    Matrix.projectiveDist x z ≤ Matrix.projectiveDist x y + Matrix.projectiveDist y z := by
  sorry

/--
The Hilbert projective distance vanishes exactly on positive scalar multiples.
-/
theorem projectiveDist_eq_zero_iff_exists_pos_smul
    (x y : PositiveVec n) :
    Matrix.projectiveDist x y = 0 ↔
      ∃ c : ℝ, 0 < c ∧ x.1 = c • y.1 := by
  sorry

/--
Non-expansiveness of a nonnegative row-allowable matrix for Hilbert's projective distance.
-/
theorem projectiveDist_mulVec_le
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_row : A.IsRowAllowable)
    (x y : PositiveVec n) :
    Matrix.projectiveDist (Matrix.mulVecPositive A hA_nonneg hA_row x)
      (Matrix.mulVecPositive A hA_nonneg hA_row y) ≤ Matrix.projectiveDist x y := by
  sorry

/--
The Birkhoff coefficient is bounded by `1` for a nonnegative row-allowable matrix.
-/
theorem birkhoffContraction_le_one
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_row : A.IsRowAllowable) :
    Matrix.birkhoffContraction A ≤ 1 := by
  sorry


/--
Scrambling implies row-allowability.
-/
theorem IsScrambling.isRowAllowable
    {A : Matrix n n ℝ} (h_scrambling : A.IsScrambling) :
    A.IsRowAllowable := by
  sorry

/--
Scrambling matrices satisfy the general Birkhoff coefficient bound `≤ 1`.

Strict Hilbert-projective contraction requires stronger hypotheses than scrambling alone.
-/
theorem scrambling_implies_birkhoffContraction_le_one
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_scrambling : A.IsScrambling) :
    Matrix.birkhoffContraction A ≤ 1 := by
  sorry

end Matrix
