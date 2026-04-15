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
  unfold projectiveDist
  simp only [coe_mulVecPositive]
  set M := Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / y.1 i with hM_def
  set m := Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / y.1 i with hm_def
  set M' := Finset.univ.sup' Finset.univ_nonempty fun i => (A *ᵥ x.1) i / (A *ᵥ y.1) i with hM'_def
  set m' := Finset.univ.inf' Finset.univ_nonempty fun i => (A *ᵥ x.1) i / (A *ᵥ y.1) i with hm'_def
  have hm_pos : 0 < m := by
    rw [Finset.lt_inf'_iff]
    intro j _
    exact div_pos (x.2 j) (y.2 j)
  have hM_pos : 0 < M := by
    obtain ⟨i₀, hi₀⟩ := Finset.univ_nonempty (α := n)
    have h1 : 0 < x.1 i₀ / y.1 i₀ := div_pos (x.2 i₀) (y.2 i₀)
    have h2 : x.1 i₀ / y.1 i₀ ≤ M := Finset.le_sup' (fun i => x.1 i / y.1 i) (Finset.mem_univ i₀)
    linarith
  have hm'_pos : 0 < m' := by
    rw [Finset.lt_inf'_iff]
    intro j _
    exact div_pos ((mulVecPositive A hA_nonneg hA_row x).2 j) ((mulVecPositive A hA_nonneg hA_row y).2 j)
  have hM'_pos : 0 < M' := by
    obtain ⟨i₀, hi₀⟩ := Finset.univ_nonempty (α := n)
    have h1 : 0 < (A *ᵥ x.1) i₀ / (A *ᵥ y.1) i₀ := div_pos ((mulVecPositive A hA_nonneg hA_row x).2 i₀) ((mulVecPositive A hA_nonneg hA_row y).2 i₀)
    have h2 : (A *ᵥ x.1) i₀ / (A *ᵥ y.1) i₀ ≤ M' := Finset.le_sup' (fun i => (A *ᵥ x.1) i / (A *ᵥ y.1) i) (Finset.mem_univ i₀)
    linarith
  have hM'_le_M : M' ≤ M := by
    apply Finset.sup'_le
    intro i _
    have hAy_pos : 0 < (A *ᵥ y.1) i := (mulVecPositive A hA_nonneg hA_row y).2 i
    rw [div_le_iff₀ hAy_pos]
    simp only [Matrix.mulVec]
    have hy_pos : ∀ j, y.1 j ≠ 0 := fun j => (y.2 j).ne'
    calc ∑ j, A i j * x.1 j
        = ∑ j, A i j * (x.1 j / y.1 j) * y.1 j := by
          congr 1; ext j; field_simp [hy_pos j]
      _ ≤ ∑ j, A i j * M * y.1 j := by
          apply Finset.sum_le_sum; intro j _
          have h1 : x.1 j / y.1 j ≤ M := Finset.le_sup' (fun k => x.1 k / y.1 k) (Finset.mem_univ j)
          have h2 : A i j * (x.1 j / y.1 j) ≤ A i j * M := mul_le_mul_of_nonneg_left h1 (hA_nonneg i j)
          exact mul_le_mul_of_nonneg_right h2 (le_of_lt (y.2 j))
      _ = M * ∑ j, A i j * y.1 j := by rw [Finset.mul_sum]; congr 1; ext j; ring
  have hm_le_m' : m ≤ m' := by
    apply Finset.le_inf'
    intro i _
    have hAy_pos : 0 < (A *ᵥ y.1) i := (mulVecPositive A hA_nonneg hA_row y).2 i
    rw [le_div_iff₀ hAy_pos]
    simp only [Matrix.mulVec]
    have hy_pos : ∀ j, y.1 j ≠ 0 := fun j => (y.2 j).ne'
    calc m * ∑ j, A i j * y.1 j
        = ∑ j, A i j * m * y.1 j := by rw [Finset.mul_sum]; congr 1; ext j; ring
      _ ≤ ∑ j, A i j * (x.1 j / y.1 j) * y.1 j := by
          apply Finset.sum_le_sum; intro j _
          have h1 : m ≤ x.1 j / y.1 j := Finset.inf'_le (fun k => x.1 k / y.1 k) (Finset.mem_univ j)
          have h2 : A i j * m ≤ A i j * (x.1 j / y.1 j) := mul_le_mul_of_nonneg_left h1 (hA_nonneg i j)
          exact mul_le_mul_of_nonneg_right h2 (le_of_lt (y.2 j))
      _ = ∑ j, A i j * x.1 j := by
          congr 1; ext j; field_simp [hy_pos j]
  have h1 : Real.log M' - Real.log m' ≤ Real.log M - Real.log m := by
    have hlog1 : Real.log M' ≤ Real.log M := Real.log_le_log hM'_pos hM'_le_M
    have hlog2 : Real.log m ≤ Real.log m' := Real.log_le_log hm_pos hm_le_m'
    linarith
  exact h1

/--
The Birkhoff coefficient is bounded by `1` for a nonnegative row-allowable matrix.
-/
theorem birkhoffContraction_le_one
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_row : A.IsRowAllowable) :
    Matrix.birkhoffContraction A ≤ 1 := by
  sorry

/--
Scrambling implies strict Birkhoff contraction.
-/
theorem scrambling_implies_birkhoffContraction_lt_one
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_scrambling : A.IsScrambling) :
    Matrix.birkhoffContraction A < 1 := by
  sorry

end Matrix
