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

omit [DecidableEq n] in
/-- Nonnegativity of the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_nonneg
    (x y : PositiveVec n) :
    0 ≤ Matrix.projectiveDist x y := by
  rw [Matrix.projectiveDist, sub_nonneg]
  refine Real.log_le_log ?hpos ?hle
  · rw [Finset.lt_inf'_iff Finset.univ_nonempty]
    intro i _
    exact div_pos (x.2 i) (y.2 i)
  · obtain ⟨i⟩ := inferInstanceAs (Nonempty n)
    exact le_trans (Finset.inf'_le _ (Finset.mem_univ i))
      (Finset.le_sup' (fun i => x.1 i / y.1 i) (Finset.mem_univ i))

/-- Symmetry of the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_symm
    (x y : PositiveVec n) :
    Matrix.projectiveDist x y = Matrix.projectiveDist y x := by
  unfold projectiveDist
  have h_inv : ∀ i, y.1 i / x.1 i = (x.1 i / y.1 i)⁻¹ := fun i => by rw [inv_div]
  simp_rw [h_inv]
  have hxy : ∀ i, 0 < x.1 i / y.1 i := fun i => div_pos (x.2 i) (y.2 i)
  have hinf_pos : 0 < Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / y.1 i := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => x.1 i / y.1 i)
    rw [hj]
    exact hxy j
  have hsup_pos : 0 < Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / y.1 i := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => x.1 i / y.1 i)
    rw [hj]
    exact hxy j
  have hsup_inv : (Finset.univ.sup' Finset.univ_nonempty fun i => (x.1 i / y.1 i)⁻¹) =
      (Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / y.1 i)⁻¹ := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      have h1 : Finset.univ.inf' Finset.univ_nonempty (fun i => x.1 i / y.1 i) ≤ x.1 i / y.1 i :=
        Finset.inf'_le (fun i => x.1 i / y.1 i) hi
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hinf_pos h1
    · obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => x.1 i / y.1 i)
      rw [hj_eq]
      exact Finset.le_sup' (fun i => (x.1 i / y.1 i)⁻¹) hj_mem
  have hinf_inv : (Finset.univ.inf' Finset.univ_nonempty fun i => (x.1 i / y.1 i)⁻¹) =
      (Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / y.1 i)⁻¹ := by
    apply le_antisymm
    · obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => x.1 i / y.1 i)
      rw [hj_eq]
      exact Finset.inf'_le (fun i => (x.1 i / y.1 i)⁻¹) hj_mem
    · apply Finset.le_inf'
      intro i hi
      have h1 : x.1 i / y.1 i ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => x.1 i / y.1 i) :=
        Finset.le_sup' (fun i => x.1 i / y.1 i) hi
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (hxy i) h1
  rw [hsup_inv, hinf_inv]
  rw [Real.log_inv, Real.log_inv]
  ring

/-- Triangle inequality for the Hilbert projective distance on the strictly positive cone. -/
theorem projectiveDist_triangle
    (x y z : PositiveVec n) :
    Matrix.projectiveDist x z ≤ Matrix.projectiveDist x y + Matrix.projectiveDist y z := by
  unfold projectiveDist
  -- Let M_xy = sup(x/y), m_xy = inf(x/y), etc.
  set M_xz := Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / z.1 i with hM_xz
  set m_xz := Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / z.1 i with hm_xz
  set M_xy := Finset.univ.sup' Finset.univ_nonempty fun i => x.1 i / y.1 i with hM_xy
  set m_xy := Finset.univ.inf' Finset.univ_nonempty fun i => x.1 i / y.1 i with hm_xy
  set M_yz := Finset.univ.sup' Finset.univ_nonempty fun i => y.1 i / z.1 i with hM_yz
  set m_yz := Finset.univ.inf' Finset.univ_nonempty fun i => y.1 i / z.1 i with hm_yz
  -- Positivity of all ratios
  have hpos_xz : ∀ i, 0 < x.1 i / z.1 i := fun i => div_pos (x.2 i) (z.2 i)
  have hpos_xy : ∀ i, 0 < x.1 i / y.1 i := fun i => div_pos (x.2 i) (y.2 i)
  have hpos_yz : ∀ i, 0 < y.1 i / z.1 i := fun i => div_pos (y.2 i) (z.2 i)
  have hM_xz_pos : 0 < M_xz := by
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := n)
    exact lt_of_lt_of_le (hpos_xz i) (Finset.le_sup' (f := fun i => x.1 i / z.1 i) hi)
  have hm_xz_pos : 0 < m_xz := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => x.1 i / z.1 i)
    rw [hm_xz, hj]
    exact hpos_xz j
  have hM_xy_pos : 0 < M_xy := by
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := n)
    exact lt_of_lt_of_le (hpos_xy i) (Finset.le_sup' (f := fun i => x.1 i / y.1 i) hi)
  have hm_xy_pos : 0 < m_xy := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => x.1 i / y.1 i)
    rw [hm_xy, hj]
    exact hpos_xy j
  have hM_yz_pos : 0 < M_yz := by
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := n)
    exact lt_of_lt_of_le (hpos_yz i) (Finset.le_sup' (f := fun i => y.1 i / z.1 i) hi)
  have hm_yz_pos : 0 < m_yz := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => y.1 i / z.1 i)
    rw [hm_yz, hj]
    exact hpos_yz j
  -- Key: x_i/z_i = (x_i/y_i) * (y_i/z_i)
  have h_ratio : ∀ i, x.1 i / z.1 i = (x.1 i / y.1 i) * (y.1 i / z.1 i) := by
    intro i
    field_simp [ne_of_gt (y.2 i), ne_of_gt (z.2 i)]
  -- M_xz ≤ M_xy * M_yz
  have hM_le : M_xz ≤ M_xy * M_yz := by
    apply Finset.sup'_le
    intro i _
    rw [h_ratio i]
    calc (x.1 i / y.1 i) * (y.1 i / z.1 i) 
        ≤ M_xy * (y.1 i / z.1 i) := by
          apply mul_le_mul_of_nonneg_right
          · exact Finset.le_sup' (f := fun i => x.1 i / y.1 i) (Finset.mem_univ i)
          · exact le_of_lt (hpos_yz i)
      _ ≤ M_xy * M_yz := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.le_sup' (f := fun i => y.1 i / z.1 i) (Finset.mem_univ i)
          · exact le_of_lt hM_xy_pos
  -- m_xz ≥ m_xy * m_yz
  have hm_ge : m_xy * m_yz ≤ m_xz := by
    apply Finset.le_inf'
    intro i _
    rw [h_ratio i]
    calc m_xy * m_yz 
        ≤ (x.1 i / y.1 i) * m_yz := by
          apply mul_le_mul_of_nonneg_right
          · exact Finset.inf'_le (f := fun i => x.1 i / y.1 i) (Finset.mem_univ i)
          · exact le_of_lt hm_yz_pos
      _ ≤ (x.1 i / y.1 i) * (y.1 i / z.1 i) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.inf'_le (f := fun i => y.1 i / z.1 i) (Finset.mem_univ i)
          · exact le_of_lt (hpos_xy i)
  -- Now use log monotonicity
  have h1 : Real.log M_xz ≤ Real.log M_xy + Real.log M_yz := by
    rw [← Real.log_mul (ne_of_gt hM_xy_pos) (ne_of_gt hM_yz_pos)]
    exact Real.log_le_log hM_xz_pos hM_le
  have h2 : Real.log m_xy + Real.log m_yz ≤ Real.log m_xz := by
    rw [← Real.log_mul (ne_of_gt hm_xy_pos) (ne_of_gt hm_yz_pos)]
    exact Real.log_le_log (mul_pos hm_xy_pos hm_yz_pos) hm_ge
  linarith

/--
The Hilbert projective distance vanishes exactly on positive scalar multiples.
-/
theorem projectiveDist_eq_zero_iff_exists_pos_smul
    (x y : PositiveVec n) :
    Matrix.projectiveDist x y = 0 ↔
      ∃ c : ℝ, 0 < c ∧ x.1 = c • y.1 := by
  unfold projectiveDist
  rw [sub_eq_zero]
  have h_pos_ratio : ∀ i, 0 < x.1 i / y.1 i := fun i => div_pos (x.2 i) (y.2 i)
  set f := fun i => x.1 i / y.1 i with hf_def
  set sup_val := Finset.univ.sup' Finset.univ_nonempty f with hsup_def
  set inf_val := Finset.univ.inf' Finset.univ_nonempty f with hinf_def
  have h_sup_pos : 0 < sup_val := by
    have i₀ : n := Classical.arbitrary n
    calc 0 < f i₀ := h_pos_ratio i₀
         _ ≤ sup_val := Finset.le_sup' f (Finset.mem_univ i₀)
  have h_inf_pos : 0 < inf_val := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact h_pos_ratio i
  constructor
  · intro h_eq
    have h_sup_eq_inf : sup_val = inf_val := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_sup_pos) (Set.mem_Ioi.mpr h_inf_pos) h_eq
    use sup_val
    constructor
    · exact h_sup_pos
    · ext i
      have h_le_sup : f i ≤ sup_val := Finset.le_sup' f (Finset.mem_univ i)
      have h_inf_le : inf_val ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
      have h_val_eq : f i = sup_val := by
        apply le_antisymm h_le_sup
        rw [h_sup_eq_inf]
        exact h_inf_le
      simp only [Pi.smul_apply, smul_eq_mul, hf_def] at h_val_eq ⊢
      have hy_pos : 0 < y.1 i := y.2 i
      have hy_ne : y.1 i ≠ 0 := ne_of_gt hy_pos
      field_simp at h_val_eq ⊢
      linarith
  · intro ⟨c, hc_pos, hc_eq⟩
    have h_ratio_const : ∀ i, f i = c := by
      intro i
      simp only [hf_def, hc_eq, Pi.smul_apply, smul_eq_mul]
      have hy_ne : y.1 i ≠ 0 := ne_of_gt (y.2 i)
      field_simp
    have h_sup_eq_c : sup_val = c := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro i _
        rw [h_ratio_const i]
      · have i₀ : n := Classical.arbitrary n
        calc c = f i₀ := (h_ratio_const i₀).symm
             _ ≤ sup_val := Finset.le_sup' f (Finset.mem_univ i₀)
    have h_inf_eq_c : inf_val = c := by
      apply le_antisymm
      · have i₀ : n := Classical.arbitrary n
        calc inf_val ≤ f i₀ := Finset.inf'_le f (Finset.mem_univ i₀)
             _ = c := h_ratio_const i₀
      · apply Finset.le_inf'
        intro i _
        rw [h_ratio_const i]
    rw [h_sup_eq_c, h_inf_eq_c]

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
  refine csSup_le ?nonempty ?upper
  · exact ⟨0, Set.mem_union_left _ rfl⟩
  · intro t ht
    rw [Set.mem_union, Set.mem_singleton_iff] at ht
    rcases ht with rfl | ht
    · norm_num
    obtain ⟨x, y, hx, hy, hdist_ne, rfl⟩ := ht
    have hdist_nonneg : 0 ≤ Matrix.projectiveDist x y :=
      Matrix.projectiveDist_nonneg x y
    have hle :
        Matrix.projectiveDist ⟨A *ᵥ x.1, hx⟩ ⟨A *ᵥ y.1, hy⟩ ≤
          Matrix.projectiveDist x y := by
      simpa [Matrix.mulVecPositive] using
        Matrix.projectiveDist_mulVec_le hA_nonneg hA_row x y
    exact div_le_one_of_le₀ hle hdist_nonneg

omit [Fintype n] [DecidableEq n] [Nonempty n] in
/--
Scrambling implies row-allowability.
-/
theorem IsScrambling.isRowAllowable
    {A : Matrix n n ℝ} (h_scrambling : A.IsScrambling) :
    A.IsRowAllowable := by
  intro i
  obtain ⟨s, hs, _⟩ := h_scrambling i i
  exact ⟨s, hs⟩

/--
Scrambling matrices satisfy the general Birkhoff coefficient bound `≤ 1`.

Strict Hilbert-projective contraction requires stronger hypotheses than scrambling alone.
-/
theorem scrambling_implies_birkhoffContraction_le_one
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_scrambling : A.IsScrambling) :
    Matrix.birkhoffContraction A ≤ 1 := by
  exact Matrix.birkhoffContraction_le_one hA_nonneg h_scrambling.isRowAllowable

end Matrix
