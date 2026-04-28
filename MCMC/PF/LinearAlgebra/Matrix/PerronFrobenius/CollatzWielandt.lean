import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import MCMC.PF.aux
import Mathlib.Data.Matrix.Basic
import MCMC.PF.Topology.Compactness.ExtremeValueUSC

namespace Matrix
open Finset Quiver Matrix
variable {n : Type*} [Fintype n]

/-!
### The Collatz-Wielandt function for Matrices

-/
section PerronFrobenius
variable {n : Type*} [Fintype n] [Nonempty n]
variable {A : Matrix n n ℝ}
open LinearMap Set Filter Topology Finset IsCompact
open scoped Convex Pointwise

/-- The Collatz-Wielandt function, `r(x)` in Seneta's notation.
For a non-zero, non-negative vector `x`, this is `min_{i | xᵢ > 0} (Ax)ᵢ / xᵢ`.
Seneta uses row vectors `x'T`; we use column vectors `Ax`. The logic is identical. -/
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  let supp := {i | 0 < x i}.toFinset
  if h : supp.Nonempty then
    supp.inf' h fun i => (A *ᵥ x) i / x i
  else 0

/-- The matrix-vector multiplication map as a continuous linear map. -/
noncomputable abbrev mulVec_continuousLinearMap (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

omit [Nonempty n] in
@[simp] lemma collatzWielandtFn_zero (A : Matrix n n ℝ) :
    collatzWielandtFn A (0 : n → ℝ) = 0 := by
  simp [collatzWielandtFn]

namespace CollatzWielandt

/-! ### Positive supports -/

/-- A vector in the standard simplex has nonempty positive support. -/
private lemma pos_support_toFinset_nonempty_of_mem_stdSimplex {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) :
    ({i | 0 < x i}.toFinset).Nonempty := by
  obtain ⟨i, hi_pos⟩ := exists_pos_of_sum_one_of_nonneg hx.2 hx.1
  exact ⟨i, by simpa using hi_pos⟩

omit [Nonempty n] in
/-- A nonnegative nonzero vector has nonempty positive support. -/
private lemma pos_support_toFinset_nonempty_of_nonneg_ne_zero {x : n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ({i | 0 < x i}.toFinset).Nonempty := by
  by_contra h_empty
  apply hx_ne_zero
  ext i
  have hi_not_pos : ¬ 0 < x i := by
    intro hi_pos
    exact h_empty ⟨i, by simpa using hi_pos⟩
  exact le_antisymm (not_lt.mp hi_not_pos) (hx_nonneg i)

omit [Nonempty n] in
/-- On a vector with nonempty positive support, `collatzWielandtFn` is the infimum of its
associated ratios. -/
lemma collatzWielandtFn_eq_inf' (A : Matrix n n ℝ) {x : n → ℝ}
    (hx : ({i | 0 < x i}.toFinset).Nonempty) :
    collatzWielandtFn A x =
      ({i | 0 < x i}.toFinset).inf' hx (fun i => (A *ᵥ x) i / x i) := by
  dsimp [collatzWielandtFn]
  rw [dif_pos hx]

omit [Nonempty n] in
private def posSupportNeighborhood (x : n → ℝ) : Set (n → ℝ) :=
  {y | ∀ i ∈ {i | 0 < x i}.toFinset, 0 < y i}

omit [Nonempty n] in
private lemma self_mem_posSupportNeighborhood (x : n → ℝ) :
    x ∈ posSupportNeighborhood x := by
  intro i hi
  simpa [Set.mem_toFinset] using hi

omit [Nonempty n] in
private lemma isOpen_posSupportNeighborhood (x : n → ℝ) :
    IsOpen (posSupportNeighborhood x) := by
  have h_eq : posSupportNeighborhood x = ⋂ i ∈ {i | 0 < x i}.toFinset, {y | 0 < y i} := by
    ext y
    simp [posSupportNeighborhood]
  rw [h_eq]
  apply isOpen_biInter_finset
  intro i _
  exact isOpen_lt continuous_const (continuous_apply i)

omit [Nonempty n] in
private lemma continuousOn_fixedSupportRatios (A : Matrix n n ℝ) {x : n → ℝ}
    (hx : ({i | 0 < x i}.toFinset).Nonempty) :
    ContinuousOn (fun y => {i | 0 < x i}.toFinset.inf' hx fun i => (A *ᵥ y) i / y i)
      (posSupportNeighborhood x) := by
  apply continuousOn_finset_inf' hx
  intro i hi
  apply ContinuousOn.div
  · exact continuous_apply i |>.comp_continuousOn ((mulVec_continuousLinearMap A).continuous.continuousOn)
  · exact (continuous_apply i).continuousOn
  · intro y hy
    exact (hy i hi).ne'

private lemma collatzWielandtFn_le_fixedSupportRatios (A : Matrix n n ℝ)
    {x y : n → ℝ} (hx : ({i | 0 < x i}.toFinset).Nonempty)
    (hy : y ∈ posSupportNeighborhood x ∩ stdSimplex ℝ n) :
    collatzWielandtFn A y ≤
      {i | 0 < x i}.toFinset.inf' hx (fun i => (A *ᵥ y) i / y i) := by
  have hy_supp : {i | 0 < y i}.toFinset.Nonempty :=
    pos_support_toFinset_nonempty_of_mem_stdSimplex hy.2
  rw [collatzWielandtFn_eq_inf' A hy_supp]
  apply finset_inf'_mono_subset
  intro i hi
  have : 0 < y i := hy.1 i hi
  simpa [Set.mem_toFinset] using this

/-- *The Collatz-Wielandt function is upper-semicontinuous*.
Seneta relies on this fact (p.15, Appendix C) to use the Extreme Value Theorem.
`r(x)` is a minimum of functions `fᵢ(x) = (Ax)ᵢ / xᵢ`. Each `fᵢ` is continuous where `xᵢ > 0`.
The minimum of continuous functions is upper-semicontinuous.
[Giaquinta-Modica, Definition 6.21, Exercise 6.28, pp: 235, 236] -/
theorem upperSemicontinuousOn
    (A : Matrix n n ℝ) : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
    intro x₀ hx₀ c hc
    have supp_x₀ : {i | 0 < x₀ i}.toFinset.Nonempty :=
      pos_support_toFinset_nonempty_of_mem_stdSimplex hx₀
    have fn_eq :
        collatzWielandtFn A x₀ =
          {i | 0 < x₀ i}.toFinset.inf' supp_x₀ (fun i => (A *ᵥ x₀) i / x₀ i) :=
      collatzWielandtFn_eq_inf' A supp_x₀
    let f := fun y => {i | 0 < x₀ i}.toFinset.inf' supp_x₀ fun i => (A *ᵥ y) i / y i
    rw [fn_eq] at hc
    have cont_at : ContinuousAt f x₀ :=
      (continuousOn_fixedSupportRatios A supp_x₀).continuousAt
        ((isOpen_posSupportNeighborhood x₀).mem_nhds (self_mem_posSupportNeighborhood x₀))
    have lt_eventually : ∀ᶠ y in 𝓝 x₀, f y < c :=
      Filter.Tendsto.eventually_lt_const hc cont_at
    rcases eventually_to_open lt_eventually with ⟨V, V_open, x₀_in_V, hV⟩
    let W := V ∩ posSupportNeighborhood x₀ ∩ stdSimplex ℝ n
    have VU_open : IsOpen (V ∩ posSupportNeighborhood x₀) :=
      IsOpen.inter V_open (isOpen_posSupportNeighborhood x₀)
    have VU_mem : x₀ ∈ V ∩ posSupportNeighborhood x₀ :=
      ⟨x₀_in_V, self_mem_posSupportNeighborhood x₀⟩
    have VU_nhds : V ∩ posSupportNeighborhood x₀ ∈ 𝓝 x₀ := VU_open.mem_nhds VU_mem
    have W_nhdsWithin : W ∈ 𝓝[stdSimplex ℝ n] x₀ := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨V ∩ posSupportNeighborhood x₀, VU_nhds, by simp [W]⟩
    exact Filter.mem_of_superset W_nhdsWithin fun y hy => by
      show collatzWielandtFn A y < c
      apply lt_of_le_of_lt
      · exact collatzWielandtFn_le_fixedSupportRatios A supp_x₀ ⟨hy.1.2, hy.2⟩
      · exact hV y hy.1.1

-- The set of vectors we are optimizing over.
def P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

/-- The Collatz-Wielandt function attains its maximum on the standard simplex.
    [Giaquinta-Modica, Theorem 6.24 (dual), p: 235] -/
theorem exists_maximizer (A : Matrix n n ℝ) :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v := by
  have h_compact : IsCompact (stdSimplex ℝ n) := by exact _root_.isCompact_stdSimplex n
  have h_nonempty : (stdSimplex ℝ n).Nonempty := stdSimplex_nonempty
  have h_usc : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) :=
    upperSemicontinuousOn A
  exact IsCompact.exists_max_on_usco h_compact h_nonempty h_usc

lemma eq_iInf_of_nonempty
  {n : Type*} [Fintype n] [Nonempty n] (A : Matrix n n ℝ)
  (v : n → ℝ) (h : {i | 0 < v i}.toFinset.Nonempty) :
  collatzWielandtFn A v =
    ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn_eq_inf' A h]
  rw [Finset.inf'_eq_ciInf h]
  let s : Set n := {i | 0 < v i}
  rw [← Set.toFinite_toFinset s]
  simpa [s] using
    ((Set.toFinite s).subtypeEquivToFinset.symm.iInf_congr
      (f := fun i : {i // i ∈ (Set.toFinite s).toFinset} => (A *ᵥ v) i / v i)
      (g := fun i : {i // i ∈ s} => (A *ᵥ v) i / v i) <| by
        rintro ⟨i, hi⟩
        rfl)

omit [Nonempty n] in
/-- If r ≤ 0 and r is the infimum of non-negative ratios, then r = 0. -/
lemma val_eq_zero_of_nonpos [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i}) (hS_nonempty : S.Nonempty)
    (r : ℝ) (hr_def : r = collatzWielandtFn A v) (hr_nonpos : r ≤ 0) :
    r = 0 := by
  have r_ge_zero : 0 ≤ r := by
    have hS_finset_nonempty : { j | 0 < v j }.toFinset.Nonempty := by
      rwa [Set.toFinset_nonempty_iff, ← hS_def]
    rw [hr_def, collatzWielandtFn_eq_inf' A hS_finset_nonempty]
    apply Finset.le_inf'
    intro j hj
    rw [Set.mem_toFinset] at hj
    exact div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hA_nonneg j k) (hv_nonneg k)) hj.le
  exact le_antisymm hr_nonpos r_ge_zero

omit [Nonempty n] in
/-- Each ratio is at least the Collatz-Wielandt value -/
lemma le_ratio [DecidableEq n] {v : n → ℝ} (i : n) (hi_pos : 0 < v i) :
    collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
  have h_support : {j | 0 < v j}.toFinset.Nonempty := ⟨i, by simpa using hi_pos⟩
  rw [collatzWielandtFn_eq_inf' A h_support]
  apply Finset.inf'_le
  simpa using hi_pos

omit [Nonempty n] in
/-- For any non-negative, non-zero vector `v`, the Collatz-Wielandt value `r` satisfies
    `r • v ≤ A *ᵥ v`. This is the fundamental inequality derived from the definition of
    the Collatz-Wielandt function. -/
lemma le_mulVec [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
  (_ : v ≠ 0) :
    (collatzWielandtFn A v) • v ≤ A *ᵥ v := by
  let r := collatzWielandtFn A v
  intro i
  by_cases hi_supp : v i > 0
  · have h_le_div : r ≤ (A *ᵥ v) i / v i :=
      le_ratio (A := A) i hi_supp
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (le_div_iff₀ hi_supp).mp h_le_div
  · have h_vi_zero : v i = 0 := by linarith [hv_nonneg i, not_lt.mp hi_supp]
    simp only [Pi.smul_apply, smul_eq_mul, h_vi_zero, mul_zero]
    exact mulVec_nonneg hA_nonneg hv_nonneg i

omit [Fintype n] [Nonempty n] in
/-- If the Collatz-Wielandt value `r` is non-positive, there must be some `i` in the support of `v`
    where the ratio, and thus `(A * v) i`, is zero. -/
lemma exists_mulVec_eq_zero_on_support_of_nonpos [Fintype n]
  (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
  (h_supp_nonempty : {i | 0 < v i}.toFinset.Nonempty)
  (h_r_nonpos : collatzWielandtFn A v ≤ 0) :
  ∃ i ∈ {i | 0 < v i}.toFinset, (A *ᵥ v) i = 0 := by
  have r_nonneg : 0 ≤ collatzWielandtFn A v := by
    rw [collatzWielandtFn_eq_inf' A h_supp_nonempty]
    apply Finset.le_inf'
    intro i hi_mem
    exact div_nonneg (mulVec_nonneg hA_nonneg hv_nonneg i) (by exact hv_nonneg i)
  have r_eq_zero : collatzWielandtFn A v = 0 := le_antisymm h_r_nonpos r_nonneg
  rw [collatzWielandtFn_eq_inf' A h_supp_nonempty] at r_eq_zero
  obtain ⟨b, hb_mem, hb_eq⟩ := Finset.exists_mem_eq_inf' h_supp_nonempty (fun i => (A *ᵥ v) i / v i)
  have h_ratio_zero : (A *ᵥ v) b / v b = 0 := by rw [← hb_eq, r_eq_zero]
  have h_vb_pos : 0 < v b := by simpa [Set.mem_toFinset] using hb_mem
  grind

/-- The set of values from the Collatz-Wielandt function is bounded above by the maximum row sum of A. -/
lemma bddAbove [DecidableEq n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' P_set) := by
  use Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ∑ j, A i j)
  rintro y ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  obtain ⟨m, h_xm_pos, h_xm_max⟩ := exists_pos_maximal_of_nonneg_ne_zero hx_nonneg hx_ne_zero
  have h_le_ratio : collatzWielandtFn A x ≤ (A *ᵥ x) m / x m :=
    le_ratio (A := A) m h_xm_pos
  have h_ratio_le : (A *ᵥ x) m / x m ≤ Finset.univ.sup' Finset.univ_nonempty (fun k ↦ ∑ l, A k l) := by
    rw [mulVec_apply, div_le_iff h_xm_pos]
    calc
      ∑ j, A m j * x j
        ≤ ∑ j, A m j * x m := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (h_xm_max j) (hA_nonneg m j)
      _ = (∑ j, A m j) * x m := by rw [Finset.sum_mul]
      _ ≤ (Finset.univ.sup' Finset.univ_nonempty (fun k ↦ ∑ l, A k l)) * x m := by
          apply mul_le_mul_of_nonneg_right
          · exact le_sup' (fun k => ∑ l, A k l) (Finset.mem_univ m)
          · exact le_of_lt h_xm_pos
  exact le_trans h_le_ratio h_ratio_le

/-- The set of values from the Collatz-Wielandt function is non-empty. -/
lemma set_nonempty :
    (collatzWielandtFn A '' P_set).Nonempty := by
  let xOnes : n → ℝ := fun _ ↦ 1
  have hxOnes_mem : xOnes ∈ P_set := by
    constructor
    · intro i; exact zero_le_one
    · intro h_zero
      have h_contra : (1 : ℝ) = 0 := by
        simpa [xOnes] using congr_fun h_zero (Classical.arbitrary n)
      exact one_ne_zero h_contra
  exact Set.Nonempty.image _ ⟨xOnes, hxOnes_mem⟩

omit [Nonempty n] in
lemma collatzWielandtFn_smul [DecidableEq n] {c : ℝ} (hc : 0 < c)
  {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
  collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  dsimp [collatzWielandtFn]
  let S := {i | 0 < x i}.toFinset
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne
  have hS_nonempty : S.Nonempty := ⟨i₀, by simp [S, hi₀]⟩
  have h_supp_eq : {i | 0 < (c • x) i}.toFinset = S := by
    ext i
    simp [S, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  rw [dif_pos (h_supp_eq.symm ▸ hS_nonempty), dif_pos hS_nonempty]
  refine inf'_congr (Eq.symm h_supp_eq ▸ hS_nonempty) h_supp_eq ?_
  intro i hi
  simp only [mulVec_smul, smul_eq_mul, Pi.smul_apply]
  rw [mul_div_mul_left _ _ (ne_of_gt hc)]

/-- The Perron root, as the supremum of the Collatz-Wielandt function (see Seneta). -/
noncomputable def perronRoot_alt (A : Matrix n n ℝ) : ℝ :=
  sSup (collatzWielandtFn A '' P_set)

omit [Nonempty n] in
theorem eq_eigenvalue_of_positive_eigenvector
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
  (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    collatzWielandtFn A v = r := by
  have h_supp_nonempty : ({i | 0 < v i}.toFinset).Nonempty := by
    let i0 : n := Classical.arbitrary n
    exact ⟨i0, by simpa using hv_pos i0⟩
  rw [eq_iInf_of_nonempty A v h_supp_nonempty]
  calc
    ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i = ⨅ _ : {i | 0 < v i}, r := by
      refine iInf_congr ?_
      intro i
      have h_eig_i : (A *ᵥ v) i = r * v i := by
        simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h_eig i
      rw [h_eig_i, mul_div_assoc, div_self i.2.ne']
      simp
    _ = r := by
      have h_support_nonempty : ({i | 0 < v i} : Set n).Nonempty := by
        rcases h_supp_nonempty with ⟨i, hi⟩
        exact ⟨i, by simpa [Set.mem_toFinset] using hi⟩
      letI : Nonempty {i | 0 < v i} := Set.Nonempty.to_subtype h_support_nonempty
      show (⨅ _ : {i | 0 < v i}, r) = r
      exact ciInf_const (ι := {i | 0 < v i}) (a := r)

variable {n : Type*} [Fintype n]
variable {A : Matrix n n ℝ}

/-- Any eigenvalue with a strictly positive eigenvector is ≤ the Perron root. -/
theorem eigenvalue_le_perron_root_of_positive_eigenvector
    {r : ℝ} {v : n → ℝ}
    [Nonempty n] [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (_ : 0 < r)
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    r ≤ perronRoot_alt A := by
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have hcontr : (0 : ℝ) < 0 := by
      have hpos := hv_pos (Classical.arbitrary n)
      simp [h] at hpos
    exact (lt_irrefl _ hcontr).elim
  have h_r : r = collatzWielandtFn A v :=
    (eq_eigenvalue_of_positive_eigenvector hv_pos h_eig).symm
  have h_le : collatzWielandtFn A v ≤ perronRoot_alt A := by
    dsimp [perronRoot_alt]
    have h_bdd : BddAbove (collatzWielandtFn A '' P_set) :=
      bddAbove A hA_nonneg
    apply le_csSup h_bdd
    have hv_in_P : v ∈ P_set := ⟨hv_nonneg, hv_ne_zero⟩
    exact Set.mem_image_of_mem (collatzWielandtFn A) hv_in_P
  simpa [h_r] using h_le

/-- A left eigenvector of the matrix is a right eigenvector of its transpose -/
lemma left_eigenvector_of_transpose {r : ℝ} {u : n → ℝ}
    (hu_left : u ᵥ* A = r • u) :
    Aᵀ *ᵥ u = r • u := by
  rwa [← vecMul_eq_mulVec_transpose]

/-- For any non-negative vector `w`, its Collatz–Wielandt value … -/
lemma le_eigenvalue_of_left_eigenvector [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (_ : 0 < r)
    {u : n → ℝ} (hu_pos : ∀ i, 0 < u i) (h_eig : u ᵥ* A = r • u)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i ↦ (hu_pos i).le
  have h_le_mulVec := CollatzWielandt.le_mulVec hA_nonneg hw_nonneg hw_ne_zero
  have h_intermediate :
      u ⬝ᵥ ((collatzWielandtFn A w) • w) ≤ u ⬝ᵥ (A *ᵥ w) := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro i _
    have hi := h_le_mulVec i
    simp [Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact mul_le_mul_of_nonneg_left hi (hu_nonneg i)
  have h_right :
      u ⬝ᵥ (A *ᵥ w) = r * (u ⬝ᵥ w) := by
    have := dotProduct_mulVec u A w
    calc
      u ⬝ᵥ (A *ᵥ w) = (u ᵥ* A) ⬝ᵥ w := this
      _ = (r • u) ⬝ᵥ w := by simp [h_eig]
      _ = r * (u ⬝ᵥ w) := by simp [smul_eq_mul]
  have h_left :
      u ⬝ᵥ ((collatzWielandtFn A w) • w)
        = (collatzWielandtFn A w) * (u ⬝ᵥ w) := by
    simp [dotProduct_smul, smul_eq_mul]
  have h_dot_le :
      (collatzWielandtFn A w) * (u ⬝ᵥ w) ≤ r * (u ⬝ᵥ w) := by
    simpa [h_left, h_right] using h_intermediate
  have h_dot_pos : 0 < u ⬝ᵥ w :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hw_nonneg hw_ne_zero
  exact le_of_mul_le_mul_right h_dot_le h_dot_pos

/--
If `u` is a strictly positive left eigenvector of `A` for eigenvalue `r > 0`,
then the Perron root of `A` is less than or equal to `r`.
That is, `perronRoot_alt A ≤ r`.
-/
lemma perron_root_le_eigenvalue_of_left_eigenvector [Nonempty n] [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r) {u : n → ℝ} (hu_pos : ∀ i, 0 < u i)
    (h_eig : u ᵥ* A = r • u) :
    perronRoot_alt A ≤ r := by
  dsimp [perronRoot_alt]
  apply csSup_le
  · exact CollatzWielandt.set_nonempty
  · rintro _ ⟨w, ⟨hw_nonneg, hw_ne_zero⟩, rfl⟩
    exact CollatzWielandt.le_eigenvalue_of_left_eigenvector hA_nonneg hr_pos hu_pos h_eig hw_nonneg hw_ne_zero

/--
If `v` is a strictly positive right eigenvector of `A` with eigenvalue `r`, then the vector
of all ones is a right eigenvector of the similarity-transformed matrix `B = D⁻¹AD`
(where `D` is `diagonal v`) with the same eigenvalue `r`.
-/
lemma ones_eigenvector_of_similarity_transform [DecidableEq n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    (diagonal (v⁻¹) * A * diagonal v) *ᵥ (fun _ => 1) = fun _ => r := by
  let D := diagonal v
  let D_inv := diagonal (v⁻¹)
  let B := D_inv * A * D
  let ones := fun _ : n => (1 : ℝ)
  calc
    B *ᵥ ones
      = D_inv *ᵥ (A *ᵥ (D *ᵥ ones)) := by
          unfold B
          rw [← mulVec_mulVec, ← mulVec_mulVec]
    _ = D_inv *ᵥ (A *ᵥ v) := by
        have h_D_ones : D *ᵥ ones = v := by
          unfold D ones
          exact diagonal_mulVec_ones v
        rw [h_D_ones]
    _ = D_inv *ᵥ (r • v) := by rw [h_eig]
    _ = r • (D_inv *ᵥ v) := by rw [mulVec_smul]
    _ = r • ones := by
        have h_D_inv_v : D_inv *ᵥ v = ones := by
          unfold D_inv ones
          have hv_ne_zero : ∀ i, v i ≠ 0 := fun i => (hv_pos i).ne'
          exact diagonal_inv_mulVec_self hv_ne_zero
        rw [h_D_inv_v]
    _ = fun _ => r := by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul, mul_one, ones]

/--
If `v` is a strictly positive right eigenvector of `A` with eigenvalue `r`, then the
similarity-transformed matrix `B = D⁻¹AD` (where `D` is `diagonal v`) has row sums equal to `r`.
-/
lemma row_sum_of_similarity_transformed_matrix [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    ∀ i, ∑ j, (Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v) i j = r := by
  intro i
  let B := Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v
  have row_sum_eq : ∑ j, B i j = (B *ᵥ (fun _ => 1)) i := by
    simp only [mulVec_apply, mul_one]
  rw [row_sum_eq]
  have h_B_eig := ones_eigenvector_of_similarity_transform hv_pos h_eig
  rw [h_B_eig]

/--
If a non-negative vector `x` satisfies `c • x ≤ B *ᵥ x` for a non-negative matrix `B`
whose row sums are all equal to `r`, then `c ≤ r`.
-/
lemma le_of_max_le_row_sum [Nonempty n] [DecidableEq n]
    {B : Matrix n n ℝ} {x : n → ℝ} {c r : ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (h_B_row_sum : ∀ i, ∑ j, B i j = r)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) (h_le_Bx : c • x ≤ B *ᵥ x) :
    c ≤ r := by
  obtain ⟨k, h_xk_pos, h_xk_max⟩ := exists_pos_maximal_of_nonneg_ne_zero hx_nonneg hx_ne_zero
  have h_le_k := h_le_Bx k
  simp only [Pi.smul_apply, smul_eq_mul] at h_le_k
  have h_Bx_le : (B *ᵥ x) k ≤ r * x k := by
    calc (B *ᵥ x) k
        = ∑ j, B k j * x j := by simp [mulVec_apply]
      _ ≤ ∑ j, B k j * x k := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (h_xk_max j) (hB_nonneg k j)
      _ = (∑ j, B k j) * x k := by rw [Finset.sum_mul]
      _ = r * x k := by rw [h_B_row_sum]
  exact le_of_mul_le_mul_right (le_trans h_le_k h_Bx_le) h_xk_pos

    /-- Positive diagonal similarity preserves entrywise nonnegativity. -/
    lemma nonneg_similarity_transform [DecidableEq n]
      {A : Matrix n n ℝ} {v : n → ℝ}
      (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_pos : ∀ i, 0 < v i) :
      ∀ i j, 0 ≤ (Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v) i j := by
      intro i j
      rw [mul_diagonal, diagonal_mul]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (hv_pos i).le) (hA_nonneg i j)) (hv_pos j).le

/--
For any non-negative vector `w`, its Collatz–Wielandt value is bounded above by a
positive eigenvalue `r` that has a strictly positive *right* eigenvector `v`.
-/
theorem le_eigenvalue_of_right_eigenvector [Nonempty n]  [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (_ : 0 < r)
    {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  let D := Matrix.diagonal v
  let D_inv := Matrix.diagonal (v⁻¹)
  let B := D_inv * A * D
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    simpa [B, D, D_inv] using nonneg_similarity_transform hA_nonneg hv_pos
  have h_B_row_sum := row_sum_of_similarity_transformed_matrix hv_pos h_eig
  let x := D_inv *ᵥ w
  have h_w_eq_Dx : w = D *ᵥ x := by
    simpa [D, D_inv, x] using
      (diagonal_mulVec_diagonal_inv_mulVec (d := v) (x := w) fun i => (hv_pos i).ne').symm
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    unfold x D_inv
    rw [mulVec_diagonal]
    exact mul_nonneg (inv_nonneg.mpr (hv_pos i).le) (hw_nonneg i)
  have hx_ne_zero : x ≠ 0 := by
    contrapose! hw_ne_zero
    rw [h_w_eq_Dx, hw_ne_zero, mulVec_zero]
  have h_smul_le : (collatzWielandtFn A w) • w ≤ A *ᵥ w :=
    CollatzWielandt.le_mulVec hA_nonneg hw_nonneg hw_ne_zero
  have h_le_Bx : (collatzWielandtFn A w) • x ≤ B *ᵥ x := by
    calc
      (collatzWielandtFn A w) • x = D_inv *ᵥ ((collatzWielandtFn A w) • w) := by
        rw [← mulVec_smul, h_w_eq_Dx]
      _ ≤ D_inv *ᵥ (A *ᵥ w) := by
        simpa [D_inv] using
          diagonal_mulVec_mono (d := v⁻¹) (x := (collatzWielandtFn A w) • w) (y := A *ᵥ w)
            (fun i => inv_nonneg.mpr (hv_pos i).le) h_smul_le
      _ = D_inv *ᵥ (A *ᵥ (D *ᵥ x)) := by rw [h_w_eq_Dx]
      _ = (D_inv * A * D) *ᵥ x := by rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = B *ᵥ x := rfl
  exact le_of_max_le_row_sum hB_nonneg h_B_row_sum hx_nonneg hx_ne_zero h_le_Bx

/- Any positive eigenvalue `r` with a strictly positive right eigenvector `v` is an
upper bound for the range of the Collatz-Wielandt function.
-/
theorem eigenvalue_is_ub_of_positive_eigenvector [Nonempty n]  [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r)
    {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    perronRoot_alt A ≤ r := by
  dsimp [perronRoot_alt]
  apply csSup_le (CollatzWielandt.set_nonempty (A := A))
  rintro _ ⟨w, ⟨hw_nonneg, hw_ne_zero⟩, rfl⟩
  exact CollatzWielandt.le_eigenvalue_of_right_eigenvector
    hA_nonneg hr_pos hv_pos h_eig hw_nonneg hw_ne_zero

theorem eq_perron_root_of_positive_eigenvector
    [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hv_pos    : ∀ i, 0 < v i)
    (hr_pos    : 0 < r)
    (h_eig     : A *ᵥ v = r • v) :
    r = CollatzWielandt.perronRoot_alt (A := A) := by
  have h₁ : r ≤ CollatzWielandt.perronRoot_alt (A := A) :=
    CollatzWielandt.eigenvalue_le_perron_root_of_positive_eigenvector
      (A := A) hA_nonneg hr_pos hv_pos h_eig
  have h₂ : CollatzWielandt.perronRoot_alt (A := A) ≤ r :=
    CollatzWielandt.eigenvalue_is_ub_of_positive_eigenvector
      hA_nonneg hr_pos hv_pos h_eig
  exact le_antisymm h₁ h₂

@[simp]
theorem Finset.sum_def {α M : Type*} [AddCommMonoid M] {s : Finset α} (f : α → M) :
  (∑ i ∈ s, f i) = s.sum f :=
rfl

/--  A finite sum of non-negative terms is strictly positive as soon as one
     summand is strictly positive.  -/
lemma Finset.sum_pos_of_nonneg_of_exists_pos {α β : Type*}
  [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
 {s : Finset α} {f : α → β}
    (h_nonneg : ∀ i ∈ s, 0 ≤ f i)
    (h_exists : ∃ i ∈ s, 0 < f i) :
    0 < ∑ i ∈ s, f i :=
  Finset.sum_pos' h_nonneg h_exists

private lemma le_of_isMaxOn_stdSimplex [DecidableEq n] {v : n → ℝ}
    (hv_max : IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A x ≤ collatzWielandtFn A v := by
  set s : ℝ := ∑ i, x i with hs
  have hs_pos : 0 < s := by
    obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne_zero
    have : 0 < ∑ i, x i :=
      Finset.sum_pos_of_nonneg_of_exists_pos
        (fun j _ => hx_nonneg j) ⟨i, Finset.mem_univ _, hi⟩
    simpa [hs] using this
  set x' : n → ℝ := s⁻¹ • x with hx'
  have hx'_in_simplex : x' ∈ stdSimplex ℝ n := by
    constructor
    · intro i
      have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_pos.le
      simpa [hx'] using mul_nonneg hs_inv_nonneg (hx_nonneg i)
    · have : (∑ i, x' i) = 1 := by
        simp only [hx', Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hs]
        field_simp [ne_of_gt hs_pos]
      exact this
  have h_max : collatzWielandtFn A x' ≤ collatzWielandtFn A v := hv_max hx'_in_simplex
  have h_scale : collatzWielandtFn A x = collatzWielandtFn A x' := by
    have h_smul := CollatzWielandt.collatzWielandtFn_smul (A := A) (c := s⁻¹)
      (inv_pos.mpr hs_pos) (x := x) hx_nonneg hx_ne_zero
    rw [← hx'] at h_smul
    exact h_smul.symm
  rwa [h_scale]

omit [Fintype n] in
lemma maximizer_satisfies_le_mulVec
    [Fintype n] [Nonempty n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot_alt A
    ∃ v ∈ stdSimplex ℝ n, r • v ≤ A *ᵥ v := by
  let r := perronRoot_alt A
  obtain ⟨v, v_in_simplex, v_is_max⟩ := exists_maximizer (A := A)
  have v_ne_zero : v ≠ 0 := by
    intro hv
    have h_sum_one : (∑ i, v i) = 1 := v_in_simplex.2
    rw [hv] at h_sum_one
    simp only [Pi.zero_apply, Finset.sum_const_zero] at h_sum_one
    norm_num at h_sum_one
  have v_nonneg : ∀ i, 0 ≤ v i := v_in_simplex.1
  have r_eq : (perronRoot_alt A) = collatzWielandtFn A v := by
    dsimp [perronRoot_alt]
    apply le_antisymm
    ·
      apply csSup_le set_nonempty
      rintro _ ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
      exact le_of_isMaxOn_stdSimplex (A := A) v_is_max hx_nonneg hx_ne_zero
    ·
      apply le_csSup (bddAbove A hA_nonneg)
      exact Set.mem_image_of_mem _ ⟨v_nonneg, v_ne_zero⟩
  have h_le : (perronRoot_alt A) • v ≤ A *ᵥ v := by
    have : (collatzWielandtFn A v) • v ≤ A *ᵥ v :=
      le_mulVec hA_nonneg v_nonneg v_ne_zero
    simpa [r_eq] using this
  refine ⟨v, v_in_simplex, ?_⟩
  simpa [r] using h_le

/--
The conditional supremum of a non-empty, bounded above set of non-negative numbers is non-negative.
-/
lemma csSup_nonneg {s : Set ℝ} (hs_nonempty : s.Nonempty) (hs_bdd : BddAbove s)
    (hs_nonneg : ∀ x ∈ s, 0 ≤ x) :
    0 ≤ sSup s := by
  obtain ⟨y, hy_mem⟩ := hs_nonempty
  have h_y_nonneg : 0 ≤ y := hs_nonneg y hy_mem
  have h_y_le_sSup : y ≤ sSup s := le_csSup hs_bdd hy_mem
  exact le_trans h_y_nonneg h_y_le_sSup

/-- The Perron root of a non-negative matrix is non-negative. -/
lemma perronRoot_nonneg {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 ≤ perronRoot_alt A := by
  unfold perronRoot_alt
  apply csSup_nonneg
  · exact CollatzWielandt.set_nonempty
  · exact CollatzWielandt.bddAbove A hA_nonneg
  · rintro _ ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
    dsimp [collatzWielandtFn]
    split_ifs with h_supp_nonempty
    · apply Finset.le_inf'
      intro i hi_mem
      apply div_nonneg
      · exact mulVec_nonneg hA_nonneg hx_nonneg i
      · exact (Set.mem_toFinset.mp hi_mem).le
    · exact le_rfl

/--
If an inequality lambda•w ≤ A•w holds for a non-negative non-zero vector w,
then lambda is bounded by the Collatz-Wielandt function value for w.
This is the property that the Collatz-Wielandt function gives
the maximum lambda satisfying such an inequality.
-/
theorem le_of_subinvariant [DecidableEq n]
    {A : Matrix n n ℝ} (_ : ∀ i j, 0 ≤ A i j)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0)
    {lambda : ℝ} (h_sub : lambda • w ≤ A *ᵥ w) :
    lambda ≤ collatzWielandtFn A w := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hw_nonneg hw_ne_zero
  let S := {j | 0 < w j}.toFinset
  have hS_nonempty : S.Nonempty := ⟨i, by simp [S]; exact hi⟩
  rw [collatzWielandtFn, dif_pos hS_nonempty]
  apply Finset.le_inf'
  intro j hj
  have h_j : lambda * w j ≤ (A *ᵥ w) j := by
    simp_all only [ne_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S]
    apply h_sub
  have hw_j_pos : 0 < w j := by simpa [S] using hj
  exact (le_div_iff₀ hw_j_pos).mpr (h_sub j)
