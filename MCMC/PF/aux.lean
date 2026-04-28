import MCMC.PF.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

open Filter Set Finset Matrix Topology Convex

/- Standard simplex definition
def stdSimplex (𝕜 ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] : Set (ι → 𝕜) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

-- Upper semicontinuous function definition
def UpperSemicontinuousOn {α β : Type*} [TopologicalSpace α] [Preorder β]
    (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y, f x < y → ∃ U ∈ 𝓝[s] x, ∀ z ∈ U, f z < y

-- Lower semicontinuous function definition
def LowerSemicontinuousOn {α β : Type*} [TopologicalSpace α] [Preorder β]
    (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y, y < f x → ∃ U ∈ 𝓝[s] x, ∀ z ∈ U, y < f z

-- Cluster point definition
def ClusterPt {X : Type*} [TopologicalSpace X] (x : X) (F : Filter X) : Prop :=
  (𝓝 x ⊓ F).NeBot

-- Ultrafilter definition
structure Ultrafilter (α : Type*) extends Filter α where
  isUltra : ∀ s, s ∈ toFilter ∨ sᶜ ∈ toFilter-/

/-!
## Key Theorems for Compactness & Ultrafilters
-/

/- Ultrafilter existence theorem
theorem Ultrafilter.exists_le {α : Type*} {F : Filter α} (h : F.NeBot) :
  ∃ U : Ultrafilter α, (U : Filter α) ≤ F := by
  exact Ultrafilter.exists_le F

-- Compactness characterization via ultrafilters
theorem isCompact_iff_ultrafilter_le_nhds {X : Type*} [TopologicalSpace X] {s : Set X} :
  IsCompact s ↔ ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, (f : Filter X) ≤ 𝓝 x := by
  exact isCompact_iff_ultrafilter_le_nhds

-- Cluster point existence in compact sets
theorem IsCompact.exists_clusterPt {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) {f : Filter X} (hf : f.NeBot) (hfs : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := by
  exact hs.exists_clusterPt hfs-/

-- Ultrafilter convergence from cluster point
theorem ClusterPt.exists_ultrafilter {X : Type*} [TopologicalSpace X] {x : X} {f : Filter X}
    (h : ClusterPt x f) : ∃ U : Ultrafilter X, (U : Filter X) ≤ f ∧ (U : Filter X) ≤ 𝓝 x := by
  exact clusterPt_iff_ultrafilter.mp h

/-!
## Semicontinuity Theorems
-/
/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is continuous on `s`,
then `f` maps `G` to the neighborhood filter of `f x`.
This is a version with lower and upper semicontinuity.
-/
lemma tendsto_of_lower_upper_semicontinuous_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder Y] [OrderTopology Y]
    {f : X → Y} {s : Set X} (h_upper : UpperSemicontinuousOn f s)
    (h_lower : LowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) :
    Tendsto f (G : Filter X) (𝓝 (f x)) := by
  have h_cont : ContinuousWithinAt f s x :=
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨h_lower x hx, h_upper x hx⟩
  exact h_cont.tendsto.comp (tendsto_id.mono_left hG)

/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is upper semicontinuous on `s`,
then for any `y' > f x`, `f` eventually maps elements of `G` to values less than `y'`.
-/
lemma upperSemicontinuousOn_eventually_lt_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X}
    (hf : UpperSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) {y' : Y} (hy' : f x < y') :
    ∀ᶠ (z : X) in (G : Filter X), f z < y' :=
  hG (hf x hx y' hy')

/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is lower semicontinuous on `s`,
then for any `y' < f x`, `f` eventually maps elements of `G` to values greater than `y'`.
-/
lemma lowerSemicontinuousOn_eventually_gt_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X}
    (hf : LowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) {y' : Y} (hy' : y' < f x) :
    ∀ᶠ (z : X) in (G : Filter X), y' < f z :=
  hG (hf x hx y' hy')

/-!
## Standard Simplex Properties
-/

/- Standard simplex is compact
theorem isCompact_stdSimplex (ι : Type*) [Fintype ι] : IsCompact (stdSimplex ℝ ι) := by
  exact _root_.isCompact_stdSimplex ι

-- Standard simplex is convex
theorem convex_stdSimplex (𝕜 ι : Type*) [OrderedRing 𝕜] [Fintype ι] :
    Convex 𝕜 (stdSimplex 𝕜 ι) := by
  exact _root_.convex_stdSimplex 𝕜 ι-/

-- Standard simplex is nonempty when ι is nonempty
theorem stdSimplex_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (stdSimplex ℝ ι).Nonempty := by
  exact ⟨(Fintype.card ι : ℝ)⁻¹ • 1, by simp [stdSimplex, Finset.sum_const, nsmul_eq_mul]⟩

/-!
## Supremum & Infimum Theorems
-/

-- Compact sets in ℝ attain their supremum
theorem IsCompact.exists_max {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty) :
  ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  let sup_s := sSup s
  have h_mem : sup_s ∈ s := sSup_mem hs hne
  use sup_s, h_mem
  intro y hy
  exact le_csSup (hs.bddAbove) hy

-- Function attaining maximum equals supremum of image
theorem isMaxOn_eq_sSup {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} {v : X}
    (hv : v ∈ s) (hmax : ∀ z ∈ s, f z ≤ f v) :
    sSup (f '' s) = f v := by
  apply le_antisymm
  · apply csSup_le
    · use f v
      refine ⟨v, hv, rfl⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmax x hx
  · apply le_csSup
    · exact ⟨f v, fun a ha => by
        rcases ha with ⟨x, hx, rfl⟩
        exact hmax x hx⟩
    · exact Set.mem_image_of_mem f hv

/-!
## Filter & Ultrafilter Operations
-/

/- Ultrafilter mapping
def Ultrafilter.map {α β : Type*} (f : α → β) (u : Ultrafilter α) : Ultrafilter β :=
  ⟨Filter.map f u, by
    intro s
    have := u.isUltra (f ⁻¹' s)
    cases this with
    | inl h => left; exact Filter.mem_map.mpr h
    | inr h => right; exact Filter.mem_map.mpr h⟩

-- Ultrafilter equality from inclusion
theorem Ultrafilter.eq_of_le {α : Type*} {u v : Ultrafilter α} (h : (u : Filter α) ≤ v) :
    u = v := by
  exact Ultrafilter.eq_of_le h

-- Tendsto characterization for ultrafilters
theorem tendsto_map'_iff {α β : Type*} {f : α → β} {u : Ultrafilter α} {l : Filter β} :
    Tendsto f (u : Filter α) l ↔ (Ultrafilter.map f u : Filter β) ≤ l := by
  exact tendsto_map'_iff-/

/-!
## Helper Lemmas for Continuity
-/

-- Eventually to open set conversion
theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ (U : Set α), IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  simp_all only
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => {exact hU
    }
    · simp_all only
    · intro x a_1
      apply hU_open
      simp_all only

-- Continuous infimum over finset
theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*} [Fintype ι]
    {s : Finset ι} {U : Set α} (hs : s.Nonempty) {f : ι → α → β}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf

-- Infimum monotonicity for subsets
theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f := by
  exact inf'_mono f h hs

/-!
## Matrix & Vector Operations
-/

-- Matrix-vector multiplication component
theorem matrix_mulVec_component {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (j : n) :
    (A *ᵥ v) j = ∑ i, A j i * v i := by
  simp [Matrix.mulVec]; rfl

-- Non-negative matrix preserves non-negative vectors
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

-- Positive matrix with positive vector gives positive result
theorem positive_mul_vec_pos {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp
    · exact mul_pos (hA_pos i k) hk_pos

/-!
## Utility Lemmas
-/

-- Existence of positive element in sum of non-negative elements
theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (h i) (hnonneg i)
  have h_sum_zero : ∑ i, x i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  have : 1 = 0 := by linarith
  exact absurd this (by norm_num)

-- Existence of non-zero element in non-zero vector
theorem exists_ne_zero_of_ne_zero {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ} (hx : x ≠ 0) : ∃ j, x j ≠ 0 := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := h
  have x_is_zero : x = 0 := by
    ext i
    exact h_all_zero i
  exact hx x_is_zero

-- Matrix power multiplication
theorem pow_mulVec_succ {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ} (k : ℕ) (x : n → ℝ) :
    (A^(k+1)).mulVec x = A.mulVec ((A^k).mulVec x) := by
  simp only [mulVec_mulVec]
  rw [pow_succ']


/-!
## Finset Operations
-/

-- Infimum over finite type equals finset infimum
theorem iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*} [Fintype α] [Nonempty α]
    [ConditionallyCompleteLinearOrder γ] (f : α → β → γ) :
    (fun x => ⨅ i, f i x) = (fun x => (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x)) := by
  ext x
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by simp only [mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr
    ext i
    simp only [mem_univ, ciInf_unique, Finset.mem_univ]
  have h3 : ⨅ i ∈ (Finset.univ : Finset α), f i x =
           (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
    rfl
  rw [h1, h2, h3]

-- Infimum over finite type equals conditional infimum
theorem iInf_eq_ciInf {α β : Type*} [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder β]
    (f : α → β) : (⨅ i, f i) = ⨅ i ∈ (Set.univ : Set α), f i := by
  apply eq_of_forall_le_iff
  intro b
  simp only [mem_univ, ciInf_unique]

/-!
## Order & Field Properties
-/

-- Multiplication cancellation for positive elements
theorem mul_div_cancel_pos_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (h : a * b = c) (hb : 0 < b) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb.ne'

-- Non-positive times positive is non-positive
theorem mul_nonpos_of_nonpos_of_pos {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (ha : a ≤ 0) (hb : 0 < b) : a * b ≤ 0 := by
  rcases le_iff_eq_or_lt.mp ha with (rfl | h)
  · rw [zero_mul]
  · exact (mul_neg_of_neg_of_pos h hb).le

-- Continuous infimum over finite index
theorem continuousOn_iInf {α β : Type*} [Fintype α] [Nonempty α] [TopologicalSpace β]
    {s : Set β} {f : α → β → ℝ} (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x => ⨅ i, f i x) s := by
  classical
  let g : β → ℝ := fun x => (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x)
  have hg : ContinuousOn g s := ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i _ => hf i
  have h_eq : (fun x => ⨅ i, f i x) = g := by
    dsimp [g]
    exact iInf_apply_eq_finset_inf'_apply_fun f
  rwa [h_eq]


namespace Fintype

lemma card_gt_one_of_nonempty_ne {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] :
    1 < Fintype.card α ↔ ∃ (i j : α), i ≠ j := by
  constructor
  · intro h
    obtain ⟨i⟩ : Nonempty α := ‹Nonempty α›
    have h_card_ne_one : Fintype.card α ≠ 1 := ne_of_gt h
    have : ∃ j, j ≠ i := by
      by_contra h_all_eq
      push_neg at h_all_eq
      have : ∀ x : α, x = i := h_all_eq
      have h_card_eq_one : Fintype.card α = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨i, this⟩
      exact h_card_ne_one h_card_eq_one
    obtain ⟨j, hj⟩ := this
    exact ⟨i, j, hj.symm⟩
  · intro ⟨i, j, hij⟩
    have : Fintype.card α ≥ 2 := by
      rw [← Finset.card_univ]
      have : ({i, j} : Finset α) ⊆ Finset.univ := by simp
      have : Finset.card ({i, j} : Finset α) ≤ Finset.card Finset.univ := Finset.card_le_card this
      have : Finset.card ({i, j} : Finset α) = 2 := by simp [hij]
      linarith
    linarith

end Fintype

/-!
## Additional Helper Theorems
-/

-- Sum of non-negative terms is positive if at least one term is positive
theorem sum_pos_of_mem {α : Type*} {s : Finset α} {f : α → ℝ}
    [DecidableEq α] (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
    Eq.symm (add_sum_erase s f ha_mem)
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (λ x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [h_sum_split]
  exact add_pos_of_pos_of_nonneg ha_pos h_erase_nonneg

-- Existence of positive element in positive sum
theorem exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h; push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := fun a ha => le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by rw [sum_eq_zero_iff_of_nonneg h_nonneg]; exact h_zero
  linarith

-- Multiplication positivity characterization
theorem mul_pos_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h_mul_pos
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · rintro rfl; simp_all only [le_refl, zero_mul, lt_self_iff_false]
    · rintro rfl; simp_all only [le_refl, mul_zero, lt_self_iff_false]
  · rintro ⟨ha_pos, hb_pos⟩; exact mul_pos ha_pos hb_pos

/-- The infimum over a non-empty finset is equal to the infimum over the corresponding subtype. -/
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]

/-- The standard simplex is a closed set. -/
lemma isClosed_stdSimplex' {n : Type*} [Fintype n] : IsClosed (stdSimplex ℝ n) := by
  have h₁ : IsClosed (⋂ i, {x : n → ℝ | 0 ≤ x i}) :=
    isClosed_iInter (fun i ↦ isClosed_le continuous_const (continuous_apply i))
  have h_set_eq : {x : n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by ext; simp
  rw [← h_set_eq] at h₁
  have h₂ : IsClosed {x : n → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finset_sum _ (fun i _ ↦ continuous_apply i)) continuous_const
  exact IsClosed.inter h₁ h₂

lemma abs_le_of_le_of_neg_le {x y : ℝ} (h_le : x ≤ y) (h_neg_le : -x ≤ y) : |x| ≤ y := by
  rw [abs_le]
  constructor
  · linarith
  · exact h_le

/-- A sum over a finset can be split into the value at a point `a`
and the sum over the rest of the finset. -/
lemma sum_add_sum_erase {n M : Type*} [AddCommMonoid M] [DecidableEq n] {s : Finset n} {f : n → M}
    (a : n) (ha : a ∈ s) :
    f a + ∑ i ∈ s.erase a, f i = ∑ i ∈ s, f i := by
  rw [add_sum_erase s f ha]

/-- A finset `s` is disjoint from its right complement. -/
@[simp]
lemma Finset.disjoint_compl_right {n : Type*} [Fintype n] [DecidableEq n] {s : Finset n} :
    Disjoint s (univ \ s) := by
  rw [@Finset.disjoint_iff_inter_eq_empty]
  rw [@inter_sdiff_self]

/-- The standard simplex is bounded. -/
lemma bounded_stdSimplex' {n : Type*} [Fintype n] [DecidableEq n] : Bornology.IsBounded (stdSimplex ℝ n) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use 1
  intro v hv
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  have h_le_one : v i ≤ 1 := by
    have h_sum_others_nonneg : 0 ≤ ∑ j ∈ univ.erase i, v j :=
      sum_nonneg fun j _ => hv.1 j
    have h_split : ∑ j ∈ univ, v j = v i + ∑ j ∈ univ.erase i, v j := by
      rw [add_sum_erase _ _ (mem_univ i)]
    linarith [hv.2, h_split, h_sum_others_nonneg]
  exact abs_le_of_le_of_neg_le h_le_one (by linarith [hv.1 i])

variable {n : Type*}

/-- For a vector on the standard simplex, if the sum of a subset of its components is 1,
    then the components outside that subset must be zero. -/
lemma mem_supp_of_sum_eq_one [Fintype n] [DecidableEq n] {v : n → ℝ} (hv : v ∈ stdSimplex ℝ n) (S : Finset n)
    (h_sum : ∑ i ∈ S, v i = 1) :
    ∀ i, v i ≠ 0 → i ∈ S := by
  intro i hi_ne_zero
  by_contra hi_not_in_S
  have h_sum_all : ∑ j, v j = 1 := hv.2
  have h_sum_split : ∑ j, v j = (∑ j ∈ S, v j) + (∑ j ∈ Sᶜ, v j) := by
    rw [Finset.sum_add_sum_compl S v]
  rw [← h_sum, h_sum_split] at h_sum_all
  have h_sum_compl_zero : ∑ j ∈ Sᶜ, v j = 0 := by linarith
  have h_nonneg : ∀ j ∈ Sᶜ, 0 ≤ v j := fun j _ ↦ hv.1 j
  have h_v_compl_zero : ∀ j ∈ Sᶜ, v j = 0 :=
    (sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_compl_zero
  specialize h_v_compl_zero i (mem_compl.mpr hi_not_in_S)
  exact hi_ne_zero h_v_compl_zero

/-- A non-negative, non-zero vector must have a positive component. -/
lemma exists_pos_of_ne_zero [Fintype n] [DecidableEq n] {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h_all_nonpos
  apply h_ne_zero
  ext i
  exact le_antisymm (by simp_all) (h_nonneg i)

/-- A set is nonempty if and only if its finite conversion is nonempty. -/
lemma Set.toFinset_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mpr hx⟩

/-- Division inequality: a / b ≤ c ↔ a ≤ c * b when b > 0. -/
lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb

/-- For real numbers, if `0 < b`, then `a ≤ c * b ↔ a / b ≤ c`. -/
lemma le_div_iff {a b c : ℝ} (hb : 0 < b) : a ≤ c * b ↔ a / b ≤ c := by
  rw [←div_le_iff hb]

/-- The ratio (A *ᵥ v) i / v i is nonnegative when A has nonnegative entries and v is nonnegative -/
lemma ratio_nonneg [Fintype n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (i : n) (hv_pos : 0 < v i) : 0 ≤ (A *ᵥ v) i / v i :=
  div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hA_nonneg i j) (hv_nonneg j)) hv_pos.le

lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f : α → ℝ} (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  have h_fb_pos : 0 < f b := h_pos b hb_mem
  rw [h_fb_is_inf]
  exact h_fb_pos

lemma lt_not_le {α : Type*} [PartialOrder α] (x y : α) : x < y → ¬ (x ≥ y) := by
  intro h_lt h_ge
  exact not_le_of_gt h_lt h_ge

section ConditionallyCompleteLinearOrder

variable {α : Type*}  [ConditionallyCompleteLinearOrder α]
/-- If y is an upper bound of a set s, and x is in s, then x ≤ y -/
lemma le_of_mem_upperBounds {s : Set α} {x : α} {y : α} (hy : y ∈ upperBounds s) (hx : x ∈ s) : x ≤ y := by
  exact hy hx

lemma bddAbove_iff_exists_upperBound {s : Set α} : BddAbove s ↔ ∃ b, ∀ x ∈ s, x ≤ b := by exact
  bddAbove_def

--lemma le_sSup_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ≤ sSup s := by
--  exact le_sSup_iff.mpr fun b a ↦ a hx

end ConditionallyCompleteLinearOrder

/--
The definition of the `i`-th component of a matrix-vector product.
This is standard in Mathlib and often available via `simp`.
-/
lemma mulVec_apply {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i : n) :
  (A *ᵥ v) i = ∑ j, A i j * v j :=
rfl

/--
An element of a set is less than or equal to the supremum of that set,
provided the set is non-empty and bounded above.
-/
lemma le_sSup_of_mem {s : Set ℝ} (_ : s.Nonempty) (hs_bdd : BddAbove s) {y : ℝ} (hy : y ∈ s) :
  y ≤ sSup s :=
le_csSup hs_bdd hy

/-- A sum of non-negative terms is strictly positive if and only if the sum is not zero.
    This is a direct consequence of the sum being non-negative. -/
lemma sum_pos_of_nonneg_of_ne_zero {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (h_ne_zero : ∑ x ∈ s, f x ≠ 0) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_nonneg : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg h_nonneg
  exact lt_of_le_of_ne h_sum_nonneg h_ne_zero.symm

-- Missing lemma: bound each component by the supremum
lemma le_sup'_of_mem {α β : Type*} [SemilatticeSup α] {s : Finset β} (hs : s.Nonempty)
    (f : β → α) {b : β} (hb : b ∈ s) : f b ≤ s.sup' hs f := by
  exact le_sup' f hb

-- Missing lemma: supremum is at least any component
lemma sup'_le_sup'_of_le {α β : Type*} [SemilatticeSup α] {s t : Finset β}
    (hs : s.Nonempty) (ht : t.Nonempty) (f : β → α) (h : s ⊆ t) :
    s.sup' hs f ≤ t.sup' ht f := by
  exact sup'_mono f h hs

-- A non-zero function must be non-zero at some point.
lemma Function.exists_ne_zero_of_ne_zero {α β} [Zero β] {f : α → β} (h : f ≠ (fun _ => 0)) : ∃ i, f i ≠ 0 := by
  by_contra hf
  push_neg at hf
  apply h
  ext x
  exact hf x

/-- If the ratio (A *ᵥ v) i / v i = 0 and v i > 0, then (A *ᵥ v) i = 0. -/
lemma mulVec_eq_zero_of_ratio_zero [Fintype n] (A : Matrix n n ℝ) {v : n → ℝ} (i : n) (hv_pos : 0 < v i)
    (h_ratio_zero : (A *ᵥ v) i / v i = 0) :
    (A *ᵥ v) i = 0 := by
  rw [div_eq_zero_iff] at h_ratio_zero
  exact h_ratio_zero.resolve_right (ne_of_gt hv_pos)

lemma mul_vec_mul_vec
  {n : Type*} [Fintype n] [Nonempty n] (A B : Matrix n n ℝ) (v : n → ℝ) :
  (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := by
  ext i
  simp only [mulVec, dotProduct, mul_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- If `A *ᵥ v` is zero on the support `S` of `v`, then for any `i ∈ S`, `A i k` must be zero
for all `k` where `v` is positive (i.e., `k ∈ S`). -/
lemma zero_block_of_mulVec_eq_zero [Fintype n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (S : Set n) (hS_def : S = {i | 0 < v i})
    (h_Av_zero : ∀ i ∈ S, (A *ᵥ v) i = 0) :
    ∀ i ∈ S, ∀ k ∈ S, A i k = 0 := by
  intro i hi_S k hk_S
  have h_sum_Aiv_eq_zero : (A *ᵥ v) i = 0 := h_Av_zero i hi_S
  rw [mulVec, dotProduct] at h_sum_Aiv_eq_zero
  have h_sum_terms_nonneg : ∀ l, 0 ≤ A i l * v l :=
    fun l ↦ mul_nonneg (hA_nonneg i l) (hv_nonneg l)
  have h_Aik_vk_zero : A i k * v k = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun l _ ↦ h_sum_terms_nonneg l)).mp h_sum_Aiv_eq_zero k (mem_univ k)
  rw [hS_def] at hk_S
  exact (mul_eq_zero.mp h_Aik_vk_zero).resolve_right (ne_of_gt hk_S)

/-- For any natural number `n > 0`, it is either equal to 1 or greater than 1.
    This is a helper for reasoning about the cardinality of a Fintype. -/
lemma Nat.eq_one_or_one_lt (n : ℕ) (hn : n ≠ 0) : n = 1 ∨ 1 < n := by
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr (Nat.succ_lt_succ (Nat.succ_pos _))

/-- For a finite type, the infimum over the type is attained at some element. -/
lemma exists_eq_iInf {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : ∃ i, f i = ⨅ j, f j :=
  exists_eq_ciInf_of_finite

/-- Functions computing pointwise infima are equal when using `iInf` vs `Finset.inf'`. -/
lemma Finset.iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*}
    [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder γ]
    (f : α → β → γ) :
    (fun x ↦ ⨅ i, f i x) = (fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)) := by
  ext x
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by
    simp only [Set.mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr
    ext i
    simp only [Set.mem_univ, ciInf_unique, mem_univ]
  have h3 : ⨅ i ∈ (Finset.univ : Finset α), f i x =
           (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [mem_univ, ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
    rfl
  rw [h1, h2, h3]

/-- For a finite index type, the point-wise (finite) infimum of a family of
    continuous functions is continuous. -/
lemma continuousOn_iInf' {α β : Type*}
    [Fintype α] [Nonempty α]
    [TopologicalSpace β]
    {s : Set β} {f : α → β → ℝ}
    (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x ↦ ⨅ i, f i x) s := by
  classical
  let g : β → ℝ :=
    fun x ↦ (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i ↦ f i x)
  have hg : ContinuousOn g s := by
    exact ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i a ↦ hf i
  have h_eq : (fun x ↦ ⨅ i, f i x) = g := by
    dsimp [g]
    exact Finset.iInf_apply_eq_finset_inf'_apply_fun f
  rwa [h_eq]

/-- An element of the image of a set is less than or equal to the supremum of that set. -/
lemma le_csSup_of_mem {α : Type*} {f : α → ℝ} {s : Set α} (hs_bdd : BddAbove (f '' s)) {y : α} (hy : y ∈ s) :
  f y ≤ sSup (f '' s) :=
le_csSup hs_bdd (Set.mem_image_of_mem f hy)

lemma div_lt_iff {a b c : ℝ} (hc : 0 < c) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le (by exact le_div_iff₀ hc)


--lemma lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
--  lt_iff_lt_of_le_iff_le (div_le_iff hc)

lemma smul_sum (α : Type*) [Fintype α] (r : ℝ) (f : α → ℝ) :
    r • (∑ i, f i) = ∑ i, r • f i := by
  simp only [smul_eq_mul, Finset.mul_sum]

lemma ones_norm_mem_simplex [Fintype n] [Nonempty n] :
  (fun _ => (Fintype.card n : ℝ)⁻¹) ∈ stdSimplex ℝ n := by
  dsimp [stdSimplex]; constructor
  · intro i; apply inv_nonneg.2; norm_cast; exact Nat.cast_nonneg _
  · simp [Finset.sum_const, Finset.card_univ];

/--
If a value `y` is a lower bound for a function `f` over a non-empty finset `s` and is
also attained by `f` for some element in `s`, then `y` is the infimum of `f` over `s`.
-/
lemma Finset.inf'_eq_of_forall_le_of_exists_le {α β} [LinearOrder β]
    {s : Finset α} (hs : s.Nonempty) (f : α → β) (y : β)
    (h_le : ∀ i ∈ s, y ≤ f i) (h_exists : ∃ i ∈ s, f i = y) :
    s.inf' hs f = y := by
  apply le_antisymm
  · obtain ⟨i, hi_mem, hi_eq⟩ := h_exists
    rw [← hi_eq]
    exact inf'_le f hi_mem
  · exact (le_inf'_iff hs f).mpr h_le

/--
If a vector `x` lies in the standard simplex, then it cannot be the zero vector.
Indeed, the coordinates of a simplex‐vector sum to `1`, whereas the coordinates of
the zero vector sum to `0`.
-/
lemma ne_zero_of_mem_stdSimplex
    {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) :
    x ≠ 0 := by
  intro h_zero
  have h_sum_zero : (∑ i, x i) = 0 := by
    subst h_zero
    simp_all only [Pi.zero_apply, Finset.sum_const_zero]
  have h_sum_one : (∑ i, x i) = 1 := hx.2
  linarith

lemma Real.le_sSup {s : Set ℝ} {y : ℝ} (h_mem : y ∈ s) (h_bdd : BddAbove s) :
    y ≤ sSup s :=
  le_csSup h_bdd h_mem

/-- The supremum of the image of `s` under `f` equals the indexed supremum over the subtype. -/
lemma csSup_image' {α β : Type*} [ConditionallyCompleteLattice α]
  {f : β → α} {s : Set β} (hs : s.Nonempty) (hb : BddAbove (f '' s)) :
  sSup (f '' s) = ⨆ i : s, f i := by
  have h₁ : IsLUB (f '' s) (sSup (f '' s)) := isLUB_csSup (hs.image _) hb
  have h₂ := isLUB_ciSup_set (f := f) (s := s) hb hs
  exact h₁.unique h₂

lemma iSup_eq_sSup {α β : Type*} [ConditionallyCompleteLattice α]
    (f : β → α) (s : Set β) :
    (⨆ i : s, f i) = sSup (f '' s) := by
  classical
  -- `sSup_image'` gives `sSup (f '' s) = ⨆ i : s, f i`
  simpa using (sSup_image' (f := f) (s := s)).symm

namespace Matrix

/-- The dot product of two strictly positive vectors is positive. -/
lemma dotProduct_pos_of_pos_of_pos {n : Type*} [Fintype n] [Nonempty n]
    {u v : n → ℝ} (hu_pos : ∀ i, 0 < u i) (hv_pos : ∀ i, 0 < v i) :
    0 < u ⬝ᵥ v := by
  simp [dotProduct]
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hu_pos i) (hv_pos i)
  · apply Finset.univ_nonempty

/-- The dot product of a positive vector with a non-negative, non-zero vector is positive. -/
lemma dotProduct_pos_of_pos_of_nonneg_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    {u v : n → ℝ} (hu_pos : ∀ i, 0 < u i) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    0 < u ⬝ᵥ v := by
  simp [dotProduct]
  have h_exists_pos : ∃ i, 0 < v i := by
    by_contra h
    push_neg at h
    have h_all_zero : ∀ i, v i = 0 := fun i =>
      le_antisymm (h i) (hv_nonneg i)
    have h_zero : v = 0 := funext h_all_zero
    contradiction
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ u i * v i :=
    fun i _ => mul_nonneg (le_of_lt (hu_pos i)) (hv_nonneg i)
  rcases h_exists_pos with ⟨i, hi⟩
  have hi_mem : i ∈ Finset.univ := Finset.mem_univ i
  have h_pos : 0 < u i * v i := mul_pos (hu_pos i) hi
  exact sum_pos_of_mem h_nonneg i hi_mem h_pos

/-- Dot‐product is linear in the first argument. -/
lemma dotProduct_smul_left {n : Type*} [Fintype n]
    (c : ℝ) (v w : n → ℝ) :
    (c • v) ⬝ᵥ w = c * (v ⬝ᵥ w) := by
  unfold dotProduct
  simp [smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

/-- The dot product is linear in the right argument. -/
lemma dotProduct_smul_right {n : Type*} [Fintype n]
    (c : ℝ) (v w : n → ℝ) :
    v ⬝ᵥ (c • w) = c * (v ⬝ᵥ w) := by
  simp [dotProduct, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/--
If `u` is a non-negative vector and `v ≤ w` component-wise, then `u ⬝ᵥ v ≤ u ⬝ᵥ w`.
This is because the dot product is a sum of products, and multiplying by non-negative
numbers preserves the inequality.
-/
lemma dotProduct_le_dotProduct_of_nonneg {n : Type*} [Fintype n] {u v w : n → ℝ}
    (hu_nonneg : ∀ i, 0 ≤ u i) (h_le : v ≤ w) :
    u ⬝ᵥ v ≤ u ⬝ᵥ w := by
  simp_rw [dotProduct, Pi.le_def] at h_le ⊢
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h_le i) (hu_nonneg i)

/--
The dot product is "associative" with matrix-vector multiplication, in the sense
that `v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w`. This is a consequence of the definition of
the matrix transpose and dot product.
-/
lemma dotProduct_mulVec_assoc {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v w : n → ℝ) :
    v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w := by
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

-- Matrix-vector multiplication component
theorem matrix_mulVec_component {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (j : n) :
    (A *ᵥ v) j = ∑ i, A j i * v i := by
  simp [Matrix.mulVec]; rfl

/--
The dot product `v ⬝ᵥ (A *ᵥ w)` can be rewritten by moving the matrix `A`
to the other argument, where it becomes its transpose `Aᵀ`.
-/
lemma transpose_mulVec {n : Type*} [Fintype n] (A : Matrix n n ℝ) (v w : n → ℝ) :
    v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w := by
  classical
  simp only [dotProduct, mulVec_apply, transpose_apply,
        Finset.mul_sum, Finset.sum_mul];
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

/--
Commutativity property for dot product with matrix-vector multiplication.
For vectors `u`, `v` and matrix `A`: `u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v`.
This follows from the fact that `u ⬝ᵥ (A *ᵥ v) = u ᵥ* A ⬝ᵥ v = (Aᵀ *ᵥ u) ⬝ᵥ v`.
-/
lemma dotProduct_mulVec_comm {n : Type*} [Fintype n] (u v : n → ℝ) (A : Matrix n n ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_eq_mulVec_transpose]

-- This could be a general lemma in the Matrix API
lemma diagonal_mulVec_ones [DecidableEq n][Fintype n] (d : n → ℝ) :
    diagonal d *ᵥ (fun _ => 1) = d := by
  ext i; simp [mulVec_diagonal]

-- This could also be a general lemma
lemma diagonal_inv_mulVec_self [DecidableEq n][Fintype n] {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal (d⁻¹) *ᵥ d = fun _ => 1 := by
  ext i
  simp [mulVec_diagonal]
  simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]

lemma diagonal_mulVec_diagonal_inv_mulVec [DecidableEq n] [Fintype n]
    {d x : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal d *ᵥ (diagonal (d⁻¹) *ᵥ x) = x := by
  ext i
  simp [mulVec_diagonal, hd i]

lemma diagonal_mulVec_mono [DecidableEq n] [Fintype n] {d x y : n → ℝ}
    (hd_nonneg : ∀ i, 0 ≤ d i) (hxy : x ≤ y) :
    diagonal d *ᵥ x ≤ diagonal d *ᵥ y := by
  intro i
  rw [mulVec_diagonal, mulVec_diagonal]
  exact mul_le_mul_of_nonneg_left (hxy i) (hd_nonneg i)

end Matrix

variable {α ι : Type*} {f : ι → α} {s : Set ι}
open Set
-- Indexed supremum equals the supremum of the image
theorem iSup_eq_sSup_image [ConditionallyCompleteLattice α] :
    (⨆ x : s, f x) = sSup (f '' s) := by
  simp [iSup, image_eq_range]

lemma eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι]
  (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ j, f j = 0) (i : ι) : f i = 0 := by
  by_contra hne0
  have hne : ¬ 0 = f i := mt Eq.symm hne0
  have hgt : 0 < f i := lt_iff_le_and_ne.mpr ⟨hf i, hne⟩
  have hsum_pos : 0 < ∑ j, f j :=
    Finset.sum_pos' (fun j _ => hf j) ⟨i, Finset.mem_univ i, hgt⟩
  simpa [hsum] using ne_of_gt hsum_pos
