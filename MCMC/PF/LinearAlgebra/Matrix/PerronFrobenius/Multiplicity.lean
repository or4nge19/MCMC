import Mathlib.Order.CompletePartialOrder
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Dominance

namespace Matrix
open Finset CollatzWielandt LinearMap

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}

omit [Nonempty n] [DecidableEq n] in
/-- A real eigenvector for the Perron root gives a subinvariant inequality for its absolute values. -/
lemma perronRoot_smul_abs_le_mulVec_abs_of_eigenvector
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hr_pos : 0 < perronRoot A)
    {w : n → ℝ} (hw_eig : A *ᵥ w = perronRoot A • w) :
    perronRoot A • (fun i => |w i|) ≤ A *ᵥ (fun i => |w i|) := by
  intro i
  calc
    (perronRoot A • fun i => |w i|) i = perronRoot A * |w i| := by simp
    _ = |perronRoot A * w i| := by rw [abs_mul, abs_of_pos hr_pos]
    _ = |(A *ᵥ w) i| := by rw [hw_eig]; simp
    _ = |∑ j, A i j * w j| := by simp [mulVec_apply]
    _ ≤ ∑ j, |A i j * w j| := by
      simpa using Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset n))
        (f := fun j => A i j * w j)
    _ = ∑ j, A i j * |w j| := by
      simp_rw [abs_mul, abs_of_nonneg (hA_nonneg i _)]
    _ = (A *ᵥ (fun i => |w i|)) i := by simp [mulVec_apply]

/-- For an irreducible matrix, absolute values of a nonzero Perron eigenvector are positive
and still form a Perron eigenvector. -/
lemma abs_perron_eigenvector_eq_and_pos_of_irreducible
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hr_pos : 0 < perronRoot A) {w : n → ℝ}
    (hw_eig : A *ᵥ w = perronRoot A • w) (hw_ne_zero : w ≠ 0) :
    A *ᵥ (fun i => |w i|) = perronRoot A • (fun i => |w i|) ∧
      ∀ i, 0 < |w i| := by
  have hw_abs_nonneg : ∀ i, 0 ≤ |w i| := fun _ => abs_nonneg _
  have hw_abs_ne_zero : (fun i => |w i|) ≠ 0 := by
    contrapose! hw_ne_zero
    ext i
    exact abs_eq_zero.mp (congr_fun hw_ne_zero i)
  have hw_abs_eig :=
    subinvariant_equality_implies_eigenvector hA_irred hA_nonneg
      hw_abs_nonneg hw_abs_ne_zero
      (perronRoot_smul_abs_le_mulVec_abs_of_eigenvector hA_nonneg hr_pos hw_eig)
  exact ⟨hw_abs_eig,
    eigenvector_is_positive_of_irreducible hA_irred hw_abs_eig hw_abs_nonneg hw_abs_ne_zero⟩

omit [Fintype n] [Nonempty n] [DecidableEq n] in
/-- A real vector whose complexification has a global phase is a real scalar multiple
of its vector of absolute values. -/
lemma real_eq_re_smul_abs_of_complex_phase
    {w : n → ℝ} {c : ℂ}
    (h_phase : (fun i => (w i : ℂ)) = fun i => c * ‖(w i : ℂ)‖) :
    w = c.re • fun i => |w i| := by
  ext j
  have h := congrArg Complex.re (congr_fun h_phase j)
  have : w j = c.re * ‖(w j : ℂ)‖ := by
    simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h
  simpa [Pi.smul_apply, Complex.norm_ofReal, smul_eq_mul] using this

/-- Every nonzero Perron eigenvector lies in the line spanned by a fixed positive Perron eigenvector. -/
lemma perron_eigenvector_mem_span_of_positive_eigenvector
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hr_pos : 0 < perronRoot A) {v w : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hv_eig : A *ᵥ v = perronRoot A • v)
    (hw_eig : A *ᵥ w = perronRoot A • w) (hw_ne_zero : w ≠ 0) :
    w ∈ Submodule.span ℝ {v} := by
  let w_abs := fun i => |w i|
  obtain ⟨hw_abs_eig, hw_abs_pos⟩ :=
    abs_perron_eigenvector_eq_and_pos_of_irreducible hA_irred hA_nonneg hr_pos hw_eig hw_ne_zero
  obtain ⟨c_abs, _, hc_abs_eq⟩ :=
    uniqueness_of_positive_eigenvector_gen hA_irred hr_pos hw_abs_pos hv_pos hw_abs_eig hv_eig
  let B := 1 + A
  let rB := perronRoot A + 1
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => Matrix.one_add_apply_nonneg hA_nonneg i j
  have hB_irred := Matrix.Irreducible.add_one (A := A) hA_irred
  have hB_prim : IsPrimitive B := by simpa [B] using one_add_isPrimitive_of_irreducible hA_irred
  have hBw_eig : toLin' B w = rB • w := by
    have hw_eig_lin : toLin' A w = perronRoot A • w := by simpa [toLin'_apply] using hw_eig
    simpa [B, rB] using toLin'_one_add_eigenvector hw_eig_lin
  have hw_abs_eig_B : toLin' B w_abs = rB • w_abs := by
    have hw_abs_eig_lin : toLin' A w_abs = perronRoot A • w_abs := by
      simpa [toLin'_apply, w_abs] using hw_abs_eig
    simpa [B, rB] using toLin'_one_add_eigenvector hw_abs_eig_lin
  let wc : n → ℂ := fun i => (w i : ℂ)
  have hwc_eig_B : (B.map (algebraMap ℝ ℂ)) *ᵥ wc = (rB : ℂ) • wc := by
    simpa [wc] using mulVec_map_complex_of_real_eigenvector hBw_eig
  have hrB_eq_perronB : rB = perronRoot B :=
    eigenvalue_is_perron_root_of_positive_eigenvector hB_irred hB_nonneg (by linarith)
      (show ∀ i, 0 < w_abs i from hw_abs_pos) (by simpa [toLin'_apply] using hw_abs_eig_B)
  have h_norm_eig : (B *ᵥ fun i => ‖wc i‖) = perronRoot B • (fun i => ‖wc i‖) := by
    simpa [toLin'_apply, hrB_eq_perronB, wc, w_abs, Complex.norm_ofReal] using hw_abs_eig_B
  obtain ⟨c, _, hc_eq⟩ := eigenvector_phase_aligned_of_primitive hB_prim hB_nonneg
    (by simpa [hrB_eq_perronB] using perronRoot_nonneg hB_nonneg) hwc_eig_B h_norm_eig
    (by
      intro i
      simpa [wc, w_abs, Complex.norm_ofReal] using hw_abs_pos i)
  have hw_eq : w = c.re • w_abs := by
    simpa [w_abs] using real_eq_re_smul_abs_of_complex_phase (by simpa [wc] using hc_eq)
  have hc_abs_eq_wabs : w_abs = c_abs • v := by simpa [w_abs] using hc_abs_eq
  rw [hw_eq, hc_abs_eq_wabs, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨c.re * c_abs, rfl⟩

/--
Helper lemma: If ker(f^2) = ker(f), then ker(f^k) = ker(f) for all k ≥ 1.
This shows that the ascent of the kernel stabilizes at 1.
-/
lemma LinearMap.ker_pow_eq_ker_of_ker_sq_eq_ker
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : M →ₗ[R] M) (h_stable : LinearMap.ker (f^2) = LinearMap.ker f) :
    ∀ k ≥ 1, LinearMap.ker (f^k) = LinearMap.ker f := by
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  induction' m with m ih
  · simp [pow_one]
  · apply le_antisymm
    · intro x hx
      have hx' : (f ^ (m + 1)) (f x) = 0 := by
        simp_all only [Nat.succ_eq_add_one, ge_iff_le, le_add_iff_nonneg_left, le_refl, List.Nat.eq_of_le_zero,
          zero_le, forall_const, LinearMap.mem_ker]
        exact hx
      have : f x ∈ LinearMap.ker (f ^ (m + 1)) := by
        simpa [LinearMap.mem_ker] using hx'
      have : f x ∈ LinearMap.ker f := by simpa [ih] using this
      rw [← h_stable]
      simpa [LinearMap.mem_ker] using this
    · intro x hx
      have : (f ^ (m + 1)) (f x) = 0 := by simp_all
      simpa [pow_succ] using this
/--
The geometric multiplicity of the Perron root of an irreducible non-negative matrix is 1.
The eigenspace is spanned by the unique positive eigenvector.
-/
lemma geometric_multiplicity_one_of_irreducible
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot A
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ Module.End.eigenspace (toLin' A) r = Submodule.span ℝ {v} := by
  let r := perronRoot A
  let f := toLin' A
  obtain ⟨r_ex, v, hr_pos, hv_pos, hv_eig_mat, hr_eq_r⟩ := perron_root_eq_positive_eigenvalue hA_irred hA_nonneg
  rw [← hr_eq_r] at hv_eig_mat hr_pos
  have hv_eig_f : f v = r • v := by rwa [toLin'_apply]
  use v, hv_pos
  apply Submodule.ext
  intro w
  constructor
  · intro hw_E_r
    have hw_eig : f w = r • w := by
      simpa [f, r] using (Module.End.mem_eigenspace_iff.mp (by assumption))
    by_cases hw_zero : w = 0
    · subst hw_zero
      exact Submodule.zero_mem _
    · have hAw_eig : A *ᵥ w = perronRoot A • w := by
        simpa [f, r, toLin'_apply] using hw_eig
      exact perron_eigenvector_mem_span_of_positive_eigenvector
        hA_irred hA_nonneg hr_pos hv_pos hv_eig_mat hAw_eig hw_zero
  · intro hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    have hc : f (c • v) = r • (c • v) := by
      calc
        f (c • v) = c • f v := by simp
        _ = c • (r • v) := by simp [hv_eig_f]
        _ = (c * r) • v := by simp [smul_smul]
        _ = (r * c) • v := by simp [mul_comm]
        _ = r • (c • v) := by simp [smul_smul]
    have : (toLin' A) (c • v) = (perronRoot A) • (c • v) := by
      simpa [f, r]
        using hc
    exact (Module.End.mem_eigenspace_iff).2 this

open scoped Matrix InnerProductSpace

/-- An irreducible nonnegative matrix has a strictly positive left Perron eigenvector. -/
lemma exists_positive_left_perron_eigenvector
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃ u : n → ℝ, (∀ i, 0 < u i) ∧ toLin' Aᵀ u = perronRoot A • u := by
  have hAT_irred := Matrix.IsIrreducible.transpose hA_irred
  obtain ⟨rT, u, hrT_pos, hu_pos, hu_eig_T_mat⟩ :=
    exists_positive_eigenvector_of_irreducible hAT_irred
  have hrT_eq_r : rT = perronRoot A := by
    calc
      rT = perronRoot Aᵀ :=
        eigenvalue_is_perron_root_of_positive_eigenvector
          hAT_irred (fun i j => hA_nonneg j i) hrT_pos hu_pos hu_eig_T_mat
      _ = perronRoot A := (perronRoot_transpose_eq A hA_irred).symm
  exact ⟨u, hu_pos, by simpa [hrT_eq_r, toLin'_apply] using hu_eig_T_mat⟩

omit [Nonempty n] in
/-- A left `r`-eigenvector annihilates the image of `A - rI` under the dot product. -/
lemma dotProduct_sub_perron_id_apply_eq_zero
    {r : ℝ} {u w : n → ℝ} (hu : toLin' Aᵀ u = r • u) :
    u ⬝ᵥ ((toLin' A - r • (LinearMap.id : (n → ℝ) →ₗ[ℝ] n → ℝ)) w) = 0 := by
  let f := toLin' A
  change u ⬝ᵥ (f w - r • w) = 0
  calc
    u ⬝ᵥ (f w - r • w) = u ⬝ᵥ (f w) - u ⬝ᵥ (r • w) := by
      simp [dotProduct_sub]
    _ = (toLin' Aᵀ u) ⬝ᵥ w - r * (u ⬝ᵥ w) := by
      have h₁ : u ⬝ᵥ (f w) = (toLin' Aᵀ u) ⬝ᵥ w := by
        simpa [f, toLin'_apply] using dotProduct_mulVec_comm u w A
      simp [h₁, dotProduct_smul, smul_eq_mul]
    _ = 0 := by simp [hu, smul_eq_mul]

/-- For an irreducible nonnegative matrix, the kernel of `(A - rI)^2` is already
the Perron eigenspace. -/
lemma ker_sq_le_ker_sub_perron
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    LinearMap.ker ((toLin' A - perronRoot A • LinearMap.id) ^ 2) ≤
      LinearMap.ker (toLin' A - perronRoot A • LinearMap.id) := by
  let r := perronRoot A
  let f := toLin' A
  let g := f - r • LinearMap.id
  change LinearMap.ker (g ^ 2) ≤ LinearMap.ker g
  intro w hw_g2
  let u := g w
  have hu_g : g u = 0 := by simpa [u, pow_two, LinearMap.comp_apply] using hw_g2
  have hu_eig : f u = r • u := by
    simpa [g, LinearMap.sub_apply, sub_eq_zero] using hu_g
  obtain ⟨u_star, hu_star_pos, hu_star_eig⟩ :=
    exists_positive_left_perron_eigenvector hA_irred hA_nonneg
  have h_dot_u : u_star ⬝ᵥ u = 0 := by
    simpa [u, g, f, r] using dotProduct_sub_perron_id_apply_eq_zero (A := A) hu_star_eig (w := w)
  obtain ⟨v, hv_pos, h_Er_span⟩ :=
    geometric_multiplicity_one_of_irreducible (A := A) hA_irred hA_nonneg
  have hu_in_Er : u ∈ Module.End.eigenspace f r := by
    simpa [Module.End.mem_eigenspace_iff, f, r] using hu_eig
  obtain ⟨c, hc_eq⟩ := Submodule.mem_span_singleton.mp (by
    simpa [h_Er_span, r, f] using hu_in_Er)
  have hc_zero_or_dot_zero : c = 0 ∨ u_star ⬝ᵥ v = 0 := by
    have hdot_smul : u_star ⬝ᵥ (c • v) = 0 := by
      simpa [hc_eq] using h_dot_u
    have : c * (u_star ⬝ᵥ v) = 0 := by
      simpa [dotProduct_smul, smul_eq_mul, mul_comm] using hdot_smul
    exact mul_eq_zero.mp this
  have h_dot_pos : 0 < u_star ⬝ᵥ v :=
    dotProduct_pos_of_pos_of_nonneg_ne_zero hu_star_pos (fun i => (hv_pos i).le)
      (Pi.ne_zero_of_pos hv_pos)
  have hu_zero : u = 0 := by
    simpa [hc_zero_or_dot_zero.resolve_right h_dot_pos.ne', zero_smul] using hc_eq.symm
  simpa [LinearMap.mem_ker, u] using hu_zero

/--
The algebraic multiplicity of the Perron root of an irreducible non-negative matrix is 1.
The generalized eigenspace equals the eigenspace.
-/
lemma algebraic_multiplicity_one_of_irreducible
    (hA_irred : A.IsIrreducible) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    Module.End.maxGenEigenspace (toLin' A) (perronRoot A) =
    Module.End.eigenspace (toLin' A) (perronRoot A) := by
  let r := perronRoot A
  let f := toLin' A
  let g := f - r • LinearMap.id
  have h_ker_sq_eq_ker : LinearMap.ker (g ^ 2) = LinearMap.ker g := by
    apply le_antisymm
    · simpa [g, f, r] using ker_sq_le_ker_sub_perron (A := A) hA_irred hA_nonneg
    · intro x hx
      have hx0 : g x = 0 := by simpa [LinearMap.mem_ker] using hx
      have : (g ^ 2) x = 0 := by
        simp [pow_two, hx0]
      simpa [LinearMap.mem_ker] using this
  haveI : FiniteDimensional ℝ (n → ℝ) := by infer_instance
  have h_stabilize := LinearMap.ker_pow_eq_ker_of_ker_sq_eq_ker g h_ker_sq_eq_ker
  have h_sup_eq : ⨆ (k : ℕ), LinearMap.ker (g ^ k) = LinearMap.ker g := by
    apply le_antisymm
    · apply iSup_le
      intro k
      cases k with
      | zero =>
        intro x hx
        have hx0 : x = 0 := by
          simpa [pow_zero, LinearMap.mem_ker] using hx
        simp [hx0]
      | succ k' =>
        have hk' : 1 ≤ k'.succ := Nat.succ_le_succ (Nat.zero_le _)
        simp [h_stabilize k'.succ hk']
    · exact le_iSup_of_le 1 (by simp [pow_one])
  calc
    Module.End.maxGenEigenspace f r
      = ⨆ k, LinearMap.ker (g ^ k) := by
        simp [Module.End.maxGenEigenspace, Module.End.genEigenspace, g]; rfl
    _ = LinearMap.ker g := h_sup_eq
    _ = Module.End.eigenspace f r := by
        simp [Module.End.eigenspace, g]; rw [@Module.End.genEigenspace_one]; rfl

end Matrix
