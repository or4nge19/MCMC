import MCMC.Finite.TotalVariation
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

set_option linter.unusedSectionVars false

namespace MCMC.Finite
open Matrix Finset Filter Topology
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Convergence Theorems -/

/-! #### The limit matrix -/

/--
  The limit matrix Π. A rank-1 matrix where every row equals the stationary distribution π.
  Πᵢⱼ = πⱼ.
-/
def LimitMatrix (π : stdSimplex ℝ n) : Matrix n n ℝ :=
  fun _ j => π.val j

omit [DecidableEq n] in
lemma LimitMatrix_is_stochastic (π : stdSimplex ℝ n) : IsStochastic (LimitMatrix π) := by
  constructor
  · intro i j; exact π.property.1 j
  · intro i; simp [LimitMatrix, π.property.2]

omit [DecidableEq n] in
/--  P * Π = Π and Π * P = Π. The limit matrix is absorbing. -/
theorem LimitMatrix_absorbing (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (h_stoch : IsStochastic P) (h_stat : IsStationary P π) :
  P * LimitMatrix π = LimitMatrix π ∧ LimitMatrix π * P = LimitMatrix π := by
  constructor
  · -- P * Π = Π (Relies on P being stochastic).
    ext i j
    simp only [LimitMatrix, mul_apply]
    calc
      ∑ k, P i k * π.val j
        = (∑ k, P i k) * π.val j := by rw [Finset.sum_mul]
      _ = π.val j := by rw [h_stoch.2 i, one_mul]
  · -- Π * P = Π (Relies on π being stationary).
    ext i j
    simp only [LimitMatrix, mul_apply]
    have h_stat_j := congrArg (fun v => v j) h_stat
    simp [mulVec, transpose_apply] at h_stat_j
    simpa [mul_comm] using h_stat_j

/-! #### Convergence to Equilibrium (Matrix Convergence) -/

/-
  Primitivity implies a spectral gap (1 is a simple eigenvalue, others < 1 in magnitude).
  This spectral gap guarantees geometric convergence of P^k.
  We encode a spectral gap by uniform exponential entrywise convergence of P^k to the rank-1
  limit matrix built from a stationary distribution π, with some rate r ∈ [0,1).
-/
/-def HasSpectralGap' (P : Matrix n n ℝ) : Prop :=
  ∃ (π : stdSimplex ℝ n) (r : ℝ),
    IsStationary P π ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ i j k, |(P^k) i j - (LimitMatrix π) i j| ≤ r^k-/

/--
  Spectral gap encoded by: there exist π, r ∈ [0,1), and a positive block length k0,
  s.t. the entrywise error is bounded by r^(k / k0) for all k.
  This form still implies convergence, and is what we can prove from Dobrushin’s coefficient
  and primitivity (a positive power strictly contracts TV).
-/
def HasSpectralGap (P : Matrix n n ℝ) : Prop :=
  ∃ (π : stdSimplex ℝ n) (r : ℝ) (k0 : ℕ),
    IsStationary P π ∧ 0 < k0 ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ i j k, |(P^k) i j - (LimitMatrix π) i j| ≤ r^(k / k0)

lemma IsPrimitive.irreducible [Nonempty n] {P : Matrix n n ℝ}
    (_ : IsStochastic P) (h_prim : IsPrimitive P) :
    Matrix.IsIrreducible P := by
  exact IsPrimitive.isIrreducible h_prim

lemma pow_stationary_mulVec [Nonempty n] (P : Matrix n n ℝ) (k : ℕ)
    (_ : IsStochastic P) (π : stdSimplex ℝ n) (h_stat : IsStationary P π) :
    (P^k)ᵀ *ᵥ π.val = π.val := by
  induction' k with k ih
  · simp [pow_zero]
  ·
    have ih' : (Pᵀ ^ k) *ᵥ π.val = π.val := by
      simpa [Matrix.transpose_pow] using ih
    calc
      (P ^ (k + 1))ᵀ *ᵥ π.val
          = (Pᵀ * (Pᵀ ^ k)) *ᵥ π.val := by
              simp [pow_succ, Matrix.transpose_mul, Matrix.transpose_pow]
      _ = Pᵀ *ᵥ ((Pᵀ ^ k) *ᵥ π.val) := by
              simp_rw [← Matrix.mulVec_mulVec]
      _ = Pᵀ *ᵥ π.val := by
              simp [ih']
      _ = π.val := by
              simpa [IsStationary] using h_stat

/-- Point mass at i as a row-distribution. -/
private def delta (i : n) : n → ℝ := fun t => if t = i then (1 : ℝ) else 0

private lemma delta_sum_one (i : n) : ∑ t, delta i t = 1 := by
  classical
  simp [delta, Finset.mem_univ]

private lemma delta_nonneg (i : n) : ∀ t, 0 ≤ delta i t := by
  intro t; classical
   by_cases h : t = i <;> simp [delta, h]

/-- Primitivity ⇒ some power has a strict Dobrushin contraction;
    from this we build a spectral gap. -/
lemma IsPrimitive.has_spectral_gap [Nonempty n] {P : Matrix n n ℝ}
    (h_stoch : IsStochastic P) (h_prim : IsPrimitive P) : HasSpectralGap P := by
  classical
  have h_irred : Matrix.IsIrreducible P := IsPrimitive.irreducible h_stoch h_prim
  obtain ⟨π, hπ_stat, _hπ_unique⟩ :=
    exists_unique_stationary_distribution_of_irreducible h_stoch h_irred
  obtain ⟨k0, hk0_pos, hδ_lt⟩ :=
    Matrix.dobrushinCoeff_lt_one_of_primitive (P := P) h_stoch h_prim
  let r := Matrix.dobrushinCoeff (P^k0)
  have hr_lt_one : r < 1 := hδ_lt
  have hr0 : 0 ≤ r := Matrix.dobrushinCoeff_nonneg (P := P^k0)
  refine ⟨π, r, k0, hπ_stat, hk0_pos, hr0, hr_lt_one, ?_⟩
  intro i j k
  set q := k / k0 with hq
  set s := k % k0 with hs
  have hk_decomp : k = q * k0 + s := by
    rw [hq, hs]; exact Eq.symm (Nat.div_add_mod' k k0)
  have h_entry_le_tv :
      |(P^k) i j - (LimitMatrix π) i j|
        ≤ Matrix.tvDist (Matrix.rowDist (P^k) i) (π.val) := by
    have hsum_row : ∑ t, Matrix.rowDist (P^k) i t = 1 := by
      have hPk : IsStochastic (P^k) := by
        simpa using (isStochastic_pow (P := P) (hP := h_stoch) k)
      simpa [Matrix.rowDist] using hPk.2 i
    have hsum_π : ∑ t, π.val t = 1 := π.property.2
    have hsum_eq : ∑ t, Matrix.rowDist (P^k) i t = ∑ t, π.val t := by
      simpa [Matrix.rowDist, hsum_row, hsum_π]
    simpa [Matrix.rowDist, LimitMatrix] using
      (Matrix.entry_abs_le_tvDist_of_rows (P := (P^k)) (i := i) (x := π.val) (j := j) (hsum := hsum_eq))
  let T (Q : Matrix n n ℝ) (p : n → ℝ) : n → ℝ := fun j => ∑ t, p t * Q t j
  have h_contract (Q : Matrix n n ℝ) (p qv : n → ℝ)
      (hp1 : ∑ t, p t = 1) (hq1 : ∑ t, qv t = 1) :
      Matrix.tvDist (T Q p) (T Q qv) ≤ Matrix.dobrushinCoeff Q * Matrix.tvDist p qv := by
    simpa [T] using Matrix.tvDist_contract (P := Q) (p := p) (q := qv) (hp1 := hp1) (hq1 := hq1)
  have row_as_T (m : ℕ) :
      Matrix.rowDist (P^m) i = T (P^m) (delta i) := by
    funext j; classical
    simp [Matrix.rowDist, T, delta]
  have T_fix (m : ℕ) : T (P^m) π.val = π.val := by
    funext j
    have := pow_stationary_mulVec (P := P) (k := m) h_stoch π hπ_stat
    have := congrArg (fun v => v j) this
    simpa [T, mulVec, transpose_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using this
  have h_tv_blocks :
      Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val ≤ r^q := by
    clear h_entry_le_tv row_as_T
    revert i
    refine Nat.rec
      (motive := fun q => ∀ i0, Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i0) π.val ≤ r^q)
      ?base ?step q
    · -- base q = 0
      intro i0
      have hsumδ : ∑ t, delta i0 t = 1 := delta_sum_one i0
      have hsumπ : ∑ t, π.val t = 1 := π.property.2
      have : Matrix.tvDist (delta i0) π.val ≤ 1 := by
        have hpt :
            ∀ t, |delta i0 t - π.val t| ≤ |delta i0 t| + |π.val t| := by
          intro t; simpa [sub_eq_add_neg] using abs_add_le (delta i0 t) (-(π.val t))
        have hsum_le :
            ∑ t, |delta i0 t - π.val t|
              ≤ ∑ t, (|delta i0 t| + |π.val t|) := by
          refine sum_le_sum (by intro t _; simpa using hpt t)
        have htwo : (∑ t, |delta i0 t|) + (∑ t, |π.val t|) = (2 : ℝ) := by
          have h1 : ∑ t, |delta i0 t| = 1 := by
            simp only [delta, abs_ite, abs_zero, abs_one]
            rw [@Fintype.sum_ite_eq']
          have h2 : ∑ t, |π.val t| = 1 := by
            have := π.property
            have h0 : ∀ t, 0 ≤ π.val t := this.1
            have hsum : ∑ t, π.val t = 1 := this.2
            rw [← hsum]
            congr 1
            ext t
            exact abs_of_nonneg (h0 t)
          simp [h1, h2]
          norm_num
        have : (∑ t, |delta i0 t - π.val t|) / 2 ≤ 1 := by
          have h2pos : (0 : ℝ) < 2 := by norm_num
          have hnum :
              ∑ t, |delta i0 t - π.val t| ≤ (2 : ℝ) := by
            calc ∑ t, |delta i0 t - π.val t|
              ≤ ∑ t, (|delta i0 t| + |π.val t|) := hsum_le
              _ = (∑ t, |delta i0 t|) + (∑ t, |π.val t|) := by rw [sum_add_distrib]
              _ = 2 := by rw [htwo]
          exact (div_le_iff h2pos).mpr (by simpa [one_mul] using hnum)
        simpa [Matrix.tvDist] using this
      have h_row_eq : Matrix.rowDist (P^(0*k0)) i0 = delta i0 := by
        ext t
        simp [Matrix.rowDist, pow_zero, delta, Matrix.one_apply, eq_comm]
      rw [h_row_eq]
      simpa [pow_zero] using this
    · intro q ih i0
      have hPq : IsStochastic (P^(q*k0)) := by
        simpa using (isStochastic_pow (P := P) (hP := h_stoch) (q*k0))
      have hp1 : ∑ t, (Matrix.rowDist (P^(q*k0)) i0) t = 1 := by
        simpa [Matrix.rowDist] using hPq.2 i0
      have hq1 : ∑ t, π.val t = 1 := π.property.2
      have hstep :
          Matrix.tvDist
            (T (P^k0) (Matrix.rowDist (P^(q*k0)) i0))
            (T (P^k0) π.val)
            ≤ r * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i0) π.val :=
        h_contract (P^k0) (Matrix.rowDist (P^(q*k0)) i0) π.val hp1 hq1
      have hleft :
          T (P^k0) (Matrix.rowDist (P^(q*k0)) i0) = Matrix.rowDist (P^((q+1)*k0)) i0 := by
        funext j
        classical
        have hmul : (q + 1) * k0 = q * k0 + k0 := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_mul q k0)
        simp [T, Matrix.rowDist, Matrix.mul_apply, pow_add, hmul]
      have hright : T (P^k0) π.val = π.val := T_fix k0
      have hstep_final :
          Matrix.tvDist (Matrix.rowDist (P^((q+1)*k0)) i0) π.val
            ≤ r * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i0) π.val := by
        rw [hleft, hright] at hstep
        exact hstep
      have ih_applied : Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i0) π.val ≤ r^q := ih i0
      have hrnonneg : 0 ≤ r := hr0
      have hmul_le :
          r * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i0) π.val ≤ r * r^q :=
        mul_le_mul_of_nonneg_left ih_applied hrnonneg
      have hpow : r * r^q = r^(q+1) := by
        simp [pow_succ, mul_comm]
      have hfinal :
          Matrix.tvDist (Matrix.rowDist (P^((q+1)*k0)) i0) π.val ≤ r^(q+1) := by
        have := hstep_final.trans hmul_le
        simpa [hpow] using this
      exact hfinal
  have hδPs_le_one (s : ℕ) : Matrix.dobrushinCoeff (P^s) ≤ 1 := by
    classical
    let f : (n × n) → ℝ :=
      fun p => Matrix.tvDist (Matrix.rowDist (P^s) p.1) (Matrix.rowDist (P^s) p.2)
    have hforall : ∀ d ∈ Set.range f, d ≤ 1 := by
      intro d hd
      rcases hd with ⟨⟨i₁, i₂⟩, rfl⟩
      have hPs : IsStochastic (P^s) := by
        simpa using (isStochastic_pow (P := P) (hP := h_stoch) s)
      have hsum1_i₁ : ∑ t, Matrix.rowDist (P^s) i₁ t = 1 := by
        simpa [Matrix.rowDist] using hPs.2 i₁
      have hsum1_i₂ : ∑ t, Matrix.rowDist (P^s) i₂ t = 1 := by
        simpa [Matrix.rowDist] using hPs.2 i₂
      have hpt :
          ∀ t, |Matrix.rowDist (P^s) i₁ t - Matrix.rowDist (P^s) i₂ t|
                ≤ |Matrix.rowDist (P^s) i₁ t| + |Matrix.rowDist (P^s) i₂ t| := by
        intro t; simpa [sub_eq_add_neg] using
          abs_add_le (Matrix.rowDist (P^s) i₁ t) (-(Matrix.rowDist (P^s) i₂ t))
      have hsum_le :
          ∑ t, |Matrix.rowDist (P^s) i₁ t - Matrix.rowDist (P^s) i₂ t|
            ≤ ∑ t, (|Matrix.rowDist (P^s) i₁ t| + |Matrix.rowDist (P^s) i₂ t|) := by
        refine sum_le_sum (by intro t _; simpa using hpt t)
      have habs1 : ∑ t, |Matrix.rowDist (P^s) i₁ t| = 1 := by
        have h0 : ∀ t, 0 ≤ Matrix.rowDist (P^s) i₁ t := by intro t; exact hPs.1 i₁ t
        simpa [abs_of_nonneg, h0] using hsum1_i₁
      have habs2 : ∑ t, |Matrix.rowDist (P^s) i₂ t| = 1 := by
        have h0 : ∀ t, 0 ≤ Matrix.rowDist (P^s) i₂ t := by intro t; exact hPs.1 i₂ t
        simpa [abs_of_nonneg, h0] using hsum1_i₂
      have hnum :
          ∑ t, |Matrix.rowDist (P^s) i₁ t - Matrix.rowDist (P^s) i₂ t| ≤ 2 := by
        calc
          _ ≤ ∑ t, (|Matrix.rowDist (P^s) i₁ t| + |Matrix.rowDist (P^s) i₂ t|) := hsum_le
          _ = (∑ t, |Matrix.rowDist (P^s) i₁ t|) + (∑ t, |Matrix.rowDist (P^s) i₂ t|) := by
                simp [sum_add_distrib]
          _ = 1 + 1 := by simp [habs1, habs2]
          _ = (2 : ℝ) := by norm_num
      have h2 : (0 : ℝ) < 2 := by norm_num
      have : (∑ t, |Matrix.rowDist (P^s) i₁ t - Matrix.rowDist (P^s) i₂ t|) / 2 ≤ 1 :=
        (div_le_iff h2).mpr (by simpa [one_mul] using hnum)
      simpa [Matrix.tvDist] using this
    have hnonempty : (Set.range f).Nonempty := by
      obtain ⟨i0, _⟩ := Finset.univ_nonempty (α := n)
      exact ⟨f ⟨i0, i0⟩, ⟨⟨i0, i0⟩, rfl⟩⟩
    have hset_eq :
      { d | ∃ i i' : n, d = Matrix.tvDist (Matrix.rowDist (P^s) i) (Matrix.rowDist (P^s) i') }
        = Set.range f := by
      ext d; constructor
      · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
      · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
    have : sSup (Set.range f) ≤ 1 := csSup_le hnonempty hforall
    simpa [Matrix.dobrushinCoeff, hset_eq] using this
  have hpq :
      Matrix.tvDist (Matrix.rowDist (P^k) i) π.val ≤ r^q := by
    have hPk_split : P^k = (P^(q*k0)) * (P^s) := by
      have : k = q*k0 + s := hk_decomp
      simp [this, pow_add, pow_mul]
    have hPq : IsStochastic (P^(q*k0)) := by
      simpa using (isStochastic_pow (P := P) (hP := h_stoch) (q*k0))
    have hp1 : ∑ t, Matrix.rowDist (P^(q*k0)) i t = 1 := by
      simpa [Matrix.rowDist] using hPq.2 i
    have hq1 : ∑ t, π.val t = 1 := π.property.2
    have hstep_s :
        Matrix.tvDist
          (T (P^s) (Matrix.rowDist (P^(q*k0)) i))
          (T (P^s) π.val)
          ≤ Matrix.dobrushinCoeff (P^s) * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val := by
      simpa [T] using h_contract (Q := (P^s)) (p := Matrix.rowDist (P^(q*k0)) i) (qv := π.val) hp1 hq1
    have hleft : T (P^s) (Matrix.rowDist (P^(q*k0)) i) = Matrix.rowDist (P^k) i := by
      funext j; classical
      simp [T, Matrix.rowDist, hPk_split, Matrix.mul_apply]
    have hright : T (P^s) π.val = π.val := T_fix s
    have hδs_le : Matrix.dobrushinCoeff (P^s) ≤ 1 := hδPs_le_one s
    have :
        Matrix.tvDist (Matrix.rowDist (P^k) i) π.val
          ≤ Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val := by
      have hrhs_le :
        Matrix.dobrushinCoeff (P^s) * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val
          ≤ 1 * Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val := by
        have htv_nonneg :
            0 ≤ Matrix.tvDist (Matrix.rowDist (P^(q*k0)) i) π.val := by
          have : 0 ≤ ∑ t, |Matrix.rowDist (P^(q*k0)) i t - π.val t| :=
            sum_nonneg (by intro _ _; exact abs_nonneg _)
          have h2 : 0 ≤ (2 : ℝ) := by norm_num
          simpa [Matrix.tvDist, div_eq_mul_inv, mul_comm] using
            (mul_nonneg this (inv_nonneg.mpr h2))
        exact mul_le_mul_of_nonneg_right hδs_le htv_nonneg
      have := hstep_s.trans hrhs_le
      simpa [hleft, hright] using this
    exact this.trans h_tv_blocks
  have : |(P^k) i j - (LimitMatrix π) i j| ≤ r^q := (le_trans h_entry_le_tv hpq)
  simpa [LimitMatrix, hq] using this

open Tendsto
/--
  Spectral Gap implies convergence to the stationary limit matrix Π.
  (Works with the block-exponent version of the spectral gap.)
-/
theorem converges_of_spectral_gap [Nonempty n] {P : Matrix n n ℝ} (_ : IsStochastic P)
    (h_gap : HasSpectralGap P) (_ : Matrix.IsIrreducible P) :
    ∃ (π : stdSimplex ℝ n), IsStationary P π ∧
      Tendsto (fun k : ℕ => P^k) atTop (𝓝 (LimitMatrix π)) := by
  classical
  rcases h_gap with ⟨π, r, k0, h_stat, hk0pos, hr0, hr1, h_bound⟩
  refine ⟨π, h_stat, ?_⟩
  set L := LimitMatrix π
  -- For each entry, the absolute error is ≤ r^(k / k0), with 0 ≤ r < 1.
  have h_pow_tendsto_zero :
      Tendsto (fun k : ℕ => r^(k / k0)) atTop (𝓝 (0 : ℝ)) := by
    have h_abs_lt_one : |r| < (1 : ℝ) := by
      rw [abs_lt]
      exact ⟨neg_lt_iff_pos_add.mpr (add_pos_of_nonneg_of_pos hr0 (by linarith [hr1])), hr1⟩
    have h_rpow : Tendsto (fun n : ℕ => r^n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one h_abs_lt_one
    have h_div : Tendsto (fun k : ℕ => k / k0) atTop atTop := by
      apply tendsto_atTop_atTop.2
      intro b
      refine ⟨b * k0, ?_⟩
      intro n hn
      exact (Nat.le_div_iff_mul_le hk0pos).mpr hn
    simpa using h_rpow.comp h_div
  refine tendsto_pi_nhds.mpr (fun i => ?_)
  refine tendsto_pi_nhds.mpr (fun j => ?_)
  have h_abs_bound :
      ∀ k, |(P^k) i j - L i j| ≤ r^(k / k0) := by
    intro k; simpa [L, LimitMatrix] using h_bound i j k
  have h_abs_tend :
      Tendsto (fun k : ℕ => |(P^k) i j - L i j|) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_pow_tendsto_zero
      (fun _ => abs_nonneg _)
      h_abs_bound
  have h_diff_tend :
      Tendsto (fun k : ℕ => (P^k) i j - L i j) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using h_abs_tend.neg)
      h_abs_tend
      (fun _ => neg_abs_le _)
      (fun _ => le_abs_self _)
  have h_add_const :
      Tendsto (fun k : ℕ => L i j + ((P^k) i j - L i j)) atTop (𝓝 (L i j + 0)) := by
    exact tendsto_const_nhds.add h_diff_tend
  simpa using h_add_const

/--
  **The Fundamental Convergence Theorem for Finite Markov Chains.**
  If P satisfies the IsMCMC conditions, then Pᵏ converges to the limit matrix Π.
-/
theorem convergence_to_stationarity [Nonempty n]
    (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π) :
    Tendsto (fun k => P^k) atTop (𝓝 (LimitMatrix π)) := by
  have h_gap : HasSpectralGap P := by
    exact IsPrimitive.has_spectral_gap hMCMC.stochastic hMCMC.primitive
  obtain ⟨π', h_stat', h_conv⟩ :=
    converges_of_spectral_gap hMCMC.stochastic h_gap hMCMC.irreducible
  obtain ⟨π_unique, h_unique⟩ :=
    exists_unique_stationary_distribution_of_irreducible hMCMC.stochastic hMCMC.irreducible
  have h_π_eq_π' : (π : stdSimplex ℝ n) = π' := by
    -- π coincides with the uniquely determined stationary distribution
    have hπ  : (π : stdSimplex ℝ n) = π_unique := h_unique.2 π  hMCMC.stationary
    -- π' also coincides with the same unique stationary distribution
    have hπ' : π' = π_unique := h_unique.2 π' h_stat'
    -- hence π = π'
    simp [hπ, hπ']
  simpa [h_π_eq_π'] using h_conv

/-! #### Convergence of Distributions -/

/--
  The distribution of the chain at time k, starting from μ₀.
  μₖ = (Pᵏ)ᵀ *ᵥ μ₀.
-/
def distributionAtTime (P : Matrix n n ℝ) (μ₀ : stdSimplex ℝ n) (k : ℕ) : n → ℝ :=
  (P^k)ᵀ *ᵥ μ₀.val

/--
  Theorem: The distribution at time k converges to the stationary distribution π,
  regardless of the initial distribution μ₀.
-/
lemma distribution_converges_to_stationarity [Nonempty n]
    (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π)
    (μ₀ : stdSimplex ℝ n) :
    Tendsto (distributionAtTime P μ₀) atTop (𝓝 π.val) := by
  let PiLim : Matrix n n ℝ := LimitMatrix π
  have h_conv : Tendsto (fun k : ℕ => P ^ k) atTop (𝓝 PiLim) :=
    convergence_to_stationarity P π hMCMC
  refine tendsto_pi_nhds.mpr ?coord
  intro i
  --  We show (distributionAtTime P μ₀ k) i  →  π i.
  have h_entry_tendsto (j : n) :
      Tendsto (fun k : ℕ => (P ^ k) j i) atTop (𝓝 (PiLim j i)) := by
    have h_eval : Continuous fun M : Matrix n n ℝ => M j i := by
      simpa using ((continuous_apply i).comp (continuous_apply j))
    exact (h_eval.tendsto _).comp h_conv
  have h_term_tendsto (j : n) :
      Tendsto (fun k : ℕ => (P ^ k) j i * μ₀.val j) atTop
              (𝓝 (PiLim j i * μ₀.val j)) :=
    (h_entry_tendsto j).mul tendsto_const_nhds
  have h_sum :
      Tendsto (fun k : ℕ => ∑ j, (P ^ k) j i * μ₀.val j)
              atTop (𝓝 (∑ j, PiLim j i * μ₀.val j)) := by
    simpa using
      tendsto_finset_sum
        (s := (Finset.univ : Finset n))
        (fun j _ ↦ h_term_tendsto j)
  have h_left :
      (fun k : ℕ => ∑ j, (P ^ k) j i * μ₀.val j)
        = fun k : ℕ => distributionAtTime P μ₀ k i := by
    funext k
    simp [distributionAtTime, Matrix.mulVec, Matrix.transpose_apply]
    rfl
  have h_right :
      (∑ j, PiLim j i * μ₀.val j) = π.val i := by
    have h_one : (∑ j, μ₀.val j) = 1 := μ₀.property.2
    have h_pull :
        (∑ j, π.val i * μ₀.val j) = (π.val i) * (∑ j, μ₀.val j) := by
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset n))
          (f := fun j => μ₀.val j) (a := π.val i)).symm
    calc
      (∑ j, PiLim j i * μ₀.val j)
          = ∑ j, π.val i * μ₀.val j := by
                simp [PiLim, LimitMatrix]
      _ = (π.val i) * (∑ j, μ₀.val j) := h_pull
      _ = π.val i := by simp [h_one]
  simpa [h_left, h_right] using h_sum

/-! #### The Ergodic Theorem (Law of Large Numbers) -/

/-- Expectation of a function f under a distribution π. E_π[f]. -/
def Expectation (π : stdSimplex ℝ n) (f : n → ℝ) : ℝ :=
  ∑ i, π.val i * f i

/-
  **The Ergodic Theorem (Law of Large Numbers) for Finite Markov Chains**.

  The time average of the expected value of `f` converges to the expectation under `π`,
  regardless of the initial distribution `μ₀`.
-/
theorem ergodic_theorem_lln [Nonempty n]
    (P : Matrix n n ℝ) (π : stdSimplex ℝ n) (hMCMC : IsMCMC P π)
    (f : n → ℝ) (μ₀ : stdSimplex ℝ n) :
    let a_k := fun k : ℕ => ∑ i, (distributionAtTime P μ₀ k i) * f i
    let expected_time_average := fun N : ℕ => (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, a_k k)
    Tendsto expected_time_average atTop (𝓝 (Expectation π f)) := by
  let μₖ := distributionAtTime P μ₀
  let a_k := fun k : ℕ => ∑ i, μₖ k i * f i
  let L   := Expectation π f
  have h_ak_conv : Tendsto a_k atTop (𝓝 L) := by
    have h_μk_conv := distribution_converges_to_stationarity P π hMCMC μ₀
    have : Tendsto (fun k : ℕ => fun i : n => μₖ k i) atTop (𝓝 fun i : n => π.val i) :=
      h_μk_conv
    have h_term (i : n) :
        Tendsto (fun k : ℕ => μₖ k i * f i) atTop (𝓝 (π.val i * f i)) := by
      exact (tendsto_pi_nhds.mp this i).mul tendsto_const_nhds
    simpa [a_k, L, Expectation] using
      tendsto_finset_sum
        (s := (Finset.univ : Finset n))
        (fun i _ ↦ h_term i)
  have h_cesaro :
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (∑ k ∈ Finset.range N, a_k k)) atTop (𝓝 L) := by
    simpa using Filter.Tendsto.cesaro h_ak_conv
  let expected_time_average :=
        fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, a_k k
  change Tendsto expected_time_average atTop (𝓝 L)
  have h_equiv :
      expected_time_average =
        fun N : ℕ => (∑ k ∈ Finset.range N, a_k k) / (N : ℝ) := by
    funext N
    simp [expected_time_average, div_eq_inv_mul]
  simp_all only [one_div, a_k, μₖ, L, expected_time_average]

end MCMC.Finite
