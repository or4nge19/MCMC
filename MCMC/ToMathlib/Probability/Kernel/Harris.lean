/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Doeblin

/-!
# Harris' ergodic theorem for Markov kernels on a measurable space

The proof of M. Hairer and J. C. Mattingly, *Yet another look at Harris' ergodic theorem for
Markov chains* (Seminar on Stochastic Analysis, Random Fields and Applications VI, 2011;
arXiv:0810.2777, read in its version 1 of 15 October 2008). For a Markov kernel `P` on a
measurable space `X` and a measurable `V : X → ℝ≥0`:

* **drift** (their Assumption 1): `∫⁻ V ∂(P x) ≤ γ V x + K` for every `x`;
* **minorization** (their Assumption 2): `α • ν ≤ P x` for every `x` with `V x ≤ R`, for a
  probability measure `ν` and `α > 0`.

The paper asks `γ ∈ (0, 1)`, `α ∈ (0, 1)` and `R > 2 K / (1 - γ)`. Here `γ = 0` and `α = 1` are
allowed, and the conditions on `γ` and `R` are single inequalities without division:
`2 K + γ R < R` (that is, `γ < 1` and `R > 2 K / (1 - γ)`) for the one-step contraction (their
Theorems 3.1 and 1.3), and `K + γ R < R` (`γ < 1` and `R > K / (1 - γ)`) for existence,
uniqueness and convergence (their Theorems 1.2 and 3.2).

* `ProbabilityTheory.Kernel.abs_integral_sub_integral_le_of_drift_of_minorization` (their
  Theorem 3.1, in the form its proof gives): for `β ≥ 0` and any `ρ` with `1 - α + β K ≤ ρ`,
  `γ ≤ ρ` and `2 + β (2 K + γ R) ≤ ρ (2 + β R)`, if `|φ x - φ y| ≤ c (2 + β V x + β V y)` for all
  `x`, `y`, then `|∫ φ ∂(P x) - ∫ φ ∂(P y)| ≤ ρ c (2 + β V x + β V y)`. The case split is on
  `V x ≤ R ∧ V y ≤ R` (minorization at both points), not on `V x + V y ≤ R`.
* `…abs_integral_sub_integral_le_max_of_drift_of_minorization`: their constants, for `K > 0` and
  `0 < α₀ < α`: `β = α₀ / K`, `ρ = max (1 - (α - α₀)) ((2 + R β γ₀) / (2 + R β))` with
  `γ₀ = γ + 2 K / R` (their Theorem 3.1; their Theorem 1.3 allows any `γ₀ ∈ (γ + 2K/R, 1)`, which
  only increases `ρ`), and `ρ < 1`.
* `…exists_forall_abs_integral_sub_le_of_drift_of_minorization`: some `β > 0` and `0 ≤ ρ < 1`,
  for every `K ≥ 0` (at `K = 0` the paper's `β = α₀ / K` is not defined).
* `…lintegral_totalVariation_comp_le_max_of_drift_of_minorization` (their Theorem 1.3, with their
  constants) and `…exists_lintegral_totalVariation_comp_le_of_drift_of_minorization` (every
  `K ≥ 0`): `ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ ᾱ ρ_β(μ₁, μ₂)` for all probability measures `μ₁`, `μ₂`, with
  `ρ_β(μ₁, μ₂) = ∫⁻ (1 + β V) ∂|μ₁ - μ₂|` (Mathlib's total variation; no moment assumed).
* `…existsUnique_invariant_of_drift_of_minorization` (their Theorems 1.2 and 3.2, under
  `K + γ R < R`): exactly one invariant probability measure `π`; by the drift alone
  (`ProbabilityTheory.Kernel.lintegral_le_of_invariant_of_drift`, `Contraction.lean`),
  `∫⁻ V ∂π ≤ K / (1 - γ)` (their Theorem 3.2 states only `∫ V ∂π < ∞`). The same from the drift
  and the minorization of a power `P ^ m`: `…existsUnique_invariant_of_drift_of_minorization_pow`.
* `…exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization` (their Theorem 1.2,
  under `K + γ R < R`): `C ≥ 0` and `0 ≤ ρ < 1` with
  `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ρⁿ M (1 + ∫ V ∂μ)` for every initial law `μ` integrating `V` and
  every measurable `φ` with `|φ| ≤ M (1 + V)`; in their form
  `‖Pⁿ φ - π φ‖ ≤ C ρⁿ ‖φ - π φ‖` (the norm `sup |φ| / (1 + V)`), from every point:
  `…exists_abs_integral_pow_sub_integral_le_of_drift_of_minorization`. Under the paper's
  `2 K + γ R < R`, with their constants, `C = max 1 β⁻¹ (2 + β K / (1 - γ) + β)` and the rate `ᾱ`
  of the one-step contraction:
  `…abs_integral_comp_pow_sub_integral_le_max_of_drift_of_minorization`.
* `…isIrreducible_of_drift_of_minorization_pow`: the drift, `K + γ R < R` and a minorization of
  `P ^ m` on `{V ≤ R}` make `P` irreducible with respect to `ν` in Mathlib's sense
  (`ProbabilityTheory.Kernel.IsIrreducible`); for Doeblin's condition,
  `…isIrreducible_of_forall_smul_le_pow` (`Doeblin.lean`).
* `…drift_minorization_pow_of_add_mul_lt`, the step from `K + γ R < R` to the paper's threshold:
  with `L = K / (1 - γ)` and any `j` with `γ ^ j < (R - L) / (2 (2 L + 1))`, the power
  `P ^ (j + 1)` has the drift `(γ ^ (j + 1), K ∑_{k ≤ j} γ ^ k)` and the minorization
  `((R - L) / (2 R) * α) • ν ≤ P ^ (j + 1) x` on `{V ≤ 2 L + 1}`, with `2 K' + γ' R' < R'`; its
  minorization comes from returns to `{V ≤ R}` (`…one_sub_le_measureReal_pow_setOf_le_of_drift`,
  Markov's inequality) and `…smul_smul_le_comp_of_forall_mem_smul_le`. The contraction of this
  power gives the rate `ρ` along the multiples of `j + 1`, and `pow_div_le_inv_mul_rpow_inv_pow`
  turns it into a rate `C ρ'ⁿ` along every `n`, with the moments of `Pʳ ∘ₘ μ`
  (`…integral_comp_pow_le_of_drift`) for the remainders.

Forced hypotheses, compiled. `2 K + γ R < R` is sharp for the contraction at `γ = 0`, `K = 1`,
`R = 2` (other values of `γ` and `K` are not compiled): there `2 K + γ R = R`, and a
deterministic chain on `ℕ` has the drift and the minorization and contracts for no `β > 0` and no
`ρ < 1` (`…exists_not_contraction_of_two_mul_add_mul_eq`), and its weighted total variation
between laws contracts for none either
(`…exists_not_lintegral_totalVariation_comp_le_of_two_mul_add_mul_eq`, through the converse
`…forall_abs_integral_sub_le_of_lintegral_totalVariation_le`); that chain is ergodic, so the
threshold of the contraction is not the threshold of ergodicity. Two absorbing states on `Bool`
(`…drift_and_minorization_id_bool`) satisfy the drift with `K = 1 - γ` and the minorization on
`{V ≤ R}` for `R < 1 = K / (1 - γ)` and have two invariant laws: a minorization on a sublevel set
below `K / (1 - γ)` gives nothing, and at `γ = 1`, `K = 0`, where `K + γ R = R` for every `R`,
uniqueness fails. `α > 0` is forced by the same chain with `V = 0` and `α = 0`
(`…not_existsUnique_invariant_id_bool`, `Doeblin.lean`), and the minorization itself by the same
chain with `R ≥ 1` (`…not_forall_smul_le_id_bool`). `Measurable V` is used by every proof (the
Lebesgue integrals of `V` against `P ∘ₘ μ` and `Pⁿ x`); without it the drift still parses, `∫⁻`
then being a lower integral, and no counterexample and no proof without it is given here.

The threshold of existence, uniqueness and convergence is `K + γ R < R`, that is
`R > K / (1 - γ)`, half the paper's. Below it uniqueness fails (the two absorbing states), and at
`K + γ R = R` convergence fails: a chain on `ℕ` whose iterates from `1` never charge the invariant
law `dirac 0` (`…exists_not_tendsto_of_add_mul_eq`), and existence fails: the shift of `ℕ` has no
invariant law (`…exists_not_exists_invariant_of_add_mul_eq`). Uniqueness holds at the threshold:
for `γ < 1`, every `R ≥ K / (1 - γ)` (`K + γ R ≤ R`) and every nonzero minorizing `ν`, any two
invariant laws are equal (`…eq_of_invariant_of_drift_of_minorization`, with no contraction: the
parts `π₁ - π₂` and `π₂ - π₁` are invariant, `…Invariant.sub`, and each charges `{V ≤ R}`,
`…measure_setOf_le_pos_of_invariant_of_drift`). The regime `K + γ R < R ≤ 2 K + γ R`, where the
one-step contraction can fail and the theorems above apply, is inhabited
(`…exists_not_contraction_and_existsUnique_invariant`).
A non-degenerate instance
(`V n = n` on `ℕ`, minorization only on `{V ≤ 3}`, so Doeblin's theorem does not apply:
`…drift_and_minorization_of_halving`) is compiled at the end of the file, with Theorem 1.3 on it
(`…lintegral_totalVariation_comp_le_of_halving`, `ᾱ = 21/22`) against the bound through the
product coupling: for `μ₁ = dirac 0`, `μ₂ = (1 - ε) • dirac 0 + ε • dirac 4`,
`ρ_β(μ₁, μ₂) = 3 ε` (`…integral_totalVariation_dirac_zero_four`) and
`ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) = 21 ε / 8` (`…integral_totalVariation_comp_of_halving`), while the product
coupling's right side is `ᾱ (2 + ε)`.

The contraction is stated on test functions (the paper's Lipschitz seminorm `|||φ|||_β`, their
Theorem 3.1) and on laws (the weighted total variation `ρ_β`, their Theorem 1.3); the two forms
are equivalent (`Contraction.lean`). The bound through the product coupling,
`ProbabilityTheory.Kernel.abs_integral_comp_pow_sub_le`, which does not vanish at `μ₁ = μ₂`, is
what the proofs of existence, uniqueness and convergence use.

A minorization for a power, from the drift of `P` itself (`α • ν ≤ (P ^ m) x` on `{V ≤ R}`,
`K + γ R < R`): it passes to `P ^ (m + 1)` with `(1 - (K + γ R) / R) α`, by Markov's inequality
on `P x` (`…smul_le_pow_add_one_of_drift_of_minorization_pow`), so `m = 0` reduces to `m = 1`;
for `0 < m` the iterated drift keeps the threshold,
`K (1 + γ + ⋯ + γ ^ (m - 1)) + γ ^ m R < R` (`NNReal.mul_sum_pow_add_pow_mul_lt`), so
`…existsUnique_invariant_of_drift_of_minorization_pow` with `…lintegral_pow_le_of_drift` gives one
invariant law; the convergence bound `C ρⁿ M (1 + ∫ V ∂μ)` holds as for `m = 1`
(`…exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow`); and every sublevel
set `{V ≤ R'}` is small for a power: `((R - K / (1 - γ)) / (2 R) * α) • ν ≤ P ^ (m + j) x` there
for some `j` (`…exists_smul_le_pow_add_of_drift_of_minorization_pow`).

Remark 1.4, that some power `Pⁿ` contracts `ρ₁`, is
`ProbabilityTheory.Kernel.lintegral_totalVariation_comp_pow_le_max` (`Contraction.lean`). Not
formalized here: Remark 1.1 (`V` with value `∞`), the other half of Remark 1.4 (`P` itself need
not contract `ρ₁`: a four-state example, computed exactly, not compiled), §3.2 (Assumptions 3–4
and the averaged kernel of Theorem 3.4, Remarks 3.3 and 3.5), and the sharpness of
`2 K + γ R < R` for `γ ≠ 0`.

Literature. S. P. Meyn, R. L. Tweedie, *Markov Chains and Stochastic Stability* (1993 edition),
Theorem 15.0.1 (iii) (p. 358) and Lemma 15.2.8 (p. 374): for a ψ-irreducible aperiodic chain, a
drift `ΔV ≤ -βV + b 1_C` to a petite set gives `V`-geometric convergence; from `PV ≤ γV + K` the
drift is strict outside `{V ≤ R}` for every `R > K / (1 - γ)` (an arithmetic remark, not a
quotation; their proof of Lemma 15.2.8 takes the level `2L / (1 - λ)`). P. H. Baxendale,
*Ann. Appl. Probab.* 15 (2005) 700–738, Theorem 1.1 with (A1)–(A3): the same conclusion with
explicit constants, under the extra hypothesis `ν(C) > 0`. So existence, uniqueness and geometric
convergence at `R > K / (1 - γ)` are implicit in the literature once irreducibility and
aperiodicity are checked; not found stated there: a self-contained statement with no aperiodicity
hypothesis, uniqueness at `R = K / (1 - γ)`, and counterexamples at and below the threshold. The
factor `2` in Hairer–Mattingly is needed for their one-step contraction. Not read: the published
version of Hairer–Mattingly; Douc, Moulines, Priouret, Soulier, *Markov Chains* (2018).

No formalization of Harris' theorem in drift–minorization form, with existence,
uniqueness and weighted geometric convergence, was found.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X} {V : X → ℝ≥0} {γ K : ℝ≥0}

/-- The drift hypothesis read with the Bochner integral of `V`. -/
theorem integral_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (x : X) :
    ∫ y, (V y : ℝ) ∂(P x) ≤ γ * V x + K := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (V _).coe_nonneg)
    hV.coe_nnreal_real.aestronglyMeasurable]
  simp only [ENNReal.ofReal_coe_nnreal]
  refine (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) (hdrift x)).trans_eq ?_
  rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top]) ENNReal.coe_ne_top, ENNReal.toReal_mul]
  simp

/-- **Hairer–Mattingly, Theorem 3.1**, in the form its proof gives: under the drift and the
minorization on `{V ≤ R}`, `P` contracts the weighted oscillation with any rate `ρ` such that
`1 - α + β K ≤ ρ`, `γ ≤ ρ` and `2 + β (2 K + γ R) ≤ ρ (2 + β R)`. -/
theorem abs_integral_sub_integral_le_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) {β ρ : ℝ}
    (hβ : 0 ≤ β) (h₁ : 1 - α + β * K ≤ ρ) (h₂ : γ ≤ ρ)
    (h₃ : 2 + β * (2 * K + γ * R) ≤ ρ * (2 + β * R)) {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ}
    (hφc : ∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) (x y : X) :
    |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y) := by
  have hc : 0 ≤ c := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφc x x))
    (by linarith [mul_nonneg hβ (V x).coe_nonneg])
  have hI : ∀ u, β * ∫ z, (V z : ℝ) ∂(P u) ≤ β * (γ * V u + K) := fun u ↦
    mul_le_mul_of_nonneg_left (integral_le_of_drift hV hdrift u) hβ
  have ht := mul_le_mul_of_nonneg_right h₂
    (add_nonneg (mul_nonneg hβ (V x).coe_nonneg) (mul_nonneg hβ (V y).coe_nonneg))
  by_cases hxy : V x ≤ R ∧ V y ≤ R
  · have h := abs_integral_sub_integral_le_of_forall_abs_sub_le (hmin x hxy.1) (hmin y hxy.2) hV
      (lintegral_ne_top_of_drift hdrift x) (lintegral_ne_top_of_drift hdrift y) hβ hφ hφc
    simp only [measureReal_nnreal_smul_apply, probReal_univ, mul_one] at h
    calc |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)|
        ≤ c * (2 + β * ∫ z, (V z : ℝ) ∂(P x) + β * ∫ z, (V z : ℝ) ∂(P y) - 2 * α) := h
      _ ≤ c * (ρ * (2 + β * V x + β * V y)) :=
          mul_le_mul_of_nonneg_left (by linarith [hI x, hI y]) hc
      _ = ρ * c * (2 + β * V x + β * V y) := by ring
  · have hs : (R : ℝ) ≤ V x + V y := by
      rcases not_and_or.1 hxy with h | h
      · linarith [NNReal.coe_lt_coe.2 (not_le.1 h), (V y).coe_nonneg]
      · linarith [NNReal.coe_lt_coe.2 (not_le.1 h), (V x).coe_nonneg]
    have h := abs_integral_sub_integral_le_of_forall_abs_sub_le (θ := 0)
      (MeasureTheory.Measure.zero_le _) (MeasureTheory.Measure.zero_le _) hV
      (lintegral_ne_top_of_drift hdrift x) (lintegral_ne_top_of_drift hdrift y) hβ hφ hφc
    simp only [measureReal_zero_apply, mul_zero, sub_zero] at h
    have hu := mul_le_mul_of_nonneg_right h₂ (mul_nonneg hβ (sub_nonneg.2 hs))
    calc |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)|
        ≤ c * (2 + β * ∫ z, (V z : ℝ) ∂(P x) + β * ∫ z, (V z : ℝ) ∂(P y)) := h
      _ ≤ c * (ρ * (2 + β * V x + β * V y)) :=
          mul_le_mul_of_nonneg_left (by linarith [hI x, hI y]) hc
      _ = ρ * c * (2 + β * V x + β * V y) := by ring

/-- `a + γ R < R` forces `γ < 1`. -/
theorem _root_.NNReal.lt_one_of_add_mul_lt {a γ R : ℝ≥0} (h : a + γ * R < R) : γ < 1 :=
  lt_of_mul_lt_mul_right ((le_add_self.trans_lt h).trans_eq (one_mul R).symm) (by positivity)

/-- `a + γ R ≤ R` and `γ < 1` give `a / (1 - γ) ≤ R`. -/
theorem _root_.NNReal.div_one_sub_le_of_add_mul_le {a γ R : ℝ≥0} (h : a + γ * R ≤ R)
    (hγ : γ < 1) : a / (1 - γ) ≤ R :=
  (div_le_iff₀ (tsub_pos_of_lt hγ)).2 (by
    rw [mul_tsub, mul_one, le_tsub_iff_right (mul_le_of_le_one_right (by positivity) hγ.le),
      mul_comm]
    exact h)

/-- `a + γ R < R` gives `a / (1 - γ) < R`. -/
theorem _root_.NNReal.div_one_sub_lt_of_add_mul_lt {a γ R : ℝ≥0} (h : a + γ * R < R) :
    a / (1 - γ) < R :=
  (div_lt_iff₀ (tsub_pos_of_lt (NNReal.lt_one_of_add_mul_lt h))).2
    (by rw [mul_tsub, mul_one, lt_tsub_iff_right, mul_comm]; exact h)

/-- **Hairer–Mattingly's constants** (their Theorem 3.1): for `K > 0`, `0 < α₀ < α`,
`β = α₀ / K` and `γ₀ = γ + 2 K / R`, the rate `ρ = max (1 - (α - α₀)) ((2 + R β γ₀) / (2 + R β))`
is `< 1` and `P` contracts the weighted oscillation with rate `ρ`. -/
theorem abs_integral_sub_integral_le_max_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) (hK : 0 < K)
    (hR : 2 * K + γ * R < R) {α₀ : ℝ} (hα₀ : 0 < α₀) (hα₀α : α₀ < α) :
    max (1 - (α - α₀)) ((2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K))) < 1 ∧
      ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
        (∀ x y, |φ x - φ y| ≤ c * (2 + α₀ / K * V x + α₀ / K * V y)) →
        ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤
          max (1 - (α - α₀)) ((2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K))) * c *
            (2 + α₀ / K * V x + α₀ / K * V y) := by
  have hRr : (2 * K + γ * R : ℝ) < R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < R := by linarith [mul_nonneg γ.coe_nonneg R.coe_nonneg, K.coe_nonneg]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hβ : 0 < α₀ / K := div_pos hα₀ hK0
  have hd : 0 < 2 + R * (α₀ / K) := by positivity
  have hγ₀ : R * (α₀ / K) * (γ + 2 * K / R) = α₀ / K * (2 * K + γ * R) := by
    field_simp
    ring
  have hγ1 : (γ : ℝ) < 1 := by exact_mod_cast NNReal.lt_one_of_add_mul_lt hR
  have hB : (2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K)) * (2 + R * (α₀ / K)) =
      2 + α₀ / K * (2 * K + γ * R) := by rw [div_mul_cancel₀ _ hd.ne', hγ₀]
  refine ⟨max_lt (by linarith) ((div_lt_one hd).2 (by nlinarith)), fun φ hφ c hφc x y ↦
    abs_integral_sub_integral_le_of_drift_of_minorization hV hdrift hmin hβ.le ?_ ?_ ?_ hφ hφc x y⟩
  · rw [div_mul_cancel₀ _ hK0.ne']
    exact le_max_of_le_left (by linarith)
  · refine le_max_of_le_right ((le_div_iff₀ hd).2 ?_)
    nlinarith [mul_nonneg hβ.le K.coe_nonneg]
  · calc 2 + α₀ / K * (2 * K + γ * R)
        = (2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K)) * (2 + α₀ / K * R) := by
          rw [mul_comm (α₀ / K) (R : ℝ), hB]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Under the drift and the minorization with `α > 0` and `2 K + γ R < R`, `P` contracts the
weighted oscillation for some `β > 0` with some rate `0 ≤ ρ < 1` (also for `K = 0`). -/
theorem exists_forall_abs_integral_sub_le_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hα : 0 < α) (hR : 2 * K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) :
    ∃ β ρ : ℝ, 0 < β ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ φ : X → ℝ, Measurable φ → ∀ c : ℝ,
      (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y) := by
  have hRr : (2 * K + γ * R : ℝ) < R := by exact_mod_cast hR
  have hγ1 : (γ : ℝ) < 1 := by exact_mod_cast NNReal.lt_one_of_add_mul_lt hR
  have hα0 : (0 : ℝ) < α := by exact_mod_cast hα
  set β : ℝ := α / (2 * (K + 1))
  have hβ : 0 < β := by positivity
  have hβK : β * K < α := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [K.coe_nonneg]
  have hd : 0 < 2 + β * R := by positivity
  refine ⟨β, max (1 - α + β * K) ((2 + β * (2 * K + γ * R)) / (2 + β * R)), hβ,
    le_max_of_le_right (by positivity), max_lt (by linarith) ((div_lt_one hd).2
      (by nlinarith)), fun φ hφ c hφc x y ↦
    abs_integral_sub_integral_le_of_drift_of_minorization hV hdrift hmin hβ.le (le_max_left _ _)
      (le_max_of_le_right ((le_div_iff₀ hd).2 (by nlinarith [mul_nonneg hβ.le K.coe_nonneg])))
      ((div_mul_cancel₀ _ hd.ne').symm.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        hd.le)) hφ hφc x y⟩

/-- **Convergence with Hairer–Mattingly's constants**: under the drift with `K > 0`, the
minorization on `{V ≤ R}` with their `2 K + γ R < R`, `0 < α₀ < α` and `β = α₀ / K`, for every
invariant law `π`, every initial law `μ` integrating `V` and every measurable `φ` with
`|φ| ≤ M (1 + V)`, `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ᾱⁿ M (1 + ∫ V ∂μ)` with the rate
`ᾱ = max (1 - (α - α₀)) ((2 + R β (γ + 2 K / R)) / (2 + R β)) < 1` of
`abs_integral_sub_integral_le_max_of_drift_of_minorization` and
`C = max 1 β⁻¹ (2 + β K / (1 - γ) + β)`. -/
theorem abs_integral_comp_pow_sub_integral_le_max_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) (hK : 0 < K)
    (hR : 2 * K + γ * R < R) {α₀ : ℝ} (hα₀ : 0 < α₀) (hα₀α : α₀ < α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : ∫⁻ x, V x ∂μ ≠ ∞) {φ : X → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ x, |φ x| ≤ M * (1 + V x)) (n : ℕ) :
    |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤
      max 1 (α₀ / K)⁻¹ * (2 + α₀ / K * (K / (1 - γ)) + α₀ / K) *
        max (1 - (α - α₀)) ((2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K))) ^ n *
          M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  exact abs_integral_comp_pow_sub_integral_le_of_contraction hV hdrift
    (NNReal.lt_one_of_add_mul_lt hR) (div_pos hα₀ hK0)
    (le_max_of_le_right (div_nonneg (by positivity) (by positivity)))
    (abs_integral_sub_integral_le_max_of_drift_of_minorization hV hdrift hmin hK hR hα₀ hα₀α).2
    hπ hμ hφ hφM n

/-- **Hairer–Mattingly, Theorem 1.3**, with their constants: under the drift with `K > 0` and the
minorization on `{V ≤ R}` with `2 K + γ R < R`, for `0 < α₀ < α`, `β = α₀ / K` and
`ᾱ = max (1 - (α - α₀)) ((2 + R β (γ + 2 K / R)) / (2 + R β))`, `ᾱ < 1` and
`ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ ᾱ ρ_β(μ₁, μ₂)` for all probability measures `μ₁`, `μ₂`, where
`ρ_β(μ₁, μ₂) = ∫⁻ (1 + β V) ∂|μ₁ - μ₂|` is the weighted total variation. No moment of `μ₁`, `μ₂`
is assumed: when `ρ_β(μ₁, μ₂) = ∞` the bound is trivial. -/
theorem lintegral_totalVariation_comp_le_max_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) (hK : 0 < K)
    (hR : 2 * K + γ * R < R) {α₀ : ℝ} (hα₀ : 0 < α₀) (hα₀α : α₀ < α) :
    max (1 - (α - α₀)) ((2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K))) < 1 ∧
      ∀ (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂],
        ∫⁻ x, ENNReal.ofReal (1 + α₀ / K * V x)
            ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
          ENNReal.ofReal (max (1 - (α - α₀))
            ((2 + R * (α₀ / K) * (γ + 2 * K / R)) / (2 + R * (α₀ / K)))) *
          ∫⁻ x, ENNReal.ofReal (1 + α₀ / K * V x)
            ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  obtain ⟨h1, hP⟩ :=
    abs_integral_sub_integral_le_max_of_drift_of_minorization hV hdrift hmin hK hR hα₀ hα₀α
  exact ⟨h1, fun μ₁ μ₂ ↦ lintegral_totalVariation_comp_le hV hdrift
    (div_pos hα₀ (by exact_mod_cast hK)).le hP μ₁ μ₂⟩

/-- **Hairer–Mattingly, Theorem 1.3**, for every `K ≥ 0`: under the drift and the minorization on
`{V ≤ R}` with `α > 0` and `2 K + γ R < R`, there are `β > 0` and `0 ≤ ρ < 1` with
`ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ ρ ρ_β(μ₁, μ₂)` for all probability measures `μ₁`, `μ₂`. -/
theorem exists_lintegral_totalVariation_comp_le_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hα : 0 < α) (hR : 2 * K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) :
    ∃ β ρ : ℝ, 0 < β ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁]
      [IsProbabilityMeasure μ₂], ∫⁻ x, ENNReal.ofReal (1 + β * V x)
          ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
        ENNReal.ofReal ρ * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
          ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  obtain ⟨β, ρ, hβ, hρ0, hρ, hP⟩ :=
    exists_forall_abs_integral_sub_le_of_drift_of_minorization hV hdrift hα hR hmin
  exact ⟨β, ρ, hβ, hρ0, hρ, fun μ₁ μ₂ ↦ lintegral_totalVariation_comp_le hV hdrift hβ.le hP μ₁ μ₂⟩

/-! ### Existence, uniqueness and convergence: the minorization above `K / (1 - γ)` -/

/-- A minorization on a set passes to a law: if `α • ν ≤ P z` for every `z ∈ S`, then
`μ S • α • ν ≤ P ∘ₘ μ`. -/
theorem smul_smul_le_comp_of_forall_mem_smul_le {μ : Measure X} {S : Set X}
    {ν : Measure X} {α : ℝ≥0} (hmin : ∀ z ∈ S, α • ν ≤ P z) : μ S • α • ν ≤ P ∘ₘ μ := by
  refine Measure.le_iff.2 fun A hA ↦ ?_
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), Measure.smul_apply, smul_eq_mul, mul_comm]
  calc (α • ν) A * μ S = ∫⁻ _ in S, (α • ν) A ∂μ := (MeasureTheory.setLIntegral_const S _).symm
    _ ≤ ∫⁻ z in S, P z A ∂μ :=
        setLIntegral_mono (P.measurable_coe hA) fun z hz ↦ Measure.le_iff.1 (hmin z hz) A hA
    _ ≤ ∫⁻ z, P z A ∂μ := setLIntegral_le_lintegral S _

/-- **Returns to a sublevel set**: under a drift with `γ < 1`, the law `Pⁿ x` charges
`{V ≤ R}` with probability at least `1 - (γⁿ V x + K / (1 - γ)) / R` (Markov's inequality). -/
theorem one_sub_le_measureReal_pow_setOf_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) (n : ℕ) (x : X) {R : ℝ≥0}
    (hR : 0 < R) :
    1 - (γ ^ n * V x + K / (1 - γ)) / R ≤ ((P ^ n) x).real {z | V z ≤ R} := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hint : Integrable (fun z ↦ (V z : ℝ)) ((P ^ n) x) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_pow_ne_top_of_drift hV hdrift n x)
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := (P ^ n) x)
    (ae_of_all _ fun z ↦ (V z).coe_nonneg) hint (R : ℝ)
  have hsub := measureReal_mono (μ := (P ^ n) x) (s₁ := {z | V z ≤ R}ᶜ)
    (s₂ := {z | (R : ℝ) ≤ V z}) fun z (hz : ¬ V z ≤ R) ↦ NNReal.coe_le_coe.2 (not_le.1 hz).le
  rw [probReal_compl_eq_one_sub (measurableSet_le hV measurable_const)] at hsub
  rw [sub_le_comm, le_div_iff₀ hR']
  nlinarith [integral_pow_le_of_drift hV hdrift hγ n x]

/-- **A power of `P` satisfies Hairer–Mattingly's hypotheses** when the minorization holds on a
sublevel set above `L = K / (1 - γ)`: under the drift and the minorization on `{V ≤ R}` with
`K + γ R < R`, for every `j` with `γ ^ j < (R - L) / (2 (2 L + 1))` (`exists_pow_lt_of_lt_one`
gives one), the power `P ^ (j + 1)` has the drift with `γ' = γ ^ (j + 1)` and
`K' = K ∑_{k ≤ j} γ ^ k`, the minorization `((R - L) / (2 R) * α) • ν ≤ P ^ (j + 1) x` on
`{V ≤ R'}`, `R' = 2 L + 1`, and `2 K' + γ' R' < R'`. -/
theorem drift_minorization_pow_of_add_mul_lt [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} {α R : ℝ≥0}
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) {j : ℕ}
    (hj : γ ^ j < (R - K / (1 - γ)) / (2 * (2 * (K / (1 - γ)) + 1))) :
    2 * (K * ∑ k ∈ Finset.range (j + 1), γ ^ k) + γ ^ (j + 1) * (2 * (K / (1 - γ)) + 1) <
        2 * (K / (1 - γ)) + 1 ∧
      (∀ x, ∫⁻ y, V y ∂((P ^ (j + 1)) x) ≤
        γ ^ (j + 1) * V x + K * ∑ k ∈ Finset.range (j + 1), γ ^ k) ∧
      ∀ x, V x ≤ 2 * (K / (1 - γ)) + 1 →
        ((R - K / (1 - γ)) / (2 * R) * α) • ν ≤ (P ^ (j + 1)) x := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hγr : (γ : ℝ) < 1 := by exact_mod_cast hγ
  have hRr : (K : ℝ) + γ * R < R := by exact_mod_cast hR
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, (K : ℝ) / (1 - γ) = L := ⟨_, rfl⟩
  have hK : (K : ℝ) = L * (1 - γ) := by rw [← hLd, div_mul_cancel₀ _ (by linarith)]
  have hR0 : (0 : ℝ) < R := by nlinarith [mul_nonneg γ.coe_nonneg R.coe_nonneg, K.coe_nonneg]
  have hL0 : 0 ≤ L := hLd ▸ div_nonneg K.coe_nonneg (by linarith)
  have e₃ : ((1 - γ : ℝ≥0) : ℝ) = 1 - γ := by rw [NNReal.coe_sub hγ.le, NNReal.coe_one]
  have e₁ : ((K / (1 - γ) : ℝ≥0) : ℝ) = L := by rw [NNReal.coe_div, e₃, hLd]
  have e₂ : ((R - K / (1 - γ) : ℝ≥0) : ℝ) = R - L := by
    rw [NNReal.coe_sub (NNReal.div_one_sub_lt_of_add_mul_lt hR).le, e₁]
  have hj' : (γ : ℝ) ^ j < (R - L) / (2 * (2 * L + 1)) := by
    simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_one, e₂, e₁] using NNReal.coe_lt_coe.2 hj
  refine ⟨?_, fun x ↦ by simpa using lintegral_pow_le_of_drift hV hdrift (j + 1) x, fun x hx ↦ ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one,
      NNReal.coe_sum, e₁]
    rw [hK]
    nlinarith [congrArg (L * ·) (geom_sum_mul_neg (γ : ℝ) (j + 1)),
      pow_lt_one₀ γ.coe_nonneg hγr (by omega : j + 1 ≠ 0)]
  have hx' : (V x : ℝ) ≤ 2 * L + 1 := by
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, e₁] using
      NNReal.coe_le_coe.2 hx
  have hδS : (((R - K / (1 - γ)) / (2 * R) : ℝ≥0) : ℝ≥0∞) ≤ ((P ^ j) x) {z | V z ≤ R} := by
    rw [← ofReal_measureReal, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (one_sub_le_measureReal_pow_setOf_le_of_drift hV
      hdrift hγ j x (by exact_mod_cast hR0)))
    rw [NNReal.coe_div, e₂, NNReal.coe_mul, NNReal.coe_ofNat, hLd,
      (by field_simp; ring : ((R : ℝ) - L) / (2 * R) = 1 - (R + L) / 2 / R)]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left hx' (pow_nonneg γ.coe_nonneg j),
      (lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * (2 * L + 1))).1 hj']
  rw [(by exact pow_succ' P j : P ^ (j + 1) = P ∘ₖ (P ^ j)), Kernel.comp_apply]
  refine le_trans (Measure.le_iff'.2 fun s ↦ ?_) (smul_smul_le_comp_of_forall_mem_smul_le
    (μ := (P ^ j) x) (S := {z | V z ≤ R}) fun z hz ↦ hmin z hz)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]
  gcongr

/-- The moments of the laws along the chain, `γ < 1`:
`∫ V ∂(Pⁿ ∘ₘ μ) ≤ ∫ V ∂μ + K / (1 - γ)`. -/
theorem integral_comp_pow_le_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : ∫⁻ x, V x ∂μ ≠ ∞) (n : ℕ) :
    ∫ x, (V x : ℝ) ∂((P ^ n) ∘ₘ μ) ≤ ∫ x, (V x : ℝ) ∂μ + K / (1 - γ) := by
  have hVμ : Integrable (fun x ↦ (V x : ℝ)) μ := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable hμ
  have hVn : Integrable (fun x ↦ (V x : ℝ)) ((P ^ n : Kernel X X) ∘ₘ μ) := by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable
      (lintegral_comp_pow_ne_top_of_drift hV hdrift hμ n)
  rw [Measure.integral_comp _ _ hVn]
  calc ∫ x, ∫ y, (V y : ℝ) ∂((P ^ n) x) ∂μ ≤ ∫ x, ((V x : ℝ) + K / (1 - γ)) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ integral_nonneg fun _ ↦ (V _).coe_nonneg)
          (hVμ.add (integrable_const _)) (ae_of_all _ fun x ↦
            (integral_pow_le_of_drift hV hdrift hγ n x).trans (add_le_add (mul_le_of_le_one_left
              (V x).coe_nonneg (pow_le_one₀ γ.coe_nonneg (by exact_mod_cast hγ.le))) le_rfl))
    _ = ∫ x, (V x : ℝ) ∂μ + K / (1 - γ) := by
        rw [integral_add hVμ (integrable_const _), integral_const]
        simp

/-- **Harris' theorem, existence and uniqueness** (Hairer–Mattingly, Theorems 1.2 and 3.2, with the
minorization on any sublevel set above `K / (1 - γ)`): under the drift and the minorization on
`{V ≤ R}` with `α > 0` and `K + γ R < R` (that is, `R > K / (1 - γ)`), the kernel has exactly one
invariant probability measure. The paper asks `R > 2 K / (1 - γ)`, the threshold of the one-step
contraction; here the power of `drift_minorization_pow_of_add_mul_lt` is contracted. -/
theorem existsUnique_invariant_of_drift_of_minorization [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} [IsProbabilityMeasure ν]
    {α R : ℝ≥0} (hα : 0 < α) (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧ Invariant P π := by
  have := nonempty_of_isProbabilityMeasure ν
  have hLR := NNReal.div_one_sub_lt_of_add_mul_lt hR
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos (tsub_pos_of_lt hLR)
    (by positivity : (0 : ℝ≥0) < 2 * (2 * (K / (1 - γ)) + 1))) (NNReal.lt_one_of_add_mul_lt hR)
  obtain ⟨hR', hd', hm'⟩ := drift_minorization_pow_of_add_mul_lt hV hdrift hR hmin hj
  have hR0 : (0 : ℝ≥0) < R := NNReal.coe_pos.1 ((NNReal.coe_nonneg _).trans_lt hLR)
  obtain ⟨β, ρ, hβ, hρ0, hρ, hP⟩ := exists_forall_abs_integral_sub_le_of_drift_of_minorization hV
    hd' (mul_pos (div_pos (tsub_pos_of_lt hLR) (mul_pos two_pos hR0)) hα) hR' hm'
  exact existsUnique_invariant_of_existsUnique_invariant_pow (existsUnique_invariant_of_contraction
    hV hd' (NNReal.lt_one_of_add_mul_lt hR') hβ.le hρ0 hρ hP)

/-- **Invariant measures charge the sublevel sets above `K / (1 - γ)`**: under a drift with
`γ < 1`, every nonzero finite invariant measure gives positive mass to `{V ≤ R}` when
`K + γ R ≤ R`. -/
theorem measure_setOf_le_pos_of_invariant_of_drift [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {R : ℝ≥0} (hR : K + γ * R ≤ R)
    {π : Measure X} [IsFiniteMeasure π] (hπ0 : π ≠ 0) (hπ : Invariant P π) :
    0 < π {x | V x ≤ R} := by
  have : NeZero π := ⟨hπ0⟩
  have hπ' : Invariant P ((π univ)⁻¹ • π) := by rw [Invariant, Measure.comp_smul, hπ.def]
  refine pos_iff_ne_zero.2 fun h₀ ↦ ?_
  have h0 : ((π univ)⁻¹ • π) {x | V x ≤ R} = 0 := by simp [h₀]
  have hKR : (K : ℝ≥0∞) / (1 - γ) ≤ R := by
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_div (tsub_pos_of_lt hγ).ne']
    exact ENNReal.coe_le_coe.2 (NNReal.div_one_sub_le_of_add_mul_le hR hγ)
  have hae : ∀ᵐ x ∂((π univ)⁻¹ • π), (R : ℝ≥0∞) < V x := by
    rw [ae_iff]
    simpa [not_lt] using h0
  have heq := ae_eq_of_ae_le_of_lintegral_le (f := fun _ ↦ (R : ℝ≥0∞))
    (g := fun x ↦ (V x : ℝ≥0∞)) (hae.mono fun x hx ↦ hx.le) (by simp)
    hV.coe_nnreal_ennreal.aemeasurable
    (((lintegral_le_of_invariant_of_drift hV hdrift hγ hπ').trans hKR).trans_eq
      (by rw [MeasureTheory.lintegral_const, measure_univ, mul_one]))
  obtain ⟨x, hx₁, hx₂⟩ := (hae.and heq).exists
  exact hx₁.ne hx₂

/-- **Uniqueness at the threshold `K + γ R = R`**: under the drift with `γ < 1` and the
minorization on `{V ≤ R}` by a nonzero `ν` with `α > 0` and `K + γ R ≤ R` (that is,
`R ≥ K / (1 - γ)`), any two invariant probability measures are equal. No contraction is used:
`π₁ - π₂` and `π₂ - π₁` are invariant (`ProbabilityTheory.Kernel.Invariant.sub`) and mutually
singular, and each of them, if nonzero, charges `{V ≤ R}` and so dominates a positive multiple of
`ν`. -/
theorem eq_of_invariant_of_drift_of_minorization [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) (hγ : γ < 1) {ν : Measure X}
    (hν : ν ≠ 0) {α R : ℝ≥0} (hα : 0 < α) (hR : K + γ * R ≤ R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) {π₁ π₂ : Measure X} [IsProbabilityMeasure π₁]
    [IsProbabilityMeasure π₂] (h₁ : Invariant P π₁) (h₂ : Invariant P π₂) : π₁ = π₂ := by
  have hdom : ∀ ξ : Measure X, IsFiniteMeasure ξ → ξ ≠ 0 → Invariant P ξ →
      0 < ξ {x | V x ≤ R} ∧ ξ {x | V x ≤ R} • α • ν ≤ ξ := fun ξ _ hξ hinv ↦
    ⟨measure_setOf_le_pos_of_invariant_of_drift hV hdrift hγ hR hξ hinv,
      (smul_smul_le_comp_of_forall_mem_smul_le fun z hz ↦ hmin z hz).trans_eq hinv.def⟩
  set θ := π₁ ⊓ π₂
  have e₁ : θ + (π₁ - π₂) = π₁ := Measure.inf_add_sub π₁ π₂
  have e₂ : θ + (π₂ - π₁) = π₂ := (congrArg (· + (π₂ - π₁)) (inf_comm π₁ π₂)).trans
    (Measure.inf_add_sub π₂ π₁)
  have : IsFiniteMeasure θ := isFiniteMeasure_of_le π₁ inf_le_left
  have hm : (π₁ - π₂) univ = (π₂ - π₁) univ := (add_right_inj_of_ne_top (measure_ne_top θ univ)).1
    (by rw [← Measure.add_apply, ← Measure.add_apply, e₁, e₂, measure_univ, measure_univ])
  by_contra hne
  have ha : π₁ - π₂ ≠ 0 := fun h ↦ hne (by
    calc π₁ = θ + (π₁ - π₂) := e₁.symm
      _ = θ + (π₂ - π₁) := by
        rw [h, Measure.measure_univ_eq_zero.1 (hm.symm.trans (by simp [h]))]
      _ = π₂ := e₂)
  have hb : π₂ - π₁ ≠ 0 := fun h ↦ ha (Measure.measure_univ_eq_zero.1 (hm.trans (by simp [h])))
  obtain ⟨ha₁, ha₂⟩ := hdom _ inferInstance ha (h₁.sub h₂)
  obtain ⟨hb₁, hb₂⟩ := hdom _ inferInstance hb (h₂.sub h₁)
  have hs := Measure.mutually_singular_measure_sub.mono ha₂ hb₂
  have k₁ := hs.measure_nullSet
  have k₂ := hs.measure_compl_nullSet
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_eq_zero, ha₁.ne',
    hb₁.ne', ENNReal.coe_eq_zero, hα.ne', false_or] at k₁ k₂
  have := measure_add_measure_compl (μ := ν) hs.measurableSet_nullSet
  rw [k₁, k₂, zero_add] at this
  exact hν (Measure.measure_univ_eq_zero.1 this.symm)

/-- **Harris' hypotheses give `ν`-irreducibility** (Mathlib's `Kernel.IsIrreducible`): under
the drift, `K + γ R < R` and the minorization `α • ν ≤ (P ^ m) x` on `{V ≤ R}`, `α > 0`, every
measurable set charged by `ν` is reached with positive probability from every state: `Pⁿ x`
charges `{V ≤ R}` for large `n` (`one_sub_le_measureReal_pow_setOf_le_of_drift`), and then
`P ^ (m + n) x ≥ (Pⁿ x {V ≤ R}) α ν`. -/
theorem isIrreducible_of_drift_of_minorization_pow [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} {α R : ℝ≥0} {m : ℕ}
    (hα : 0 < α) (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    IsIrreducible ν P := by
  refine ⟨fun A hA hνA x ↦ ?_⟩
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hLR := NNReal.coe_lt_coe.2 (NNReal.div_one_sub_lt_of_add_mul_lt hR)
  rw [NNReal.coe_div, NNReal.coe_sub hγ.le, NNReal.coe_one] at hLR
  have hR0 : (0 : ℝ≥0) < R := lt_of_le_of_lt zero_le hR
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.2 hLR) (by positivity :
    (0 : ℝ) < V x + 1)) (by exact_mod_cast hγ : (γ : ℝ) < 1)
  have h₁ := one_sub_le_measureReal_pow_setOf_le_of_drift hV hdrift hγ n x hR0
  rw [lt_div_iff₀ (by positivity)] at hn
  have hS : 0 < ((P ^ n) x) {z | V z ≤ R} := by
    refine ENNReal.toReal_pos_iff.1 (lt_of_lt_of_le ?_ h₁) |>.1
    rw [sub_pos, div_lt_one (by exact_mod_cast hR0)]
    nlinarith [(V x).coe_nonneg, pow_nonneg γ.coe_nonneg n]
  refine ⟨m + n, ?_⟩
  rw [Kernel.pow_add, Kernel.comp_apply]
  refine lt_of_lt_of_le ?_ ((smul_smul_le_comp_of_forall_mem_smul_le (P := P ^ m)
    (μ := (P ^ n) x) (S := {z | V z ≤ R}) fun z hz ↦ hmin z hz) A)
  simpa [Measure.smul_apply, hS.ne', hα.ne', hνA.ne'] using pos_iff_ne_zero.2 (by simp [hS.ne',
    hα.ne', hνA.ne'] : ((P ^ n) x) {z | V z ≤ R} * (α * ν A) ≠ 0)

/-- **Harris' theorem from a power**: if `P ^ m` has the drift and the minorization on `{V ≤ R}`
with `α > 0` and `K + γ R < R`, then `P` has exactly one invariant probability measure. -/
theorem existsUnique_invariant_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) {m : ℕ} (hdrift : ∀ x, ∫⁻ y, V y ∂((P ^ m) x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧ Invariant P π :=
  existsUnique_invariant_of_existsUnique_invariant_pow
    (existsUnique_invariant_of_drift_of_minorization hV hdrift hα hR hmin)

/-- **Harris' theorem, convergence** (Hairer–Mattingly, Theorem 1.2, with the minorization on any
sublevel set above `K / (1 - γ)`): under the drift and the minorization on `{V ≤ R}` with `α > 0`
and `K + γ R < R`, there are `C ≥ 0` and `0 ≤ ρ < 1` with
`|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ρⁿ M (1 + ∫ V ∂μ)` for the invariant law `π`, every initial law `μ`
integrating `V` and every measurable `φ` with `|φ| ≤ M (1 + V)`. -/
theorem exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ φ : X → ℝ, Measurable φ → ∀ M : ℝ, (∀ x, |φ x| ≤ M * (1 + V x)) → ∀ n : ℕ,
        |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤
          C * ρ ^ n * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hLR := NNReal.div_one_sub_lt_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos (tsub_pos_of_lt hLR)
    (by positivity : (0 : ℝ≥0) < 2 * (2 * (K / (1 - γ)) + 1))) hγ
  obtain ⟨hR', hd', hm'⟩ := drift_minorization_pow_of_add_mul_lt hV hdrift hR hmin hj
  have hγ' := NNReal.lt_one_of_add_mul_lt hR'
  have hR0 : (0 : ℝ≥0) < R := NNReal.coe_pos.1 ((NNReal.coe_nonneg _).trans_lt hLR)
  obtain ⟨β, ρ, hβ, hρ0, hρ, hP⟩ := exists_forall_abs_integral_sub_le_of_drift_of_minorization hV
    hd' (mul_pos (div_pos (tsub_pos_of_lt hLR) (mul_pos two_pos hR0)) hα) hR' hm'
  obtain ⟨C₀, hC₀, hC₀e⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ C₀ = max 1 β⁻¹ *
      (2 + β * (((K * ∑ k ∈ Finset.range (j + 1), γ ^ k : ℝ≥0) : ℝ) /
        (1 - ((γ ^ (j + 1) : ℝ≥0) : ℝ))) + β) :=
    ⟨_, mul_nonneg (zero_le_one.trans (le_max_left _ _)) (add_nonneg (add_nonneg zero_le_two
      (mul_nonneg hβ.le (div_nonneg (NNReal.coe_nonneg _) (sub_nonneg.2 (by
        exact_mod_cast hγ'.le))))) hβ.le), rfl⟩
  have hr0 : 0 < max ρ 2⁻¹ := lt_max_of_lt_right (by norm_num)
  refine ⟨C₀ * (1 + K / (1 - γ)) * (max ρ 2⁻¹)⁻¹, max ρ 2⁻¹ ^ ((j + 1 : ℕ) : ℝ)⁻¹,
    by positivity, Real.rpow_nonneg hr0.le _,
    (pow_div_le_inv_mul_rpow_inv_pow hρ0 hρ j.succ_pos 0).2,
    fun π hπ hinv μ hμ hμV φ hφ M hφM n ↦ ?_⟩
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφM x₀)) (by positivity)
  have hr := abs_integral_comp_pow_sub_integral_le_of_contraction hV hd' hγ' hβ hρ0 hP
    (hinv.pow (j + 1)) (μ := (P ^ (n % (j + 1)) : Kernel X X) ∘ₘ μ)
    (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV _) hφ hφM (n / (j + 1))
  rw [Measure.comp_assoc, ← pow_mul, ← Kernel.pow_add, Nat.div_add_mod, ← hC₀e] at hr
  have hmom := integral_comp_pow_le_of_drift hV hdrift hγ hμV (n % (j + 1))
  have hI : 0 ≤ ∫ x, (V x : ℝ) ∂μ := integral_nonneg fun _ ↦ (V _).coe_nonneg
  calc |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π|
      ≤ C₀ * ρ ^ (n / (j + 1)) * M * (1 + ∫ x, (V x : ℝ) ∂((P ^ (n % (j + 1))) ∘ₘ μ)) := hr
    _ ≤ C₀ * ((max ρ 2⁻¹)⁻¹ * (max ρ 2⁻¹ ^ ((j + 1 : ℕ) : ℝ)⁻¹) ^ n) * M *
        ((1 + K / (1 - γ)) * (1 + ∫ x, (V x : ℝ) ∂μ)) := by
        gcongr
        · exact (pow_div_le_inv_mul_rpow_inv_pow hρ0 hρ j.succ_pos n).1
        · nlinarith [mul_nonneg hL hI]
    _ = _ := by ring

/-- **Harris' theorem, convergence from a point, in the paper's form** (Hairer–Mattingly,
Theorem 1.2: `‖Pⁿ φ - π φ‖ ≤ C ρⁿ ‖φ - π φ‖` in the norm `sup |φ| / (1 + V)`): under the drift and
the minorization on `{V ≤ R}` with `α > 0` and `K + γ R < R`, there are `C` and `0 ≤ ρ < 1` with
`|∫ φ ∂(Pⁿ x) - ∫ φ ∂π| ≤ C ρⁿ M (1 + V x)` for the invariant law `π` and every measurable `φ`
with `|φ - ∫ φ ∂π| ≤ M (1 + V)`. -/
theorem exists_abs_integral_pow_sub_integral_le_of_drift_of_minorization [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    [IsProbabilityMeasure ν] {α R : ℝ≥0} (hα : 0 < α) (hR : K + γ * R < R)
    (hmin : ∀ x, V x ≤ R → α • ν ≤ P x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ φ : X → ℝ, Measurable φ → ∀ M : ℝ, (∀ x, |φ x - ∫ y, φ y ∂π| ≤ M * (1 + V x)) →
        ∀ (n : ℕ) (x : X), |∫ y, φ y ∂((P ^ n) x) - ∫ y, φ y ∂π| ≤ C * ρ ^ n * M * (1 + V x) := by
  obtain ⟨C, ρ, hC, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization hV hdrift hα hR hmin
  refine ⟨C, ρ, hC, hρ0, hρ, fun π hπ hinv φ hφ M hφM n x ↦ ?_⟩
  have hπV := lintegral_le_of_invariant_of_drift hV hdrift (NNReal.lt_one_of_add_mul_lt hR) hinv
  have hVi : ∀ μ : Measure X, ∫⁻ x, V x ∂μ ≠ ∞ → Integrable (fun x ↦ (V x : ℝ)) μ := fun μ hμ ↦ by
    simpa using integrable_toReal_of_lintegral_ne_top hV.coe_nnreal_ennreal.aemeasurable hμ
  have hφi : ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ → Integrable φ μ :=
    fun μ _ hμ ↦ ((integrable_const |∫ y, φ y ∂π|).add (((integrable_const 1).add
      (hVi μ hμ)).const_mul M) : Integrable (fun x ↦ |∫ y, φ y ∂π| + M * (1 + V x)) μ).mono'
      hφ.aestronglyMeasurable (ae_of_all _ fun z ↦
        (Real.norm_eq_abs _).trans_le (by
          simp only [Pi.add_apply]
          linarith [hφM z, abs_sub_abs_le_abs_sub (φ z) (∫ y, φ y ∂π)]))
  have hPn : ∫⁻ y, V y ∂((P ^ n) x) ≠ ∞ := lintegral_pow_ne_top_of_drift hV hdrift n x
  have hb := h π hπ hinv (Measure.dirac x) inferInstance
    (by rw [lintegral_dirac' _ hV.coe_nnreal_ennreal]; exact ENNReal.coe_ne_top)
    (fun y ↦ φ y - ∫ y, φ y ∂π) (hφ.sub_const _) M hφM n
  have hπV' : ∫⁻ x, V x ∂π ≠ ∞ := ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top
    (tsub_pos_of_lt (by exact_mod_cast NNReal.lt_one_of_add_mul_lt hR)).ne') hπV
  rw [integral_sub (hφi _ inferInstance (by simpa [Measure.dirac_bind (Kernel.measurable _)]))
    (integrable_const _), integral_sub (hφi π hπ hπV') (integrable_const _)] at hb
  simpa [Measure.dirac_bind (Kernel.measurable _),
    integral_dirac' _ _ hV.coe_nnreal_real.stronglyMeasurable] using hb

/-! ### A minorization for a power: convergence, and every sublevel set is small -/

/-- `K + γ R < R` passes to the iterated drift of `P ^ m`, `0 < m`:
`K (1 + γ + ⋯ + γ ^ (m - 1)) + γ ^ m R < R`. -/
theorem _root_.NNReal.mul_sum_pow_add_pow_mul_lt {K γ R : ℝ≥0} (hR : K + γ * R < R) {m : ℕ}
    (hm : 0 < m) : K * ∑ k ∈ Finset.range m, γ ^ k + γ ^ m * R < R := by
  have hS : (1 : ℝ) ≤ ∑ k ∈ Finset.range m, (γ : ℝ) ^ k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
    rw [Finset.sum_range_succ', pow_zero]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ ↦ by positivity)
  have hR' : (K : ℝ) + γ * R < R := by exact_mod_cast hR
  rw [← NNReal.coe_lt_coe]
  push_cast
  nlinarith [congrArg ((R : ℝ) * ·) (geom_sum_mul_neg (γ : ℝ) m), mul_lt_mul_of_pos_right
    (sub_pos.2 hR') (by linarith : (0 : ℝ) < ∑ k ∈ Finset.range m, (γ : ℝ) ^ k)]

/-- **A minorization of `P ^ m` on a sublevel set passes to `P ^ (m + 1)`**: under the drift,
`K + γ R < R` and `α • ν ≤ (P ^ m) x` on `{V ≤ R}`, Markov's inequality gives
`P x {V ≤ R} ≥ 1 - (K + γ R) / R` there, hence `((1 - (K + γ R) / R) α) • ν ≤ (P ^ (m + 1)) x`. -/
theorem smul_le_pow_add_one_of_drift_of_minorization_pow [IsMarkovKernel P] (hV : Measurable V)
    (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X} {α R : ℝ≥0} {m : ℕ}
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) (x : X) (hx : V x ≤ R) :
    ((1 - (K + γ * R) / R) * α) • ν ≤ (P ^ (m + 1)) x := by
  have hR0 : R ≠ 0 := (lt_of_le_of_lt zero_le hR).ne'
  have hC : MeasurableSet {z | V z ≤ R} := measurableSet_le hV measurable_const
  have hc : (P x) {z | V z ≤ R}ᶜ ≤ (((K + γ * R) / R : ℝ≥0) : ℝ≥0∞) := by
    calc (P x) {z | V z ≤ R}ᶜ ≤ (P x) {z | (R : ℝ≥0∞) ≤ V z} :=
          measure_mono fun z hz ↦ by
            simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hz ⊢
            exact_mod_cast hz.le
      _ ≤ (∫⁻ z, V z ∂(P x)) / R :=
          meas_ge_le_lintegral_div hV.coe_nnreal_ennreal.aemeasurable
            (by exact_mod_cast hR0) ENNReal.coe_ne_top
      _ ≤ ((γ : ℝ≥0∞) * V x + K) / R := by gcongr; exact hdrift x
      _ ≤ ((γ : ℝ≥0∞) * R + K) / R := by gcongr
      _ = (((K + γ * R) / R : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_div hR0, add_comm]; push_cast; rfl
  have hS : ((1 - (K + γ * R) / R : ℝ≥0) : ℝ≥0∞) ≤ (P x) {z | V z ≤ R} := by
    rw [ENNReal.coe_sub, ENNReal.coe_one]
    calc 1 - (((K + γ * R) / R : ℝ≥0) : ℝ≥0∞) ≤ 1 - (P x) {z | V z ≤ R}ᶜ :=
          tsub_le_tsub_left hc 1
      _ = (P x) {z | V z ≤ R} := by
          rw [prob_compl_eq_one_sub hC, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [Kernel.pow_add, Kernel.comp_apply, pow_one]
  refine le_trans (Measure.le_iff'.2 fun t ↦ ?_) (smul_smul_le_comp_of_forall_mem_smul_le
    (P := P ^ m) (μ := P x) (S := {z | V z ≤ R}) fun z hz ↦ hmin z hz)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]
  gcongr

/-- **Harris' theorem with the minorization for a power**: under the drift of `P` and the
minorization `α • ν ≤ (P ^ m) x` on `{V ≤ R}`, `α > 0`, `K + γ R < R`, there are `C ≥ 0`
and `0 ≤ ρ < 1` with `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ C ρⁿ M (1 + ∫ V ∂μ)` for every invariant law
`π`, every initial law `μ` integrating `V` and every measurable `φ` with `|φ| ≤ M (1 + V)`. -/
theorem exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization_pow
    [IsMarkovKernel P] (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K)
    {ν : Measure X} [IsProbabilityMeasure ν] {α R : ℝ≥0} {m : ℕ} (hα : 0 < α)
    (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ π : Measure X, IsProbabilityMeasure π → Invariant P π →
      ∀ μ : Measure X, IsProbabilityMeasure μ → ∫⁻ x, V x ∂μ ≠ ∞ →
      ∀ φ : X → ℝ, Measurable φ → ∀ M : ℝ, (∀ x, |φ x| ≤ M * (1 + V x)) → ∀ n : ℕ,
        |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤
          C * ρ ^ n * M * (1 + ∫ x, (V x : ℝ) ∂μ) := by
  obtain ⟨m, hm, α, hα, hmin⟩ : ∃ m, 0 < m ∧ ∃ α : ℝ≥0, 0 < α ∧ ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x :=
    ⟨m + 1, m.succ_pos, _, mul_pos (tsub_pos_of_lt ((div_lt_one (hR.trans_le' zero_le)).2 hR)) hα,
      smul_le_pow_add_one_of_drift_of_minorization_pow hV hdrift hR hmin⟩
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hL : 0 ≤ (K : ℝ) / (1 - γ) :=
    div_nonneg K.coe_nonneg (by linarith [(by exact_mod_cast hγ : (γ : ℝ) < 1)])
  obtain ⟨C₀, ρ₀, hC₀, hρ0, hρ, h⟩ :=
    exists_abs_integral_comp_pow_sub_integral_le_of_drift_of_minorization (P := P ^ m)
      (γ := γ ^ m) (K := K * ∑ k ∈ Finset.range m, γ ^ k) hV
      (fun x ↦ by simpa using lintegral_pow_le_of_drift hV hdrift m x) hα
      (NNReal.mul_sum_pow_add_pow_mul_lt hR hm) hmin
  refine ⟨C₀ * (1 + K / (1 - γ)) * (max ρ₀ 2⁻¹)⁻¹, max ρ₀ 2⁻¹ ^ (m : ℝ)⁻¹, by positivity,
    Real.rpow_nonneg (lt_max_of_lt_right (by norm_num)).le _,
    (pow_div_le_inv_mul_rpow_inv_pow hρ0 hρ hm 0).2, fun π hπ hinv μ hμ hμV φ hφ M hφM n ↦ ?_⟩
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure μ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hφM x₀)) (by positivity)
  have hr := h π hπ (hinv.pow m) ((P ^ (n % m) : Kernel X X) ∘ₘ μ) inferInstance
    (lintegral_comp_pow_ne_top_of_drift hV hdrift hμV _) φ hφ M hφM (n / m)
  rw [Measure.comp_assoc, ← pow_mul, ← Kernel.pow_add, Nat.div_add_mod] at hr
  have hmom := integral_comp_pow_le_of_drift hV hdrift hγ hμV (n % m)
  have hI : 0 ≤ ∫ x, (V x : ℝ) ∂μ := integral_nonneg fun _ ↦ (V _).coe_nonneg
  calc |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π|
      ≤ C₀ * ρ₀ ^ (n / m) * M * (1 + ∫ x, (V x : ℝ) ∂((P ^ (n % m)) ∘ₘ μ)) := hr
    _ ≤ C₀ * ((max ρ₀ 2⁻¹)⁻¹ * (max ρ₀ 2⁻¹ ^ (m : ℝ)⁻¹) ^ n) * M *
        ((1 + K / (1 - γ)) * (1 + ∫ x, (V x : ℝ) ∂μ)) := by
        gcongr
        · exact (pow_div_le_inv_mul_rpow_inv_pow hρ0 hρ hm n).1
        · nlinarith [mul_nonneg hL hI]
    _ = _ := by ring

/-- **Every sublevel set of `V` is small**: under the drift and the minorization
`α • ν ≤ (P ^ m) x` on `{V ≤ R}` with `K + γ R < R`, for every `R'` there is `j` with
`((R - K / (1 - γ)) / (2 R) * α) • ν ≤ (P ^ (m + j)) x` whenever `V x ≤ R'`. -/
theorem exists_smul_le_pow_add_of_drift_of_minorization_pow [IsMarkovKernel P]
    (hV : Measurable V) (hdrift : ∀ x, ∫⁻ y, V y ∂(P x) ≤ γ * V x + K) {ν : Measure X}
    {α R : ℝ≥0} {m : ℕ} (hR : K + γ * R < R) (hmin : ∀ x, V x ≤ R → α • ν ≤ (P ^ m) x)
    (R' : ℝ≥0) :
    ∃ j : ℕ, ∀ x, V x ≤ R' → ((R - K / (1 - γ)) / (2 * R) * α) • ν ≤ (P ^ (m + j)) x := by
  have hγ := NNReal.lt_one_of_add_mul_lt hR
  have hγr : (γ : ℝ) < 1 := by exact_mod_cast hγ
  have hLR := NNReal.div_one_sub_lt_of_add_mul_lt hR
  have hR0 : (0 : ℝ≥0) < R := NNReal.coe_pos.1 ((NNReal.coe_nonneg _).trans_lt hLR)
  have hR0r : (0 : ℝ) < R := by exact_mod_cast hR0
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, (K : ℝ) / (1 - γ) = L := ⟨_, rfl⟩
  have e₃ : ((1 - γ : ℝ≥0) : ℝ) = 1 - γ := by rw [NNReal.coe_sub hγ.le, NNReal.coe_one]
  have e₁ : ((K / (1 - γ) : ℝ≥0) : ℝ) = L := by rw [NNReal.coe_div, e₃, hLd]
  have e₂ : ((R - K / (1 - γ) : ℝ≥0) : ℝ) = R - L := by rw [NNReal.coe_sub hLR.le, e₁]
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos (tsub_pos_of_lt hLR)
    (by positivity : (0 : ℝ≥0) < 2 * (R' + 1))) hγ
  have hj' : (γ : ℝ) ^ j < (R - L) / (2 * (R' + 1)) := by
    simpa only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_one, e₂] using NNReal.coe_lt_coe.2 hj
  rw [lt_div_iff₀ (by positivity)] at hj'
  refine ⟨j, fun x hx ↦ ?_⟩
  have hx' : (V x : ℝ) ≤ R' := by exact_mod_cast hx
  have hδS : (((R - K / (1 - γ)) / (2 * R) : ℝ≥0) : ℝ≥0∞) ≤ ((P ^ j) x) {z | V z ≤ R} := by
    rw [← ofReal_measureReal, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (one_sub_le_measureReal_pow_setOf_le_of_drift hV
      hdrift hγ j x hR0))
    rw [NNReal.coe_div, e₂, NNReal.coe_mul, NNReal.coe_ofNat, hLd,
      (by field_simp; ring : ((R : ℝ) - L) / (2 * R) = 1 - (R + L) / 2 / R)]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left hx' (pow_nonneg γ.coe_nonneg j),
      pow_nonneg γ.coe_nonneg j, R'.coe_nonneg]
  rw [Kernel.pow_add, Kernel.comp_apply]
  refine le_trans (Measure.le_iff'.2 fun s ↦ ?_) (smul_smul_le_comp_of_forall_mem_smul_le
    (μ := (P ^ j) x) (S := {z | V z ≤ R}) fun z hz ↦ hmin z hz)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, mul_assoc]
  gcongr

/-! ### The hypotheses are forced; a non-degenerate instance -/

/-- **`2 K + γ R < R` is sharp for the contraction** (Hairer–Mattingly, Theorem 1.3): on `ℕ`, a
deterministic kernel with the drift `γ = 0`, `K = 1` and the minorization `dirac 1 ≤ P x` on
`{V ≤ 2}`, where `2 K + γ R = R`, contracts the weighted oscillation for no `β > 0` and no
`ρ < 1`. (The chain reaches `1` in two steps, so it is ergodic: the threshold is the one of the
one-step contraction, not of ergodicity.) -/
theorem exists_not_contraction_of_two_mul_add_mul_eq :
    ∃ (P : Kernel ℕ ℕ) (V : ℕ → ℝ≥0), IsMarkovKernel P ∧ Measurable V ∧
      (∀ x, ∫⁻ y, V y ∂(P x) ≤ (0 : ℝ≥0) * V x + (1 : ℝ≥0)) ∧
      (∀ x, V x ≤ 2 → (1 : ℝ≥0) • Measure.dirac 1 ≤ P x) ∧
      2 * (1 : ℝ≥0) + 0 * 2 = 2 ∧
      ∀ β ρ : ℝ, 0 < β → ρ < 1 → ¬ ∀ φ : ℕ → ℝ, Measurable φ → ∀ c : ℝ,
        (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
        ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y) := by
  set f : ℕ → ℕ := fun n ↦ if n ≤ 2 then 1 else 2
  set V : ℕ → ℝ≥0 := fun n ↦ if n = 0 then 0 else if n ≤ 2 then 1 else 2 + (n : ℝ≥0)⁻¹
  have hV2 : ∀ n, 2 < n → 2 < V n := fun n hn ↦ by
    simp only [V]
    split_ifs with h0 h2
    · exact absurd h0 (by omega)
    · exact absurd h2 (by omega)
    · exact lt_add_of_pos_right _ (inv_pos.2 (Nat.cast_pos.2 (by omega)))
  refine ⟨deterministic f (measurable_of_countable f), V, inferInstance, measurable_of_countable V,
    fun x ↦ ?_, fun x hx ↦ ?_, by norm_num, fun β ρ hβ hρ hP ↦ ?_⟩
  · rw [deterministic_apply, lintegral_dirac]
    by_cases hx : x ≤ 2 <;> simp [f, V, hx]
  · rw [deterministic_apply, one_smul]
    simp [f, (by by_contra h; exact absurd hx (not_le.2 (hV2 x (by omega))) : x ≤ 2)]
  · obtain ⟨n, hn⟩ := exists_nat_gt (β / ((1 - ρ) * (2 + 2 * β)) + 3)
    have hD : 0 < (1 - ρ) * (2 + 2 * β) := by nlinarith
    have hn3 : (3 : ℝ) < n := by linarith [div_pos hβ hD]
    have hβn : β * (n : ℝ)⁻¹ < (1 - ρ) * (2 + 2 * β) := by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith)]
      nlinarith [(div_lt_iff₀ hD).1 (by linarith : β / ((1 - ρ) * (2 + 2 * β)) < n)]
    set φ : ℕ → ℝ := fun z ↦ if z = 2 then 1 + β * V z else -(1 + β * V z)
    have hn' : ¬ n ≤ 2 := by exact_mod_cast (by linarith : ¬ (n : ℝ) ≤ 2)
    have hn0 : n ≠ 0 := by omega
    have e0 : ∫ z, φ z ∂(deterministic f (measurable_of_countable f) 0) = -(1 + β) := by
      simp [φ, f, V, deterministic_apply, integral_dirac]
    have en : ∫ z, φ z ∂(deterministic f (measurable_of_countable f) n) = 1 + β := by
      simp [φ, f, V, deterministic_apply, integral_dirac, hn']
    have eVn : (V n : ℝ) = 2 + (n : ℝ)⁻¹ := by simp [V, hn', hn0]
    have h := hP φ (measurable_of_countable _) 1 (fun x y ↦ by
      simp only [φ]
      split_ifs <;> rw [abs_le] <;> constructor <;>
        linarith [mul_nonneg hβ.le (V x).coe_nonneg, mul_nonneg hβ.le (V y).coe_nonneg]) 0 n
    rw [e0, en, eVn] at h
    have h' := (abs_le.1 h).1
    simp only [V, ↓reduceIte, NNReal.coe_zero, mul_zero, add_zero] at h'
    have hβn' : 0 ≤ β * (n : ℝ)⁻¹ := by positivity
    by_cases hρ0 : 0 ≤ ρ
    · nlinarith [mul_le_mul_of_nonneg_right hρ.le hβn']
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hρ0) (le_refl (0 : ℝ))]

/-- **`2 K + γ R < R` is sharp for Theorem 1.3 on laws**: on the chain of
`ProbabilityTheory.Kernel.exists_not_contraction_of_two_mul_add_mul_eq` (`γ = 0`, `K = 1`,
`R = 2`), the weighted total variation between laws contracts for no `β > 0` and no `ρ < 1`. -/
theorem exists_not_lintegral_totalVariation_comp_le_of_two_mul_add_mul_eq :
    ∃ (P : Kernel ℕ ℕ) (_ : IsMarkovKernel P) (V : ℕ → ℝ≥0), Measurable V ∧
      (∀ x, ∫⁻ y, V y ∂(P x) ≤ (0 : ℝ≥0) * V x + (1 : ℝ≥0)) ∧
      (∀ x, V x ≤ 2 → (1 : ℝ≥0) • Measure.dirac 1 ≤ P x) ∧ 2 * (1 : ℝ≥0) + 0 * 2 = 2 ∧
      ∀ β ρ : ℝ, 0 < β → ρ < 1 → ¬ ∀ (μ₁ μ₂ : Measure ℕ) [IsProbabilityMeasure μ₁]
        [IsProbabilityMeasure μ₂], ∫⁻ x, ENNReal.ofReal (1 + β * V x)
            ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
          ENNReal.ofReal ρ * ∫⁻ x, ENNReal.ofReal (1 + β * V x)
            ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  obtain ⟨P, V, hP, hV, hd, hm, he, hnc⟩ := exists_not_contraction_of_two_mul_add_mul_eq
  refine ⟨P, hP, V, hV, hd, hm, he, fun β ρ hβ hρ h ↦
    hnc β (max ρ 0) hβ (max_lt hρ one_pos) ?_⟩
  have hc := forall_abs_integral_sub_le_of_lintegral_totalVariation_le (β := β.toNNReal)
    (ρ := (max ρ 0).toNNReal) hV hd fun x y ↦ by
      rw [Real.coe_toNNReal _ hβ.le]
      exact (h _ _).trans (by gcongr; exact ENNReal.ofReal_le_ofReal (le_max_left ρ 0))
  simpa only [Real.coe_toNNReal _ hβ.le, Real.coe_toNNReal _ (le_max_right ρ 0)] using hc

/-- **At `K + γ R = R` existence fails**: on `ℕ`, the shift `k ↦ k + 1` with `V k = 2 + (1/2)ᵏ`
has the drift `γ = 1/2`, `K = 1` with equality, `{V ≤ 2} = ∅` (the minorization holds with
`α = 1`, `ν = dirac 0`), `K + γ R = R` at `R = 2`, and no invariant probability measure. -/
theorem exists_not_exists_invariant_of_add_mul_eq :
    ∃ (P : Kernel ℕ ℕ) (V : ℕ → ℝ≥0), IsMarkovKernel P ∧ Measurable V ∧
      (∀ x, ∫⁻ y, V y ∂(P x) ≤ (1 / 2 : ℝ≥0) * V x + (1 : ℝ≥0)) ∧
      (∀ x, V x ≤ 2 → (1 : ℝ≥0) • Measure.dirac 0 ≤ P x) ∧ (1 : ℝ≥0) + 1 / 2 * 2 = 2 ∧
      ¬ ∃ π : Measure ℕ, IsProbabilityMeasure π ∧ Invariant P π := by
  set f : ℕ → ℕ := fun k ↦ k + 1
  set V : ℕ → ℝ≥0 := fun k ↦ 2 + (1 / 2) ^ k
  refine ⟨deterministic f (measurable_of_countable f), V, inferInstance, measurable_of_countable V,
    fun x ↦ ?_, fun x hx ↦ ?_, by norm_num, ?_⟩
  · rw [deterministic_apply, lintegral_dirac]
    simp only [V, f]
    exact_mod_cast (le_of_eq (by rw [mul_add, ← pow_succ']; norm_num; ring) :
      (2 + (1 / 2 : ℝ≥0) ^ (x + 1) ≤ 1 / 2 * (2 + (1 / 2) ^ x) + 1))
  · exact absurd hx (not_le.2 (lt_add_of_pos_right _ (by positivity)))
  · rintro ⟨π, hπ, hinv⟩
    have hmap : π.map f = π := by
      rw [← Measure.deterministic_comp_eq_map (measurable_of_countable f)]
      exact hinv
    have h0 : ∀ n, π {n} = 0 := by
      intro n
      induction n with
      | zero =>
        rw [← hmap, Measure.map_apply (measurable_of_countable f) (measurableSet_singleton 0)]
        convert measure_empty (μ := π)
        ext k
        simp [f]
      | succ n ih =>
        rw [← hmap, Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _)]
        convert ih using 2
        ext k
        simp [f]
    exact IsProbabilityMeasure.ne_zero π (Measure.ext_of_singleton fun n ↦ by simp [h0 n])

/-- **The regime `K + γ R < R ≤ 2 K + γ R` is inhabited**: the chain of
`ProbabilityTheory.Kernel.exists_not_contraction_of_two_mul_add_mul_eq` (`γ = 0`, `K = 1`,
`R = 2`, so `K + γ R = 1 < 2 = 2 K + γ R`) has the drift and the minorization, contracts the
weighted oscillation for no `β > 0`, `ρ < 1`, and has exactly one invariant law. -/
theorem exists_not_contraction_and_existsUnique_invariant :
    ∃ (P : Kernel ℕ ℕ) (V : ℕ → ℝ≥0), IsMarkovKernel P ∧
      (∀ x, ∫⁻ y, V y ∂(P x) ≤ (0 : ℝ≥0) * V x + (1 : ℝ≥0)) ∧
      (∀ x, V x ≤ 2 → (1 : ℝ≥0) • Measure.dirac 1 ≤ P x) ∧
      (∀ β ρ : ℝ, 0 < β → ρ < 1 → ¬ ∀ φ : ℕ → ℝ, Measurable φ → ∀ c : ℝ,
        (∀ x y, |φ x - φ y| ≤ c * (2 + β * V x + β * V y)) →
        ∀ x y, |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ ρ * c * (2 + β * V x + β * V y)) ∧
      ∃! π : Measure ℕ, IsProbabilityMeasure π ∧ Invariant P π := by
  obtain ⟨P, V, hP, hV, hd, hm, -, hnc⟩ := exists_not_contraction_of_two_mul_add_mul_eq
  exact ⟨P, V, hP, hd, hm, hnc, existsUnique_invariant_of_drift_of_minorization
    (ν := Measure.dirac 1) hV hd one_pos (by norm_num) hm⟩

/-- **At `K + γ R = R` convergence fails**: on `ℕ`, the deterministic kernel fixing `0` and moving
`k ≥ 1` to `k + 1`, with `V k = 2 + (1/2)ᵏ` for `k ≥ 1`, has the drift `γ = 1/2`, `K = 1` and the
minorization `dirac 0 ≤ P x` on `{V ≤ 2} = {0}`, where `K + γ R = R`; `dirac 0` is invariant and
`Pⁿ 1` never charges `0`. -/
theorem exists_not_tendsto_of_add_mul_eq :
    ∃ (P : Kernel ℕ ℕ) (V : ℕ → ℝ≥0), IsMarkovKernel P ∧ Measurable V ∧
      (∀ x, ∫⁻ y, V y ∂(P x) ≤ (1 / 2 : ℝ≥0) * V x + (1 : ℝ≥0)) ∧
      (∀ x, V x ≤ 2 → (1 : ℝ≥0) • Measure.dirac 0 ≤ P x) ∧ (1 : ℝ≥0) + 1 / 2 * 2 = 2 ∧
      Invariant P (Measure.dirac 0) ∧ ∀ n, (P ^ n) 1 {0} = 0 := by
  set f : ℕ → ℕ := fun k ↦ if k = 0 then 0 else k + 1
  set V : ℕ → ℝ≥0 := fun k ↦ if k = 0 then 0 else 2 + (1 / 2) ^ k
  have hf : ∀ n, f^[n] 1 = n + 1 := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [f]
  refine ⟨deterministic f (measurable_of_countable f), V, inferInstance, measurable_of_countable V,
    fun x ↦ ?_, fun x hx ↦ ?_, by norm_num, ?_, fun n ↦ ?_⟩
  · rw [deterministic_apply, lintegral_dirac]
    rcases x with _ | k
    · simp [f, V]
    · simp only [f, V, Nat.add_one_ne_zero, ↓reduceIte]
      exact_mod_cast (le_of_eq (by rw [mul_add, ← pow_succ']; norm_num; ring) :
        (2 + (1 / 2 : ℝ≥0) ^ (k + 1 + 1) ≤ 1 / 2 * (2 + (1 / 2) ^ (k + 1)) + 1))
  · rcases x with _ | k
    · simp [f, deterministic_apply]
    · refine absurd hx (not_le.2 ?_)
      simp only [V, Nat.add_one_ne_zero, ↓reduceIte]
      exact lt_add_of_pos_right _ (by positivity)
  · simp [Invariant, Measure.dirac_bind (Kernel.measurable _), deterministic_apply, f]
  · simp [deterministic_pow, deterministic_apply, hf n]

/-- **Two absorbing states**: for every `γ ≤ 1`, the identity kernel of `Bool` with
`V = 1` at `true`, `0` at `false`, satisfies the drift with `K = 1 - γ` and the minorization
`dirac false ≤ P x` on `{V ≤ R}` for every `R < 1`, and has two invariant laws. Here
`R < 1 = K / (1 - γ)`: the minorization on a sublevel set below `K / (1 - γ)` gives nothing, and
at `γ = 1`, `K = 0`, where `K + γ R = R` for every `R`, uniqueness fails. -/
theorem drift_and_minorization_id_bool {γ : ℝ≥0} (hγ : γ ≤ 1) {R : ℝ≥0} (hR : R < 1) :
    (∀ x, ∫⁻ y, (if y then (1 : ℝ≥0) else 0) ∂((Kernel.id : Kernel Bool Bool) x) ≤
      γ * (if x then (1 : ℝ≥0) else 0) + (1 - γ : ℝ≥0)) ∧
    (∀ x, (if x then (1 : ℝ≥0) else 0) ≤ R →
      (1 : ℝ≥0) • Measure.dirac false ≤ (Kernel.id : Kernel Bool Bool) x) ∧
    ¬ ∃! π : Measure Bool, IsProbabilityMeasure π ∧ Invariant (Kernel.id : Kernel Bool Bool) π := by
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_, not_existsUnique_invariant_id_bool⟩
  · rw [Kernel.id_apply, lintegral_dirac]
    cases x
    · simp
    · simp only [ite_true, ENNReal.coe_one, mul_one]
      rw [← ENNReal.coe_add, add_tsub_cancel_of_le hγ]
      simp
  · cases x
    · simp [Kernel.id_apply]
    · exact absurd hx (not_le.2 (by simpa using hR))

/-- The chain on `ℕ` that halves `n ≥ 2` and from `{0, 1}` moves to `0` or `1` with probability
`1/2` each is Markov, has the drift `∫⁻ V ∂(P x) ≤ (1/2) V x + 1/2` for `V n = n`, and has the
minorization `(1/2) • dirac 1 ≤ P x` on `{V ≤ 3}` (`2 K + γ R = 5/2 < 3`). No common component of
all `P x` exists (`P 4 = dirac 2`, `P 6 = dirac 3`): Harris' theorem applies, Doeblin's does not. -/
theorem drift_and_minorization_of_halving {P : Kernel ℕ ℕ} (hP : ∀ n, P n = if n ≤ 1 then
    (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1 else Measure.dirac (n / 2)) :
    IsMarkovKernel P ∧
      (∀ x, ∫⁻ y, ((y : ℝ≥0) : ℝ≥0∞) ∂(P x) ≤ (1 / 2 : ℝ≥0) * (x : ℝ≥0) + (1 / 2 : ℝ≥0)) ∧
      ∀ x : ℕ, (x : ℝ≥0) ≤ 3 → (1 / 2 : ℝ≥0) • Measure.dirac 1 ≤ P x := by
  refine ⟨⟨fun n ↦ ⟨?_⟩⟩, fun x ↦ ?_, fun x hx ↦ ?_⟩ <;> rw [hP]
  · split_ifs
    · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ]
      rw [← add_smul, add_halves, one_smul]
    · exact measure_univ
  · split_ifs with h
    · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
        lintegral_dirac]
      interval_cases x <;> norm_num [ENNReal.smul_def]
    · rw [lintegral_dirac]
      have h2 : ((x / 2 : ℕ) : ℝ≥0) ≤ 1 / 2 * x + 1 / 2 :=
        (Nat.cast_div_le.trans_eq (by rw [Nat.cast_ofNat, one_div, div_eq_inv_mul])).trans
          le_self_add
      exact_mod_cast h2
  · have hx3 : x ≤ 3 := by exact_mod_cast hx
    split_ifs with h
    · exact Measure.le_add_left le_rfl
    · rw [(by omega : x / 2 = 1)]
      refine Measure.le_iff'.2 fun s ↦ ?_
      rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      exact mul_le_of_le_one_left (by positivity) (by norm_num)

/-- A non-degenerate instance of Harris' theorem on `ℕ` with `V n = n`: the chain of
`ProbabilityTheory.Kernel.drift_and_minorization_of_halving` has exactly one invariant law. -/
example : ∃! π : Measure ℕ, IsProbabilityMeasure π ∧ Invariant (ofFunOfCountable fun n : ℕ ↦
    if n ≤ 1 then (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1
    else Measure.dirac (n / 2)) π := by
  obtain ⟨_, hd, hm⟩ := drift_and_minorization_of_halving (P := ofFunOfCountable fun n : ℕ ↦
    if n ≤ 1 then (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1
    else Measure.dirac (n / 2)) fun n ↦ rfl
  exact existsUnique_invariant_of_drift_of_minorization (V := fun n ↦ (n : ℝ≥0))
    (ν := Measure.dirac 1) (measurable_of_countable _) hd (by norm_num) (by norm_num) hm

/-- **Theorem 1.3 against the bound through the product coupling**, the initial laws: on `ℕ` with
`V n = n` and `β = 1/4`, for `μ₁ = dirac 0` and `μ₂ = (1 - ε) • dirac 0 + ε • dirac 4`,
`ρ_β(μ₁, μ₂) = 3 ε`, while `2 + β ∫ V ∂μ₁ + β ∫ V ∂μ₂ = 2 + ε`. On the chain of
`ProbabilityTheory.Kernel.drift_and_minorization_of_halving`, Theorem 1.3 bounds
`ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂)` by `(21/22) 3 ε` (`…lintegral_totalVariation_comp_le_of_halving`; the
value is `21 ε / 8`, `…integral_totalVariation_comp_of_halving`), while the right side of the bound
through the product coupling (`…abs_integral_comp_pow_sub_le` with `n = 1`, `c = 1`),
`(21/22) (2 + ε)`, does not vanish as `ε → 0`. -/
theorem integral_totalVariation_dirac_zero_four {ε : ℝ≥0} (hε : ε ≤ 1) :
    ∫ x : ℕ, (1 + 1 / 4 * (x : ℝ)) ∂((Measure.dirac (0 : ℕ)).toSignedMeasure -
      ((1 - ε) • Measure.dirac 0 + ε • Measure.dirac 4).toSignedMeasure).totalVariation = 3 * ε ∧
    2 + 1 / 4 * ∫ x : ℕ, (x : ℝ) ∂(Measure.dirac 0) +
      1 / 4 * ∫ x : ℕ, (x : ℝ) ∂((1 - ε) • Measure.dirac 0 + ε • Measure.dirac 4) = 2 + ε := by
  have hi : ∀ a : ℕ, Integrable (fun x : ℕ ↦ 1 + 1 / 4 * (x : ℝ)) (Measure.dirac a) :=
    fun a ↦ integrable_dirac (by simp)
  have e₀ : ((Measure.dirac (0 : ℕ)).toSignedMeasure -
      ((1 - ε) • Measure.dirac 0 + ε • Measure.dirac 4).toSignedMeasure).totalVariation =
        ε • Measure.dirac 0 + ε • Measure.dirac (4 : ℕ) := by
    rw [Measure.toSignedMeasure_sub_eq_of_add_eq (θ := (1 - ε) • Measure.dirac 0)
      (ν₁ := ε • Measure.dirac 0) (ν₂ := ε • Measure.dirac 4)
      (by rw [← add_smul, tsub_add_cancel_of_le hε, one_smul]) rfl,
      Measure.totalVariation_toSignedMeasure_sub_of_mutuallySingular
        ((((mutuallySingular_dirac_dirac_iff.2 (by norm_num)).smul_nnreal ε).symm.smul_nnreal
          ε).symm)]
  refine ⟨?_, ?_⟩
  · rw [e₀, integral_add_measure (hi 0).smul_measure_nnreal (hi 4).smul_measure_nnreal,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac, integral_dirac]
    norm_num [NNReal.smul_def]
    ring
  · rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure_nnreal)
      ((integrable_dirac (by simp)).smul_measure_nnreal), integral_smul_nnreal_measure,
      integral_smul_nnreal_measure, integral_dirac, integral_dirac]
    norm_num [NNReal.smul_def]
    ring

/-- **Theorem 1.3 against the bound through the product coupling**, the laws after one step: on the
chain of `ProbabilityTheory.Kernel.drift_and_minorization_of_halving`, for `μ₁ = dirac 0` and
`μ₂ = (1 - ε) • dirac 0 + ε • dirac 4`, `ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) = 21 ε / 8` (`V n = n`,
`β = 1/4`). -/
theorem integral_totalVariation_comp_of_halving {P : Kernel ℕ ℕ} [IsMarkovKernel P]
    (hP : ∀ n, P n = if n ≤ 1 then (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) •
      Measure.dirac 1 else Measure.dirac (n / 2)) {ε : ℝ≥0} (hε : ε ≤ 1) :
    ∫ x : ℕ, (1 + 1 / 4 * (x : ℝ)) ∂((P ∘ₘ Measure.dirac 0).toSignedMeasure -
      (P ∘ₘ ((1 - ε) • Measure.dirac 0 + ε • Measure.dirac 4)).toSignedMeasure).totalVariation =
        21 / 8 * ε := by
  have hi : ∀ a : ℕ, Integrable (fun x : ℕ ↦ 1 + 1 / 4 * (x : ℝ)) (Measure.dirac a) :=
    fun a ↦ integrable_dirac (by simp)
  have hm : (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1 ⟂ₘ
      Measure.dirac (2 : ℕ) :=
    ((mutuallySingular_dirac_dirac_iff.2 (by norm_num)).smul_nnreal _).add_left
      ((mutuallySingular_dirac_dirac_iff.2 (by norm_num)).smul_nnreal _)
  have e₁ : ((P ∘ₘ Measure.dirac 0).toSignedMeasure -
      (P ∘ₘ ((1 - ε) • Measure.dirac 0 + ε • Measure.dirac 4)).toSignedMeasure).totalVariation =
        ε • ((1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1) +
          ε • Measure.dirac (2 : ℕ) := by
    rw [Measure.toSignedMeasure_sub_eq_of_add_eq
      (θ := (1 - ε) • ((1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1))
      (ν₁ := ε • ((1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 1))
      (ν₂ := ε • Measure.dirac 2), Measure.totalVariation_toSignedMeasure_sub_of_mutuallySingular
        (((hm.smul_nnreal ε).symm.smul_nnreal ε).symm)]
    · rw [← add_smul, tsub_add_cancel_of_le hε, one_smul, Measure.dirac_bind (Kernel.measurable _),
        hP]
      simp
    · ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      simp [lintegral_add_measure, hP]
  rw [e₁, integral_add_measure (((hi 0).smul_measure_nnreal).add_measure
    (hi 1).smul_measure_nnreal).smul_measure_nnreal (hi 2).smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_add_measure (hi 0).smul_measure_nnreal
    (hi 1).smul_measure_nnreal, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac, integral_dirac]
  norm_num [NNReal.smul_def]
  ring

/-- **Theorem 1.3 on the chain of `ProbabilityTheory.Kernel.drift_and_minorization_of_halving`**
(`V n = n`, `γ = K = 1/2`, `R = 3`, `α = 1/2`; with `α₀ = 1/8`, `β = α₀ / K = 1/4` and
`ᾱ = 21/22`): `ρ_β(P ∘ₘ μ₁, P ∘ₘ μ₂) ≤ (21/22) ρ_β(μ₁, μ₂)` for all probability measures. -/
theorem lintegral_totalVariation_comp_le_of_halving {P : Kernel ℕ ℕ} [IsMarkovKernel P]
    (hP : ∀ n, P n = if n ≤ 1 then (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) •
      Measure.dirac 1 else Measure.dirac (n / 2)) (μ₁ μ₂ : Measure ℕ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] :
    ∫⁻ x : ℕ, ENNReal.ofReal (1 + 1 / 4 * (x : ℝ))
        ∂((P ∘ₘ μ₁).toSignedMeasure - (P ∘ₘ μ₂).toSignedMeasure).totalVariation ≤
      ENNReal.ofReal (21 / 22) * ∫⁻ x : ℕ, ENNReal.ofReal (1 + 1 / 4 * (x : ℝ))
        ∂(μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation := by
  obtain ⟨_, hd, hmin⟩ := drift_and_minorization_of_halving hP
  have h := (lintegral_totalVariation_comp_le_max_of_drift_of_minorization
    (V := fun n : ℕ ↦ (n : ℝ≥0)) (R := 3) (ν := Measure.dirac 1) (measurable_of_countable _) hd
    hmin (by norm_num) (by norm_num) (α₀ := 1 / 8) (by norm_num) (by norm_num)).2 μ₁ μ₂
  have h₃ : (1 : ℝ) / 8 / ((1 / 2 : ℝ≥0) : ℝ) = 1 / 4 := by norm_num
  simp only [h₃, NNReal.coe_natCast] at h
  refine h.trans_eq ?_
  congr 2
  norm_num

end ProbabilityTheory.Kernel
