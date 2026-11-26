/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Composition.CompMap
public import MCMC.ToMathlib.Probability.Kernel.Contraction
public import Mathlib.Probability.Kernel.Irreducible

/-!
# Doeblin's theorem for Markov kernels on a measurable space

A Markov kernel `P` on a measurable space `X` satisfies Doeblin's condition when
`α • ν ≤ P x` for every `x`, for a probability measure `ν` and `α > 0`.

* `ProbabilityTheory.Kernel.abs_integral_sub_integral_le_of_forall_smul_le`: the oscillation of
  `x ↦ ∫ φ ∂(P x)` is at most `1 - α` times that of `φ`, i.e. Dobrushin's coefficient of `P` is
  at most `1 - α`.
* `ProbabilityTheory.Kernel.existsUnique_invariant_of_forall_smul_le`: `P` has exactly one
  invariant probability measure `π`.
* `ProbabilityTheory.Kernel.abs_integral_comp_pow_sub_integral_le_of_forall_smul_le` and
  `…abs_measureReal_comp_pow_sub_le_of_forall_smul_le`: from every initial law `μ`,
  `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ (1 - α)ⁿ c` when `|φ x - φ y| ≤ c`, and
  `|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - α)ⁿ` for every measurable `s` (total variation).
* `…existsUnique_invariant_of_forall_smul_le_pow`,
  `…abs_integral_comp_pow_sub_integral_le_of_forall_smul_le_pow` and
  `…abs_measureReal_comp_pow_sub_le_of_forall_smul_le_pow`: Doeblin's condition for a power
  `P ^ m` gives exactly one invariant law of `P`,
  `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ (1 - α) ^ (n / m) c` when `|φ x - φ y| ≤ c`, and
  `|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - α) ^ (n / m)` (natural division; informative for `0 < m`); and
  `P` is irreducible with respect to `ν` (`…isIrreducible_of_forall_smul_le_pow`, Mathlib's
  `ProbabilityTheory.Kernel.IsIrreducible`).

The hypotheses are forced: on `Bool`, the identity kernel (two absorbing states) has two invariant
laws (`ProbabilityTheory.Kernel.Invariant` of `dirac true` and of `dirac false`); it satisfies
Doeblin's condition with `α = 0` and with no `α > 0`
(`ProbabilityTheory.Kernel.not_existsUnique_invariant_id_bool`,
`…not_forall_smul_le_id_bool`). Periodicity is excluded by Doeblin's condition for any power `P ^ m`
(the conclusion above holds along every `n`): the flip of `Bool` does not converge from `false`
(`…not_tendsto_pow_flip_bool`) and no power of it satisfies the condition
(`…not_forall_smul_le_pow_flip_bool`). A non-degenerate instance (`α = 1/2`, a kernel neither
constant nor deterministic) is compiled at the end of the file.

Literature: M. Hairer and J. C. Mattingly (*Yet another look at Harris' ergodic theorem for Markov
chains*, arXiv:0810.2777) call their minorization "reminiscent of Doeblin's condition"; the bound
here is the case `V = 0` of the second case of the proof of their Theorem 3.1. Doeblin's and
Dobrushin's papers were not read.

Literature on drift conditions and prior formalizations. S. P. Meyn, R. L. Tweedie, *Markov
Chains and Stochastic Stability* (1993 edition), Theorem 15.0.1 (iii) (p. 358) and Lemma 15.2.8
(p. 374): for a ψ-irreducible aperiodic chain, a drift `ΔV ≤ -βV + b 1_C` to a petite set gives
`V`-geometric convergence; from `PV ≤ γV + K` the drift is strict outside `{V ≤ R}` for every
`R > K / (1 - γ)` (an arithmetic remark, not a quotation; their proof of Lemma 15.2.8 takes the
level `2L / (1 - λ)`). P. H. Baxendale,
*Ann. Appl. Probab.* 15 (2005) 700–738, Theorem 1.1 with (A1)–(A3): the same conclusion with
explicit constants, under the extra hypothesis `ν(C) > 0`. So existence, uniqueness and geometric
convergence at `R > K / (1 - γ)` are implicit in the literature once irreducibility and
aperiodicity are checked; not found stated there: a self-contained statement with no aperiodicity
hypothesis, uniqueness at `R = K / (1 - γ)`, and counterexamples at and below the threshold. The
factor `2` in Hairer–Mattingly is needed for their one-step contraction. Not read: the published
version of Hairer–Mattingly; Douc, Moulines, Priouret, Soulier, *Markov Chains* (2018).

Prior formalizations (read as source): `or4nge19/markov-semigroups`,
`Convergence/Doeblin.lean` (M. R. Douglas), gives `(1 - ε)ⁿ` when the minorizing measure is the
invariant law and that law is assumed. Finite-state Doeblin is in this library. Countable-state
convergence without a rate is in Isabelle's Archive of Formal Proofs (`Markov_Models`).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {P : Kernel X X}

/-- **Doeblin's contraction** (Dobrushin's coefficient at most `1 - α`): if `α • ν ≤ P x` and
`α • ν ≤ P y`, then `|∫ φ ∂(P x) - ∫ φ ∂(P y)| ≤ (1 - α) c` whenever `|φ u - φ v| ≤ c`. -/
theorem abs_integral_sub_integral_le_of_forall_smul_le [IsMarkovKernel P] {ν : Measure X}
    [IsProbabilityMeasure ν] {α : ℝ≥0} {x y : X} (hx : α • ν ≤ P x) (hy : α • ν ≤ P y)
    {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ} (hφc : ∀ u v, |φ u - φ v| ≤ c) :
    |∫ z, φ z ∂(P x) - ∫ z, φ z ∂(P y)| ≤ (1 - α) * c := by
  have h := abs_integral_sub_integral_le_of_forall_abs_sub_le hx hy (V := fun _ ↦ 0)
    measurable_const (by simp) (by simp) le_rfl hφ (c := c / 2) fun u v ↦ by
      simpa using hφc u v
  simp only [NNReal.coe_zero, mul_zero, add_zero, integral_zero, measureReal_nnreal_smul_apply,
    probReal_univ, mul_one] at h
  linarith

/-- **Doeblin's theorem, existence and uniqueness**: under Doeblin's condition `α • ν ≤ P x` for
all `x`, `α > 0`, the kernel has exactly one invariant probability measure. -/
theorem existsUnique_invariant_of_forall_smul_le [IsMarkovKernel P]
    {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} (hα : 0 < α) (hmin : ∀ x, α • ν ≤ P x) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧ Invariant P π := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure ν
  have : Nonempty X := ⟨x₀⟩
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast Measure.le_one_of_smul_le (hmin x₀)
  obtain ⟨π, hπ, hinv, -⟩ := exists_invariant_of_contraction (V := fun _ ↦ 0) (γ := 0) (K := 0)
    (β := 0) (ρ := 1 - α) measurable_const (fun x ↦ by simp) zero_lt_one le_rfl
    (by linarith) (by linarith [NNReal.coe_pos.2 hα])
    fun φ hφ c hφc x y ↦ by
      linarith [abs_integral_sub_integral_le_of_forall_smul_le (hmin x) (hmin y) hφ (c := 2 * c)
        fun u v ↦ by linarith [hφc u v]]
  refine ⟨π, ⟨hπ, hinv⟩, fun π₁ ⟨_, h₁⟩ ↦ eq_of_invariant_of_contraction (V := fun _ ↦ 0)
    (γ := 0) (K := 0) (β := 0) (ρ := 1 - α) measurable_const (fun x ↦ by simp) le_rfl
    (by linarith) (by linarith [NNReal.coe_pos.2 hα]) (fun φ hφ c hφc x y ↦ by
      linarith [abs_integral_sub_integral_le_of_forall_smul_le (hmin x) (hmin y) hφ (c := 2 * c)
        fun u v ↦ by linarith [hφc u v]]) hinv (by simp) h₁⟩

/-- **Doeblin's theorem, convergence**: under Doeblin's condition, from every initial law `μ`,
`|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ (1 - α)ⁿ c` for the invariant law `π` and every measurable `φ`
with `|φ x - φ y| ≤ c`. -/
theorem abs_integral_comp_pow_sub_integral_le_of_forall_smul_le [IsMarkovKernel P]
    {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} (hmin : ∀ x, α • ν ≤ P x)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X}
    [IsProbabilityMeasure μ] {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ}
    (hφc : ∀ x y, |φ x - φ y| ≤ c) (n : ℕ) :
    |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤ (1 - α) ^ n * c := by
  have h := abs_integral_comp_pow_sub_le (V := fun _ ↦ 0) (γ := 0) (K := 0) (β := 0)
    (ρ := 1 - α) measurable_const (fun x ↦ by simp) le_rfl (fun ψ hψ c hψc x y ↦ by
      linarith [abs_integral_sub_integral_le_of_forall_smul_le (hmin x) (hmin y) hψ (c := 2 * c)
        fun u v ↦ by linarith [hψc u v]]) hφ (c := c / 2) (fun x y ↦ by linarith [hφc x y])
    (μ₁ := μ) (μ₂ := π) (by simp) (by simp) n
  rw [(hπ.pow n).def] at h
  linarith

/-- **Doeblin's theorem in total variation**: under Doeblin's condition, from every initial law
`μ`, `|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - α)ⁿ` for every measurable set `s`. -/
theorem abs_measureReal_comp_pow_sub_le_of_forall_smul_le [IsMarkovKernel P] {ν : Measure X}
    [IsProbabilityMeasure ν] {α : ℝ≥0} (hmin : ∀ x, α • ν ≤ P x) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X} [IsProbabilityMeasure μ]
    (n : ℕ) {s : Set X} (hs : MeasurableSet s) :
    |((P ^ n) ∘ₘ μ).real s - π.real s| ≤ (1 - α) ^ n := by
  simpa [integral_indicator_one hs] using abs_integral_comp_pow_sub_integral_le_of_forall_smul_le
    hmin hπ (μ := μ) (measurable_one.indicator hs) (abs_indicator_one_sub_indicator_one_le s) n

/-- **Doeblin's condition for a power gives `ν`-irreducibility** (Mathlib's
`Kernel.IsIrreducible`): if `α • ν ≤ (P ^ m) x` for every `x`, `α > 0`, every measurable set
charged by `ν` is reached at time `m` with probability at least `α ν A > 0`. -/
theorem isIrreducible_of_forall_smul_le_pow {ν : Measure X} {α : ℝ≥0} (hα : 0 < α) {m : ℕ}
    (hmin : ∀ x, α • ν ≤ (P ^ m) x) : IsIrreducible ν P :=
  ⟨fun A _ hνA x ↦ ⟨m, lt_of_lt_of_le (by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_pos (by exact_mod_cast hα.ne') hνA.ne') (hmin x A)⟩⟩

/-- **Doeblin's condition for a power**: if `α • ν ≤ (P ^ m) x` for every `x`, `α > 0`, then `P`
has exactly one invariant probability measure. -/
theorem existsUnique_invariant_of_forall_smul_le_pow [IsMarkovKernel P]
    {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} (hα : 0 < α) {m : ℕ}
    (hmin : ∀ x, α • ν ≤ (P ^ m) x) :
    ∃! π : Measure X, IsProbabilityMeasure π ∧ Invariant P π :=
  existsUnique_invariant_of_existsUnique_invariant_pow
    (existsUnique_invariant_of_forall_smul_le hα hmin)

/-- **Doeblin's condition for a power, test functions**: if `α • ν ≤ (P ^ m) x` for every `x`,
then from every initial law `μ`, `|∫ φ ∂(Pⁿ ∘ₘ μ) - ∫ φ ∂π| ≤ (1 - α) ^ (n / m) c` for the
invariant law `π` and every measurable `φ` with `|φ x - φ y| ≤ c`. -/
theorem abs_integral_comp_pow_sub_integral_le_of_forall_smul_le_pow [IsMarkovKernel P]
    {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} {m : ℕ} (hmin : ∀ x, α • ν ≤ (P ^ m) x)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X}
    [IsProbabilityMeasure μ] {φ : X → ℝ} (hφ : Measurable φ) {c : ℝ}
    (hφc : ∀ x y, |φ x - φ y| ≤ c) (n : ℕ) :
    |∫ x, φ x ∂((P ^ n) ∘ₘ μ) - ∫ x, φ x ∂π| ≤ (1 - α) ^ (n / m) * c := by
  have h := abs_integral_comp_pow_sub_integral_le_of_forall_smul_le (P := P ^ m) hmin (hπ.pow m)
    (μ := (P ^ (n % m) : Kernel X X) ∘ₘ μ) hφ hφc (n / m)
  rwa [Measure.comp_assoc, ← pow_mul, ← Kernel.pow_add, Nat.div_add_mod] at h

/-- **Doeblin's condition for a power, convergence**: if `α • ν ≤ (P ^ m) x` for every `x`, then
from every initial law `μ`, `|(Pⁿ ∘ₘ μ)(s) - π(s)| ≤ (1 - α) ^ (n / m)` for every measurable `s`
and the invariant law `π` of `P`. -/
theorem abs_measureReal_comp_pow_sub_le_of_forall_smul_le_pow [IsMarkovKernel P]
    {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} {m : ℕ} (hmin : ∀ x, α • ν ≤ (P ^ m) x)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Invariant P π) {μ : Measure X}
    [IsProbabilityMeasure μ] (n : ℕ) {s : Set X} (hs : MeasurableSet s) :
    |((P ^ n) ∘ₘ μ).real s - π.real s| ≤ (1 - α) ^ (n / m) := by
  have h := abs_measureReal_comp_pow_sub_le_of_forall_smul_le (P := P ^ m) hmin (hπ.pow m)
    (μ := (P ^ (n % m) : Kernel X X) ∘ₘ μ) (n / m) hs
  rwa [Measure.comp_assoc, ← pow_mul, ← Kernel.pow_add, Nat.div_add_mod] at h

/-! ### The hypotheses are forced; a non-degenerate instance -/

/-- Two distinct Dirac measures have no common component `α • ν`, `α > 0`, `ν` a probability
measure. -/
theorem _root_.MeasureTheory.Measure.not_smul_le_dirac_and_smul_le_dirac
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν] {α : ℝ≥0} (hα : 0 < α)
    {a b : X} (hab : a ≠ b) : ¬ (α • ν ≤ Measure.dirac a ∧ α • ν ≤ Measure.dirac b) := by
  rintro ⟨ha, hb⟩
  have h := congrArg (· univ) ((Measure.MutuallySingular.self_iff (α • ν)).1
    ((mutuallySingular_dirac_dirac_iff.2 hab).mono ha hb))
  simp [hα.ne'] at h

/-- **Minorization is forced**: the identity kernel of `Bool` (two absorbing states) does not have a
unique invariant probability measure. It satisfies Doeblin's condition with `α = 0` and with no
`α > 0` (`ProbabilityTheory.Kernel.not_forall_smul_le_id_bool`). -/
theorem not_existsUnique_invariant_id_bool :
    ¬ ∃! π : Measure Bool, IsProbabilityMeasure π ∧ Invariant (Kernel.id : Kernel Bool Bool) π := by
  rintro ⟨π, -, huniq⟩
  have h := (huniq (Measure.dirac true) ⟨inferInstance, Measure.id_comp⟩).trans
    (huniq (Measure.dirac false) ⟨inferInstance, Measure.id_comp⟩).symm
  simpa using congrArg (· {true}) h

theorem not_forall_smul_le_id_bool {ν : Measure Bool} [IsProbabilityMeasure ν] {α : ℝ≥0}
    (hα : 0 < α) : ¬ ∀ x, α • ν ≤ (Kernel.id : Kernel Bool Bool) x := fun h ↦
  Measure.not_smul_le_dirac_and_smul_le_dirac hα (by decide : true ≠ false)
    ⟨by simpa [Kernel.id_apply] using h true, by simpa [Kernel.id_apply] using h false⟩

/-- **Periodicity**: the iterates of the flip of `Bool` from `false` do not converge on `{true}`. -/
theorem not_tendsto_pow_flip_bool (a : ℝ≥0∞) :
    ¬ Tendsto (fun n ↦ (deterministic (fun b : Bool ↦ !b) (measurable_of_countable _) ^ n)
      false {true}) atTop (𝓝 a) := by
  intro h
  have hinv : Function.Involutive fun b : Bool ↦ !b := Bool.not_not
  have h₀ := h.comp (tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun c hc ↦ by omega⟩ :
    Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop)
  have h₁ := h.comp (tendsto_atTop_atTop.2 fun b ↦ ⟨b, fun c hc ↦ by omega⟩ :
    Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop)
  simp only [Function.comp_def, deterministic_pow, deterministic_apply, hinv.iterate_two_mul,
    hinv.iterate_two_mul_add_one, id] at h₀ h₁
  simp at h₀ h₁
  exact one_ne_zero (h₁.trans h₀.symm)

/-- **Periodicity excludes Doeblin's condition for every power**: no power of the flip of `Bool`
has a common component `α • ν`, `α > 0`. -/
theorem not_forall_smul_le_pow_flip_bool (m : ℕ) {ν : Measure Bool} [IsProbabilityMeasure ν]
    {α : ℝ≥0} (hα : 0 < α) :
    ¬ ∀ x, α • ν ≤ (deterministic (fun b : Bool ↦ !b) (measurable_of_countable _) ^ m) x :=
  fun h ↦ Measure.not_smul_le_dirac_and_smul_le_dirac hα
    (a := (fun b : Bool ↦ !b)^[m] true) (b := (fun b : Bool ↦ !b)^[m] false)
    ((Function.Injective.iterate (f := fun b : Bool ↦ !b) (fun a b hab ↦ by simpa using hab)
      m).ne (a₁ := true) (a₂ := false) (by decide))
    ⟨by simpa [deterministic_pow, deterministic_apply] using h true,
      by simpa [deterministic_pow, deterministic_apply] using h false⟩

/-- A non-degenerate instance of Doeblin's theorem: on `Bool`, stay with probability `1/2`, else
move to `true` (`α = 1/2`, `ν = dirac true`; the kernel is neither constant nor deterministic). -/
example : ∃! π : Measure Bool, IsProbabilityMeasure π ∧ Invariant (ofFunOfCountable fun b : Bool ↦
    (1 / 2 : ℝ≥0) • Measure.dirac b + (1 / 2 : ℝ≥0) • Measure.dirac true) π := by
  have : IsMarkovKernel (ofFunOfCountable fun b : Bool ↦
      (1 / 2 : ℝ≥0) • Measure.dirac b + (1 / 2 : ℝ≥0) • Measure.dirac true) :=
    ⟨fun b ↦ ⟨by
      simp only [ofFunOfCountable, coe_mk, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
        Pi.smul_apply, measure_univ]
      rw [← add_smul, add_halves, one_smul]⟩⟩
  exact existsUnique_invariant_of_forall_smul_le (ν := Measure.dirac true) (α := 1 / 2)
    (by norm_num) fun b ↦ Measure.le_add_left le_rfl

end ProbabilityTheory.Kernel
