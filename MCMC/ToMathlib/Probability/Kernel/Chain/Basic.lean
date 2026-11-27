/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import MCMC.ToMathlib.Probability.Kernel.Composition.CompMap
public import MCMC.ToMathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The Markov chain of a kernel

For a Markov kernel `P : Kernel X X` on a measurable space `X`, `P.chain : Kernel X (ℕ → X)` maps
a point `x` to the law of the trajectory of the chain of `P` started at `x`. It is Mathlib's
Ionescu-Tulcea kernel `traj κ 0` for the kernels `κ n = P.comap (· ⟨n, _⟩)`, which read the
point at time `n` and move by `P`, read on the initial point instead of the trajectory up to
time `0`. No assumption on `X` is made.

* `ProbabilityTheory.Kernel.chain_comp_eq_trajMeasure`: started at any measure `μ`, the law of
  the trajectory is Mathlib's `trajMeasure μ κ`.
* `ProbabilityTheory.Kernel.chain_map_eval`: the point at time `n` has the law `P ^ n`.
* `ProbabilityTheory.Kernel.chain_map_eval_eval_add`: the pair of points at times `k` and
  `k + m` has the law `(P ^ k) ⊗ₖ prodMkLeft X (P ^ m)`, that is, `(P ^ k) x (dy) (P ^ m) y (dz)`.
* `ProbabilityTheory.Kernel.integral_comp_mul_comp_chain_comp`: from an s-finite initial measure
  `μ`, `∫ ψ (ω k) φ (ω (k + l)) = ∫ ψ · (∫ φ ∂(P ^ l ·)) ∂((P ^ k) ∘ₘ μ)` when the product is
  integrable and `ψ`, `φ` are almost everywhere measurable under the laws of the two times.
* `ProbabilityTheory.Kernel.ae_forall_eq_iterate_chain_deterministic`: the chain of a
  deterministic kernel follows the orbit of its map, when singletons are measurable.

The two laws are identities of kernels, so they hold from every initial measure, finite or not,
by `MeasureTheory.Measure.map_comp`.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed. (from the extracted text; numbers
  to be checked against the printed book): Lemma 11.7 (mixtures: the measures `P_x` form
  a probability kernel from `S` to `S^T`, and `P_ν A = ∫ P_x A ν(dx)`) is `Kernel.chain` with
  `chain_comp_eq_trajMeasure`; Proposition 11.2 (finite-dimensional distributions) has
  `chain_map_eval` and `chain_map_eval_eval_add` as its cases of one time and of two times, for a
  time-homogeneous chain. The statements were read; the proofs here are from Mathlib's
  Ionescu-Tulcea kernel and do not follow the book's.
* Not in this file: Lemma 11.1 (extended Markov property), Proposition 11.9 (strong Markov
  property) and Lemma 11.11 (stationarity and invariance) of the same chapter.

## Search

At Mathlib `d13f23b`: `grep -rn "def chain\|Kernel.chain\|markovChain" Mathlib` finds nothing;
`grep -rn "trajMeasure\|traj κ" Mathlib` finds the trajectory measure and the kernel `traj` of a
family of kernels on varying spaces (`Probability/Kernel/IonescuTulcea/Traj.lean`) and their
use for product measures (`Probability/ProductMeasure.lean`), with no kernel of the chain of a
single kernel and no law of its points.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} (P : Kernel X X) [IsMarkovKernel P]

/-- **The Markov chain of a kernel**: the kernel that maps a point `x` to the law of the
trajectory `(ω 0, ω 1, …)` of the chain of `P` started at `x`. -/
noncomputable def chain : Kernel X (ℕ → X) :=
  (traj (X := fun _ ↦ X) (fun n ↦ P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)) 0).comap (MeasurableEquiv.piUnique fun _ : Iic 0 ↦ X).symm
      (MeasurableEquiv.piUnique fun _ : Iic 0 ↦ X).symm.measurable

instance : IsMarkovKernel P.chain := by
  rw [chain]
  infer_instance

/-- **The chain is the trajectory measure**: started at a measure `μ`, the law of the trajectory
of the chain of `P` is Mathlib's `trajMeasure μ κ` for `κ n = P.comap (· ⟨n, _⟩)`. -/
theorem chain_comp_eq_trajMeasure (μ : Measure X) :
    P.chain ∘ₘ μ = trajMeasure (X := fun _ ↦ X) μ fun n ↦
      P.comap (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _) := by
  rw [chain, ← comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

/-- **The law of the point at time `n`**: from `x`, the point at time `n` of the chain of `P` has
law `(P ^ n) x`. -/
theorem chain_map_eval (n : ℕ) : P.chain.map (fun ω ↦ ω n) = P ^ n := by
  ext1 x
  rw [map_apply _ (measurable_pi_apply n), ← Measure.dirac_bind P.chain.measurable x,
    chain_comp_eq_trajMeasure, trajMeasure_map_eval, Measure.dirac_bind (P ^ n).measurable]

/-- **The law of a pair of points**: from `x`, the points at times `k` and `k + m` of the chain of
`P` have the joint law `(P ^ k) x (dy) (P ^ m) y (dz)`. -/
theorem chain_map_eval_eval_add (k m : ℕ) :
    P.chain.map (fun ω ↦ (ω k, ω (k + m))) = (P ^ k) ⊗ₖ prodMkLeft X (P ^ m) := by
  ext1 x
  rw [map_apply _ ((measurable_pi_apply k).prodMk (measurable_pi_apply (k + m))),
    ← Measure.dirac_bind P.chain.measurable x, chain_comp_eq_trajMeasure,
    trajMeasure_map_eval_eval_add, Measure.dirac_bind (P ^ k).measurable,
    compProd_apply_eq_compProd_sectR, sectR_prodMkLeft]

/-- **Correlations of two times of the chain**: started at an s-finite measure `μ`,
`∫ ψ (ω k) φ (ω (k + l)) ∂(P.chain ∘ₘ μ) = ∫ ψ · (∫ φ ∂(P ^ l ·)) ∂((P ^ k) ∘ₘ μ)` whenever
`ψ (ω k) φ (ω (k + l))` is integrable, for `ψ` and `φ` almost everywhere measurable under the laws
`(P ^ k) ∘ₘ μ` and `(P ^ (k + l)) ∘ₘ μ` of the two times. -/
theorem integral_comp_mul_comp_chain_comp (μ : Measure X) [SFinite μ] {φ ψ : X → ℝ} (k l : ℕ)
    (hφ : AEMeasurable φ ((P ^ (k + l) : Kernel X X) ∘ₘ μ))
    (hψ : AEMeasurable ψ ((P ^ k : Kernel X X) ∘ₘ μ))
    (hint : Integrable (fun ω ↦ ψ (ω k) * φ (ω (k + l))) (P.chain ∘ₘ μ)) :
    ∫ ω, ψ (ω k) * φ (ω (k + l)) ∂(P.chain ∘ₘ μ) =
      ∫ x, ψ x * ∫ y, φ y ∂((P ^ l) x) ∂((P ^ k) ∘ₘ μ) := by
  have hp : Measurable fun ω : ℕ → X ↦ (ω k, ω (k + l)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply (k + l))
  have hpair : (P.chain ∘ₘ μ).map (fun ω ↦ (ω k, ω (k + l))) = ((P ^ k) ∘ₘ μ) ⊗ₘ (P ^ l) := by
    rw [Measure.map_comp _ _ hp, chain_map_eval_eval_add, compProd_prodMkLeft_eq_comp,
      ← Measure.comp_assoc, Measure.compProd_eq_comp_prod]
  have hψ' : AEMeasurable (fun p : X × X ↦ ψ p.1) (((P ^ k : Kernel X X) ∘ₘ μ) ⊗ₘ (P ^ l)) :=
    AEMeasurable.comp_aemeasurable' (f := Prod.fst)
      (by rw [Measure.fst_compProd]; exact hψ :
        AEMeasurable ψ (((P ^ k : Kernel X X) ∘ₘ μ) ⊗ₘ (P ^ l)).fst) measurable_fst.aemeasurable
  have hφ' : AEMeasurable (fun p : X × X ↦ φ p.2) (((P ^ k : Kernel X X) ∘ₘ μ) ⊗ₘ (P ^ l)) :=
    AEMeasurable.comp_aemeasurable' (f := Prod.snd)
      (by rw [Measure.snd_compProd, Measure.comp_assoc,
            (by exact (pow_add P l k).symm : (P ^ l) ∘ₖ (P ^ k) = P ^ (l + k)), add_comm l k]
          exact hφ :
        AEMeasurable φ (((P ^ k : Kernel X X) ∘ₘ μ) ⊗ₘ (P ^ l)).snd) measurable_snd.aemeasurable
  have hg := (hψ'.mul hφ').aestronglyMeasurable
  have hint' : Integrable (fun p : X × X ↦ ψ p.1 * φ p.2)
      (((P ^ k : Kernel X X) ∘ₘ μ) ⊗ₘ (P ^ l)) := by
    rw [← hpair, integrable_map_measure (hpair ▸ hg) hp.aemeasurable]
    exact hint
  calc ∫ ω, ψ (ω k) * φ (ω (k + l)) ∂(P.chain ∘ₘ μ)
      = ∫ p, ψ p.1 * φ p.2 ∂((P.chain ∘ₘ μ).map fun ω ↦ (ω k, ω (k + l))) :=
        (integral_map hp.aemeasurable (hpair ▸ hg)).symm
    _ = _ := by
        rw [hpair, Measure.integral_compProd hint']
        simp_rw [integral_const_mul]

/-- **The chain of a deterministic map follows the orbit**: with measurable singletons, for
`(deterministic f hf).chain x`-almost every `ω`, `ω k = f^[k] x` for every `k`. -/
theorem ae_forall_eq_iterate_chain_deterministic [MeasurableSingletonClass X] {f : X → X}
    (hf : Measurable f) (x : X) :
    ∀ᵐ ω ∂((deterministic f hf).chain x), ∀ k, ω k = f^[k] x := by
  refine ae_all_iff.2 fun k ↦ ae_of_ae_map (f := fun ω : ℕ → X ↦ ω k)
    (p := fun y ↦ y = f^[k] x) (measurable_pi_apply k).aemeasurable ?_
  rw [← map_apply _ (measurable_pi_apply k), chain_map_eval, deterministic_pow,
    deterministic_apply]
  exact (ae_dirac_iff (measurableSet_singleton _)).2 rfl

end ProbabilityTheory.Kernel
