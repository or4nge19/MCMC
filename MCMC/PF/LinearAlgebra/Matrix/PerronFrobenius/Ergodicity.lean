import MCMC.Finite.Core
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.ProjectiveMetric

/-!
# Inhomogeneous products and ergodicity

This file contains the Chapter 3 scaffold for inhomogeneous products of nonnegative matrices.

The basic multiplicative object is `Matrix.forwardProd`. Weak and strong ergodicity are stated in
forms adapted to the existing finite-matrix API, with the projective-metric formulation expressed
through `Matrix.birkhoffContraction`.
-/

namespace Matrix

open Filter Topology

section ForwardProducts

variable {R : Type*} [Semiring R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/--
The forward inhomogeneous product
`H (p + 1) * H (p + 2) * ... * H (p + r)`.
-/
def forwardProd (H : ℕ → Matrix n n R) (p r : ℕ) : Matrix n n R :=
  match r with
  | 0 => 1
  | r + 1 => Matrix.forwardProd H p r * H (p + r + 1)

@[simp] theorem forwardProd_zero (H : ℕ → Matrix n n R) (p : ℕ) :
    Matrix.forwardProd H p 0 = 1 := by
  rfl

@[simp] theorem forwardProd_succ (H : ℕ → Matrix n n R) (p r : ℕ) :
    Matrix.forwardProd H p (r + 1) =
      Matrix.forwardProd H p r * H (p + r + 1) := by
  rfl

end ForwardProducts

section Ergodicity

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/--
Weak ergodicity in row-difference form: the rows of the forward products become asymptotically
independent of the initial row.
-/
def IsWeaklyErgodic (H : ℕ → Matrix n n ℝ) : Prop :=
  ∀ p i j, Tendsto (fun r : ℕ => (Matrix.forwardProd H p r) i - (Matrix.forwardProd H p r) j)
    atTop (nhds (0 : n → ℝ))

/--
Weak ergodicity in Seneta's ratio form.
This is the natural formulation in the positive cone.
-/
def IsWeaklyErgodicRatio (H : ℕ → Matrix n n ℝ) : Prop :=
  ∀ p i j s,
    (∀ᶠ r in atTop, 0 < (Matrix.forwardProd H p r) j s) ∧
      Tendsto (fun r : ℕ => (Matrix.forwardProd H p r) i s / (Matrix.forwardProd H p r) j s)
        atTop (nhds (1 : ℝ))

/--
Strong ergodicity: every row of every forward product converges to the same limit vector.
-/
def IsStronglyErgodic (H : ℕ → Matrix n n ℝ) : Prop :=
  ∃ v : n → ℝ, ∀ p i,
    Tendsto (fun r : ℕ => (Matrix.forwardProd H p r) i) atTop (nhds v)

/-- Forward products preserve entrywise nonnegativity. -/
theorem forwardProd_nonneg
    {H : ℕ → Matrix n n ℝ} (hH_nonneg : ∀ k i j, 0 ≤ H k i j) :
    ∀ p r i j, 0 ≤ Matrix.forwardProd H p r i j := by
  sorry

/-- Forward products of stochastic matrices remain stochastic. -/
theorem forwardProd_isStochastic
    {H : ℕ → Matrix n n ℝ} (hH_stoch : ∀ k, MCMC.Finite.IsStochastic (H k)) :
    ∀ p r, MCMC.Finite.IsStochastic (Matrix.forwardProd H p r) := by
  sorry

/--
Ratio weak ergodicity is detected by decay of Birkhoff's contraction coefficient.
-/
theorem weaklyErgodicRatio_iff_tendsto_birkhoffContraction_zero
    {H : ℕ → Matrix n n ℝ}
    (hH_nonneg : ∀ k i j, 0 ≤ H k i j) (hH_allow : ∀ k, (H k).IsAllowable) :
    Matrix.IsWeaklyErgodicRatio H ↔
      ∀ p, Tendsto (fun r : ℕ => Matrix.birkhoffContraction (Matrix.forwardProd H p r))
        atTop (nhds (0 : ℝ)) := by
  sorry

/-- Strong ergodicity implies weak ergodicity. -/
theorem stronglyErgodic_implies_weaklyErgodic
    {H : ℕ → Matrix n n ℝ} :
    Matrix.IsStronglyErgodic H → Matrix.IsWeaklyErgodic H := by
  sorry

/--
If every row of every forward product converges to the same strictly positive limit vector, then
Seneta's ratio-form weak ergodicity holds.
-/
theorem weaklyErgodicRatio_of_tendsto_rows_to_positive
    {H : ℕ → Matrix n n ℝ} {v : PositiveVec n}
    (hH : ∀ p i, Tendsto (fun r : ℕ => (Matrix.forwardProd H p r) i) atTop (nhds v.1)) :
    Matrix.IsWeaklyErgodicRatio H := by
  sorry

end Ergodicity

end Matrix
