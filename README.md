# Markov Chains Monte Carlo and Perron–Frobenius in Lean 4

Formalization of:
- finite-state Markov chains (kernels, total variation, convergence),
- basic MCMC algorithms (Gibbs, Metropolis–Hastings),
- Perron–Frobenius theory and supporting spectral material,
- the Krein–Rutman theorem on real Banach spaces (`MCMC/ToMathlib`, sorry-free),
- groundwork for a general MCMC kernel interface (non-finite).

## Build

Lean/Mathlib `v4.34.1` (elan recommended):
```bash
lake exe cache get
lake build MCMC
```
Open the folder in VS Code for interactive proofs.

## Directory overview

- `MCMC/Finite/`
  - `Core.lean`: finite Markov chains; states, transitions, stationary distributions
  - `toKernel.lean`: bridge to kernel transitions
  - `TotalVariation.lean`: total variation distance and Dobrushin coefficient
  - `Convergence.lean`: convergence/mixing statements for finite chains
  - `MetropolisHastings.lean`: Metropolis–Hastings kernel
  - `Gibbs.lean`: Gibbs sampling
- `MCMC/PF/`
  - `Auxiliary.lean`: auxiliary lemmas
  - `LinearAlgebra/Matrix/PerronFrobenius/`: PF and spectral/JNF files
    - core: `Defs`, `Irreducible`, `Primitive`, `Aperiodic`, `CollatzWielandt`, `Multiplicity`,`Dominance`
    - stochastic/sampling: `Stochastic.lean`
- `MCMC/Kernel/`: WIP general-state kernel interface
- `MCMC/ToMathlib/`: Mathlib-ready additions at their Mathlib paths (below)

## Krein–Rutman (`MCMC/ToMathlib`)

Spectral radius of a real operator is `gelfandRadius T = lim ‖Tⁿ‖^{1/n}` (backport of
mathlib #42607); cones are `ProperCone ℝ E`. Following Bourbaki, *Théories spectrales* III §6:
- `KreinRutman/Compact.lean`: if `T` preserves a total salient cone and is quasi-compact
  (`gelfandRadius (T ^ n - K) < gelfandRadius T ^ n`, `K` compact; compact `T` with `r > 0` is a
  special case), `r = gelfandRadius T` is an isolated eigenvalue with an eigenvector in the cone
  and a positive dual eigenfunctional.
- `KreinRutman/StronglyPositive.lean`: strongly positive and primitive operators: interior
  eigenvector, algebraic simplicity, spectral gap `gelfandRadius (T - r P) < r`, `(r⁻¹T)ⁿ → P`,
  peripheral spectrum `{r}`; irreducible ones (`(1 + T)ᵏ` strongly positive): interior eigenvector
  and algebraic simplicity.
- `KreinRutman/OrderBounded.lean`: the same for cones with empty interior (`Lᵖ`, Jentzsch
  kernels) under `u₀`-positivity `ψ x • u₀ ≤ T x ≤ (β‖x‖) • u₀`.
- `KreinRutman/{FiniteDimensional,Order}.lean`, `CStarAlgebra/`: finite dimension
  (Birkhoff–Vandergraft), ordered spaces and Banach lattices (`C(K)`, `Lᵖ`), positive and
  completely positive maps of C⋆-algebras (Evans–Høegh-Krohn); `Analysis/Matrix/`: Perron–Frobenius
  and convergence of primitive stochastic matrices.
- Supporting theory: Riesz–Schauder, a local analytic Fredholm theorem, poles beyond the essential
  spectral radius (`Normed/Operator/Compact/`), real-Banach complexification
  (`TaylorComplexification`).

Headline statements are checked against Mathlib-only specifications on branch
`palomar-comparator`.

## Finite-state TV and Dobrushin (key results)

`MCMC/Finite/TotalVariation.lean` provides:
- `tvDist`: total variation on finite distributions (L1/2 formulation).
- `dobrushinCoeff`: sup TV distance between rows of a stochastic matrix.
- contraction: `tvDist_contract` (TV contracts by `dobrushinCoeff` under a kernel).
- submultiplicativity: `dobrushinCoeff_mul`, powers: `dobrushinCoeff_pow`.
- primitive link: `dobrushinCoeff_lt_one_of_primitive` (∃ k, δ(P^k) < 1 for primitive P).

Consequences (used in `Convergence.lean` and PF links):
- quantitative TV convergence for finite primitive chains,
- geometric decay along powers once some δ(P^k) < 1,
- bridge to PF primitivity results in `PF/…/PerronFrobenius`.

## Contributing

Feel free to open issues or PRs for discussion and suggestions.
