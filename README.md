# Markov Chains Monte Carlo and Perron–Frobenius in Lean 4

Formalization of:
- finite-state Markov chains (kernels, total variation, convergence),
- basic MCMC algorithms (Gibbs, Metropolis–Hastings),
- Perron–Frobenius theory and supporting spectral material,
- groundwork for a general MCMC kernel interface (non-finite).

## Build

Prerequisites: Lean 4 and Lake (elan recommended).
- macOS:
  ```bash
  cd MCMC
  lake build
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
