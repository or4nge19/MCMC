/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Powers of a deterministic kernel

`ProbabilityTheory.Kernel.deterministic_pow`: `deterministic f hf ^ n = deterministic f^[n] _`,
next to Mathlib's `ProbabilityTheory.Kernel.deterministic_comp_deterministic`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "deterministic_pow\|deterministic.*\^"
Probability/Kernel` finds nothing.
-/

@[expose] public section

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The powers of the deterministic kernel of `f` are the deterministic kernels of the iterates
of `f`. -/
theorem deterministic_pow {f : α → α} (hf : Measurable f) (n : ℕ) :
    deterministic f hf ^ n = deterministic f^[n] (hf.iterate n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, ih]
    exact deterministic_comp_deterministic hf (hf.iterate n)

end ProbabilityTheory.Kernel
