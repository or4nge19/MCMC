/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Powers of a kernel on one space are Markov, finite or s-finite with the kernel

The powers `κ ^ n` of a kernel `κ : Kernel α α` are Mathlib's (`Kernel.instMonoid`,
multiplication `∘ₖ`, unit `Kernel.id`). This file adds the instance `IsMarkovKernel 1` (the unit
is `Kernel.id`, so it is finite and s-finite) and the instances `IsMarkovKernel (κ ^ n)`,
`IsFiniteKernel (κ ^ n)` and `IsSFiniteKernel (κ ^ n)`, each from the same property of `κ`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "IsMarkovKernel (.* \^\|IsFiniteKernel
(.* \^\|IsSFiniteKernel (.* \^\|isMarkovKernel_pow\|IsMarkovKernel.pow" Probability` finds
nothing.
-/

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The unit `1 = Kernel.id` of the monoid of kernels is a Markov kernel. -/
instance IsMarkovKernel.one : IsMarkovKernel (1 : Kernel α α) :=
  inferInstanceAs (IsMarkovKernel Kernel.id)

instance IsMarkovKernel.pow (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    exact (inferInstance : IsMarkovKernel ((κ ^ n) ∘ₖ κ))

instance IsFiniteKernel.pow (κ : Kernel α α) [IsFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (κ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    exact (inferInstance : IsFiniteKernel ((κ ^ n) ∘ₖ κ))

instance IsSFiniteKernel.pow (κ : Kernel α α) [IsSFiniteKernel κ] (n : ℕ) :
    IsSFiniteKernel (κ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    exact (inferInstance : IsSFiniteKernel ((κ ^ n) ∘ₖ κ))

end ProbabilityTheory.Kernel
