/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Kernels and ranges of iterates after stabilization

For an endomorphism `f` of a module, `ker (f ^ n)` increases and `range (f ^ n)` decreases with
`n`. If `ker (f ^ n) = ker (f ^ (n + 1))`, the kernel chain is constant from `n` on and
`ker (f ^ n) ⊓ range (f ^ n) = ⊥`. If `range (f ^ n) = range (f ^ (n + 1))`, the range chain is
constant from `n` on and `ker (f ^ n) ⊔ range (f ^ n) = ⊤`. With both, the two are complements
(Fitting decomposition at `n`).

Mathlib proves the eventual versions (`Module.End.eventually_disjoint_ker_pow_range_pow`,
`LinearMap.eventually_codisjoint_ker_pow_range_pow`,
`LinearMap.eventually_isCompl_ker_pow_range_pow`) under Noetherian and Artinian hypotheses, whose
only role is to stop the chains. Here stabilization is a hypothesis: this is the algebraic half of
the Riesz theory of compact operators, where the chains stop for analytic reasons.

## Main statements

* `Module.End.ker_pow_add_eq`, `Module.End.range_pow_add_eq`,
  `Module.End.ker_pow_eq_ker_pow_succ_of_le`, `Module.End.range_pow_eq_range_pow_succ_of_le`:
  stabilization propagates.
* `Module.End.disjoint_ker_pow_range_pow`, `Module.End.codisjoint_ker_pow_range_pow`,
  `Module.End.isCompl_ker_pow_range_pow`: the Fitting decomposition at a stable index.
* `Commute.ker_mem_invtSubmodule`, `Commute.range_mem_invtSubmodule`: kernels and ranges of
  commuting endomorphisms are invariant.

Staged for `Mathlib/RingTheory/Artinian/Module.lean`, next to
`LinearMap.eventually_isCompl_ker_pow_range_pow` (the `Commute` lemmas for
`Mathlib/Algebra/Module/Submodule/Invariant.lean`); `Module.End.ker_pow_add_eq` generalizes
`Module.End.ker_pow_constant` from division rings to semirings. Searched on 2026-10-17: pinned
mathlib (`v4.34.1`) and mathlib master (`gh api` on `RingTheory/Artinian/Module.lean`,
`Algebra/Module/Submodule/Invariant.lean`) state these facts only under Noetherian/Artinian
hypotheses or over a division ring. Prior art: TauCeti, `TauCeti/LinearAlgebra/End/RangePow.lean`
(commit `a65deaded1ca`, Apache 2.0), whose range lemmas are re-proved here.
-/
open LinearMap (ker range)

namespace Module.End

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- Once two consecutive kernels of iterates of `f` agree, all later ones agree. -/
theorem ker_pow_add_eq (h : ker (f ^ n) = ker (f ^ (n + 1))) (m : ℕ) :
    ker (f ^ (n + m)) = ker (f ^ n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc ker (f ^ (n + (m + 1))) = ker (f ^ (n + 1) * f ^ m) := by
          rw [← pow_add, ← add_assoc, add_right_comm]
      _ = (ker (f ^ (n + 1))).comap (f ^ m) := LinearMap.ker_comp _ _
      _ = ker (f ^ (n + m)) := by rw [← h, pow_add, mul_eq_comp, LinearMap.ker_comp]
      _ = ker (f ^ n) := ih

/-- Once two consecutive ranges of iterates of `f` agree, all later ones agree. -/
theorem range_pow_add_eq (h : range (f ^ n) = range (f ^ (n + 1))) (m : ℕ) :
    range (f ^ (n + m)) = range (f ^ n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc range (f ^ (n + (m + 1))) = range (f ^ m * f ^ (n + 1)) := by
          rw [← pow_add, add_left_comm n m 1]
      _ = (range (f ^ (n + 1))).map (f ^ m) := LinearMap.range_comp _ _
      _ = range (f ^ (n + m)) := by rw [← h, add_comm n, pow_add, mul_eq_comp, LinearMap.range_comp]
      _ = range (f ^ n) := ih

/-- Once the kernel chain of `f` is stable at `n`, it is stable at every `m ≥ n`. -/
theorem ker_pow_eq_ker_pow_succ_of_le (h : ker (f ^ n) = ker (f ^ (n + 1))) {m : ℕ}
    (hm : n ≤ m) : ker (f ^ m) = ker (f ^ (m + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [ker_pow_add_eq h, add_assoc, ker_pow_add_eq h]

/-- Once the range chain of `f` is stable at `n`, it is stable at every `m ≥ n`. -/
theorem range_pow_eq_range_pow_succ_of_le (h : range (f ^ n) = range (f ^ (n + 1))) {m : ℕ}
    (hm : n ≤ m) : range (f ^ m) = range (f ^ (m + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [range_pow_add_eq h, add_assoc, range_pow_add_eq h]

/-- If `ker (f ^ n) = ker (f ^ (n + 1))`, then `ker (f ^ n)` and `range (f ^ n)` are disjoint. -/
theorem disjoint_ker_pow_range_pow (h : ker (f ^ n) = ker (f ^ (n + 1))) :
    Disjoint (ker (f ^ n)) (range (f ^ n)) := by
  refine disjoint_iff.mpr ((Submodule.eq_bot_iff _).mpr ?_)
  rintro - ⟨hx, ⟨y, rfl⟩⟩
  have hy : y ∈ ker (f ^ (n + n)) := by
    rw [LinearMap.mem_ker, pow_add, mul_apply]
    exact LinearMap.mem_ker.mp hx
  rw [ker_pow_add_eq h n] at hy
  exact LinearMap.mem_ker.mp hy

/-- If `f` commutes with `g`, then `ker g` is `f`-invariant. -/
theorem _root_.Commute.ker_mem_invtSubmodule {g : Module.End R M} (h : Commute f g) :
    ker g ∈ f.invtSubmodule :=
  (mem_invtSubmodule_iff_forall_mem_of_mem f).mpr fun x hx ↦ by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← mul_apply, ← h.eq, mul_apply, hx, map_zero]

/-- If `f` commutes with `g`, then `range g` is `f`-invariant. -/
theorem _root_.Commute.range_mem_invtSubmodule {g : Module.End R M} (h : Commute f g) :
    range g ∈ f.invtSubmodule :=
  (mem_invtSubmodule_iff_forall_mem_of_mem f).mpr fun _ ⟨y, hy⟩ ↦
    ⟨f y, hy ▸ DFunLike.congr_fun h.eq.symm y⟩

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- If `range (f ^ n) = range (f ^ (n + 1))`, then `ker (f ^ n)` and `range (f ^ n)` span. -/
theorem codisjoint_ker_pow_range_pow (h : range (f ^ n) = range (f ^ (n + 1))) :
    Codisjoint (ker (f ^ n)) (range (f ^ n)) := by
  refine codisjoint_iff.mpr (Submodule.eq_top_iff'.mpr fun x ↦ ?_)
  obtain ⟨z, hz⟩ : (f ^ n) x ∈ range (f ^ (n + n)) := by
    rw [range_pow_add_eq h]
    exact LinearMap.mem_range_self _ x
  rw [pow_add, mul_apply] at hz
  exact Submodule.mem_sup.mpr ⟨x - (f ^ n) z, by simp [hz], (f ^ n) z,
    LinearMap.mem_range_self _ z, sub_add_cancel x _⟩

/-- **Fitting decomposition at a stable index**: if both the kernel and the range chains of `f`
are stable at `n`, then `ker (f ^ n)` and `range (f ^ n)` are complements. -/
theorem isCompl_ker_pow_range_pow (hker : ker (f ^ n) = ker (f ^ (n + 1)))
    (hrange : range (f ^ n) = range (f ^ (n + 1))) :
    IsCompl (ker (f ^ n)) (range (f ^ n)) :=
  ⟨disjoint_ker_pow_range_pow hker, codisjoint_ker_pow_range_pow hrange⟩

end Ring

end Module.End
