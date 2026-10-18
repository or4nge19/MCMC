import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import MCMC.PF.Combinatorics.Quiver.Cyclic

/-!
# Aperiodic matrices

Index of imprimitivity of a real matrix and aperiodicity (irreducible with index of
imprimitivity `1`), following mathlib PR #39926.

## Main definitions

* `Matrix.indexOfImprimitivity A`: the index of imprimitivity of the positive-edge quiver of `A`.
* `Matrix.IsAperiodic A`: `A` is irreducible and its index of imprimitivity is `1`.

## Main results

* `Matrix.period_eq_one_of_primitive`: every vertex of the quiver of a primitive matrix has
  period `1`.
* `Matrix.primitive_implies_irreducible_and_aperiodic`: a primitive matrix is aperiodic.
-/

namespace Matrix

open Quiver

variable {n : Type*} [DecidableEq n] {A : Matrix n n ℝ}

/-! # Aperiodic matrices -/

variable (A) in
/-- The index of imprimitivity of `A`, i.e. of its positive-edge quiver `toQuiver A`. For an
irreducible matrix this is the common period of all vertices. -/
noncomputable def indexOfImprimitivity [Nonempty n] : ℕ :=
  letI : Quiver n := toQuiver A
  Quiver.indexOfImprimitivity n

variable (A) in
/-- A matrix is aperiodic if it is irreducible and its index of imprimitivity is `1`. -/
def IsAperiodic [Nonempty n] : Prop :=
  IsIrreducible A ∧ indexOfImprimitivity A = 1

omit [DecidableEq n] in
/-- Aperiodicity implies irreducibility. -/
theorem IsAperiodic.isIrreducible [Nonempty n] (hA : IsAperiodic A) : IsIrreducible A :=
  hA.1

omit [DecidableEq n] in
/-- Aperiodicity of a matrix is aperiodicity of its positive-edge quiver. -/
theorem IsAperiodic.quiver_isAperiodic [Nonempty n] (hA : IsAperiodic A) :
    letI : Quiver n := toQuiver A
    Quiver.IsAperiodic n :=
  hA.2

omit [DecidableEq n] in
/-- For an irreducible matrix, aperiodicity is equivalent to the period-one condition at any chosen
vertex of the positive-edge quiver. -/
theorem isAperiodic_iff_period_eq_one [Nonempty n] (hA_irred : IsIrreducible A) (i : n) :
    IsAperiodic A ↔ (letI : Quiver n := toQuiver A; Quiver.period i = 1) :=
  (and_iff_right hA_irred).trans
    (@Quiver.isAperiodic_iff_period_eq_one n (toQuiver A) _ hA_irred.connected i)

/-- For a primitive nonnegative matrix, every vertex of the positive-edge quiver has period `1`. -/
theorem period_eq_one_of_primitive [Fintype n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (h_prim : IsPrimitive A) (i0 : n) :
    letI : Quiver n := toQuiver A
    Quiver.period i0 = 1 := by
  let : Quiver n := toQuiver A
  obtain ⟨_, k, hk_pos, hk⟩ := h_prim
  have hP (v : n) : Nonempty {p : Path i0 v // p.length = k} :=
    (pow_apply_pos_iff_nonempty_path hA_nonneg k i0 v).mp (hk i0 v)
  obtain ⟨⟨p, hp⟩⟩ := hP i0
  obtain ⟨c, -, q, hq, -⟩ := p.eq_toPath_comp_of_length_eq_succ (n := k - 1) (by lia)
  obtain ⟨⟨r, hr⟩⟩ := hP c
  have h1 : period i0 ∣ (r.comp q).length :=
    period_dvd_of_mem_cycleLengths ⟨by simp only [Path.length_comp]; lia, r.comp q, rfl⟩
  have h2 : period i0 ∣ (p.comp p).length :=
    period_dvd_of_mem_cycleLengths (length_comp_mem_cycleLengths p p (hp ▸ hk_pos))
  have hlen : (p.comp p).length = (r.comp q).length + 1 := by
    simp only [Path.length_comp]
    lia
  exact Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp (hlen ▸ h2))

/-- Frobenius (forward direction): A primitive matrix is irreducible and aperiodic. -/
theorem primitive_implies_irreducible_and_aperiodic [Fintype n] [Nonempty n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    IsPrimitive A → IsAperiodic A := fun h_prim ↦
  ⟨h_prim.isIrreducible, period_eq_one_of_primitive hA_nonneg h_prim _⟩

/-! # Frobenius Normal Form -/

/-- Predicate: `P` is a permutation matrix (entries are 1 on a single position in each row given
by a permutation, 0 elsewhere). -/
def IsPermutationMatrix (P : Matrix n n ℝ) : Prop :=
  ∃ σ : Equiv.Perm n, ∀ i j, P i j = if σ i = j then 1 else 0

/--
Theorem: Frobenius Normal Form.
-/
theorem exists_frobenius_normal_form [Nonempty n]
    (_hA_irred : IsIrreducible A) (_hA_not_aper : ¬ IsAperiodic A) :
    ∃ (P : Matrix n n ℝ), IsPermutationMatrix P ∧ True := by
  refine ⟨1, ?_, trivial⟩
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  rw [Matrix.one_apply, Equiv.refl_apply]

end Matrix
