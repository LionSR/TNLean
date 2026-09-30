/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.MPU.GroupCocycleMPO
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Group matrix product operators from a three-cocycle: the fusion algebra and the defect

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection "Periodic
boundary condition case", `Papers/2203.12563/REsubmission.tex` lines 2202–2205: the periodic
operators `U_g` built from a three-cocycle `ω` form a representation of the finite group `G`;
lines 361–362: the periodic operators of a matrix product operator algebra satisfy
`O_a O_b = ∑_c N_{ab}^c O_c` at every system size.

**Formalized here.** The periodic operators of the construction in `GroupCocycleMPO` form a
matrix product operator fusion algebra whose structure constants are those of the group,
`N_{gh}^k = δ_{k, gh}`, for every three-cocycle. Consequently the sum `A = ∑_g U_g` of the
group operators, the condensation defect of the representation, satisfies `A² = |G| A` at
every positive length: its structure constants do not depend on the length. This last
identity is a project result; the source does not consider the sum.

## Main results

* `MPOTensor.GroupCocycle.isMPOFusionAlgebra`: the group fusion algebra.
* `MPOTensor.GroupCocycle.sum_mpo_mul_sum_mpo`: `A² = |G| A` for `A = ∑_g U_g`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.GroupCocycle

open TNLean.Algebra

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : ℕ} (e : G ≃ Fin n)

/-- **The group operators form a matrix product operator fusion algebra** with the structure
constants `N_{gh}^k = δ_{k, gh}` of the group, for every three-cocycle `ω`.

Source: arXiv:2203.12563, lines 2204–2205 (`U_g U_h = U_{gh}`), read as an instance of the
fusion rules of lines 361–362. -/
theorem isMPOFusionAlgebra {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω) :
    IsMPOFusionAlgebra (tensor e ω) fun g h k ↦ if k = g * h then 1 else 0 := by
  intro g h L hL
  have : NeZero L := ⟨by omega⟩
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mpo_tensor_mul e hω g h

omit [DecidableEq G] in
/-- Project result: **the condensation defect of an exact group representation has constant
structure constants**: the sum `A = ∑_g U_g` of the periodic group operators satisfies
`A² = |G| A` on every nonempty chain, for every three-cocycle `ω`. -/
theorem sum_mpo_mul_sum_mpo {ω : ScalarThreeCochain G} (hω : ScalarThreeCochain.IsCocycle ω)
    (N : ℕ) [NeZero N] :
    (∑ g, mpo (tensor e ω g) N) * (∑ g, mpo (tensor e ω g) N) =
      (Fintype.card G : ℂ) • ∑ g, mpo (tensor e ω g) N := by
  rw [Finset.sum_mul_sum]
  simp_rw [mpo_tensor_mul e hω]
  rw [Finset.sum_congr rfl fun g _ ↦
      Fintype.sum_equiv (Equiv.mulLeft g) (fun h ↦ mpo (tensor e ω (g * h)) N)
        (fun k ↦ mpo (tensor e ω k) N) fun _ ↦ rfl,
    Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

end MPOTensor.GroupCocycle
