/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalFormBlocking
import TNLean.MPS.MPU.SimpleTensorEquivalence
import TNLean.MPS.MPU.StandardForm

/-!
# Two-site standard form with supplied gates

A two-site standard form consists of two unitary gates and two half factors
whose open-leg contraction is the blocked tensor. The gates are supplied: they
need not be a prescribed choice of source-cut factorization. In particular,
the definition does not assume that the tensor already generates a unitary
family of periodic operators.

For a simple tensor in canonical form II, the paper's source factors give
such a standard form. The two gate unitarity statements are consequences of
the simple-tensor equivalence, not assumptions on the source factors.

**Scope restriction (reduced full support):** The source constructions in this
module use a chosen canonical-form-II representative with full ambient
support; bare `IsMPU` does not provide that same-tensor presentation. This is
the admissible reading of arXiv:1703.09188, Definition `SF`, lines 619--622.
See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

- arXiv:1703.09188, equations `uuvv` and `StandardForm`, and Definition `SF`,
  lines 532--543 and 603--622.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

/-- The open two-site standard form with specified gates
`u : d² → ℓ × r` and `v : r × ℓ → d²`.

The first two tensor letters carry physical output indices `i₁,i₂` and input
indices `j₁,j₂` in their original order. Contracting the virtual ends then
places `v` on the shifted physical pair; no reflected input pair is imposed
on arbitrary supplied gates.

Source: arXiv:1703.09188, equations `uuvv`, `uu`, `vdagger`, and
`StandardForm`, lines 532--543 and 603--617. -/
structure TwoSiteStandardFormData
    {d D ℓ r : ℕ}
    (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) where
  /-- The physical dimension is positive. -/
  phys_pos : 0 < d
  /-- The bond dimension is positive. -/
  bond_pos : 0 < D
  /-- The left intermediate dimension is positive. -/
  left_pos : 0 < ℓ
  /-- The right intermediate dimension is positive. -/
  right_pos : 0 < r
  /-- The half factor joining the second output leg to the right virtual end. -/
  X₁ : Matrix (Fin d × Fin D) (Fin r) ℂ
  /-- The half factor joining the left virtual end to the first output leg. -/
  X₂ : Matrix (Fin D × Fin d) (Fin ℓ) ℂ
  /-- The gate on the unshifted pair is unitary. -/
  u_unitary : u.IsUnitaryBetween
  /-- The gate on the shifted pair is unitary. -/
  v_unitary : v.IsUnitaryBetween
  /-- The shifted gate is the contraction of the two half factors. -/
  v_apply (i₁ i₂ : Fin d) (s : Fin r) (t : Fin ℓ) :
    v (i₁, i₂) (s, t) = ∑ β : Fin D, X₁ (i₁, β) s * X₂ (β, i₂) t
  /-- The tensor is the open contraction through the unshifted gate. -/
  W_apply (i j : Fin (d * d)) (α γ : Fin D) :
    W i j α γ = ∑ t : Fin ℓ, ∑ s : Fin r,
      X₂ (α, (finProdFinEquiv.symm i).1) t *
        u (t, s) (finProdFinEquiv.symm j) *
          X₁ ((finProdFinEquiv.symm i).2, γ) s

/-- The two-site block of a simple MPU in canonical form II has the standard
form supplied by its source cuts, with both gates unitary.

Source: arXiv:1703.09188, equation `StandardForm` and Definition `SF`, lines
603--622. -/
noncomputable def IsMPUCanonicalFormII.twoSiteStandardFormData
    {d D : ℕ} {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    TwoSiteStandardFormData (blockTwo U)
      (sourceU U hU.ρ hU.ρ_posDef) (sourceV U hU.ρ hU.ρ_posDef) := by
  letI : NeZero d := hU.neZero_phys
  letI : NeZero D := hU.neZero_bond
  have hprod : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 0 1).mp hsimple
  have hrl : 0 < r[U] * ℓ[U] := by
    rw [hprod]
    exact Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  refine {
    X₁ := S.X₁
    X₂ := S.X₂
    phys_pos := NeZero.pos d
    bond_pos := NeZero.pos D
    left_pos := Nat.pos_of_mul_pos_left hrl
    right_pos := Nat.pos_of_mul_pos_right hrl
    u_unitary := (hU.isMPUSimple_tfae.out 0 2).mp hsimple
    v_unitary := (hU.isMPUSimple_tfae.out 0 3).mp hsimple
    v_apply := by
      intro i₁ i₂ s t
      rfl
    W_apply := by
      intro i j α γ
      exact SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁ U S i j α γ
  }

/-- Relabel a direct block of length `k * 2` as two consecutive blocks of
length `k`, each with its two physical indices kept in order.

Source: arXiv:1703.09188, lines 603--617. -/
private noncomputable def twoSiteBlockedPhysicalEquiv (d k : ℕ) :
    Fin (MPSTensor.blockPhysDim d (k * 2)) ≃
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) :=
  (MPSTensor.directIteratedBlockEquiv d k 2).trans
    (twoSiteBlockEquiv (MPSTensor.blockPhysDim d k)).symm

/-- The two-site block of a length-`k` block is direct blocking by `k * 2`,
after the stated physical-index relabeling.

Source: arXiv:1703.09188, lines 603--617. -/
private theorem reindexPhysical_blockTwo_blockTensor
    {d D : ℕ} (U : MPOTensor d D) (k : ℕ) :
    reindexPhysical (twoSiteBlockedPhysicalEquiv d k)
        (blockTwo (blockTensor U k)) = blockTensor U (k * 2) := by
  funext i j
  rw [blockTwo_eq_blockTensor_reindex]
  simp only [reindexPhysical, twoSiteBlockedPhysicalEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  exact congrFun (congrFun (reindexPhysical_blockTensor_blockTensor U k 2) i) j

/-- The physical-index equivalence from a direct block of length `2 * k`
to the two-site block of a length-`k` tensor. -/
noncomputable def twoSiteDirectBlockEquiv (d k : ℕ) :
    Fin (MPSTensor.blockPhysDim d (2 * k)) ≃
      Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k) :=
  (finCongr (congrArg (MPSTensor.blockPhysDim d) (Nat.mul_comm 2 k))).trans
    (twoSiteBlockedPhysicalEquiv d k)

private theorem reindexPhysical_blockTwo_blockTensor_of_eq
    {d D : ℕ} (U : MPOTensor d D) (k L : ℕ) (hL : L = k * 2) :
    reindexPhysical
        ((finCongr (congrArg (MPSTensor.blockPhysDim d) hL)).trans
          (twoSiteBlockedPhysicalEquiv d k))
        (blockTwo (blockTensor U k)) = blockTensor U L := by
  subst L
  simpa using reindexPhysical_blockTwo_blockTensor U k

/-- In the source's length convention, the two-site block of a length-`k`
block is direct blocking by `2 * k`, after its physical-index relabeling.

Source: arXiv:1703.09188, lines 603--617. -/
theorem reindexPhysical_blockTwo_blockTensor_two_mul
    {d D : ℕ} (U : MPOTensor d D) (k : ℕ) :
    reindexPhysical (twoSiteDirectBlockEquiv d k)
        (blockTwo (blockTensor U k)) = blockTensor U (2 * k) := by
  exact reindexPhysical_blockTwo_blockTensor_of_eq U k (2 * k) (Nat.mul_comm 2 k)

/-- A canonical-form-II MPU has a positive simple block of length at most
`D ^ 4` whose two-site block has the supplied source standard form. Its
physical coordinates agree with direct blocking by `2 * k` through the
displayed equivalence. The source cuts and gates are formed on the same
length-`k` block, with the fixed matrix recorded by the original datum.

Source: arXiv:1703.09188, Proposition III.3(ii), Theorem `ThmFund1`, and
Definition `SF`, lines 378--427 and 563--622. -/
theorem IsMPUCanonicalFormII.exists_twoSiteStandardFormData_blockTensor
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ D ^ 4 ∧
      IsMPUSimple (MPOTensor.blockTensor U k) ∧
      Nonempty (TwoSiteStandardFormData (blockTwo (MPOTensor.blockTensor U k))
        (sourceU (MPOTensor.blockTensor U k) hU.ρ hU.ρ_posDef)
        (sourceV (MPOTensor.blockTensor U k) hU.ρ hU.ρ_posDef)) ∧
      reindexPhysical (twoSiteDirectBlockEquiv d k)
        (blockTwo (MPOTensor.blockTensor U k)) = MPOTensor.blockTensor U (2 * k) := by
  have : NeZero d := hU.neZero_phys
  have : NeZero D := hU.neZero_bond
  obtain ⟨k, hk, hkD, hsimple⟩ := hU.isMPU.exists_blockTensor_isMPUSimple
  refine ⟨k, hk, hkD, hsimple, ?_, reindexPhysical_blockTwo_blockTensor_two_mul U k⟩
  exact ⟨(hU.blockTensor k hk).twoSiteStandardFormData hsimple⟩

end MPOTensor
