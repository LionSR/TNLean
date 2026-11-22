/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.DensityOperator.AreaLaw
import QICLean.ManyBody.Sites.Relabel
import TNLean.MPS.MPU.QuasiLocal.FiniteWindowSupport
import QICLean.Algebra.Combinatorics.IndexInduction
import QICLean.ManyBody.Sites.Lattice.Ring

/-!
# Cyclic relocation of actual finite MPO conjugation

The closed virtual trace makes the finite periodic MPO invariant under
simultaneously rotating its bra and ket configurations. Thus both its
forward and adjoint conjugations commute with the actual cyclic site
permutation. Existing finite operator support is transported by that
permutation, including across the periodic seam.

These identities do not assume unitarity or inverse locality. For an MPU
at the source's permitted lengths the adjoint conjugation is its actual
inverse action. They supply the relocation step for inverse propagation
in arXiv:1703.09188, Appendix eq:appendix-1, lines 2300–2306.

## Uniform finite-ring propagation from a supplied standard form

The actual finite standard-form conjugation controls an arbitrary observable
on the complete central interval. Closed-trace cyclic covariance transports
that bound to every singleton, including those at the periodic seam. The
radius is independent of the ring length; no inverse or propagation bound
is supplied as a hypothesis.

Source: arXiv:1703.09188, StandardForm/SF and Appendix eq:appendix-1,
lines 603–622 and 2300–2306.

**Scope restriction (supplied standard form):** These results consume
actual MPU unitarity, a positive block length and supplied two-site
standard-form data, and their neighbourhoods are measured in that block
length. The standard-form construction from bare MPU data and the source
bond-dimension radius remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

section

open scoped Matrix

namespace MPOTensor

variable {d D N : ℕ}

/-- Actual forward MPO conjugation commutes with a cyclic change of the
finite-chain cut. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306; periodicity follows from the closed virtual trace. -/
theorem mpo_conjugation_submatrix_rotateConfig
    (U : MPOTensor d D) (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    (mpo U N * A * (mpo U N)ᴴ).submatrix (rotateConfig N d) (rotateConfig N d) =
      mpo U N * A.submatrix (rotateConfig N d) (rotateConfig N d) * (mpo U N)ᴴ := by
  rw [← Matrix.submatrix_mul_equiv (mpo U N * A) (mpo U N)ᴴ
    (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.submatrix_mul_equiv (mpo U N) A
      (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.conjTranspose_submatrix]
  simp only [mpo_submatrix_rotateConfig]

/-- Actual adjoint MPO conjugation commutes with the same cyclic cut
change. No inverse support bound is assumed. Source context:
arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem mpo_adjointConjugation_submatrix_rotateConfig
    (U : MPOTensor d D) (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    ((mpo U N)ᴴ * A * mpo U N).submatrix (rotateConfig N d) (rotateConfig N d) =
      (mpo U N)ᴴ * A.submatrix (rotateConfig N d) (rotateConfig N d) * mpo U N := by
  rw [← Matrix.submatrix_mul_equiv ((mpo U N)ᴴ * A) (mpo U N)
    (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.submatrix_mul_equiv (mpo U N)ᴴ A
      (rotateConfig N d) (rotateConfig N d) (rotateConfig N d),
    ← Matrix.conjTranspose_submatrix]
  simp only [mpo_submatrix_rotateConfig]

/-- A forward finite MPO support bound relocates with the input through
the periodic seam. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306. -/
theorem mpo_conjugation_mem_supportedOperators_rotate
    (U : MPOTensor d D) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {S : Finset (Fin N)}
    (hA : mpo U N * A * (mpo U N)ᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    mpo U N * A.submatrix (rotateConfig N d) (rotateConfig N d) * (mpo U N)ᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) := by
  have h := ManyBody.submatrix_comp_perm_mem_supportedOperators (finRotate N) hA
  change (mpo U N * A * (mpo U N)ᴴ).submatrix (rotateConfig N d) (rotateConfig N d) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) at h
  simpa only [mpo_conjugation_submatrix_rotateConfig] using h

/-- A finite support bound for the actual adjoint conjugation rotates
through the periodic seam with the input observable. This is the cyclic
relocation step toward the boundary-free inverse propagation statement,
not an assumed inverse-family compatibility condition.
Source context: arXiv:1703.09188, eq:appendix-1, lines 2300–2306. -/
theorem mpo_adjointConjugation_mem_supportedOperators_rotate
    (U : MPOTensor d D) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    {S : Finset (Fin N)}
    (hA : (mpo U N)ᴴ * A * mpo U N ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    (mpo U N)ᴴ * A.submatrix (rotateConfig N d) (rotateConfig N d) * mpo U N ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) := by
  have h := ManyBody.submatrix_comp_perm_mem_supportedOperators (finRotate N) hA
  change ((mpo U N)ᴴ * A * mpo U N).submatrix (rotateConfig N d) (rotateConfig N d) ∈
    ManyBody.supportedOperators (fun _ ↦ Fin d) (S.image (finRotate N)) at h
  simpa only [mpo_adjointConjugation_submatrix_rotateConfig] using h

end MPOTensor

end

section

open scoped Matrix
open Fin.CommRing

namespace MPOTensor

/-- A forward singleton bound at one site propagates cyclically to every
site for the actual periodic MPO. No unitarity or locality hypothesis at
other sites is required. Source context: arXiv:1703.09188, eq:appendix-1,
lines 2300–2306; cyclic covariance is the closed virtual trace identity. -/
theorem mpo_conjugation_singleton_propagation_of_one
    {d D N : ℕ} [NeZero N] (U : MPOTensor d D) (x₀ : Fin N) (r : ℕ)
    (h₀ : ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x₀} : Finset (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        ManyBody.supportedOperators (fun _ ↦ Fin d)
          (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x₀} r)) :
    ∀ x : Fin N, ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x} : Finset (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        ManyBody.supportedOperators (fun _ ↦ Fin d)
          (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x} r) := by
  classical
  have hbase : ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x₀ + 0} : Finset (Fin N)),
      mpo U N * A * (mpo U N)ᴴ ∈
        ManyBody.supportedOperators (fun _ ↦ Fin d)
          (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x₀ + 0} r) := by
    simpa only [add_zero] using h₀
  have hstep (i : Fin N)
      (hi : ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x₀ + i} : Finset (Fin N)),
        mpo U N * A * (mpo U N)ᴴ ∈
          ManyBody.supportedOperators (fun _ ↦ Fin d)
            (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x₀ + i} r)) :
      ∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x₀ + (i + 1)} : Finset (Fin N)),
        mpo U N * A * (mpo U N)ᴴ ∈
          ManyBody.supportedOperators (fun _ ↦ Fin d)
            (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x₀ + (i + 1)} r) := by
    intro A hA
    let A₀ := A.submatrix (fun σ => σ ∘ (finRotate N).symm)
      (fun σ => σ ∘ (finRotate N).symm)
    have hpred : (finRotate N).symm (x₀ + (i + 1)) = x₀ + i := by
      apply (finRotate N).injective
      simp only [Equiv.apply_symm_apply, finRotate_apply, add_assoc]
    have hA₀ : A₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x₀ + i} : Finset (Fin N)) := by
      have h := ManyBody.submatrix_comp_perm_mem_supportedOperators (finRotate N).symm hA
      simpa only [Finset.image_singleton, hpred] using h
    have hcancel : A₀.submatrix (rotateConfig N d) (rotateConfig N d) = A := by
      ext σ τ
      simp only [A₀, Matrix.submatrix_apply, rotateConfig_apply, Function.comp_def,
        Equiv.apply_symm_apply]
    have h := mpo_conjugation_mem_supportedOperators_rotate U (hi A₀ hA₀)
    rw [ManyBody.graphNeighborhood_cycleGraph_image_finRotate, Finset.image_singleton] at h
    simpa only [hcancel, finRotate_apply, add_assoc] using h
  intro x
  have h := Fin.cyclic_induction hbase hstep (x - x₀)
  have hx : x₀ + (x - x₀) = x := by abel
  simpa only [hx] using h

/-- A supplied actual unitary two-site standard form gives a uniform
singleton propagation radius on every sufficiently long periodic ring,
including the seam. Source: arXiv:1703.09188, StandardForm/SF and
Appendix eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpo_conjugation_mem_supportedOperators_singleton
    {d D ℓ r N : ℕ} [NeZero N] {U : MPOTensor d D} (hU : U.IsMPU)
    (k : ℕ) (hk : 0 < k) (hN : 3 * (2 * k) ≤ N)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (x : Fin N) {A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) ({x} : Finset (Fin N))) :
    mpo U N * A * (mpo U N)ᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (ManyBody.graphNeighborhood (SimpleGraph.cycleGraph N) {x} (4 * k)) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, N = 0 + (3 * (2 * k) + s) := ⟨N - 3 * (2 * k), by omega⟩
  let x₀ : Fin (0 + (3 * (2 * k) + s)) := ⟨2 * k, by omega⟩
  apply mpo_conjugation_singleton_propagation_of_one U x₀ (4 * k) ?_ x A hA
  intro B hB
  have hCentral : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun (i : Fin (0 + (3 * (2 * k) + s))) ↦
          0 + 2 * k ≤ i.val ∧ i.val < 0 + 2 * k + 2 * k) :=
    ManyBody.supportedOperators_mono (by
      intro i hi
      obtain rfl := Finset.mem_singleton.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change 0 + 2 * k ≤ 2 * k ∧ 2 * k < 0 + 2 * k + 2 * k
      omega) hB
  have hForward := mpo_conjugation_mem_supportedOperators_central hU k 0 s hk S hCentral
  apply ManyBody.supportedOperators_mono ?_ hForward
  intro j hj
  have hj' : j.val < 0 + 3 * (2 * k) := (Finset.mem_filter.mp hj).2.2
  refine ManyBody.mem_graphNeighborhood_cycleGraph.mpr
    ⟨x₀, Finset.mem_singleton_self x₀, (j.val : ℤ) - x₀.val, ?_, ?_⟩
  · apply abs_le.mpr
    change -((4 * k : ℕ) : ℤ) ≤ (j.val : ℤ) - (2 * k : ℕ) ∧
      (j.val : ℤ) - (2 * k : ℕ) ≤ (4 * k : ℕ)
    constructor <;> omega
  · simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self]
    abel

end MPOTensor

end
