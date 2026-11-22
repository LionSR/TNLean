/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence.PhysicalMatrixSymmetryTransport

/-!
# Stabilized equivalence for a retained physical matrix

A fixed labelled physical space retains its matrix through common positive
identity ancillas and canonical positive blocking. A unitary involution
transports the full path comparison for adjunction, transposition or
conjugation under the corresponding matrix symmetry hypothesis. The same
ancilla and blocking witnesses work in both directions.

**Scope restriction (labelled physical space):** this relation uses the
existing strict path predicate on each specified enlarged physical space.
It does not replace the general commensurate-dimension relation or require
a globally dimension-indexed action. See
`docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

Source: arXiv:1703.09188, `SSymmetries`, lines 1301--1322,
`def:equivalent-symmetry`, lines 1356--1366, and `lemma:sym-trafo-swap`.
-/

open scoped Matrix

namespace MPOTensor

variable {d Da Db : ℕ}

/-- The three finite-chain symmetry operations compared in
arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
inductive PhysicalSymmetryKind where
  | dagger
  | transpose
  | conjugation

/-- Specify the full action using the retained physical matrix. Ordinary
conjugation is independent of that matrix.
Source: arXiv:1703.09188, `SSymmetries`, lines 1301--1322. -/
noncomputable def PhysicalSymmetryKind.withMatrix (kind : PhysicalSymmetryKind)
    (Q : Matrix (Fin d) (Fin d) ℂ) : FiniteChainOperatorSymmetry d :=
  match kind with
  | .dagger => .daggerWithPhysicalMatrix Q
  | .transpose => .transposeWithPhysicalMatrix Q
  | .conjugation => conjugationSymmetry d

/-- Equivalence on a fixed labelled physical space, retaining its physical
matrix through arbitrary common positive identity ancillas and canonical
positive blocking. The original endpoints are MPUs; canonical form of the
blocked endpoints and arbitrary common virtual dimension are supplied by
the existing strict-equivalence predicate.

This states the concrete labelled-spin convention in arXiv:1703.09188,
`def:equivalent-symmetry`, lines 1356--1366, including the additional labelled
ancillary spin in `prop:U1-U2-equiv-ancillatrick`, lines 2210--2234.
It makes no assertion about the general dimension-indexed family convention. -/
def EquivalentUnderPhysicalMatrixSymmetry (kind : PhysicalSymmetryKind)
    (Q : Matrix (Fin d) (Fin d) ℂ) (U : MPOTensor d Da) (V : MPOTensor d Db) : Prop :=
  IsMPU U ∧ IsMPU V ∧ ∃ x > 0, ∃ k > 0,
    StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix Q x)).block k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl

private theorem isMPU_ketLeftMul_iff (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) (hQQ : Q * Q = 1)
    {D : ℕ} (U : MPOTensor d D) : IsMPU U ↔ IsMPU (U.ketLeftMul Q) := by
  constructor
  · exact fun hU => hU.ketLeftMul hQ
  · intro hU
    simpa only [ketLeftMul_involutive Q hQQ U] using hU.ketLeftMul hQ

private theorem equivalent_of_strict_comparisons
    (kind : PhysicalSymmetryKind)
    (Q_src Q_tgt Q_transport : Matrix (Fin d) (Fin d) ℂ)
    (h_transport : Q_transport ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h_transport_sq : Q_transport * Q_transport = 1)
    (U : MPOTensor d Da) (V : MPOTensor d Db)
    (hstrict : ∀ x k : ℕ, 0 < k →
      (StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix Q_src x)).block k)
        (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl ↔
      StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix Q_tgt x)).block k)
        (blockTensor (tensorPhysicalId (U.ketLeftMul Q_transport) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul Q_transport) x) k) rfl)) :
    EquivalentUnderPhysicalMatrixSymmetry kind Q_src U V ↔
      EquivalentUnderPhysicalMatrixSymmetry kind Q_tgt
        (U.ketLeftMul Q_transport) (V.ketLeftMul Q_transport) := by
  unfold EquivalentUnderPhysicalMatrixSymmetry
  refine and_congr (isMPU_ketLeftMul_iff Q_transport h_transport h_transport_sq U)
    (and_congr (isMPU_ketLeftMul_iff Q_transport h_transport h_transport_sq V) ?_)
  exact exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun k => and_congr_right fun hk => hstrict x k hk

private theorem physicalIdMatrix_involution (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQQ : Q * Q = 1) (x : ℕ) : physicalIdMatrix Q x * physicalIdMatrix Q x = 1 := by
  rw [physicalIdMatrix_mul, hQQ, physicalIdMatrix_one]

/-- A dagger-compatible unitary involution identifies the retained-matrix
stabilized comparison with the ordinary comparison of transformed tensors.
The positive ancilla and blocking witnesses are unchanged in both directions.
Source: arXiv:1703.09188, `SSymmetries` and `lemma:sym-trafo-swap`. -/
theorem equivalentUnderPhysicalMatrixSymmetry_dagger_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hS : Qᴴ = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) :
    EquivalentUnderPhysicalMatrixSymmetry .dagger Q U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .dagger 1 (U.ketLeftMul Q) (V.ketLeftMul Q) := by
  apply equivalent_of_strict_comparisons _ _ _ Q hQ hQQ
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix]
  rw [FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_block _ hk,
    FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_block _ hk,
    physicalIdMatrix_one, MPSTensor.blockKron_one,
    FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_one]
  simpa only [FiniteChainOperatorSymmetry.blockedDaggerWithPhysicalMatrix_eq,
    ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedDaggerWithPhysicalMatrix_iff
      (physicalIdMatrix Q x) (physicalIdMatrix_mem_unitaryGroup Q x hQ)
      (physicalIdMatrix_involution Q hQQ x) (by rw [physicalIdMatrix_conjTranspose, hS])
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

/-- A transpose-compatible unitary involution identifies the retained-matrix
stabilized comparison with the ordinary comparison of transformed tensors.
The positive ancilla and blocking witnesses are unchanged in both directions.
Source: arXiv:1703.09188, `SSymmetries` and `lemma:sym-trafo-swap`. -/
theorem equivalentUnderPhysicalMatrixSymmetry_transpose_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hS : Qᵀ = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) :
    EquivalentUnderPhysicalMatrixSymmetry .transpose Q U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .transpose 1 (U.ketLeftMul Q) (V.ketLeftMul Q) := by
  apply equivalent_of_strict_comparisons _ _ _ Q hQ hQQ
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix]
  rw [FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_block _ hk,
    FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_block _ hk,
    physicalIdMatrix_one, MPSTensor.blockKron_one,
    FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_one]
  simpa only [FiniteChainOperatorSymmetry.blockedTransposeWithPhysicalMatrix_eq,
    ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedTransposeWithPhysicalMatrix_iff
      (physicalIdMatrix Q x) (physicalIdMatrix_mem_unitaryGroup Q x hQ)
      (physicalIdMatrix_involution Q hQQ x) (by rw [physicalIdMatrix_transpose, hS])
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

/-- A conjugation-compatible unitary involution identifies the retained-matrix
stabilized comparison with the ordinary comparison of transformed tensors.
The positive ancilla and blocking witnesses are unchanged in both directions.
Source: arXiv:1703.09188, `SSymmetries` and `lemma:sym-trafo-swap`. -/
theorem equivalentUnderPhysicalMatrixSymmetry_conjugation_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hS : Q.map (starRingEnd ℂ) = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) :
    EquivalentUnderPhysicalMatrixSymmetry .conjugation Q U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .conjugation 1 (U.ketLeftMul Q) (V.ketLeftMul Q) := by
  apply equivalent_of_strict_comparisons _ _ _ Q hQ hQQ
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix, conjugationSymmetry_block hk]
  simpa only [ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedConjugationWithPhysicalMatrix_iff
      (physicalIdMatrix Q x) (physicalIdMatrix_mem_unitaryGroup Q x hQ)
      (physicalIdMatrix_involution Q hQQ x) (physicalIdMatrix_map_star Q x hS)
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

end MPOTensor
