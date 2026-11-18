/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
import TNLean.Circuit.SitewiseTensorSupport
import QICLean.Analysis.TraceMulBound

/-!
# Two copies of a finite-range chain Hamiltonian

Pairing the two local configuration values at every original site turns
`H ⊗ 1 + 1 ⊗ H` into a chain Hamiltonian with local dimension `q * q`.
Each interaction keeps its original support and has norm at most `2 * J`.
No positivity of the local dimension or nonemptiness of the chain is required.

## Main results

* `ManyBody.ChainInteraction.doubled`: the paired two-copy interaction family.
* `ManyBody.ChainInteraction.doubled_hamiltonian`: its sum is the reindexed two-copy operator.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360.
This construction does not transport a ground state or spectral gap and does
not assert the separate replica-swap difference estimate.
-/

open ManyBody (ChainInteraction)

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q R : ℕ} {J : ℝ}

/-- The two-copy interaction, with the copies paired at each original site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
noncomputable def _root_.ManyBody.ChainInteraction.doubled (h : ManyBody.ChainInteraction L q R) :
    ManyBody.ChainInteraction L (q * q) R where
  term X := Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
    (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)
  mem X := by
    change (Matrix.reindexAddEquiv ℂ (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)) (_ + _) ∈ _
    rw [map_add]
    have hterm := h.mem X
    have hone := one_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) X.1)
    have hleft := QuantumCircuit.reindex_kronecker_mem_supportedOperators hterm hone
    have hright := QuantumCircuit.reindex_kronecker_mem_supportedOperators hone hterm
    simpa only [Finset.union_self, Matrix.coe_reindexAddEquiv] using
      add_mem hleft hright

/-- The paired terms of Hermitian terms are Hermitian.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_doubled_term
    (h : ManyBody.ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (X : ManyBody.ChainSupport L R) : (h.doubled.term X).IsHermitian := by
  apply Matrix.IsHermitian.reindex
  change (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)ᴴ = _
  rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, hh X,
    conjTranspose_one]

/-- Each paired term has norm at most `2 * J`.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.ChainInteraction.norm_doubled_term_le
    (h : ManyBody.ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : ManyBody.ChainSupport L R) : ‖h.doubled.term X‖ ≤ 2 * J := by
  change ‖Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
    (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)‖ ≤ 2 * J
  rw [Matrix.l2_opNorm_reindex_equiv]
  calc
    _ ≤ ‖h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)‖ +
        ‖(1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X‖ := norm_add_le _ _
    _ ≤ ‖h.term X‖ + ‖h.term X‖ :=
      add_le_add (Matrix.l2_opNorm_kronecker_one_le _)
        (Matrix.l2_opNorm_one_kronecker_le _)
    _ ≤ J + J := add_le_add (hhJ X) (hhJ X)
    _ = 2 * J := by ring

/-- Summing the paired interactions gives exactly the sum of the two copies of
`H`, after grouping their local coordinates at each site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
lemma _root_.ManyBody.ChainInteraction.doubled_hamiltonian (h : ChainInteraction L q R) :
    h.doubled.hamiltonian =
      Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
        (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
        (h.hamiltonian ⊗ₖ 1 + 1 ⊗ₖ h.hamiltonian) := by
  ext σ τ
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.ChainInteraction.doubled, Matrix.sum_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

end TNLean.MPS.AreaLaw
