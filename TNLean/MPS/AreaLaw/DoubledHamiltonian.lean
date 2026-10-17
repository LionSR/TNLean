/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import TNLean.Circuit.EntropySupport
import TNLean.Circuit.SitewiseTensorSupport
import QICLean.Analysis.TraceMulBound

/-!
# Two copies of a finite-range chain Hamiltonian

Pairing the two local configuration values at every original site turns
`H ⊗ 1 + 1 ⊗ H` into a chain Hamiltonian with local dimension `q * q`.
Each interaction keeps its original support and has norm at most `2 * J`.
No positivity of the local dimension or nonemptiness of the chain is required.

## Main results

* `ChainHamiltonian.doubled`: the paired two-copy interaction family.
* `ChainHamiltonian.doubled_operator`: its sum is the reindexed two-copy operator.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360.
This construction does not transport a ground state or spectral gap and does
not assert the separate replica-swap difference estimate.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q R : ℕ} {J : ℝ}

/-- The two-copy Hamiltonian, with the copies paired at each original site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
noncomputable def ChainHamiltonian.doubled (h : ChainHamiltonian L q R J) :
    ChainHamiltonian L (q * q) R (2 * J) where
  term X := Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
    (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)
  supported X := by
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    change (Matrix.reindexAddEquiv ℂ (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)) (_ + _) ∈ _
    rw [map_add]
    have hterm := QuantumCircuit.mem_supportedOperators_of_isSupportedOn (h.supported X)
    have hone := QuantumCircuit.one_mem_supportedOperators (d := q) (X.1 : Set (Fin L))
    have hleft := QuantumCircuit.reindex_kronecker_mem_supportedOperators hterm hone
    have hright := QuantumCircuit.reindex_kronecker_mem_supportedOperators hone hterm
    simpa only [Set.union_self, Matrix.coe_reindexAddEquiv] using
      (QuantumCircuit.supportedOperators (q * q)
        ((X.1 : Set (Fin L)) ∪ (X.1 : Set (Fin L)))).add_mem hleft hright
  hermitian X := by
    apply Matrix.IsHermitian.reindex
    change (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)ᴴ = _
    rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker,
      h.hermitian X, conjTranspose_one]
  norm_le X := by
    rw [Matrix.l2_opNorm_reindex_equiv]
    calc
      _ ≤ ‖h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)‖ +
          ‖(1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X‖ := norm_add_le _ _
      _ ≤ ‖h.term X‖ + ‖h.term X‖ :=
        add_le_add (Matrix.l2_opNorm_kronecker_one_le _)
          (Matrix.l2_opNorm_one_kronecker_le _)
      _ ≤ J + J := add_le_add (h.norm_le X) (h.norm_le X)
      _ = 2 * J := by ring

/-- Summing the paired interactions gives exactly the sum of the two copies of
`H`, after grouping their local coordinates at each site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
lemma ChainHamiltonian.doubled_operator (h : ChainHamiltonian L q R J) :
    h.doubled.operator =
      Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
        (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
        (h.operator ⊗ₖ 1 + 1 ⊗ₖ h.operator) := by
  ext σ τ
  simp only [ChainHamiltonian.operator, ChainHamiltonian.doubled, Matrix.sum_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

end TNLean.MPS.AreaLaw
