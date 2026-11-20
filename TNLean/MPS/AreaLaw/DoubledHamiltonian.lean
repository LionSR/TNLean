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
import QICLean.ManyBody.Dynamics.InteractionOperations

/-!
# Two copies of a finite-range Hamiltonian with paired local alphabets

The doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` (`ManyBody.Interaction.doubled`) lives on the
system with basis `Fin q × Fin q` at every site. Encoding each pair in `Fin (q * q)` by
`finProdFinEquiv`, a relabelling of the basis at every site, gives an interaction with local
dimension `q * q`, the alphabet of the chain and domain models. Each term keeps its original
support, and the sum of the terms is `H ⊗ 1 + 1 ⊗ H` in the paired coordinates
`QuantumCircuit.sitePairConfigurationEquiv`. The norms and Hermiticity of the terms are those
of `ManyBody.Interaction.doubled`, since relabelling preserves both. No positivity of the local
dimension or nonemptiness of the sites is required.

## Main definitions

* `ManyBody.Interaction.doubledFin`: the doubled interaction with local alphabet `Fin (q * q)`.

## Main results

* `ManyBody.Interaction.doubledFin_term`: its terms in the paired coordinates.
* `ManyBody.Interaction.hamiltonian_doubledFin`: its sum is the reindexed two-copy operator.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360.
This construction does not transport a ground state or spectral gap and does
not assert the separate replica-swap difference estimate.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} {S : ι → Finset V} {q : ℕ}

/-- The doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` with the two copies of every site paired into
the local alphabet `Fin (q * q)`: the relabelling of `ManyBody.Interaction.doubled` along
`finProdFinEquiv` at every site. Each term keeps the support of the original term.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
noncomputable def _root_.ManyBody.Interaction.doubledFin
    (Φ : ManyBody.Interaction (fun _ : V ↦ Fin q) S) :
    ManyBody.Interaction (fun _ : V ↦ Fin (q * q)) S :=
  Φ.doubled.relabel (X' := fun _ : V ↦ Fin (q * q)) (Equiv.refl V) (fun _ ↦ finProdFinEquiv) S
    fun _ _ ↦ Iff.rfl

/-- The paired doubled term with index `i` is `hᵢ ⊗ 1 + 1 ⊗ hᵢ` in the paired coordinates.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.Interaction.doubledFin_term
    (Φ : ManyBody.Interaction (fun _ : V ↦ Fin q) S) (i : ι) :
    Φ.doubledFin.term i = Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv V q q)
      (QuantumCircuit.sitePairConfigurationEquiv V q q) (Φ.term i ⊗ₖ 1 + 1 ⊗ₖ Φ.term i) :=
  rfl

/-- Summing the paired doubled terms gives exactly the sum of the two copies of `H`, after
grouping their local coordinates at each site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.Interaction.hamiltonian_doubledFin [Fintype ι]
    (Φ : ManyBody.Interaction (fun _ : V ↦ Fin q) S) :
    Φ.doubledFin.hamiltonian = Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv V q q)
      (QuantumCircuit.sitePairConfigurationEquiv V q q)
        (Φ.hamiltonian ⊗ₖ 1 + 1 ⊗ₖ Φ.hamiltonian) := by
  refine (ManyBody.Interaction.hamiltonian_relabel _ _ _ _ _).trans ?_
  rw [ManyBody.Interaction.hamiltonian_doubled]
  ext x y
  simp [QuantumCircuit.sitePairConfigurationEquiv, ManyBody.siteConfigurationEquiv,
    Matrix.doubledHamiltonian]

end TNLean.MPS.AreaLaw
