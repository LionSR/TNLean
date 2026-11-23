/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.Hamiltonian
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Sites.SitewiseProduct
import QICLean.ManyBody.Sites.ReplicaSwap
import QICLean.Analysis.TraceInequality.TraceMulBound
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.Analysis.Norm.MatrixKroneckerContraction
import QICLean.ManyBody.Sites.ConfigurationMap

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

## The swapped doubled Hamiltonian on a chain

The swapped doubled interaction is the doubled interaction `ManyBody.Interaction.doubled`
conjugated by the exchange `ManyBody.pairSwapOp D` of the two copies on `D`
(`ManyBody.Interaction.conj`), in paired coordinates; its Hamiltonian is the conjugate
`F K Fᴴ` of the doubled Hamiltonian `K` by the regional sheet swap `F`
(`TNLean.Lattice.hamiltonian_relabel_conj_pairSwapOp_doubled`). The normalized tensor square
of the original ground vector and its swap image have energy `2 * E₀` and lower gap `Δ` for
`K` and `F K Fᴴ`.

### Main results

* `ManyBody.ChainInteraction.doubled_swappedDoubled_isGapped`: the normalized
  explicit ground vectors, their doubled energy and their inherited lower gap.

**Scope restriction (contiguous chains):** The physical sites are `Fin L`.
The broader source domain may have gaps; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–363.
No equality of spectral gaps or Gaussian-filter construction is asserted.
-/

section

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

end

section

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

open ManyBody (IsGapped groundSpace ChainInteraction)

namespace TNLean.MPS.AreaLaw

/-- The paired tensor-square ground vector and its regional swap image
have doubled energy and the original positive lower-gap bound.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.doubled_swappedDoubled_isGapped
    {L q R : ℕ} {E₀ Δ : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin L)) {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ) :
    let e := QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
    let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (ψ₀ ∘ e.symm)
    let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
      WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
    (‖Ψ‖ = 1 ∧ IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ ∧
      groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
      (‖Φ‖ = 1 ∧ IsGapped (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) Δ ∧
        groundSpace (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) = Submodule.span ℂ {Φ}) := by
  classical
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let ψ₀ := Matrix.doubledVector (WithLp.ofLp Ω)
  let Ψ : EuclideanSpace ℂ (Fin L → Fin (q * q)) := WithLp.toLp 2 (ψ₀ ∘ e.symm)
  let Φ : EuclideanSpace ℂ (Fin L → Fin (q * q)) :=
    WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)
  change (‖Ψ‖ = 1 ∧ IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ ∧
    groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ}) ∧
    (‖Φ‖ = 1 ∧ IsGapped (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) Δ ∧
      groundSpace (F * h.doubledFin.hamiltonian * Fᴴ) (2 * E₀) = Submodule.span ℂ {Φ})
  have hH := (ManyBody.Interaction.isHermitian_hamiltonian hh)
  have hgK := hgap.kronecker_add hH hH hgap (Or.inl hΔ.le)
  have hsK := ManyBody.groundSpace_kronecker_add_eq_span hH hH hgap hgap hΔ.le hΔ.le hspan hspan
  rw [min_self] at hgK
  have hgapD : IsGapped h.doubledFin.hamiltonian (2 * E₀) Δ := by
    rw [h.hamiltonian_doubledFin, ManyBody.isGapped_reindex_iff, two_mul]
    exact hgK
  have hspanD : groundSpace h.doubledFin.hamiltonian (2 * E₀) = Submodule.span ℂ {Ψ} := by
    rw [h.hamiltonian_doubledFin, two_mul]
    exact ManyBody.groundSpace_reindex_eq_span e hsK
  have hΩsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hΨ : ‖Ψ‖ = 1 := by
    have hi := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
      (WithLp.toLp 2 ψ₀)
    change ‖Ψ‖ = ‖WithLp.toLp 2 ψ₀‖ at hi
    exact hi.trans (Matrix.norm_doubledVector hΩsum)
  have hF : F ∈ Matrix.unitaryGroup _ ℂ :=
    Matrix.reindex_mem_unitaryGroup e (sheetSwapOp q D)
      (sheetSwap q D).permMatrix_mem_unitaryGroup
  refine ⟨⟨hΨ, hgapD, hspanD⟩, ?_⟩
  have hΦ : Matrix.toEuclideanLin F Ψ = Φ := rfl
  have hΦn : ‖Φ‖ = 1 := by
    change ‖WithLp.toLp 2 (F *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [Matrix.norm_toLp_mulVec_of_unitary hF]
    exact hΨ
  rw [← hΦ]
  exact ⟨by rw [hΦ]; exact hΦn, (ManyBody.isGapped_unitary_conj_iff hF).mpr hgapD,
    ManyBody.groundSpace_unitary_conj_eq_span hF hspanD⟩

end TNLean.MPS.AreaLaw

end
