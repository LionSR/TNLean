/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BulkObservable.PrimitiveLocalCommutatorGap
import TNLean.MPS.ParentHamiltonian.Continuity.OpenParentInteractionGap

/-!
# A primitive-sector local commutator bound for positive parent interactions

A positive finite-range interaction with the prescribed local MPS kernel is
comparable to the canonical parent projection. Its open-chain Hamiltonians
therefore have the same kernels and a uniform positive gap at sufficient
range. Locality and primitive transfer convergence give the corresponding
local commutator inequality, without supplied limiting energy estimates.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6,
lines 2649--2675; CPGSV21, arXiv:2011.12127, lines 2170--2172.

**Scope restriction (one primitive sector):** The commutator conclusions
concern finite-interval expectations of one normalized primitive tensor. The
unconditional existence theorem assumes range at least \(D^4+1\).
The quasi-local formulation, construction of the GNS Hamiltonian, and the
pure multiblock conclusion are not treated here; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

-/

open Filter
open scoped Matrix Topology ComplexOrder InnerProductSpace

open ManyBody.Interaction (chainTranslates)

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D R k : ℕ}

/-- The Hamiltonians of the open-chain translates of a positive parent interaction and of the
canonical parent interaction on the open chain have identical kernels at every length.
Source: CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem IsParentInteraction.ker_hamiltonian_chainTranslates_eq_ker_parentChainInteraction
    {A : MPTensor α (Fin D)} {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) (N : ℕ) :
    LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) := by
  obtain ⟨κ, C, hκ, hC, hComparison⟩ := hh.exists_pos_hamiltonian_chainTranslates_comparison
  refine ((Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_parentChainInteraction A R N)).ker_eq_of_smul_le_of_le_smul
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates
        (Matrix.isPositive_toEuclideanLin_iff.mp hh.isPositive) N)) hκ zero_lt_one hC ?_ ?_).symm
  · rw [Complex.ofReal_one, one_smul, ← map_smul, Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    exact (hComparison N).1
  · rw [Complex.ofReal_one, one_smul, ← map_smul, Matrix.toEuclideanLin_le_toEuclideanLin_iff]
    exact (hComparison N).2

/-- Along unit ground vectors, the commutator energies of an open interaction
with a bulk observable converge to the insertion expectation of the local
commutator observable. Source: Nachtergaele, arXiv:cond-mat/9410110,
Section 6, lines 2649--2675. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.openInteraction_commutator_energy_tendsto
    [NeZero D] {A : MPTensor α (Fin D)} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Fin R → α) (Fin R → α) ℂ)
    (X : Matrix (Fin k → α) (Fin k → α) ℂ) (hR : 0 < R)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((n + (R - 1) + k) + (R - 1 + n))))
    (hGround : ∀ᶠ n in atTop,
      ψ n ∈ ((groundSpace A ((n + (R - 1) + k) + (R - 1 + n))).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
    let H (n : ℕ) := Matrix.toEuclideanLin (chainTranslates R (N n) h).hamiltonian
    let B (n : ℕ) := ((Matrix.toEuclideanCLM (n := (Fin (N n) → α)) (𝕜 := ℂ))
      (bulkObservable X (n + (R - 1)) (R - 1 + n))).toLinearMap
    Tendsto (fun n =>
      (inner ℂ (((B n).adjoint.comp ((H n).comp (B n) - (B n).comp (H n)))
        (ψ n)) (ψ n)).re) atTop
      (nhds (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re) := by
  intro N H B
  apply (hP.localCommutatorObservable_expectation_tendsto hρ h X hR
    N (fun n => by dsimp [N]; omega) ψ hGround hUnit).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hH : Matrix.toEuclideanCLM (n := (Fin (N n) → α)) (𝕜 := ℂ)
      ((chainTranslates R (N n) h).hamiltonian) = (H n).toContinuousLinearMap := rfl
  dsimp only
  rw [map_mul, map_sub, map_mul, map_mul, ← Matrix.star_eq_conjTranspose,
    map_star, ContinuousLinearMap.star_eq_adjoint, hH,
    ← bulkObservable_eq_placeAlong_chainWindow X (n + (R - 1)) (R - 1 + n)]
  rfl

/-- The local commutator inequality for a positive open interaction follows
from its eventual kernel identity and uniform gap above the kernel. Tensor convergence
derives the energy, excitation norm, and ground-projection limits.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem _root_.Kraus.HasComplementaryFixedPointGap.localCommutator_gap_of_openInteraction_gap
    [NeZero D] {A : MPTensor α (Fin D)} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Fin R → α) (Fin R → α) ℂ)
    (hh : h.PosSemidef)
    (X : Matrix (Fin k → α) (Fin k → α) ℂ) (hR : 0 < R)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    (ψ : (n : ℕ) → EuclideanSpace ℂ (Cfg d ((n + (R - 1) + k) + (R - 1 + n))))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hKernel : ∀ᶠ n in atTop,
      LinearMap.ker (Matrix.toEuclideanLin
        (chainTranslates R ((n + (R - 1) + k) + (R - 1 + n)) h).hamiltonian) =
          ((groundSpace A ((n + (R - 1) + k) + (R - 1 + n))).map (WithLp.linearEquiv 2 ℂ
              _).symm.toLinearMap))
    (hGap : ∀ᶠ n in atTop, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (chainTranslates R ((n + (R - 1) + k) + (R - 1 + n)) h).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ)
    (hGround : ∀ᶠ n in atTop,
      ψ n ∈ ((groundSpace A ((n + (R - 1) + k) + (R - 1 + n))).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap))
    (hUnit : ∀ᶠ n in atTop, ‖ψ n‖ = 1) :
    γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
      (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re := by
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  let H (n : ℕ) := Matrix.toEuclideanLin (chainTranslates R (N n) h).hamiltonian
  have hEnergy := hP.openInteraction_commutator_energy_tendsto hρ h X hR ψ hGround hUnit
  exact hP.commutator_gap_of_bulkObservable_energy_limit hρ X hcenter
    (ℓ := fun n : ℕ => n + (R - 1)) (r := fun n => (R - 1) + n)
    (tendsto_add_atTop_nat (R - 1))
    (tendsto_atTop_mono (fun n => Nat.le_add_left n (R - 1)) tendsto_id)
    H ψ hγ (Eventually.of_forall fun n => Matrix.isPositive_toEuclideanLin_iff.mpr
      (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates hh (N n)))
    hGap
    hKernel hGround hUnit hEnergy

end MPSTensor

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D R k : ℕ}

/-- Every positive parent interaction at range at least \(D^4+1\) has one
positive local commutator bound throughout the normalized primitive sector.
All finite-volume and limiting estimates are derived internally.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2 and Section 6;
CPGSV21, arXiv:2011.12127, lines 2170--2172. -/
theorem exists_pos_localCommutator_gap_of_isParentInteraction
    [NeZero D] {A : MPTensor α (Fin D)} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef)
    (h : Matrix (Fin R → α) (Fin R → α) ℂ)
    (hh : IsParentInteraction A R (Matrix.toEuclideanLin h)) (hR : D ^ 4 + 1 ≤ R) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {k : ℕ} (X : Matrix (Fin k → α) (Fin k → α) ℂ),
      0 < k → observableInsertionExpectation A ρ X = 0 →
        γ * (observableInsertionExpectation A ρ (Xᴴ * X)).re ≤
          (observableInsertionExpectation A ρ (localCommutatorObservable h X)).re := by
  have hNormal := isNormal_of_hasComplementaryFixedPointGap_with_posDef hP hρ
  have hD : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
  have hRpos : 0 < R := by omega
  obtain ⟨δ, hδ, hcanonicalGap⟩ :=
    exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNormal_of_le A hNormal hR
  obtain ⟨γ, hγ, hgap⟩ :=
    hh.exists_hamiltonian_chainTranslates_uniform_gap_of_canonical_gap hδ hcanonicalGap
  refine ⟨γ, hγ, ?_⟩
  intro k X _ hcenter
  let N (n : ℕ) := (n + (R - 1) + k) + (R - 1 + n)
  have hN : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [N]; omega) tendsto_id
  obtain ⟨ψ, hg, hu⟩ := hP.exists_eventually_unit_map_groundSpace hρ N hN
  have hInj : Kraus.IsNBlkInjective A (R - 1) :=
    Kraus.isNBlkInjective_of_le hD (isNBlkInjective_pow_four_of_isNormal A hNormal) (by omega)
  have hRange : R - 1 + 1 = R := by omega
  apply hP.localCommutator_gap_of_openInteraction_gap hρ h
    (Matrix.isPositive_toEuclideanLin_iff.mp hh.isPositive) X hRpos
    hcenter ψ hγ.le
  · exact Eventually.of_forall fun n => by
      rw [hh.ker_hamiltonian_chainTranslates_eq_ker_parentChainInteraction]
      have h := ker_hamiltonian_parentChainInteraction_eq_map_groundSpace_of_isNBlkInjective
        hInj (by omega : 0 < R - 1) (by dsimp [N]; omega : R - 1 + 1 ≤ N n)
      rwa [hRange] at h
  · exact Eventually.of_forall fun n => hgap (N n) (by dsimp [N]; omega)
  · exact Eventually.of_forall hg
  · exact hu

end Kraus.HasComplementaryFixedPointGap
