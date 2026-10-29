/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.DependentPairCoordinates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The open parent on genuinely varying physical spaces

Each actual pair trace range is projected onto its orthogonal complement,
extended by the identity outside that pair, and transported back through the
dependent pair/outside coordinate bijection. Summing adjacent terms defines
the open parent directly on the true physical configuration space. Sitewise
physical embeddings intertwine these actual local terms and their full sum.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and equation unique-OBC,
source lines 1195–1220. No chain record, local annihilation condition or
Hamiltonian transport identity is supplied as an additional hypothesis.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The actual complementary pair projection, extended by the identity on
every other physical site. Source: PGVWC07, Theorem 9, lines 1201–1217. -/
noncomputable def physicalPairParentTerm (β : ι → Type*) [∀ k, Fintype (β k)]
    (i j : ι) (hji : j ≠ i) (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ) :
    EuclideanSpace ℂ ((k : ι) → β k) →ₗ[ℂ] EuclideanSpace ℂ ((k : ι) → β k) :=
  (pairConfigurationReindex β i j hji).symm.toLinearEquiv.conj
    (ContinuousLinearMap.rightFiberwiseMap
      (S := (k : {k : {k : ι // k ≠ i} // k ≠ ⟨j, hji⟩}) → β k.val.val)
      (LinearMap.range (rectangularPairBoundary A B))ᗮ.starProjection).toLinearMap

private theorem physicalPairParentTerm_in_coordinates
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (v : EuclideanSpace ℂ ((k : ι) → β k)) :
    pairConfigurationReindex β i j hji (physicalPairParentTerm β i j hji A B v) =
      ContinuousLinearMap.rightFiberwiseMap
        (LinearMap.range (rectangularPairBoundary A B))ᗮ.starProjection
        (pairConfigurationReindex β i j hji v) := by
  exact (pairConfigurationReindex β i j hji).apply_symm_apply _

/-- Every actual local parent term on dependent physical spaces is positive.
Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem physicalPairParentTerm_isPositive
    (β : ι → Type*) [∀ k, Fintype (β k)] (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ) :
    (physicalPairParentTerm β i j hji A B).IsPositive := by
  apply (LinearMap.isPositive_linearIsometryEquiv_conj_iff
    (pairConfigurationReindex β i j hji).symm).mpr
  exact (ContinuousLinearMap.isSymmetricProjection_rightFiberwiseMap _
    (Submodule.isSymmetricProjection_starProjection _)).isPositive

/-- The actual local parent terms intertwine with the full dependent physical
embedding. Their ranges, projections and outside extensions are all derived.
Source: PGVWC07, Theorem 9, lines 1195–1220. -/
theorem physicalPairParentTerm_extend_physical (β γ : ι → Type*)
    [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (i j : ι) (hji : j ≠ i)
    (A : β i → Matrix a b ℂ) (B : β j → Matrix b c ℂ)
    (v : EuclideanSpace ℂ ((k : ι) → β k)) :
    physicalPairParentTerm γ i j hji (Function.extend (e i) A 0)
        (Function.extend (e j) B 0)
        ((Function.Embedding.piCongrRight e).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight e).euclideanExtendByZero
        (physicalPairParentTerm β i j hji A B v) := by
  apply (pairConfigurationReindex γ i j hji).injective
  rw [physicalPairParentTerm_in_coordinates, pairConfigurationReindex_extendByZero,
    pair_parent_localTerm_extend_physical, pairConfigurationReindex_extendByZero,
    physicalPairParentTerm_in_coordinates]

private def adjacentLeft {N : ℕ} (j : Fin (N - 1)) : Fin N :=
  ⟨j.val, by have := j.isLt; omega⟩

private def adjacentRight {N : ℕ} (j : Fin (N - 1)) : Fin N :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

private theorem adjacentRight_ne_left {N : ℕ} (j : Fin (N - 1)) :
    adjacentRight j ≠ adjacentLeft j := by
  intro h
  have hv := congrArg Fin.val h
  change j.val + 1 = j.val at hv
  omega

/-- The actual varying-physical-space open parent Hamiltonian is the sum of
the adjacent complementary pair projections extended by identity. Its state
space is the true dependent product, with no common-alphabet premise.
Source: PGVWC07, Theorem 9, lines 1195–1217. -/
noncomputable def varyingPhysicalParentHamiltonian {N : ℕ}
    (β : Fin N → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ) :
    EuclideanSpace ℂ ((k : Fin N) → β k) →ₗ[ℂ]
      EuclideanSpace ℂ ((k : Fin N) → β k) :=
  ∑ j : Fin (N - 1), physicalPairParentTerm β (adjacentLeft j) (adjacentRight j)
    (adjacentRight_ne_left j) (A (adjacentLeft j)) (A (adjacentRight j))

/-- Positivity of the actual open sum requires no canonical or spanning
hypothesis. Source: PGVWC07, Theorem 9 proof, lines 1213–1217. -/
theorem varyingPhysicalParentHamiltonian_isPositive {N : ℕ}
    (β : Fin N → Type*) [∀ k, Fintype (β k)] (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ) :
    (varyingPhysicalParentHamiltonian β D A).IsPositive := by
  exact LinearMap.isPositive_sum Finset.univ fun j _ ↦
    physicalPairParentTerm_isPositive β _ _ _ _ _

/-- Sitewise physical embeddings intertwine the actual full open Hamiltonians.
The local identities and their sum are proved, not supplied as premises.
Source: PGVWC07, Theorem 9, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_extend_physical {N : ℕ}
    (β γ : Fin N → Type*) [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (v : EuclideanSpace ℂ ((k : Fin N) → β k)) :
    varyingPhysicalParentHamiltonian γ D (fun k ↦ Function.extend (e k) (A k) 0)
        ((Function.Embedding.piCongrRight e).euclideanExtendByZero v) =
      (Function.Embedding.piCongrRight e).euclideanExtendByZero
        (varyingPhysicalParentHamiltonian β D A v) := by
  simp only [varyingPhysicalParentHamiltonian, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact physicalPairParentTerm_extend_physical β γ e _ _ _ _ _ v

/-- The actual dependent parent kernel is transported faithfully by physical
extension; no zero-energy equation is assumed on either side.
Source: PGVWC07, Theorem 9 and proof, lines 1195–1220. -/
theorem varyingPhysicalParentHamiltonian_extend_eq_zero_iff {N : ℕ}
    (β γ : Fin N → Type*) [∀ k, Fintype (β k)] [∀ k, Fintype (γ k)]
    (e : ∀ k, β k ↪ γ k) (D : ℕ → ℕ)
    (A : ∀ k : Fin N, β k → Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (v : EuclideanSpace ℂ ((k : Fin N) → β k)) :
    varyingPhysicalParentHamiltonian γ D (fun k ↦ Function.extend (e k) (A k) 0)
        ((Function.Embedding.piCongrRight e).euclideanExtendByZero v) = 0 ↔
      varyingPhysicalParentHamiltonian β D A v = 0 := by
  rw [varyingPhysicalParentHamiltonian_extend_physical]
  constructor
  · intro hzero
    apply (Function.Embedding.piCongrRight e).euclideanExtendByZero.injective
    rw [map_zero]
    exact hzero
  · intro hzero
    rw [hzero, map_zero]

end Matrix
