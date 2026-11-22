/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# Open-chain sums of a fixed local operator on Euclidean space

Extend a local operator by the identity on the remaining physical sites, and sum its translates
whose windows remain inside the open chain. For the canonical complementary ground-space
projection this is the operator of the Hamiltonian of the parent interaction on the open chain.

Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12); CPGSV21,
arXiv:2011.12127, Section IV.C, lines 1996--1999 and 2170--2172.

**Transitional (#10948).** For a local matrix `h` the open-chain sum is the Hamiltonian of
`ManyBody.Interaction.chainTranslates R N h`, and all statements about open chains outside the
mixed-endpoint files of `TNLean/MPS/Symmetry/MPOSymmetry` are made for it. The two declarations
of this file are kept for those files and are deleted when they are converted.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Sum a fixed local interaction over all nonwrapping windows of an open chain.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12); the local
parent-interaction convention is CPGSV21, arXiv:2011.12127, lines 1996--1999. -/
noncomputable def openInteractionHamiltonianES {R : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (N : ℕ) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : NonwrappingStart R N, periodicLocalInteractionES h i.1

/-- The open sum of the canonical parent projection is the canonical open Hamiltonian. -/
theorem openInteractionHamiltonianES_parentInteractionES {R : ℕ}
    (A : MPSTensor d D) (hR : 0 < R) (N : ℕ) :
    openInteractionHamiltonianES (parentInteractionES A R) N =
      Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian := by
  simp only [openInteractionHamiltonianES, periodicLocalInteractionES_parentInteractionES A hR]
  exact (hamiltonian_parentChainInteraction_eq_sum_localTermES A hR N).symm

end MPSTensor
