/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicInteraction
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.ParentInteraction.CanonicalParentInteractionMatrix

/-!
# Open-chain sums of a fixed local interaction

Extend a local interaction by the identity on the remaining physical sites,
and sum its translates whose windows remain inside the open chain. Positivity,
order, and scalar multiplication are preserved. The canonical complementary
ground-space projection gives the canonical open parent Hamiltonian.

Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.12); CPGSV21,
arXiv:2011.12127, Section IV.C, lines 1996--1999 and 2170--2172.

## The positive canonical interaction from exact open kernels

An exact kernel identity for the canonical range-\(R\) open Hamiltonian gives
an explicit positive local interaction with those same open kernels. The
witness is recorded as the canonical projection matrix itself. This equality
retains the literal local support when subsequent gap and state arguments
use the constructed interaction.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `existenceinteraction`,
lines 2195--2230, the orthogonal-complement construction of the interaction.
-/

section

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

/-- Extension and summation over nonwrapping windows preserve local order. -/
theorem openInteractionHamiltonianES_mono {R : ℕ}
    {h k : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hle : h ≤ k) (N : ℕ) :
    openInteractionHamiltonianES h N ≤ openInteractionHamiltonianES k N :=
  Finset.sum_le_sum fun i _ ↦ periodicLocalInteractionES_mono hle i.1

/-- The open interaction sum commutes with scalar multiplication. -/
theorem openInteractionHamiltonianES_smul {R : ℕ} (c : ℂ)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) (N : ℕ) :
    openInteractionHamiltonianES (c • h) N = c • openInteractionHamiltonianES h N := by
  simp only [openInteractionHamiltonianES, periodicLocalInteractionES_smul, Finset.smul_sum]
/-- The open Hamiltonian of a zero interaction is zero. -/
@[simp] theorem openInteractionHamiltonianES_zero {R : ℕ} (N : ℕ) :
    openInteractionHamiltonianES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) N = 0 := by
  simp [openInteractionHamiltonianES, periodicLocalInteractionES]
/-- A positive local interaction gives a positive open-chain Hamiltonian. -/
theorem openInteractionHamiltonianES_isPositive {R : ℕ}
    {h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)}
    (hh : h.IsPositive) (N : ℕ) : (openInteractionHamiltonianES h N).IsPositive := by
  exact LinearMap.nonneg_iff_isPositive.mp (by
    simpa only [openInteractionHamiltonianES_zero] using
      openInteractionHamiltonianES_mono (LinearMap.nonneg_iff_isPositive.mpr hh) N)
/-- The open sum of the canonical parent projection is the canonical open Hamiltonian. -/
theorem openInteractionHamiltonianES_parentInteractionES {R : ℕ}
    (A : MPSTensor d D) (hR : 0 < R) (N : ℕ) :
    openInteractionHamiltonianES (parentInteractionES A R) N =
      openParentHamiltonianES A R N := by
  simp only [openInteractionHamiltonianES,
    periodicLocalInteractionES_parentInteractionES A hR, openParentHamiltonianES]

end MPSTensor

end

section

open scoped ComplexOrder
namespace MPSTensor
variable {d D R : ℕ}

/-- Exact canonical open kernels give a positive interaction equal to the
canonical local projection matrix, with the same kernels at every volume
at least its positive range. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma `existenceinteraction`, lines 2195--2230. -/
theorem exists_positive_canonical_parent_interaction_of_exact_open_kernels
    (A : MPSTensor d D) (hR : 0 < R)
    (hKernel : ∀ N, R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N) :
    ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h = canonicalParentInteractionMatrix A R ∧ h.PosSemidef ∧
      ∀ N, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N := by
  refine ⟨canonicalParentInteractionMatrix A R, rfl,
    canonicalParentInteractionMatrix_posSemidef A R, ?_⟩
  intro N hN
  rw [toEuclideanLin_canonicalParentInteractionMatrix,
    openInteractionHamiltonianES_parentInteractionES A hR]
  exact hKernel N hN

end MPSTensor

end
