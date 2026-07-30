/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.SharedInfra.SectorDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Eventual dimension of nearest-neighbor parent ground spaces

For a sector decomposition whose basis matrix product vectors are eventually
linearly independent, the all-chain nearest-neighbor ground-space spanning
condition makes the parent-Hamiltonian ground-space dimension eventually equal
to the number of basis sectors. This is the scale-invariance hypothesis used in
Beigi's classification of one-dimensional commuting Hamiltonians.

## Main statement

* `HasBNTSectorData.eventually_parentHamiltonian_groundSpace_finrank_eq`:
  the parent ground-space dimension is eventually the number of distinct BNT
  representatives.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 3.9 and Theorem 3.10, lines 517--540.
* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, arXiv:1105.1019.
-/

namespace MPSTensor

/-- If the basis-sector matrix product vectors are eventually linearly independent and
span every sufficiently long nearest-neighbor parent ground space, then the dimension of
that ground space is eventually the number of distinct basis sectors.

Comparison: arXiv:1606.00608, Definition 3.9 and Theorem 3.10, lines 517--540.
Those passages do not state this dimension count. It is a local consequence of
the all-chain spanning equality and eventual linear independence, and supplies
the eventual ground-state degeneracy used in Beigi, arXiv:1105.1019,
Section IV. Documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem HasBNTSectorData.eventually_parentHamiltonian_groundSpace_finrank_eq
    {d : ℕ} {P : SectorDecomposition d}
    (hBNT : HasBNTSectorData P)
    (hNNCPH : HasNNCPHGroundSpaces P.toTensor P.basis) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      Module.finrank ℂ (LinearMap.ker (parentHamiltonian P.toTensor 2 N)) =
        P.basisCount := by
  rcases hBNT with ⟨N₁, hLI⟩
  refine ⟨max N₁ 2, ?_⟩
  intro N hN
  have hN₁ : N₁ < N := lt_of_le_of_lt (Nat.le_max_left _ _) hN
  have hTwo : 2 < N := lt_of_le_of_lt (Nat.le_max_right _ _) hN
  have hImage : LinearIndependent ℂ
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘
        fun j : Fin P.basisCount ↦ (mpv (P.basis j) : NSiteSpace d N)) := by
    convert hLI N hN₁ using 1
    funext j
    ext σ
    simp [Function.comp_apply, mpvState_apply]
  have hCoefficients : LinearIndependent ℂ
      (fun j : Fin P.basisCount ↦ (mpv (P.basis j) : NSiteSpace d N)) :=
    LinearIndependent.of_comp
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap hImage
  rw [(hNNCPH N hTwo).groundSpaceSpanning, bntMPSVectorSpan]
  simpa using finrank_span_eq_card hCoefficients

end MPSTensor
