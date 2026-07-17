/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InverseMapPhysicalSectorFactorization
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition
import TNLean.MPS.MPDO.SectorEtaPositivity

/-!
# Positive cyclic sector products from the strong area law

This file combines the raw physical-sector factorization obtained from an
injective tensor satisfying the strong area law with positivity of the
finite-chain operators. Every complete cyclic product of neighboring
contractions is positive semidefinite because it is a diagonal sector
compression of a physically conjugated finite-chain operator.

No positivity of an individual neighboring contraction is asserted.

## Main declaration

- `MPOTensor.exists_physicalSectorFactorization_with_cyclicNeighboringProduct_posSemidef_of_isSAL`:
  existence of a physical-sector factorization whose complete nonempty cyclic
  neighboring products are positive semidefinite.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemma C.4, lines 1406--1450
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- An injective MPO tensor satisfying SAL admits a physical-sector
factorization for which every complete nonempty cyclic product of neighboring
operators is positive semidefinite.

The product is a diagonal sector compression of the physically conjugated
finite-chain MPO. This does not give a single coherent positive choice for
the individual neighboring operators.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.4 (`propSN`), lines
1406--1450. -/
theorem
    exists_physicalSectorFactorization_with_cyclicNeighboringProduct_posSemidef_of_isSAL
    (K : MPOTensor d D) (hK : K.IsInjective) (hSAL : IsSAL K) :
    ∃ F : PhysicalSectorFactorization K,
      ∀ {N : ℕ} [NeZero N] (k : Fin N → Fin F.sectorCount),
        (F.cyclicNeighboringProduct k).PosSemidef := by
  obtain ⟨F⟩ := nonempty_physicalSectorFactorization_of_isSAL K hK hSAL
  refine ⟨F, ?_⟩
  intro N _ k
  rw [← F.mpo_submatrix_sector_eq_cyclicNeighboringProduct k]
  exact (mpo_conjugatePhysical_posSemidef K F.physicalIsometry
    (Classical.choose hSAL N (NeZero.pos N))).submatrix _

end MPOTensor
