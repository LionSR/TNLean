/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicTransport
import TNLean.MPS.MPDO.FixedBondPositivePhysicalSectorConstructor
import TNLean.MPS.MPDO.FixedBondProductTensor

/-!
# Fixed matrix-product tensors from neighboring operators

This file records the cyclic edge-weight identity and exposes the selected
fixed-product tensor constructed from positive physical sectors.  Its retained
factorization reconstructs the input commuting bond and has positive
neighboring operators.  The virtual dimension is independent of the chain
length.

## Main definitions and statements

* `etaCyclicEdgeWeight` gives the scalar neighboring-operator weight.
* `reindex_mpo_cyclicEdgeWeightTensor_etaCyclicEdgeWeight` identifies its
  closed operator in sector-edge coordinates.
* `TranslationInvariantBondData.fixedProductTensorData` constructs an exact
  selected fixed tensor for an arbitrary positive commuting bond.
* `TranslationInvariantBondData.fixedProductTensorDataPhysicalSectorFactorization`
  retains the positive physical-sector factorization of the selected tensor.
* `fixedProductTensorDataPhysicalSectorFactorization_physicalBond_eq`
  identifies its reconstructed bond with the input bond.
* `fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos`
  records positivity of its neighboring operators.

## References

* arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines 1581--1593.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MPOTensor

variable {d : ℕ}

open PhysicalSectorFactorization

/-- The scalar edge weight obtained from a family of neighboring operators.

The current site contributes its right coordinate and the following site
contributes its left coordinate.  The block-diagonal matrix forces the ket and
bra sector labels to agree at both endpoints of the edge.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1593. -/
noncomputable def etaCyclicEdgeWeight {K : ℕ} (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ) :
    Fin d → Fin d → Fin d → Fin d → ℂ :=
  fun i j i' j' ↦
    let x := e.symm i
    let y := e.symm j
    let x' := e.symm i'
    let y' := e.symm j'
    Matrix.blockDiagonal' (fun qh : Fin K × Fin K ↦ η qh.1 qh.2)
      ⟨(x.1, x'.1), (x.2.1, x'.2.2)⟩
      ⟨(y.1, y'.1), (y.2.1, y'.2.2)⟩

/-- The cyclic edge-weight tensor is the direct sum of the cyclic products of
the neighboring operators in sector-edge coordinates.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589. -/
theorem reindex_mpo_cyclicEdgeWeightTensor_etaCyclicEdgeWeight
    {K N : ℕ} [NeZero N] (dl dr : Fin K → ℕ)
    (e : Matrix.EtaSiteIndex K dl dr ≃ Fin d)
    (η : (q h : Fin K) →
      Matrix (Matrix.EtaEdgeIndex dl dr q h)
        (Matrix.EtaEdgeIndex dl dr q h) ℂ) :
    Matrix.reindex (Matrix.etaCyclicEdgeEquiv dl dr e)
        (Matrix.etaCyclicEdgeEquiv dl dr e)
        (mpo (cyclicEdgeWeightTensor (etaCyclicEdgeWeight dl dr e η)) N) =
      Matrix.blockDiagonal' fun k : Fin N → Fin K ↦
        fun x y ↦ ∏ n : Fin N, η (k n) (k (n + 1)) (x n) (y n) := by
  classical
  ext ⟨k, x⟩ ⟨h, y⟩
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    mpo_cyclicEdgeWeightTensor]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    apply Finset.prod_congr rfl
    intro n _
    have hx (m : Fin N) :
        e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ m) =
          ⟨k m, (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm x m⟩ := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    have hy (m : Fin N) :
        e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, y⟩ m) =
          ⟨k m, (Matrix.etaFixedSectorCyclicEdgeEquiv dl dr k).symm y m⟩ := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    rw [etaCyclicEdgeWeight]
    rw [hx n, hx (n + 1), hy n, hy (n + 1)]
    rw [Matrix.blockDiagonal'_apply_eq]
    exact congrArg₂ (η (k n) (k (n + 1)))
      (Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge dl dr k x n)
      (Matrix.etaFixedSectorCyclicEdgeEquiv_symm_edge dl dr k y n)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hkh
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    have hk :
        (e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨k, x⟩ n)).1 = k n := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    have hh :
        (e.symm ((Matrix.etaCyclicEdgeEquiv dl dr e).symm ⟨h, y⟩ n)).1 = h n := by
      rw [Matrix.etaCyclicEdgeEquiv_symm_apply, e.symm_apply_apply]
    rw [etaCyclicEdgeWeight]
    rw [Matrix.blockDiagonal'_apply_ne]
    intro hpairs
    apply hn
    simpa only [hk, hh] using congrArg Prod.fst hpairs

namespace TranslationInvariantBondData

/-- A chosen exact matrix-product representation of the fixed commuting-bond
product.  This is the representative whose positive physical sectors are
exposed by `fixedProductTensorDataPhysicalSectorFactorization`.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
noncomputable def fixedProductTensorData (data : TranslationInvariantBondData d) :
    FixedProductTensorData data :=
  data.positivePhysicalSectorFixedProductTensorData.repr

/-- Every positive fixed bond whose periodic translates commute has one
exact matrix-product representation with positive bond dimension, independent
of the chain length.

This theorem asserts existence without specifying a representative.  The
distinguished representative `fixedProductTensorData` carries the factorization
`fixedProductTensorDataPhysicalSectorFactorization`; an arbitrary witness of
this proposition need not be that representative.

This proves only the finite representation of the product.  It does not assert
that the representing tensor is normal and does not constrain the positive
realization scalar of the source MPO.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1. -/
theorem nonempty_fixedProductTensorData (data : TranslationInvariantBondData d) :
    Nonempty (FixedProductTensorData data) :=
  ⟨data.fixedProductTensorData⟩

/-- The positive physical-sector factorization retained by the exact selected
fixed-product tensor.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
noncomputable def fixedProductTensorDataPhysicalSectorFactorization
    (data : TranslationInvariantBondData d) :
    PhysicalSectorFactorization data.fixedProductTensorData.tensor :=
  data.positivePhysicalSectorFixedProductTensorData.factorization

/-- The physical bond reconstructed from the selected fixed-product
factorization is the input commuting bond.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
theorem fixedProductTensorDataPhysicalSectorFactorization_physicalBond_eq
    (data : TranslationInvariantBondData d) :
    data.fixedProductTensorDataPhysicalSectorFactorization.physicalBond =
      data.bond :=
  data.positivePhysicalSectorFixedProductTensorData.physicalBond_eq

/-- The neighboring operators retained by the selected fixed-product
factorization are positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1581--1589; Beigi, J. Phys. A 45 (2012) 025306, Lemma 2.1 and Section III. -/
theorem fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos
    (data : TranslationInvariantBondData d) :
    ∀ q h,
      (data.fixedProductTensorDataPhysicalSectorFactorization
        |>.neighboringOperator q h).PosSemidef :=
  data.positivePhysicalSectorFixedProductTensorData.neighboring_pos

end TranslationInvariantBondData

namespace EtaLocalStructureData

variable {D : ℕ} {M : MPOTensor d D}

/-- The bond carried by an eta-local structure has one exact fixed matrix-product
representation.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605. -/
theorem nonempty_fixedProductTensorData (data : EtaLocalStructureData M) :
    Nonempty (TranslationInvariantBondData.FixedProductTensorData data.bondData) :=
  data.bondData.nonempty_fixedProductTensorData

/-- A chosen exact fixed matrix-product representation of the bond carried by an eta-local
structure.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2` and Proposition
`4to2`, lines 1581--1605. -/
noncomputable def fixedProductTensorData (data : EtaLocalStructureData M) :
    TranslationInvariantBondData.FixedProductTensorData data.bondData :=
  data.bondData.fixedProductTensorData

end EtaLocalStructureData

end MPOTensor
