/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.PhysicalReindex
import TNLean.MPS.CanonicalForm.NormalBlocks.TensorProduct
import TNLean.MPS.Tensor.Physical.TensorProduct
import TNLean.MPS.CanonicalForm.SimpleMPU.FullSupport
import TNLean.MPS.MPU.CanonicalForm.TensorProduct
import TNLean.MPS.CanonicalForm.SimpleMPU.TransferMatrix

/-!
# Canonical-form-II data for an independent tensor product

This file identifies the normalized tensor of an independent MPO tensor product
with the independent tensor product of the two normalized tensors on their pair
alphabets.  The physical coordinate is regrouped in the canonical
product-coordinate order
`((i, k), (j, l)) ↦ ((i, j), (k, l))`.

It then transports the generic product canonical-form-II data through this
identity.  Full support is supplied separately for the two input data; it is
not part of the generic canonical-form construction.

## Main statement

* `MPOTensor.tensorProductPairEquiv`: the regrouping of the pair alphabet of a
  tensor product.
* `MPOTensor.normalizedFlattening_tensorProduct`: normalized flattening commutes
  with independent tensor products after the regrouping of the pair alphabet.
* `MPOTensor.tensorProductCFIIData`: product canonical-form-II data for the
  normalized flattening.
* `MPOTensor.hasFullSupport_tensorProductCFIIData`: full support of those data
  from full support of the two inputs.
* `MPOTensor.IsMPUCanonicalFormII.tensorProduct`: independent tensor products
  preserve the bundled presentation, with the reindexed product fixed matrix.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188], equation
  `eq:transfer-op`, lines 336--340, and the proof of Theorem `IndexTh` (ii),
  lines 824--845.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPSTensor.CPSVCanonicalFormIIData

variable {α β : Type*} [Fintype α] [Fintype β] {D E : ℕ}
  {A : MPTensor α (Fin D)} {B : MPTensor β (Fin E)}

/-- Full support of two canonical-form-II data is preserved by their
independent tensor product.

The dimension identity is
`∑_(a,b) D_a E_b = (∑_a D_a)(∑_b E_b)`.  Full support is a supplied
reduced-representative restriction, not a statement of CPSV16 or CPSV17; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem hasFullSupport_tensorProduct (dataA : CPSVCanonicalFormIIData A)
    (dataB : CPSVCanonicalFormIIData B)
    (hA : dataA.toCPSVCanonicalFormData.HasFullSupport)
    (hB : dataB.toCPSVCanonicalFormData.HasFullSupport) :
    (dataA.tensorProduct dataB).toCPSVCanonicalFormData.HasFullSupport := by
  change
    (∑ ab : Fin (dataA.r * dataB.r),
      dataA.dim (finProdFinEquiv.symm ab).1 *
        dataB.dim (finProdFinEquiv.symm ab).2) = D * E
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  rw [← Fintype.sum_mul_sum, hA, hB]

end MPSTensor.CPSVCanonicalFormIIData

namespace MPOTensor

variable {d D e E : ℕ}

/-- The regrouping `((i, k), (j, l)) ↦ ((i, j), (k, l))` of the pair alphabet of
an independent MPO tensor product, whose ket and bra indices encode the pairs
`(i, k)` and `(j, l)` by `finProdFinEquiv`.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845. -/
def tensorProductPairEquiv (d e : ℕ) :
    Fin (d * e) × Fin (d * e) ≃ (Fin d × Fin d) × (Fin e × Fin e) :=
  (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    (Equiv.prodProdProdComm (Fin d) (Fin e) (Fin d) (Fin e))

/-- Normalized flattening commutes with independent tensor products after the
regrouping `((i, k), (j, l)) ↦ ((i, j), (k, l))` of the pair alphabet.

The scalar equality is
`(sqrt (d * e))⁻¹ = (sqrt d)⁻¹ * (sqrt e)⁻¹`; it holds without nonzero-dimension
hypotheses because inverses in `ℂ` are totalized.
This identity makes explicit the normalized-flattening compatibility
corresponding to the tensoring clause in arXiv:1703.09188, proof of Theorem
`IndexTh` (ii), lines 824--845; the paper does not state it separately. -/
theorem normalizedFlattening_tensorProduct (U : MPOTensor d D) (V : MPOTensor e E) :
    (tensorProduct U V).normalizedFlattening =
      Kraus.reindexPhysical (tensorProductPairEquiv d e)
        (MPSTensor.tensorProduct U.normalizedFlattening V.normalizedFlattening) := by
  have hsqrt :
      (Real.sqrt ((d * e : ℕ) : ℝ) : ℂ) =
        (Real.sqrt d : ℂ) * (Real.sqrt e : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  funext ⟨ik, jl⟩
  rcases finProdFinEquiv.surjective ik with ⟨⟨i, k⟩, rfl⟩
  rcases finProdFinEquiv.surjective jl with ⟨⟨j, l⟩, rfl⟩
  ext ac bd
  rcases finProdFinEquiv.surjective ac with ⟨⟨a, c⟩, rfl⟩
  rcases finProdFinEquiv.surjective bd with ⟨⟨b, b'⟩, rfl⟩
  simp only [normalizedFlattening, Kraus.reindexPhysical, tensorProductPairEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply,
    Equiv.prodProdProdComm_apply, MPSTensor.tensorProduct_apply,
    MPOTensor.tensorProduct_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsqrt, mul_inv]
  ring

/-- Canonical-form-II data for the normalized flattening of an independent
MPO tensor product.

For retained labels `(a,b)`, this uses the CPSV16 data
`D_(a,b) = D_a E_b`, `ω_(a,b) = μ_a ν_b`,
`C_(a,b) = A_a ⊠ B_b`, and the reindexed fixed point
`Λ_(a,b) = reind (Λ_a ⊗ Γ_b)`.  The canonical-form and CFII conditions are
arXiv:1606.00608, equation `II_CF1`, lines 214--245, and Appendix A,
equations `TP` and `Lambda`, lines 1054--1077.  The final physical relabeling
uses `normalizedFlattening_tensorProduct`.  This is project infrastructure for
the tensoring sentence in arXiv:1703.09188, proof of Theorem `IndexTh` (ii),
lines 824--845, not a theorem separately stated there. -/
noncomputable def tensorProductCFIIData (U : MPOTensor d D) (V : MPOTensor e E)
    (dataU : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (dataV : MPSTensor.CPSVCanonicalFormIIData V.normalizedFlattening) :
    MPSTensor.CPSVCanonicalFormIIData (tensorProduct U V).normalizedFlattening :=
  (normalizedFlattening_tensorProduct U V).symm ▸
    (dataU.tensorProduct dataV).reindexPhysical (tensorProductPairEquiv d e)

/-- The product canonical-form-II data have full support when both supplied
input data have full support.

**Scope restriction (full support):** full support selects TNLean's reduced
representatives and is not asserted by the tensoring sentence in CPSV17.
Documented in `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem hasFullSupport_tensorProductCFIIData (U : MPOTensor d D)
    (V : MPOTensor e E)
    (dataU : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (dataV : MPSTensor.CPSVCanonicalFormIIData V.normalizedFlattening)
    (hU : dataU.toCPSVCanonicalFormData.HasFullSupport)
    (hV : dataV.toCPSVCanonicalFormData.HasFullSupport) :
    (tensorProductCFIIData U V dataU dataV).toCPSVCanonicalFormData.HasFullSupport := by
  have hprod := dataU.hasFullSupport_tensorProduct dataV hU hV
  have hreindex :=
    MPTensor.CPSVCanonicalFormData.hasFullSupport_reindexPhysical
      (dataU.tensorProduct dataV).toCPSVCanonicalFormData hprod (tensorProductPairEquiv d e)
  exact ((dataU.tensorProduct dataV).reindexPhysical
    (tensorProductPairEquiv d e)).hasFullSupport_cast hreindex
      (normalizedFlattening_tensorProduct U V)

/-- The independent tensor product of two MPUs in canonical form II is again
in canonical form II. Its ambient right fixed matrix is the reindexed tensor
product of the two recorded matrices, in the product bond coordinates.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--845;
canonical-form-II convention, lines 269--281. The full-support convention is
documented in `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
noncomputable def IsMPUCanonicalFormII.tensorProduct
    {U : MPOTensor d D} {V : MPOTensor e E}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V) :
    IsMPUCanonicalFormII (tensorProduct U V) where
  isMPU := hU.isMPU.tensorProduct hV.isMPU
  cfii := tensorProductCFIIData U V hU.cfii hV.cfii
  fullSupport_eq := hasFullSupport_tensorProductCFIIData U V hU.cfii hV.cfii
    hU.hasFullSupport hV.hasFullSupport
  ρ := Matrix.reindex finProdFinEquiv finProdFinEquiv (hU.ρ ⊗ₖ hV.ρ)
  ρ_posDef := (hU.ρ_posDef.kronecker hV.ρ_posDef).submatrix finProdFinEquiv.symm.injective
  ρ_isDiag := (hU.ρ_isDiag.kronecker hV.ρ_isDiag).submatrix finProdFinEquiv.symm.injective
  ρ_trace := by
    rw [Matrix.trace_reindex, Matrix.trace_kronecker, hU.ρ_trace, hV.ρ_trace, one_mul]
  ρ_fixed := by
    rw [normalizedFlattening_tensorProduct, Kraus.transferMap_reindexPhysical_equiv,
      MPSTensor.transferMap_tensorProduct_kronecker, hU.ρ_fixed, hV.ρ_fixed]

end MPOTensor
