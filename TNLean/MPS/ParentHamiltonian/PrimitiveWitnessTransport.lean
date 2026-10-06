/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks
import TNLean.MPS.Core.PhysicalReindexTransport

/-!
# Primitive fixed-point witnesses under blocking and physical relabelling

Positive blocking preserves a primitive tensor with its supplied faithful
stationary matrix. A bijective change of the physical alphabet preserves
the same witness without any additional faithfulness assumption. These
statements retain the stationary matrix, rather than choosing another
representative of its ray.

Source: De las Cuevas--Cirac--Schuch--Perez-Garcia, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 434--451; Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435,
and the grouping argument in Section 6, lines 2649--2675.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D : ℕ} [NeZero D]

/-- Every positive blocking retains the same faithful primitive fixed-point
witness. Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451, specialized to a period-one tensor; Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPrimitiveMPS.blockTensor {A : MPSTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : IsPrimitiveMPS A ρ)
    (hρ : ρ.PosDef) {q : ℕ} (hq : 0 < q) :
    IsPrimitiveMPS (blockTensor A q) ρ := by
  obtain ⟨hTP, hPrim, hIrr⟩ := tp_primitive_irreducible_extra_blocking A
    hP.norm hP.isPrimitive (hP.isIrreducibleFamily_of_posDef hρ) hq
  have hFix := transferMap_blockTensor_fixedPoint A q ρ hP.fixedPoint_is_fixed
  obtain ⟨htr, hGap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (Kraus.transferMap (MPSTensor.blockTensor A q)) (Kraus.isChannel_mapLM _ hTP)
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrr)
      hPrim ρ hP.fixedPoint_psd hP.fixedPoint_ne_zero hFix
  exact ⟨hTP, hP.fixedPoint_ne_zero, hP.fixedPoint_psd, hFix, hGap⟩

/-- A bijective relabelling of physical letters preserves a primitive
fixed-point witness, since both the Kraus normalization and transfer map
are unchanged. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), lines 1394--1435. -/
theorem IsPrimitiveMPS.reindexPhysical {d₁ d₂ : ℕ} {A : MPSTensor d₂ D}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : IsPrimitiveMPS A ρ)
    (e : Fin d₁ ≃ Fin d₂) : IsPrimitiveMPS (Kraus.reindexPhysical e A) ρ := by
  have hMap : Kraus.mapLM (Kraus.reindexPhysical e A) = Kraus.mapLM A :=
    transferMap_reindexPhysical_equiv e A
  refine ⟨(leftCanonical_reindexPhysical_equiv e A).mpr hP.norm,
    hP.fixedPoint_ne_zero, hP.fixedPoint_psd, ?_, ?_⟩
  · simpa only [hMap] using hP.fixedPoint_is_fixed
  · simpa only [hMap] using hP.complementary_transfer_map_gap

end MPSTensor
