/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveBlockMatchingData
import TNLean.MPS.Core.PhysicalReindexTransport

/-!
# Physical reindexing for normal-form BNT hypotheses

This file transports the normal-form and BNT hypotheses used in the common primitive
comparison along a bijection of physical alphabets.

## Main statements

* `IsNormalCanonicalForm.reindexPhysical_equiv` — normal canonical form is preserved by
  reindexing all physical letters.
* `BlocksNotGaugePhaseEquiv.reindexPhysical_equiv` and
  `IsNormalCanonicalFormBNT.reindexPhysical_equiv` — BNT separation and normal-CF-BNT
  hypotheses are preserved.
-/

open scoped BigOperators

namespace MPSTensor

namespace IsNormalCanonicalForm

/-- Transport a normal canonical form proof along a physical-index equivalence. -/
def reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (h : IsNormalCanonicalForm (d := d₂) μ A) (e : Fin d₁ ≃ Fin d₂) :
    IsNormalCanonicalForm (d := d₁) μ (fun k => reindexPhysical e (A k)) where
  block_irreducible := fun k =>
    (isIrreducibleTensor_reindexPhysical_equiv e (A k)).mpr (h.block_irreducible k)
  leftCanonical := fun k =>
    (leftCanonical_reindexPhysical_equiv e (A k)).mpr (h.leftCanonical k)
  block_primitive := fun k =>
    (isPrimitive_transferMap_reindexPhysical_equiv e (A k)).mpr (h.block_primitive k)
  mu_antitone := h.mu_antitone
  mu_ne_zero := h.mu_ne_zero
  dim_pos := h.dim_pos

end IsNormalCanonicalForm

namespace BlocksNotGaugePhaseEquiv

/-- Transport BNT separation along a physical-index equivalence. -/
theorem reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d₂) A) (e : Fin d₁ ≃ Fin d₂) :
    BlocksNotGaugePhaseEquiv (d := d₁) (fun k => reindexPhysical e (A k)) := by
  intro j k hjk hdim hG
  apply hBlocks j k hjk hdim
  have hG' : GaugePhaseEquiv
      (reindexPhysical e (cast (congr_arg (MPSTensor d₂) hdim) (A j)))
      (reindexPhysical e (A k)) := by
    rw [reindexPhysical_cast_dim e hdim (A j)]
    exact hG
  exact (gaugePhaseEquiv_reindexPhysical_equiv e
    (cast (congr_arg (MPSTensor d₂) hdim) (A j)) (A k)).mp hG'

end BlocksNotGaugePhaseEquiv

namespace IsNormalCanonicalFormBNT

/-- Transport a normal-CF-BNT proof along a physical-index equivalence. -/
def reindexPhysical_equiv
    {d₁ d₂ r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    {A : (k : Fin r) → MPSTensor d₂ (dim k)}
    (h : IsNormalCanonicalFormBNT (d := d₂) μ A) (e : Fin d₁ ≃ Fin d₂) :
    IsNormalCanonicalFormBNT (d := d₁) μ (fun k => reindexPhysical e (A k)) where
  toIsNormalCanonicalForm := h.toIsNormalCanonicalForm.reindexPhysical_equiv e
  mu_strict_anti := h.mu_strict_anti
  blocks_not_equiv := BlocksNotGaugePhaseEquiv.reindexPhysical_equiv h.blocks_not_equiv e
  mu_dom_norm_one := h.mu_dom_norm_one

end IsNormalCanonicalFormBNT

end MPSTensor
