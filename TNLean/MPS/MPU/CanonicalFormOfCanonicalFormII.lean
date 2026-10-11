/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MPUCanonicalForm

/-!
# Canonical form from canonical form II

An MPU tensor in canonical form II is in canonical form. Canonical form II
writes the normalized flattening `d^{-1/2} U` as a weighted retained-block
reconstruction with normal blocks; a normal block is irreducible and has
transfer spectral radius one, so the same blocks, with weights multiplied by
`d^{1/2}`, give canonical-form data for the flattening of `U` itself.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.isMPUCanonicalForm`: canonical form II implies
  canonical form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, canonical form,
  lines 259--267, and canonical form II, lines 269--281 and 344--356.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

namespace IsMPUCanonicalFormII

/-- The retained-block data of canonical form II are canonical-form data for the
normalized flattening: normal blocks are irreducible with transfer spectral radius
one, and the retained blocks fill the bond space.

Source: arXiv:1703.09188, lines 259--267 and 269--281. -/
noncomputable def normalizedFlatteningCanonicalFormData {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) :
    MPSTensor.MPUCanonicalFormData U.normalizedFlattening where
  toRetainedBlockReconstructionData :=
    hU.cfii.toCPSVCanonicalFormData.toRetainedBlockReconstructionData
  blocks_canonical k :=
    ⟨(hU.cfii.blocks_normal k).no_invariant_proj,
      (hU.cfii.blocks_normal k).spectral_radius_one⟩
  total_dim_eq := hU.fullSupport_eq

/-- An MPU tensor in canonical form II is in canonical form: the normal blocks of
the normalized flattening `d^{-1/2} U`, with weights multiplied by `d^{1/2}`,
reconstruct the flattening of `U`.

Source: arXiv:1703.09188, canonical form, lines 259--267, and canonical form II,
lines 269--281 and 344--356. -/
theorem isMPUCanonicalForm [NeZero d] {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) : MPSTensor.IsMPUCanonicalForm U.toMPSTensor := by
  have hc : (Real.sqrt d : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hU' : (fun i => (Real.sqrt d : ℂ) • U.normalizedFlattening i) = U.toMPSTensor := by
    funext i
    simp only [normalizedFlattening, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [← hU']
  exact ⟨hU.normalizedFlatteningCanonicalFormData.smul _ hc⟩

end IsMPUCanonicalFormII

end MPOTensor
