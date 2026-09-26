/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalBlockingResiduals
import TNLean.MPS.MPU.TwoSiteStandardFormOpenWord

/-!
# Original-site residual words and the two-site blocked tensor

The residual-site physical-blocking identity keeps the original prefix and
suffix words on the two sides of a directly blocked middle word. The middle
word can be relabeled as the two-site block of a length-`k` tensor without
altering either residual factor. This is the coordinate bridge needed to
apply open standard-form identities on an arbitrary finite interval.

The identities alone do not establish stabilization of finite-chain
conjugations.

## References

* arXiv:1703.09188, lines 603--622 and 2300--2306.
* arXiv:1606.00608, Appendix C.4, lines 1952--2017.
-/

namespace MPOTensor

/-- The original-site MPO entry is a trace of its residual prefix and suffix
products with a middle word of two-site blocks of `blockTensor U k`. The
physical labels of the complete blocks are relabeled by the explicit
equivalence `twoSiteDirectBlockEquiv`; neither residual word is discarded.

Source context: arXiv:1703.09188, lines 603--622 and 2300--2306, and
arXiv:1606.00608, Appendix C.4, lines 1952--2017. -/
theorem mpo_apply_prefix_twoSiteBlock_suffix
    {d D : ℕ} (U : MPOTensor d D) (k p m s : ℕ)
    (i₀ j₀ : Fin p → Fin d)
    (i₁ j₁ : Fin m → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (i₂ j₂ : Fin s → Fin d) :
    mpo U (p + (m * (2 * k) + s))
        (Fin.append i₀
          (Fin.append (MPSTensor.blockedConfigEquiv d m (2 * k) i₁) i₂))
        (Fin.append j₀
          (Fin.append (MPSTensor.blockedConfigEquiv d m (2 * k) j₁) j₂)) =
      Matrix.trace
        (evalWord U (List.ofFn i₀) (List.ofFn j₀) *
          evalWord (blockTwo (blockTensor U k))
            ((List.ofFn i₁).map (twoSiteDirectBlockEquiv d k))
            ((List.ofFn j₁).map (twoSiteDirectBlockEquiv d k)) *
          evalWord U (List.ofFn i₂) (List.ofFn j₂)) := by
  rw [mpo_apply_prefix_blockTensor_suffix U (2 * k) p m s i₀ j₀ i₁ j₁ i₂ j₂]
  rw [← reindexPhysical_blockTwo_blockTensor_two_mul U k]
  rw [evalWord_reindexPhysical]

/-- Original-site prefix and suffix products may be used as the virtual end
matrices in the three-block local intertwiner. They remain arbitrary, so this
identity does not require the total chain length to be divisible by `2 * k`.

Source context: arXiv:1703.09188, equations `uuvv` and `StandardForm`, lines
532--543 and 603--622; residual sites as in arXiv:1606.00608, Appendix C.4,
lines 1952--2017. -/
theorem twoSite_threeBlock_originalSite_residual_intertwiner
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k : ℕ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (preI preJ sufI sufJ : List (Fin d))
    (eL eR : Fin (MPSTensor.blockPhysDim d k))
    (j₀ j₂ : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (A : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    twoSiteThreeBlockTrace S
        (evalWord U preI preJ) (evalWord U sufI sufJ) eL eR j₀ j₂ * A =
      twoLinkOutputObservable u v A *
        twoSiteThreeBlockTrace S
          (evalWord U preI preJ) (evalWord U sufI sufJ) eL eR j₀ j₂ := by
  exact twoSite_threeBlock_trace_intertwiner_with_endpoints S _ _ eL eR j₀ j₂ A

end MPOTensor
