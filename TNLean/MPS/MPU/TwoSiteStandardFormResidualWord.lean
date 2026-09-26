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

/-- A three-block window of the original MPO, with arbitrary original-site
residual words, is the corresponding three-letter standard-form trace. The
coordinate equalities specify the row and column labels of this window
after the direct `2 * k` blocks are relabeled as two-site blocks. They are
independent of any canonical-form or MPU hypothesis on `U`.

Source context: arXiv:1703.09188, lines 603--622 and 2300--2306;
arXiv:1606.00608, Appendix C.4, lines 1952--2017. -/
theorem originalSite_threeBlock_window_entry
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k p s : ℕ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (preI preJ : Fin p → Fin d) (sufI sufJ : Fin s → Fin d)
    (midI midJ : Fin 3 → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (eL eR : Fin (MPSTensor.blockPhysDim d k))
    (j₀ j₂ : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (x : (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)))
    (j : Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (hI : (fun t => twoSiteDirectBlockEquiv d k (midI t)) =
      ![finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, eR)])
    (hJ : (fun t => twoSiteDirectBlockEquiv d k (midJ t)) =
      ![j₀, finProdFinEquiv j, j₂]) :
    mpo U (p + (3 * (2 * k) + s))
        (Fin.append preI (Fin.append
          (MPSTensor.blockedConfigEquiv d 3 (2 * k) midI) sufI))
        (Fin.append preJ (Fin.append
          (MPSTensor.blockedConfigEquiv d 3 (2 * k) midJ) sufJ)) =
      twoSiteThreeBlockTrace S
        (evalWord U (List.ofFn preI) (List.ofFn preJ))
        (evalWord U (List.ofFn sufI) (List.ofFn sufJ))
        eL eR j₀ j₂ x j := by
  rw [mpo_apply_prefix_twoSiteBlock_suffix U k p 3 s
    preI preJ midI midJ sufI sufJ]
  have hmI : (List.ofFn midI).map (twoSiteDirectBlockEquiv d k) =
      [finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, eR)] := by
    rw [← List.ofFn_comp']
    rw [hI]
    rfl
  have hmJ : (List.ofFn midJ).map (twoSiteDirectBlockEquiv d k) =
      [j₀, finProdFinEquiv j, j₂] := by
    rw [← List.ofFn_comp']
    rw [hJ]
    rfl
  rw [hmI, hmJ]
  rfl

/-- A three-block window may have arbitrary complete two-site blocks on both
sides, in addition to original-site residual prefix and suffix words. The
coordinate equalities specify the full relabeled middle word. Both kinds of
boundary product remain inside the virtual trace.

Source context: arXiv:1703.09188, lines 603--622 and 2300--2306;
arXiv:1606.00608, Appendix C.4, lines 1952--2017. -/
theorem originalSite_threeBlock_window_with_buffers_entry
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k p m s : ℕ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (resPreI resPreJ : Fin p → Fin d) (resSufI resSufJ : Fin s → Fin d)
    (midI midJ : Fin m → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (preI preJ sufI sufJ : List
      (Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)))
    (hpre : preI.length = preJ.length)
    (eL eR : Fin (MPSTensor.blockPhysDim d k))
    (j₀ j₂ : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (x : (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)))
    (j : Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
    (hI : (List.ofFn midI).map (twoSiteDirectBlockEquiv d k) =
      preI ++ ([finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, eR)] ++ sufI))
    (hJ : (List.ofFn midJ).map (twoSiteDirectBlockEquiv d k) =
      preJ ++ ([j₀, finProdFinEquiv j, j₂] ++ sufJ)) :
    mpo U (p + (m * (2 * k) + s))
        (Fin.append resPreI (Fin.append
          (MPSTensor.blockedConfigEquiv d m (2 * k) midI) resSufI))
        (Fin.append resPreJ (Fin.append
          (MPSTensor.blockedConfigEquiv d m (2 * k) midJ) resSufJ)) =
      twoSiteThreeBlockTrace S
        (evalWord U (List.ofFn resPreI) (List.ofFn resPreJ) *
          evalWord (blockTwo (blockTensor U k)) preI preJ)
        (evalWord (blockTwo (blockTensor U k)) sufI sufJ *
          evalWord U (List.ofFn resSufI) (List.ofFn resSufJ))
        eL eR j₀ j₂ x j := by
  rw [mpo_apply_prefix_twoSiteBlock_suffix U k p m s
    resPreI resPreJ midI midJ resSufI resSufJ]
  rw [hI, hJ]
  rw [evalWord_append (blockTwo (blockTensor U k)) preI preJ _ _ hpre]
  rw [evalWord_append (blockTwo (blockTensor U k))
    [finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
      finProdFinEquiv (x.2.2, eR)]
    [j₀, finProdFinEquiv j, j₂] sufI sufJ (by simp)]
  simp only [twoSiteThreeBlockTrace, Matrix.mul_assoc]

/-- The matrix of original-chain coefficients obtained by varying the two
neighboring output pairs and the intervening input pair, with all other
original and blocked labels fixed. -/
noncomputable def originalSiteThreeBlockWindow
    {d D : ℕ} (U : MPOTensor d D) (k p m s : ℕ)
    (resPreI resPreJ : Fin p → Fin d) (resSufI resSufJ : Fin s → Fin d)
    (midI : ((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))) →
      Fin m → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (midJ : (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) →
      Fin m → Fin (MPSTensor.blockPhysDim d (2 * k))) :
    Matrix
      ((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
        (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ :=
  fun x j => mpo U (p + (m * (2 * k) + s))
    (Fin.append resPreI (Fin.append
      (MPSTensor.blockedConfigEquiv d m (2 * k) (midI x)) resSufI))
    (Fin.append resPreJ (Fin.append
      (MPSTensor.blockedConfigEquiv d m (2 * k) (midJ j)) resSufJ))

/-- The three-block locality identity is an operator identity for a window
inside an arbitrarily buffered original chain. The matrices of coefficients
are assembled from full original MPO entries; both original-site residuals
and complete two-site-block buffers are allowed.

Source context: arXiv:1703.09188, equations `uuvv` and `StandardForm`, lines
532--543 and 603--622; original-chain coordinates, lines 2300--2306. -/
theorem originalSite_threeBlock_window_with_buffers_intertwiner
    {d D ℓ r : ℕ} (U : MPOTensor d D) (k p m s : ℕ)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (resPreI resPreJ : Fin p → Fin d) (resSufI resSufJ : Fin s → Fin d)
    (midI : ((Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ×
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))) →
      Fin m → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (midJ : (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) →
      Fin m → Fin (MPSTensor.blockPhysDim d (2 * k)))
    (preI preJ sufI sufJ : List
      (Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k)))
    (hpre : preI.length = preJ.length)
    (eL eR : Fin (MPSTensor.blockPhysDim d k))
    (j₀ j₂ : Fin (MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k))
    (hI : ∀ x, (List.ofFn (midI x)).map (twoSiteDirectBlockEquiv d k) =
      preI ++ ([finProdFinEquiv (eL, x.1.1), finProdFinEquiv (x.1.2, x.2.1),
        finProdFinEquiv (x.2.2, eR)] ++ sufI))
    (hJ : ∀ j, (List.ofFn (midJ j)).map (twoSiteDirectBlockEquiv d k) =
      preJ ++ ([j₀, finProdFinEquiv j, j₂] ++ sufJ))
    (A : Matrix
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    originalSiteThreeBlockWindow U k p m s
        resPreI resPreJ resSufI resSufJ midI midJ * A =
      twoLinkOutputObservable u v A *
        originalSiteThreeBlockWindow U k p m s
          resPreI resPreJ resSufI resSufJ midI midJ := by
  let P := evalWord U (List.ofFn resPreI) (List.ofFn resPreJ) *
    evalWord (blockTwo (blockTensor U k)) preI preJ
  let Q := evalWord (blockTwo (blockTensor U k)) sufI sufJ *
    evalWord U (List.ofFn resSufI) (List.ofFn resSufJ)
  have hF : originalSiteThreeBlockWindow U k p m s
      resPreI resPreJ resSufI resSufJ midI midJ =
      twoSiteThreeBlockTrace S P Q eL eR j₀ j₂ := by
    ext x j
    exact originalSite_threeBlock_window_with_buffers_entry U k p m s S
      resPreI resPreJ resSufI resSufJ (midI x) (midJ j)
      preI preJ sufI sufJ hpre eL eR j₀ j₂ x j (hI x) (hJ j)
  rw [hF]
  exact twoSite_threeBlock_trace_intertwiner_with_endpoints S P Q eL eR j₀ j₂ A

end MPOTensor
