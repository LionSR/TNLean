/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.InjectivePeriodicCuts
import TNLean.MPS.Preparation.MinimalCutRepresentation

/-!
# Virtual cut bases in actual physical-site coordinates

The virtual basis of an injective periodic tensor is transported to the
actual physical cut column space. Slicing one more physical letter has
matrix equal to that letter tensored with the identity on the spectator
virtual index. These are actual coefficient column spaces and actual
physical-coordinate slicing maps; no window gauge is supplied.

Source: PGVWC07, arXiv:quant-ph/0608197, MPSarchive.tex lines 921--931,
1080--1086 and 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators Kronecker

namespace MPSTensor

variable {d D N k : ℕ}

/-- Numbered and actual-site physical prefix column spaces are linearly
equivalent by their explicit physical configuration bijection.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
noncomputable def physicalCutCoordinates (ψ : (Fin N → Fin d) → ℂ) (hk : k ≤ N) :
    (Submodule.span ℂ (Set.range (cutMatrix ψ k).col)) ≃ₗ[ℂ] cutColumnSpace ψ k := by
  let E := LinearEquiv.funCongrLeft ℂ ℂ (cutPrefixConfigEquiv (d := d) hk).symm
  let Q := LinearEquiv.funCongrLeft ℂ ℂ (cutSuffixConfigEquiv (d := d) hk)
  have hrange : cutColumnSpace ψ k =
      (Submodule.span ℂ (Set.range (cutMatrix ψ k).col)).map E.toLinearMap := by
    change Submodule.span ℂ (Set.range (cutCoefficientMatrix ψ k).col) = _
    rw [← Matrix.range_mulVecLin, ← Matrix.range_mulVecLin,
      cutCoefficientMatrix_eq_reindex_cutMatrix ψ hk, Matrix.mulVecLin_reindex]
    change LinearMap.range (E.toLinearMap.comp ((cutMatrix ψ k).mulVecLin.comp
      Q.toLinearMap)) = _
    rw [LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr Q.surjective)]
  exact E.ofSubmodules _ _ hrange.symm

/-- The physical-coordinate identification acts by the original prefix
configuration bijection, retaining every coefficient.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
@[simp] theorem physicalCutCoordinates_apply (ψ : (Fin N → Fin d) → ℂ) (hk : k ≤ N)
    (v : Submodule.span ℂ (Set.range (cutMatrix ψ k).col))
    (u : CutPrefixConfig d N k) :
    (physicalCutCoordinates ψ hk v).val u = v.val ((cutPrefixConfigEquiv hk).symm u) :=
  rfl

/-- The actual physical prefix column space has the virtual left cut
vectors as a basis, expressed on the original site subset.
Source: PGVWC07, MPSarchive.tex lines 921--931. -/
noncomputable def physicalPeriodicCutBasis {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k)) :
    Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace (mpv A (N := N)) k) :=
  (periodicCutBasis hk hleft hright).map (physicalCutCoordinates (mpv A) hk)

/-- The actual-site virtual basis has precisely the source's cut-vector
coefficients. Source: PGVWC07, MPSarchive.tex lines 921--931. -/
@[simp] theorem physicalPeriodicCutBasis_apply {A : MPSTensor d D} (hk : k ≤ N)
    (hleft : Kraus.IsNBlkInjective A k) (hright : Kraus.IsNBlkInjective A (N - k))
    (a : Fin D × Fin D) (u : CutPrefixConfig d N k) :
    (physicalPeriodicCutBasis hk hleft hright a).val u =
      leftCutVector A k a ((cutPrefixConfigEquiv hk).symm u) := rfl

private theorem cutPrefixConfigEquiv_extend (hk : k + 1 ≤ N)
    (u : CutPrefixConfig d N k) (i : Fin d) :
    (cutPrefixConfigEquiv hk).symm (extendCutPrefix k u i) =
      Fin.append ((cutPrefixConfigEquiv (by omega : k ≤ N)).symm u)
        (fun _ : Fin 1 ↦ i) := by
  funext p
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
  · rw [Fin.append_left]
    change (if _h : j.val < k then u _ else i) = u _
    rw [dif_pos j.isLt]
    congr 1
    exact Subtype.ext (Fin.ext rfl)
  · rw [Fin.append_right]
    change (if _h : k + j.val < k then u _ else i) = i
    rw [dif_neg (by omega)]

/-- Actual coordinate slicing in the derived virtual bases has the
amplified letter matrix. This is the doubled-bond local relation from
which the quadratic window gauges are obtained by changing cut bases.
Source: PGVWC07, MPSarchive.tex lines 1080--1086 and 1139--1152. -/
theorem toMatrix_cutSlice_physicalPeriodicCutBasis {A : MPSTensor d D}
    (hk : k + 1 ≤ N) (hleft : Kraus.IsNBlkInjective A k)
    (hright : Kraus.IsNBlkInjective A (N - k))
    (hleftNext : Kraus.IsNBlkInjective A (k + 1))
    (hrightNext : Kraus.IsNBlkInjective A (N - (k + 1))) (i : Fin d) :
    LinearMap.toMatrix (physicalPeriodicCutBasis hk hleftNext hrightNext)
      (physicalPeriodicCutBasis (by omega : k ≤ N) hleft hright)
      (cutSlice (mpv A (N := N)) k i) = A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  let C := physicalPeriodicCutBasis (by omega : k ≤ N) hleft hright
  let C' := physicalPeriodicCutBasis hk hleftNext hrightNext
  have hslice (a : Fin D × Fin D) :
      cutSlice (mpv A (N := N)) k i (C' a) =
        ∑ b : Fin D × Fin D, (A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) b a • C b := by
    apply Subtype.ext
    funext u
    change (C' a).val (extendCutPrefix k u i) = _
    simp only [C', C, physicalPeriodicCutBasis_apply, cutPrefixConfigEquiv_extend hk,
      leftCutVector_append_single, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_comm]
  ext b a
  change C.repr (cutSlice (mpv A (N := N)) k i (C' a)) b = _
  rw [hslice]
  simp

end MPSTensor
