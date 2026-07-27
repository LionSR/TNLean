/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBNT

/-!
# Nonemptiness of the retained vertical phase classes

This file proves that the vertical decomposition of a matrix product density
operator in normalized BNT-refined horizontal form contains a nonzero sector.
This horizontal hypothesis is stronger than literal CPSV canonical form.  The
literal reconstruction of the vertical tensor then shows that the finite
partition of the retained sectors into matrix-product-vector phase classes is
nonempty.

This is the nonemptiness observation used in arXiv:1606.00608, Proposition
`prop:vertical`, lines 1895--1902.

## Main result

* `IsHorizontalCF.exists_nonempty_verticalBNTGrouping`: a matrix product
  density operator in normalized BNT-refined horizontal form has a retained
  vertical decomposition whose phase-class family is nonempty.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- A tensor in BNT canonical form is nonzero.

The global unit-modulus witness selects a basis block and one of its copies.
Left canonicity makes that basis tensor nonzero, while the selected copy has a
nonzero weight. -/
private theorem bntCanonicalForm_toTensor_ne_zero
    (P : MPSTensor.SectorDecomposition d)
    (hP : MPSTensor.IsBNTCanonicalForm P) : P.toTensor ≠ 0 := by
  classical
  obtain ⟨j, q, _hq⟩ := hP.weight_unit_exists
  haveI : NeZero (P.basisDim j) := ⟨(hP.basis_dim_pos j).ne'⟩
  have hBasis : ∃ i, P.basis j i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hsum : ∑ i : Fin d, (P.basis j i)ᴴ * P.basis j i = 0 := by
      simp [hzero]
    rw [hP.basis_left_canonical j] at hsum
    exact one_ne_zero hsum
  obtain ⟨i, hi⟩ := hBasis
  let s : Fin P.totalCopies := P.flatIndexEquiv ⟨j, q⟩
  have hs : P.flatIndexEquiv.symm s = ⟨j, q⟩ :=
    P.flatIndexEquiv.symm_apply_apply ⟨j, q⟩
  have hflat : P.flatBasis s i ≠ 0 := by
    change P.basis (P.flatIndexEquiv.symm s).1 i ≠ 0
    rw [hs]
    exact hi
  obtain ⟨a, b, hab⟩ : ∃ a b, P.flatBasis s i a b ≠ 0 := by
    by_contra hentry
    push Not at hentry
    apply hflat
    ext a b
    exact hentry a b
  intro hzero
  have hentry := congrFun (congrFun (congrFun hzero i)
    (finSigmaFinEquiv ⟨s, a⟩)) (finSigmaFinEquiv ⟨s, b⟩)
  have hweight : P.flatWeight s ≠ 0 := by
    change P.weight (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2 ≠ 0
    rw [hs]
    exact P.weight_ne_zero j q
  apply hab
  have : P.flatWeight s * P.flatBasis s i a b = 0 := by
    simpa [MPSTensor.SectorDecomposition.toTensor, MPSTensor.toTensorFromBlocks,
      Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq] using hentry.symm
  exact (mul_eq_zero.mp this).resolve_left hweight

/-- The vertical tensor of an MPO tensor in normalized BNT-refined horizontal
form is nonzero.

**Scope restriction (BNT-refined horizontal form):** The horizontal hypothesis
`IsHorizontalCF` is stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, canonical form at lines 237--246 and Proposition
`prop:vertical`, lines 1895--1902. -/
theorem IsHorizontalCF.verticalTensor_ne_zero
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) : verticalTensor M ≠ 0 := by
  obtain ⟨S, hCF, hTotal, X, hX⟩ := hHorizontal
  subst D
  have hSTensor : S.toTensor ≠ 0 := bntCanonicalForm_toTensor_ne_zero S hCF
  intro hVertical
  apply hSTensor
  have hMzero : M.toMPSTensor = 0 := by
    funext ij
    apply Matrix.ext
    intro a b
    have hz := congrFun (congrFun (congrFun hVertical
      (finProdFinEquiv (a, b))) ij.divNat) ij.modNat
    simpa [verticalTensor, toMPSTensor,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat] using hz
  let G := MPSTensor.globalGaugeOfBlocks X
  have hConj : ∀ i, (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
      S.toTensor i * (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) = 0 := by
    intro i
    have hi := hX i
    rw [hMzero] at hi
    simpa using hi.symm
  funext i
  have hi := hConj i
  have hcancel := congrArg
    (fun Z : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ ↦
      (↑(G⁻¹) : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * Z *
        (G : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) hi
  simpa [Matrix.mul_assoc] using hcancel

/-- A matrix product density operator in normalized BNT-refined horizontal form
has a nonempty family of retained vertical phase classes.

**Scope restriction (BNT-refined horizontal form):** The horizontal hypothesis
`IsHorizontalCF` is stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

The retained normal sectors reconstruct every vertical letter.  Since the
vertical tensor is nonzero, the sector index set is nonempty.  Its partition
into matrix-product-vector phase classes is therefore nonempty as well.

Source: arXiv:1606.00608, Proposition `prop:vertical`, lines 1895--1902. -/
theorem IsHorizontalCF.exists_nonempty_verticalBNTGrouping
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ v, verticalTensor M v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ) ∧
      0 < (MPSTensor.mpvPhaseClassData blocks).g := by
  classical
  obtain ⟨r, dim, μ, blocks, V, hdim, hμ, hnormal, hiso, horth,
    _hint, _hintStar, _hcorner, hreconstruct, _hgrouped⟩ :=
    hHorizontal.exists_verticalBNTGrouping_with_isometry M hM
  have hr : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos hr
    apply hHorizontal.verticalTensor_ne_zero M
    funext v
    rw [hreconstruct v]
    subst r
    simp
  refine ⟨r, dim, μ, blocks, V, hdim, hμ, hnormal, hiso, horth,
    hreconstruct, ?_⟩
  exact (MPSTensor.mpvPhaseClassData blocks).g_pos_of_r_pos hr

end MPOTensor
