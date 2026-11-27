/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureDecomposition
import TNLean.MPS.MPDO.Vertical.CPSVOriginalSpaceLemmaL
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.MPDO.Vertical.CyclicProjector

/-!
# Reducing sectors of the vertically viewed tensor

This file carries the invariant-projection argument of arXiv:1606.00608,
Proposition 4.13, lines 1873--1887, into the general canonical-form
decomposition at lines 200--225 and 253--255.

For a tensor in horizontal canonical form that generates matrix product
density operators, every one-sided invariant orthogonal projection of the
vertically viewed tensor is reducing. The general decomposition under this
closure condition then gives complete pairwise orthogonal physical sectors,
their exact corner tensors, and both intertwining identities. No spectral
normalization or grouping into a basis of normal tensors is asserted here.

## Main results

* `MPOTensor.IsHorizontalCF.hasInvariantProjectorClosure_verticalTensor`:
  every one-sided invariant orthogonal projection of the vertically viewed
  tensor is reducing under normalized BNT-refined horizontal form.
* `BNTRefinement.hasInvariantProjectorClosure_verticalTensor`: the same
  closure from explicit literal-CF data and its BNT refinement.
* `MPTensor.IsCPSVCanonicalForm.hasInvariantProjectorClosure_verticalTensor`:
  the predicate-level literal-CF conclusion.
* `MPOTensor.IsHorizontalCF.exists_irreducible_verticalBlockDecomp_with_isometry`:
  the physical space splits into complete orthogonal irreducible reducing
  sectors for the vertically viewed tensor.
* `MPOTensor.IsHorizontalCF.exists_complete_verticalReducingProjectors`:
  the range projections of these sectors are complete, pairwise orthogonal,
  and commute with every vertical letter.

## Spectral normalization of the vertical reducing sectors

This file retains the physical sector isometries from the vertical reducing
decomposition while removing zero corners and normalizing every remaining
corner to spectral radius one.

The construction is the isometry-preserving form of the canonical-form steps
in arXiv:1606.00608, lines 214--225, applied after the invariant-projection and
periodic-sector arguments of Proposition 4.13, lines 1873--1893.  It assumes
normalized BNT-refined horizontal form, which is stronger than literal CPSV
canonical form.  It gives a literal reconstruction of every vertical letter
on the retained support.  It does not yet group gauge-equivalent normal tensors
into a basis of normal tensors or prove positivity of the grouped multiplicity
weights at lines 1895--1921.
-/

section

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Every invariant orthogonal projection of the vertically viewed tensor is
reducing for an MPO tensor in horizontal canonical form that generates matrix
product density operators.

This is the conclusion of the invariant-projection argument in
arXiv:1606.00608, Proposition 4.13, lines 1873--1887. The left-invariance
identity is translated to the one-site MPO actions, the horizontal Lemma L
reduction gives right invariance, and the result is translated back to the
vertically viewed tensor. -/
theorem IsHorizontalCF.hasInvariantProjectorClosure_verticalTensor
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    MPSTensor.HasInvariantProjectorClosure (verticalTensor M) := by
  intro P hP hInv v
  have hLeft : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P := by
    funext ⟨i, j⟩
    ext a b
    let w := finProdFinEquiv (a, b)
    have hw : verticalTensor (M.ketLeftMul P) w =
        verticalTensor ((M.ketLeftMul P).braRightMul P) w := by
      rw [verticalTensor_ketLeftMul, verticalTensor_braRightMul,
        verticalTensor_ketLeftMul]
      exact hInv w
    have hij := congrFun (congrFun hw i) j
    simpa [w, verticalTensor_finProdFinEquiv] using hij
  have hRight :=
    hHorizontal.braRight_eq_ketLeftBraRight_of_invariant M hM hP.1 hLeft
  rw [← verticalTensor_braRightMul, hRight, verticalTensor_braRightMul,
    verticalTensor_ketLeftMul]

end MPOTensor

namespace MPTensor.CPSVCanonicalFormData.BNTRefinement

open MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- Every invariant orthogonal projection of the vertically viewed tensor is reducing when the
original doubled-index tensor carries a literal CPSV canonical-form refinement and generates
matrix product density operators.

The two positive-length first-site identities follow from positivity.  Lemma L in the original
bond coordinates identifies the opposite-corner insertions, after which the vertical identities
give right invariance.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem hasInvariantProjectorClosure_verticalTensor
    (M : MPOTensor d D) (data : MPTensor.CPSVCanonicalFormData M.toMPSTensor)
    (ref : data.BNTRefinement) (hM : IsMPDO M) :
    MPSTensor.HasInvariantProjectorClosure (verticalTensor M) := by
  intro P hP hInv v
  have hLeft : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P := by
    funext ⟨i, j⟩
    ext a b
    let w := finProdFinEquiv (a, b)
    have hw : verticalTensor (M.ketLeftMul P) w =
        verticalTensor ((M.ketLeftMul P).braRightMul P) w := by
      rw [verticalTensor_ketLeftMul, verticalTensor_braRightMul,
        verticalTensor_ketLeftMul]
      exact hInv w
    have hij := congrFun (congrFun hw i) j
    simpa [w, verticalTensor_finProdFinEquiv] using hij
  have hAct := firstSiteActionAgree_braRight_ketLeftBraRight_of_invariant
    M hM hP.1 hLeft
  have hInserted := ref.insertedTensor_eq_of_firstSiteActionAgree hAct
  have hRight : M.braRightMul P = (M.ketLeftMul P).braRightMul P := by
    have hTensor : (M.braRightMul P).toMPSTensor =
        ((M.ketLeftMul P).braRightMul P).toMPSTensor := by
      rw [← insertedTensor_braRightAction_toMPSTensor,
        ← insertedTensor_ketLeftBraRightAction_toMPSTensor]
      exact hInserted
    funext ⟨i, j⟩
    have hij := congrFun hTensor (finProdFinEquiv (i, j))
    simpa [toMPSTensor] using hij
  rw [← verticalTensor_braRightMul, hRight, verticalTensor_braRightMul,
    verticalTensor_ketLeftMul]

end MPTensor.CPSVCanonicalFormData.BNTRefinement

namespace MPTensor.IsCPSVCanonicalForm

open MPSTensor

open MPOTensor

variable {d D : ℕ}

/-- Literal CPSV canonical form and MPDO positivity imply invariant-projector closure for the
vertically viewed tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem hasInvariantProjectorClosure_verticalTensor
    (M : MPOTensor d D) (hCanonical : MPTensor.IsCPSVCanonicalForm M)
    (hM : IsMPDO M) :
    MPSTensor.HasInvariantProjectorClosure (verticalTensor M) := by
  have hC : MPTensor.IsCPSVCanonicalForm M.toMPSTensor := by
    rw [toMPSTensor_eq_reindexPhysical]
    exact hCanonical.reindexPhysical _
  let data := Classical.choice hC
  let ref := data.bntRefinement
  exact ref.hasInvariantProjectorClosure_verticalTensor M data hM

end MPTensor.IsCPSVCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- Complete orthogonal decomposition of the vertically viewed tensor into
irreducible reducing corners.

For a horizontally canonical MPO tensor generating matrix product density
operators, there are isometries `V k` with pairwise orthogonal ranges summing
to the physical identity. Every vertical letter intertwines each `V k` with
the corresponding irreducible corner, and the adjoint intertwining and exact
compression formula hold as well. The unit-weight direct sum of these corners
has the same positive-length matrix product vector family as the vertically
viewed tensor.

This specializes the canonical-form construction of arXiv:1606.00608,
lines 200--225 and 253--255, after the invariant-projection argument of
Proposition 4.13, lines 1873--1887. -/
theorem IsHorizontalCF.exists_irreducible_verticalBlockDecomp_with_isometry
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∑ k : Fin r, V k * (V k)ᴴ = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * blocks k v) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = blocks k v * (V k)ᴴ) ∧
      (∀ k v, blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      (∀ k, Kraus.IsIrreducibleFamily (blocks k)) ∧
      MPTensor.SameMPV₂Pos (verticalTensor M)
        (MPTensor.toTensorFromBlocks
          (α := Fin (D * D)) (μ := fun _ : Fin r => (1 : ℂ)) blocks) := by
  obtain ⟨r, dim, blocks, V, hdim, hIso, hSum, hOrth, hIntertwine,
      hIntertwineStar, hCompress, hIrred, hSame⟩ :=
    MPSTensor.exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure
      (verticalTensor M)
      (hHorizontal.hasInvariantProjectorClosure_verticalTensor M hM)
  exact ⟨r, dim, blocks, V, hdim, hIso, hSum, hOrth, hIntertwine,
    hIntertwineStar, hCompress, hIrred, hSame.toSameMPV₂Pos⟩

/-- The ranges of the vertical corner isometries form complete pairwise
orthogonal reducing projections.

This is the precursor of the grouped sector projections used in
arXiv:1606.00608, Proposition 4.13, line 1898. At this stage the corners are
irreducible, but possible zero corners have not been removed and the remaining
corners have not been spectrally normalized or grouped into a basis of normal
tensors. -/
theorem IsHorizontalCF.exists_complete_verticalReducingProjectors
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (P : Fin r → Matrix (Fin d) (Fin d) ℂ),
      (∀ k, IsOrthogonalProjection (P k)) ∧
      (∑ k, P k = 1) ∧
      (∀ k l, k ≠ l → P k * P l = 0) ∧
      ∀ k v, verticalTensor M v * P k = P k * verticalTensor M v := by
  obtain ⟨r, _dim, blocks, V, _hpos, hiso, hsum, horth, hint, hintStar,
    _hcorner, _hirr, _hMPV⟩ :=
    hHorizontal.exists_irreducible_verticalBlockDecomp_with_isometry M hM
  let P : Fin r → Matrix (Fin d) (Fin d) ℂ := fun k => V k * (V k)ᴴ
  refine ⟨r, P, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · change (V k * (V k)ᴴ)ᴴ = V k * (V k)ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    · change (V k * (V k)ᴴ) * (V k * (V k)ᴴ) = V k * (V k)ᴴ
      calc
        (V k * (V k)ᴴ) * (V k * (V k)ᴴ)
            = V k * ((V k)ᴴ * V k) * (V k)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = V k * (V k)ᴴ := by rw [hiso k, Matrix.mul_one]
  · exact hsum
  · intro k l hkl
    change (V k * (V k)ᴴ) * (V l * (V l)ᴴ) = 0
    calc
      (V k * (V k)ᴴ) * (V l * (V l)ᴴ)
          = V k * ((V k)ᴴ * V l) * (V l)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [horth k l hkl, Matrix.mul_zero, Matrix.zero_mul]
  · intro k v
    change verticalTensor M v * (V k * (V k)ᴴ) =
      (V k * (V k)ᴴ) * verticalTensor M v
    calc
      verticalTensor M v * (V k * (V k)ᴴ)
          = (verticalTensor M v * V k) * (V k)ᴴ :=
            (Matrix.mul_assoc _ _ _).symm
      _ = (V k * blocks k v) * (V k)ᴴ := by rw [hint k v]
      _ = V k * (blocks k v * (V k)ᴴ) := Matrix.mul_assoc _ _ _
      _ = V k * ((V k)ᴴ * verticalTensor M v) := by rw [hintStar k v]
      _ = (V k * (V k)ᴴ) * verticalTensor M v :=
        (Matrix.mul_assoc _ _ _).symm

end MPOTensor

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Spectrally normalized nonzero vertical corners, with their physical
isometries retained.

Let `M` generate matrix product density operators and be in normalized
BNT-refined horizontal form.  The nonzero irreducible reducing corners of its
vertically viewed tensor can be written as positive scalar multiples of normal
tensors.

Their physical isometries remain pairwise orthogonal, both intertwining
identities and the exact compression formula are preserved, and the retained
corners reconstruct every vertical letter literally.

The omitted irreducible corners have every letter equal to zero.  Consequently
the retained range projections need not sum to the physical identity, but
their orthogonal complement is a zero sector.  This is the zero-corner removal
allowed by arXiv:1606.00608, lines 216--225, and supplies the sector embeddings
used at lines 1895--1898 of Proposition 4.13. -/
theorem IsHorizontalCF.exists_normal_verticalBlockDecomp_with_isometry
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      ∀ v, verticalTensor M v =
        ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ := by
  classical
  obtain ⟨r₀, dim₀, blocks₀, V₀, hpos, hiso, hsum, horth, hint, hintStar,
    hcorner, hirr, _hMPV⟩ :=
    hHorizontal.exists_irreducible_verticalBlockDecomp_with_isometry M hM
  have hPF : ∀ k : Fin r₀, (∃ v, blocks₀ k v ≠ 0) →
      ∃ (ρ : Matrix (Fin (dim₀ k)) (Fin (dim₀ k)) ℂ) (t : ℝ),
        ρ.PosDef ∧ 0 < t ∧
        Kraus.transferMap (ι := Fin (D * D)) (n := Fin (dim₀ k)) (blocks₀ k) ρ =
          (t : ℂ) • ρ := by
    intro k hk
    have : NeZero (dim₀ k) := ⟨(hpos k).ne'⟩
    exact MPSTensor.exists_posDef_transferMap_eigenvector_of_irreducible
      (blocks₀ k) (hirr k) hk
  choose ρf tf hρf htf hEigf using hPF
  let κ := {k : Fin r₀ // ∃ v, blocks₀ k v ≠ 0}
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let μf : κ → ℂ := fun x => ((Real.sqrt (tf x.1 x.2) : ℝ) : ℂ)
  let normalized : (x : κ) → MPSTensor (D * D) (dim₀ x.1) := fun x v =>
    (μf x)⁻¹ • blocks₀ x.1 v
  have hμpos : ∀ x : κ, (0 : ℂ) < μf x := by
    intro x
    change (0 : ℂ) < ((Real.sqrt (tf x.1 x.2) : ℝ) : ℂ)
    exact Complex.zero_lt_real.mpr (Real.sqrt_pos.mpr (htf x.1 x.2))
  have hμne : ∀ x : κ, μf x ≠ 0 := fun x => (hμpos x).ne'
  have hrecover : ∀ (x : κ) (v : Fin (D * D)),
      μf x • normalized x v = blocks₀ x.1 v := by
    intro x v
    simp only [normalized, smul_smul, mul_inv_cancel₀ (hμne x), one_smul]
  have hPer := hasNoPeriodicVectors_verticalTensor_of_horizontalCF M hM hHorizontal
  refine ⟨Fintype.card κ, fun j => dim₀ (e j).1, fun j => μf (e j),
    fun j => normalized (e j), fun j => V₀ (e j).1,
    fun j => hpos (e j).1, fun j => hμpos (e j), ?_,
    fun j => hiso (e j).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have : NeZero (dim₀ (e j).1) := ⟨(hpos (e j).1).ne'⟩
    exact MPSTensor.isNormalTensor_invSqrt_smul_of_unique_peripheral
      (blocks₀ (e j).1) (hirr (e j).1)
      (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2)
      (hρf (e j).1 (e j).2) (htf (e j).1 (e j).2)
      (hEigf (e j).1 (e j).2)
      (fun z hz hnorm =>
        hPer (V₀ (e j).1) (blocks₀ (e j).1)
          (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2)
          (hiso (e j).1) (hint (e j).1) (hirr (e j).1)
          (hρf (e j).1 (e j).2) (htf (e j).1 (e j).2)
          (hEigf (e j).1 (e j).2) z hz hnorm)
  · intro j l hjl
    exact horth (e j).1 (e l).1 fun h => hjl (e.injective (Subtype.ext h))
  · intro j v
    rw [hrecover]
    exact hint (e j).1 v
  · intro j v
    rw [hrecover]
    exact hintStar (e j).1 v
  · intro j v
    rw [hrecover]
    exact hcorner (e j).1 v
  · intro v
    have hfull : verticalTensor M v =
        ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
      calc
        verticalTensor M v = verticalTensor M v * 1 :=
          (Matrix.mul_one _).symm
        _ = verticalTensor M v * ∑ k : Fin r₀, V₀ k * (V₀ k)ᴴ := by
          rw [hsum]
        _ = ∑ k : Fin r₀, verticalTensor M v * (V₀ k * (V₀ k)ᴴ) := by
          rw [Matrix.mul_sum]
        _ = ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Matrix.mul_assoc, hint k v, Matrix.mul_assoc]
    have hkeep :
        ∑ k ∈ Finset.univ.filter (fun k => ∃ w, blocks₀ k w ≠ 0),
            V₀ k * blocks₀ k v * (V₀ k)ᴴ =
          ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
      refine Finset.sum_filter_of_ne ?_
      intro k _ hne
      by_contra hk
      push Not at hk
      exact hne (by rw [hk v, Matrix.mul_zero, Matrix.zero_mul])
    have hsubtype :
        ∑ k ∈ Finset.univ.filter (fun k => ∃ w, blocks₀ k w ≠ 0),
            V₀ k * blocks₀ k v * (V₀ k)ᴴ =
          ∑ x : κ, V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ :=
      Finset.sum_subtype _ (by simp) _
    calc
      verticalTensor M v =
          ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := hfull
      _ = ∑ x : κ, V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ := by
        rw [← hkeep, hsubtype]
      _ = ∑ j : Fin (Fintype.card κ),
          V₀ (e j).1 * blocks₀ (e j).1 v * (V₀ (e j).1)ᴴ :=
        (Equiv.sum_comp e
          (fun x : κ => V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ)).symm
      _ = ∑ j : Fin (Fintype.card κ),
          V₀ (e j).1 * (μf (e j) • normalized (e j) v) * (V₀ (e j).1)ᴴ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hrecover]

end MPOTensor

end
