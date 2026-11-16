/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXPermutedBlocks
import TNLean.MPS.Symmetry.MPOSymmetry.PhysicalTwistAnomaly
import TNLean.PEPS.Examples.CZXWrappingRectangle

/-!
# CZX: the boundary symmetry of the CZX PEPS carries the nontrivial three-cocycle

**Source.** arXiv:2011.12127, Appendix A, `Papers/2011.12127/TN-Review-main.tex`.
Line 2516: "As explained in Section~\ref{sec:3:2D-SPT}, the CZX model belongs to the
non-trivial SPT sector of a global on-site $\mathbb{Z}_2$ symmetry."
Line 2584: "As explained in Section \ref{sec:3:2D-SPT}, the reason behind the fact that the
CZX model is a non-trivial SPT phase is the existence of a non trivial MPU symmetry in the
associated PEPS determined by a nontrivial 3-cocycle. This MPU is given by the tensor
$$\ket{0}\bra{1} \otimes |0)(+|+ \ket{1}\bra{0}\otimes |1)(-|\ ,$$"
Section `sec:3:2D-SPT`, line 1464: "To be consistent, the MPOs $O_g$ should form a
representation of the group $G$: $O_g.O_h=O_{gh}$."
Lines 2600--2601: "we arrive at the following canonical form for the MPO
$B^{ij}= (-1)\delta_{ij}$, which globally means ${O}(A)^2=(-1)^N I$."

**Formalized here.** On every positive proper bounded or cyclic coordinate rectangle of the
torus, the physical CZX symmetry acts on the faithful boundary image as the periodic matrix
product operator, on `w + h` blocked boundary sites, of the generator of a `ℤ₂` family
`czxBoundaryFamily` (`e ↦ 1`, `g ↦` the review's tensor blocked over two sites). This family is
a normal representation of `ℤ₂`, and for every choice of its fusion tensors the anomaly
three-cocycle is not cohomologous to the trivial one; its class in `H³(ℤ₂, ℂˣ)` is nonzero.

The anomaly is transported from the once-blocked decorated CZX tensor
`MPOTensor.CZX.tensor`, whose anomaly is `MPOTensor.CZX.not_isTrivialGaugeClass_omega`. With
`S = diag(1, i)`, the change of physical basis by `S ⊗ S` takes the blocked review tensor to
`-MPOTensor.CZX.tensor` (`pairTwist_czxPhaseGate_blockTwo_reviewCZXTensor`), and the sign is the
character `x ↦ (-1)^x` of `ℤ₂`. Both operations leave the anomaly three-cochain unchanged
(`MPOTensor.GroupFamily.FusionData.omega_physicalTwist`,
`MPOTensor.GroupFamily.FusionData.omega_smulTensor`).

**Local fix (two-site blocking):** the review's operator `O(A)` satisfies `O(A)^2 = (-1)^N I`
(line 2601), so on a chain of odd length `e ↦ 1`, `g ↦ O(A)` is not the representation that
line 1464 requires and its three-cocycle is not defined there. The boundary of a rectangle has
even length `2 w + 2 h`, and the statements here pair consecutive boundary sites into `w + h`
blocked sites, as the review blocks sites to make a symmetric PEPS uniform (line 1451) and to
define the CZX tensor itself (line 2508); at every blocked length the square is the identity,
and on the boundary the blocked operator is exactly `O(A)`. Documented in
`docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

**Scope restriction (boundary region):** the boundary identification is the one already proved
for positive proper bounded and cyclic coordinate rectangles; general regions are not covered.
Documented in `docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

## Main definitions

* `TNLean.PEPS.czxBoundaryFamily`: the `ℤ₂` family of the blocked boundary operator.
* `TNLean.PEPS.czxBoundaryPairing`: the pairing of `2 n` boundary spins into `n` blocked sites.

## Main results

* `TNLean.PEPS.czxBoundaryFamily_isNormalRepresentation`: the family represents `ℤ₂`.
* `TNLean.PEPS.not_isTrivialGaugeClass_omega_czxBoundaryFamily`,
  `TNLean.PEPS.czxBoundaryFamily_anomalyClass_ne_zero`: the anomaly class is nontrivial.
* `TNLean.PEPS.regionPhysicalProductMatrix_czxRectangleBoundaryMatrix_czxBoundaryFamily`,
  `TNLean.PEPS.regionPhysicalProductMatrix_czxWrappingRectangleBoundaryMatrix_czxBoundaryFamily`:
  the physical boundary action is the operator of the generator of the family.
-/

noncomputable section

open scoped BigOperators Matrix
open TNLean.Algebra MPOTensor MPOTensor.GroupFamily

namespace TNLean.PEPS

/-! ### The blocked boundary family -/

/-- **The `ℤ₂` family of the CZX boundary symmetry**: the identity tensor for `e` and the
review's CZX tensor blocked over two sites for the generator.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2584--2591 (the CZX
MPU), with the two-site blocking of line 2508. -/
def czxBoundaryFamily : GroupFamily (Multiplicative (ZMod 2)) 4 :=
  orderTwoFamily (idTensor 4) (blockTwo CZXCompression.reviewCZXTensor)

/-- The phase gate `S ⊗ S = diag(1, i, i, -1)` on a blocked pair of qubits, `S = diag(1, i)`. -/
def czxPhaseGate : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, Complex.I, Complex.I, -1]

theorem czxPhaseGate_unitary : star czxPhaseGate * czxPhaseGate = 1 := by
  rw [czxPhaseGate, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [Complex.conj_I]

/-- **The change of basis by `S ⊗ S`** takes the blocked review tensor to minus the
once-blocked decorated CZX tensor of arXiv:2502.20257, `eq:MPU_CZX`. -/
theorem pairTwist_czxPhaseGate_blockTwo_reviewCZXTensor :
    pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ))
        (blockTwo CZXCompression.reviewCZXTensor) = -CZX.tensor := by
  funext i j
  ext l r
  simp only [pairTwist, czxPhaseGate, Matrix.map_apply, Matrix.diagonal_apply, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.smul_apply, Pi.neg_apply,
    Matrix.neg_apply, CZX.tensor, blockTwo]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    simp [Matrix.sum_apply, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
      CZXCompression.reviewCZXTensor_apply, CZX.decoratedSiteTensor, Fin.rev, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Complex.conj_I]

/-- The sign character `x ↦ (-1)^x` of `ℤ₂`. -/
def czxSign (x : Multiplicative (ZMod 2)) : ℂ := if Multiplicative.toAdd x = 0 then 1 else -1

theorem czxSign_mul (x y : Multiplicative (ZMod 2)) : czxSign x * czxSign y = czxSign (x * y) := by
  revert x y
  refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
    (Multiplicative.forall_zmod_two ?_ ?_) <;>
    simp [czxSign, ← ofAdd_add, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem czxSign_ne_zero (x : Multiplicative (ZMod 2)) : czxSign x ≠ 0 := by
  unfold czxSign
  split_ifs <;> norm_num

/-- The boundary family after the change of basis by `S ⊗ S`. -/
private def twistedFamily : GroupFamily (Multiplicative (ZMod 2)) 4 :=
  czxBoundaryFamily.withTensor fun g ↦
    pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ)) (czxBoundaryFamily.tensor g)

/-- The decorated CZX family is the twisted boundary family times the sign character. -/
private theorem family_tensor_eq (g : Multiplicative (ZMod 2)) :
    CZX.family.tensor g = czxSign g • twistedFamily.tensor g := by
  revert g
  refine Multiplicative.forall_zmod_two ?_ ?_
  · change idTensor 4 = czxSign 1 •
      pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ)) (idTensor 4)
    rw [pairTwist_idTensor czxPhaseGate_unitary]
    simp [czxSign]
  · change CZX.tensor = czxSign (Multiplicative.ofAdd 1) •
      pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ))
        (blockTwo CZXCompression.reviewCZXTensor)
    rw [pairTwist_czxPhaseGate_blockTwo_reviewCZXTensor]
    simp [czxSign]

private theorem twistedFamily_tensor_eq (g : Multiplicative (ZMod 2)) :
    twistedFamily.tensor g = czxSign g • CZX.family.tensor g := by
  revert g
  refine Multiplicative.forall_zmod_two ?_ ?_
  · change pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ)) (idTensor 4) =
      czxSign 1 • idTensor 4
    rw [pairTwist_idTensor czxPhaseGate_unitary]
    simp [czxSign]
  · change pairTwist czxPhaseGate (czxPhaseGate.map (starRingEnd ℂ))
        (blockTwo CZXCompression.reviewCZXTensor) = czxSign (Multiplicative.ofAdd 1) • CZX.tensor
    rw [pairTwist_czxPhaseGate_blockTwo_reviewCZXTensor]
    simp [czxSign]

private theorem twistedFamily_isNormalRepresentation :
    twistedFamily.IsNormalRepresentation := by
  have h := IsNormalRepresentation.withTensor_smul (F := CZX.family)
    (T := twistedFamily.tensor) CZX.family_isNormalRepresentation czxSign_mul czxSign_ne_zero
    twistedFamily_tensor_eq
  exact h

/-- **The CZX boundary family is a normal representation of `ℤ₂`**: both tensors are normal
and the blocked operators satisfy `O_g O_h = O_{gh}` on every nonempty chain.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 1464 (the representation
law) and lines 2593--2601 (`O(A)^2 = (-1)^N I`, the identity at even length). -/
theorem czxBoundaryFamily_isNormalRepresentation :
    czxBoundaryFamily.IsNormalRepresentation := by
  have h := IsNormalRepresentation.withTensor_pairTwist (F := twistedFamily)
    twistedFamily_isNormalRepresentation (u := star czxPhaseGate) (T := czxBoundaryFamily.tensor)
    (by rw [star_star]; exact mul_eq_one_comm.1 czxPhaseGate_unitary)
    fun g ↦ (pairTwist_star_pairTwist czxPhaseGate_unitary (czxBoundaryFamily.tensor g)).symm
  exact h

/-- **The CZX boundary symmetry is anomalous**: for every choice of fusion tensors of the
blocked boundary family, the anomaly three-cocycle is not cohomologous to the trivial one.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2584 ("a non trivial
MPU symmetry in the associated PEPS determined by a nontrivial 3-cocycle"). -/
theorem not_isTrivialGaugeClass_omega_czxBoundaryFamily (fd : czxBoundaryFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  let fd₁ : twistedFamily.FusionData := fd.physicalTwist czxPhaseGate_unitary fun _ ↦ rfl
  let fd₂ : CZX.family.FusionData := fd₁.smulTensor czxSign_mul family_tensor_eq
  have h₁ : fd₁.omega = fd.omega :=
    FusionData.omega_physicalTwist czxBoundaryFamily_isNormalRepresentation fd _ _
  have h₂ : fd₂.omega = fd₁.omega :=
    FusionData.omega_smulTensor twistedFamily_isNormalRepresentation fd₁ _ czxSign_ne_zero _
  rw [← h₁, ← h₂]
  exact CZX.not_isTrivialGaugeClass_omega fd₂

/-- The anomaly class of the CZX boundary symmetry in `H³(ℤ₂, ℂˣ)` is nonzero.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2584. -/
theorem czxBoundaryFamily_anomalyClass_ne_zero :
    czxBoundaryFamily_isNormalRepresentation.anomalyClass ≠ 0 := fun h ↦
  not_isTrivialGaugeClass_omega_czxBoundaryFamily
    czxBoundaryFamily_isNormalRepresentation.nonempty_fusionData.some
    ((FusionData.isTrivialGaugeClass_omega_iff _ _).2 h)

/-! ### The physical boundary action -/

/-- The pairing of `m = 2 n` consecutive boundary spins into `n` blocked sites, the pair
`(c_{2k}, c_{2k+1})` being the blocked site `k` in the order `2 a + b`. -/
def czxBoundaryPairing (n m : ℕ) (hm : n * 2 = m) : (Fin n → Fin 4) ≃ (Fin m → Fin 2) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin n)) (twoSiteBlockEquiv 2)).trans
      (MPSTensor.blockedConfigEquiv 2 n 2)).trans
    (Equiv.arrowCongr (finCongr hm) (Equiv.refl (Fin 2)))

/-- The review's operator on `2 n` boundary spins is the operator of the generator of the
boundary family on `n` blocked sites. -/
theorem mpo_reviewCZXTensor_eq_reindex (n m : ℕ) (hm : n * 2 = m) :
    mpo CZXCompression.reviewCZXTensor m =
      Matrix.reindex (czxBoundaryPairing n m hm) (czxBoundaryPairing n m hm)
        (mpo (czxBoundaryFamily.tensor orderTwoGen) n) := by
  subst hm
  change _ = Matrix.reindex _ _ (mpo (blockTwo CZXCompression.reviewCZXTensor) n)
  rw [mpo_blockTwo_eq_reindex_blockTensor, mpo_blockTensor_eq_reindex]
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, czxBoundaryPairing,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

section Bounded

variable (xStart yStart w h : ℕ) (hw : 0 < w) (hh : 0 < h)
variable (hx : xStart + w ≤ width) (hy : yStart + h ≤ height)
variable (hwp : w < width) (hhp : h < height) [NeZero (2 * w + 2 * h)]

/-- **The physical CZX symmetry on a bounded rectangle is the anomalous `ℤ₂` boundary
operator**: on the faithful boundary image of the rectangle, the physical action is the
operator of the generator of `czxBoundaryFamily` on the `w + h` blocked boundary sites.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2584--2591. -/
theorem regionPhysicalProductMatrix_czxRectangleBoundaryMatrix_czxBoundaryFamily :
    regionPhysicalProductMatrix (torusContiguousRectangle xStart yStart w h)
        (fun _ => czxOnSite) *
      czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp =
    czxRectangleBoundaryMatrix xStart yStart w h hw hh hx hy hwp hhp *
      Matrix.reindex (czxBoundaryPairing (w + h) (2 * w + 2 * h) (by ring))
        (czxBoundaryPairing (w + h) (2 * w + 2 * h) (by ring))
        (mpo (czxBoundaryFamily.tensor orderTwoGen) (w + h)) := by
  rw [← mpo_reviewCZXTensor_eq_reindex]
  exact regionPhysicalProductMatrix_czxRectangleBoundaryMatrix_review
    xStart yStart w h hw hh hx hy hwp hhp

end Bounded

section Wrapping

variable (s : TorusVertex width height) (w h : ℕ)
variable (hw : 0 < w) (hh : 0 < h) (hwp : w < width) (hhp : h < height)
variable [NeZero (2 * w + 2 * h)]

/-- **The physical CZX symmetry on a cyclic coordinate rectangle is the anomalous `ℤ₂`
boundary operator**, on the `w + h` blocked boundary sites of its faithful boundary image.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2584--2591. -/
theorem regionPhysicalProductMatrix_czxWrappingRectangleBoundaryMatrix_czxBoundaryFamily :
    regionPhysicalProductMatrix (torusArcRectangle s w h) (fun _ => czxOnSite) *
        czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp =
      czxWrappingRectangleBoundaryMatrix s w h hw hh hwp hhp *
        Matrix.reindex (czxBoundaryPairing (w + h) (2 * w + 2 * h) (by ring))
          (czxBoundaryPairing (w + h) (2 * w + 2 * h) (by ring))
          (mpo (czxBoundaryFamily.tensor orderTwoGen) (w + h)) := by
  rw [← mpo_reviewCZXTensor_eq_reindex]
  exact regionPhysicalProductMatrix_czxWrappingRectangleBoundaryMatrix_review
    s w h hw hh hwp hhp

end Wrapping

end TNLean.PEPS
