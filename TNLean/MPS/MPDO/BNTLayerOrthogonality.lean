/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorProductRealization
import TNLean.MPS.MPDO.PhysicalSupportSALTransport
import TNLean.MPS.MPDO.StackedLayers

/-!
# Orthogonality of vertically composed BNT layers

Distinct elements of a basis of normal tensors in the simple matrix-product-density-operator
setting have disjoint physical sectors.  The corresponding local identity is ordinary vertical
composition: the layer labelled by $y$ is placed above the layer labelled by $x$, with no
adjoint, and the resulting MPO tensor vanishes when $x \ne y$.

This file records that identity for families whose bond dimensions may depend on the label,
characterizes it by products of physical slices and their entries, and derives it from pairwise
orthogonal two-sided physical supports.  A two-label square-zero example shows that the raw
local identity alone does not provide such support projections for arbitrary MPO tensors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9(iv), equation `KxKy=0`, lines 863--868, and Appendix C.2,
  equations `AppKxKy=0` and `PjKiPj`, lines 1634--1639 and 1680--1691
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d g : ℕ} {bondDim : Fin g → ℕ}

/-- Positivity of every neighbouring sector operator makes the original tensor an MPDO.  The
sector-coordinate operators are positive by their cyclic product decomposition, and the
physical isometry transports positivity back to the original physical space.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `Appetakhetc`,
lines 1383--1450. -/
theorem PhysicalSectorFactorization.isMPDO_of_neighboringOperator_pos
    {K : MPOTensor d D} (F : PhysicalSectorFactorization K)
    (hpos : ∀ q h, (F.neighboringOperator q h).PosSemidef) : IsMPDO K := by
  apply isMPDO_of_changePhysicalBasis_isMPDO_of_isometry
    F.physicalCoordinateMatrix F.physicalCoordinateMatrix_isometry K
  rw [← F.sectorCoordinateTensor_eq_changePhysicalBasis]
  intro N hN
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact F.mpo_sectorCoordinateTensor_posSemidef hpos

/-! ### Physical adjoint -/

/-- The physical adjoint of an MPO tensor swaps its ket and bra indices and conjugates each
virtual matrix entry, without transposing the virtual indices:
$$(K^\sharp)^{ij}_{\beta\alpha} = \overline{K^{ji}_{\beta\alpha}}.$$

This local adjoint relates layer annihilation to the two-sided support condition in equation
`PjKiPj`; unlike `adjointTensor`, it does not reverse virtual multiplication.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`--`PjKiPj`,
lines 1634--1689. -/
def physicalAdjointTensor (K : MPOTensor d D) : MPOTensor d D :=
  fun i j β α ↦ star (K j i β α)

/-- Evaluating the physical adjoint swaps the physical indices and conjugates the entry. -/
@[simp] theorem physicalAdjointTensor_apply (K : MPOTensor d D)
    (i j : Fin d) (β α : Fin D) :
    physicalAdjointTensor K i j β α = star (K j i β α) := rfl

/-- Physical slices of the physical adjoint are the conjugate transposes of the original
physical slices.  Only physical indices are transposed.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem physicalSlice_physicalAdjointTensor (K : MPOTensor d D) (β α : Fin D) :
    physicalSlice (physicalAdjointTensor K) β α = (physicalSlice K β α)ᴴ := by
  ext i j
  rfl

/-- Closed words of the physical adjoint are entrywise conjugates of the words with ket and
bra configurations exchanged. -/
theorem evalWord_physicalAdjointTensor (K : MPOTensor d D)
    (is js : List (Fin d)) (hlen : is.length = js.length) :
    evalWord (physicalAdjointTensor K) is js =
      (evalWord K js is).map (starRingEnd ℂ) := by
  induction is generalizing js with
  | nil =>
      simp only [List.length_nil, eq_comm, List.length_eq_zero_iff] at hlen
      subst js
      exact (starRingEnd ℂ).mapMatrix.map_one.symm
  | cons i is ih =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [evalWord_cons, ih js hlen]
          exact ((starRingEnd ℂ).mapMatrix.map_mul (K j i) (evalWord K js is)).symm

/-- The physical adjoint generates the conjugate-transposed periodic operator family without
spatial reflection.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem mpo_physicalAdjointTensor (K : MPOTensor d D) (N : ℕ)
    (σ τ : Fin N → Fin d) :
    mpo (physicalAdjointTensor K) N σ τ = star (mpo K N τ σ) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_physicalAdjointTensor K _ _ (by simp),
    ← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

/-- Positivity of every nonempty periodic operator makes an MPO tensor and its physical adjoint
produce the same positive-length MPV family.  The positive-length convention is the weakest
one supplied directly by `IsMPDO`; no assertion at length zero is used.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem IsMPDO.sameMPV₂Pos_physicalAdjointTensor {K : MPOTensor d D} (hK : IsMPDO K) :
    MPSTensor.SameMPV₂Pos K.toMPSTensor (physicalAdjointTensor K).toMPSTensor := by
  intro N hN ρ
  let σ : Fin N → Fin d := fun n ↦ (ρ n).divNat
  let τ : Fin N → Fin d := fun n ↦ (ρ n).modNat
  have hρ : ρ = fun n ↦ finProdFinEquiv (σ n, τ n) := by
    funext n
    exact (finProdFinEquiv.apply_symm_apply (ρ n)).symm
  calc
    MPSTensor.mpv K.toMPSTensor ρ = mpo K N σ τ := by
      rw [hρ, MPSTensor.mpv_toMPSTensor_pairConfig]
    _ = star (mpo K N τ σ) := ((hK N hN).isHermitian.apply σ τ).symm
    _ = mpo (physicalAdjointTensor K) N σ τ :=
      (mpo_physicalAdjointTensor K N σ τ).symm
    _ = MPSTensor.mpv (physicalAdjointTensor K).toMPSTensor ρ := by
      rw [hρ, MPSTensor.mpv_toMPSTensor_pairConfig]

/-- Since the two tensors have the same bond dimension, the positive-length equality extends
at length zero by the universal zero-length MPV formula. -/
theorem IsMPDO.sameMPV_physicalAdjointTensor {K : MPOTensor d D} (hK : IsMPDO K) :
    MPSTensor.SameMPV K.toMPSTensor (physicalAdjointTensor K).toMPSTensor := by
  intro N ρ
  by_cases hN : 0 < N
  · exact hK.sameMPV₂Pos_physicalAdjointTensor N hN ρ
  · have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp

/-- For an injective MPDO tensor, every conjugate-transposed physical slice has an explicit
finite expansion in the original physical slices.  The coefficients are matrix entries of the
inner gauge comparing the tensor with its physical adjoint.

This is the adjoint-closure step that connects equations `AppKxKy=0` and `PjKiPj`.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1639 and 1680--1691. -/
theorem exists_physicalSlice_conjTranspose_eq_sum_of_isInjective_isMPDO
    (K : MPOTensor d D) (hInj : MPSTensor.IsInjective K.toMPSTensor) (hK : IsMPDO K) :
    ∃ X : GL (Fin D) ℂ, ∀ β α : Fin D,
      (physicalSlice K β α)ᴴ =
        ∑ ν : Fin D, ∑ μ : Fin D,
          (X β μ * (X⁻¹ : Matrix (Fin D) (Fin D) ℂ) ν α) • physicalSlice K μ ν := by
  obtain ⟨X, hX⟩ :=
    MPSTensor.fundamentalTheorem_singleBlock hInj hK.sameMPV_physicalAdjointTensor
  refine ⟨X, fun β α ↦ ?_⟩
  ext i j
  have hEntry := congrArg
    (fun A : Matrix (Fin D) (Fin D) ℂ ↦ A β α)
    (hX (finProdFinEquiv (i, j)))
  simpa [toMPSTensor, physicalAdjointTensor, physicalSlice, Matrix.mul_apply,
    Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_left_comm, mul_comm] using hEntry

/-! ### Finite physical supports -/

/-- Stack all columns of all physical slices into one finite matrix.  A column is indexed by a
virtual-index pair followed by a physical column index. -/
noncomputable def physicalSliceColumns (K : MPOTensor d D) :
    Matrix (Fin d) (Fin (D * D * d)) ℂ :=
  fun i q ↦ K i q.modNat q.divNat.divNat q.divNat.modNat

/-- The orthogonal projection onto the span of all columns of all physical slices. -/
noncomputable def physicalSupportProj (K : MPOTensor d D) : Matrix (Fin d) (Fin d) ℂ :=
  MPSTensor.supportProj
    (physicalSliceColumns K * (physicalSliceColumns K)ᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose (physicalSliceColumns K))

/-- The product index selects the corresponding virtual pair and physical column. -/
@[simp] theorem physicalSliceColumns_apply_finProdFinEquiv (K : MPOTensor d D)
    (i j : Fin d) (β α : Fin D) :
    physicalSliceColumns K i (finProdFinEquiv (finProdFinEquiv (β, α), j)) = K i j β α := by
  simp [physicalSliceColumns]

/-- Orthogonal column spaces give orthogonal support projections. -/
theorem supportProj_mul_supportProj_eq_zero_of_conjTranspose_mul_eq_zero
    {k l : ℕ} (Y : Matrix (Fin d) (Fin k) ℂ) (Z : Matrix (Fin d) (Fin l) ℂ)
    (hYZ : Yᴴ * Z = 0) :
    MPSTensor.supportProj (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y) *
      MPSTensor.supportProj (Z * Zᴴ) (Matrix.posSemidef_self_mul_conjTranspose Z) = 0 := by
  let πY := MPSTensor.supportProj (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y)
  let πZ := MPSTensor.supportProj (Z * Zᴴ) (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hπYZ : πY * Z = 0 := by
    ext i j
    have hmat : (Y * Yᴴ) * Z = 0 :=
      (Matrix.self_mul_conjTranspose_mul_eq_zero Y Z).2 hYZ
    have hker : (Y * Yᴴ) *ᵥ (fun a ↦ Z a j) = 0 := by
      funext a
      have hEntry := congrArg (fun A : Matrix (Fin d) (Fin l) ℂ ↦ A a j) hmat
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using hEntry
    have hsupport := MPSTensor.supportProj_mulVec_eq_zero_of_mulVec_eq_zero
      (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y) (fun a ↦ Z a j) hker
    simpa [πY, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hsupport i
  obtain ⟨W, hW⟩ := MPSTensor.exists_supportProj_eq_mul
    (Z * Zᴴ) (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hπZ : πZ = Z * Zᴴ * W := by simpa [πZ] using hW
  calc
    πY * πZ = πY * (Z * Zᴴ * W) := by rw [hπZ]
    _ = (πY * Z) * (Zᴴ * W) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hπYZ, Matrix.zero_mul]

/-- The support projection of the stacked physical columns fixes every physical slice on the
left. -/
theorem physicalSupportProj_mul_physicalSlice (K : MPOTensor d D) (β α : Fin D) :
    physicalSupportProj K * physicalSlice K β α = physicalSlice K β α := by
  have hColumns := MPSTensor.supportProj_mul_left_eq_self (physicalSliceColumns K)
  ext i j
  have hEntry := congrArg
    (fun A : Matrix (Fin d) (Fin (D * D * d)) ℂ ↦
      A i (finProdFinEquiv (finProdFinEquiv (β, α), j))) hColumns
  simpa [physicalSupportProj, Matrix.mul_apply, physicalSlice] using hEntry

/-- Adjoint closure makes the same physical support projection fix every slice on the right. -/
theorem physicalSlice_mul_physicalSupportProj_of_isInjective_isMPDO
    (K : MPOTensor d D) (hInj : MPSTensor.IsInjective K.toMPSTensor) (hK : IsMPDO K)
    (β α : Fin D) :
    physicalSlice K β α * physicalSupportProj K = physicalSlice K β α := by
  obtain ⟨_, hAdj⟩ :=
    exists_physicalSlice_conjTranspose_eq_sum_of_isInjective_isMPDO K hInj hK
  have hleftAdj : physicalSupportProj K * (physicalSlice K β α)ᴴ =
      (physicalSlice K β α)ᴴ := by
    rw [hAdj β α, Matrix.mul_sum]
    simp_rw [Matrix.mul_sum, Matrix.mul_smul, physicalSupportProj_mul_physicalSlice]
  have hHerm : (physicalSupportProj K).IsHermitian :=
    (MPSTensor.isOrthogonalProjection_supportProj
      (physicalSliceColumns K * (physicalSliceColumns K)ᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose (physicalSliceColumns K))).1
  have hstar := congrArg Matrix.conjTranspose hleftAdj
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHerm.eq] using hstar

/-- Distinct BNT layers vanish under ordinary vertical composition, with the $y$ layer above
 the $x$ layer.

The dependent bond dimension permits different BNT elements to have different virtual spaces.
There is no adjoint in this identity.

Source: arXiv:1606.00608, Theorem 4.9(iv), equation `KxKy=0`, lines 863--868,
and Appendix C.2, equation `AppKxKy=0`, lines 1634--1639. -/
def IsBNTLayerOrthogonal (K : (x : Fin g) → MPOTensor d (bondDim x)) : Prop :=
  ∀ x y, x ≠ y → layerMul (K y) (K x) = 0

/-- Layer orthogonality is equivalent to vanishing of every ordered product of physical slices.
The first factor is a slice of the $y$ layer and the second a slice of the $x$ layer, matching
the vertical order in equation `AppKxKy=0`.

Source: arXiv:1606.00608, Appendix C.2, equation `AppKxKy=0`, lines 1634--1639. -/
theorem isBNTLayerOrthogonal_iff_physicalSlice_mul_eq_zero
    (K : (x : Fin g) → MPOTensor d (bondDim x)) :
    IsBNTLayerOrthogonal K ↔
      ∀ x y, x ≠ y → ∀ (βy αy : Fin (bondDim y)) (βx αx : Fin (bondDim x)),
        physicalSlice (K y) βy αy * physicalSlice (K x) βx αx = 0 := by
  constructor
  · intro h x y hxy βy αy βx αx
    ext i j
    have hEntry := congrArg
      (fun T : MPOTensor d (bondDim y * bondDim x) ↦
        T i j (finProdFinEquiv (βy, βx)) (finProdFinEquiv (αy, αx)))
      (h x y hxy)
    simpa [layerMul_apply, physicalSlice, Matrix.mul_apply] using hEntry
  · intro h x y hxy
    funext i j
    ext a b
    obtain ⟨⟨βy, βx⟩, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨αy, αx⟩, rfl⟩ := finProdFinEquiv.surjective b
    have hEntry := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ ↦ A i j)
      (h x y hxy βy αy βx αx)
    simpa [layerMul_apply, physicalSlice, Matrix.mul_apply] using hEntry

/-- Entrywise form of BNT layer orthogonality.  It keeps both heterogeneous bond-index pairs
explicit and preserves the exact order $K_y K_x$.

Source: arXiv:1606.00608, Appendix C.2, equation `AppKxKy=0`, lines 1634--1639. -/
theorem isBNTLayerOrthogonal_iff_physicalSlice_mul_apply_eq_zero
    (K : (x : Fin g) → MPOTensor d (bondDim x)) :
    IsBNTLayerOrthogonal K ↔
      ∀ x y, x ≠ y → ∀ (βy αy : Fin (bondDim y)) (βx αx : Fin (bondDim x))
        (i j : Fin d),
        ∑ k : Fin d, K y i k βy αy * K x k j βx αx = 0 := by
  rw [isBNTLayerOrthogonal_iff_physicalSlice_mul_eq_zero]
  constructor
  · intro h x y hxy βy αy βx αx i j
    have hEntry := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ ↦ A i j)
      (h x y hxy βy αy βx αx)
    simpa [physicalSlice, Matrix.mul_apply] using hEntry
  · intro h x y hxy βy αy βx αx
    ext i j
    simpa [physicalSlice, Matrix.mul_apply] using h x y hxy βy αy βx αx i j

/-- For distinct injective MPDO layers, ordinary layer annihilation makes the stacked physical
column spaces orthogonal. -/
theorem physicalSliceColumns_conjTranspose_mul_eq_zero
    (K : (x : Fin g) → MPOTensor d (bondDim x))
    (hInj : ∀ x, MPSTensor.IsInjective (K x).toMPSTensor)
    (hMPDO : ∀ x, IsMPDO (K x)) (hOrth : IsBNTLayerOrthogonal K)
    {x y : Fin g} (hxy : x ≠ y) :
    (physicalSliceColumns (K x))ᴴ * physicalSliceColumns (K y) = 0 := by
  have hMul := (isBNTLayerOrthogonal_iff_physicalSlice_mul_eq_zero K).mp hOrth
  obtain ⟨_, hAdj⟩ :=
    exists_physicalSlice_conjTranspose_eq_sum_of_isInjective_isMPDO
      (K x) (hInj x) (hMPDO x)
  have hSlice (βx αx : Fin (bondDim x)) (βy αy : Fin (bondDim y)) :
      (physicalSlice (K x) βx αx)ᴴ * physicalSlice (K y) βy αy = 0 := by
    rw [hAdj βx αx, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro μ _
    rw [Matrix.smul_mul, hMul y x hxy.symm μ ν βy αy, smul_zero]
  ext qx qy
  have hEntry := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ ↦
    A qx.modNat qy.modNat)
    (hSlice qx.divNat.divNat qx.divNat.modNat qy.divNat.divNat qy.divNat.modNat)
  simpa [physicalSliceColumns, physicalSlice, Matrix.mul_apply,
    Matrix.conjTranspose_apply] using hEntry

/-- An injective MPDO family satisfying ordinary BNT layer orthogonality has pairwise
orthogonal physical support projections, and each projection fixes every physical slice on
both sides.  Positivity supplies adjoint closure; no adjoint orthogonality is assumed.  This
constructs the pairwise supports, but not the completeness identity `Pis` from the paper.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0` and `PjKiPj`,
lines 1634--1639 and 1680--1691. -/
theorem exists_pairwise_orthogonal_twoSided_physicalSupport
    (K : (x : Fin g) → MPOTensor d (bondDim x))
    (hInj : ∀ x, MPSTensor.IsInjective (K x).toMPSTensor)
    (hMPDO : ∀ x, IsMPDO (K x)) (hOrth : IsBNTLayerOrthogonal K) :
    ∃ P : Fin g → Matrix (Fin d) (Fin d) ℂ,
      (∀ x, IsOrthogonalProjection (P x)) ∧
      (∀ {x y}, x ≠ y → P x * P y = 0) ∧
      (∀ x (β α : Fin (bondDim x)),
        P x * physicalSlice (K x) β α = physicalSlice (K x) β α ∧
          physicalSlice (K x) β α * P x = physicalSlice (K x) β α) := by
  let P : Fin g → Matrix (Fin d) (Fin d) ℂ := fun x ↦ physicalSupportProj (K x)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x
    exact MPSTensor.isOrthogonalProjection_supportProj
      (physicalSliceColumns (K x) * (physicalSliceColumns (K x))ᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose (physicalSliceColumns (K x)))
  · intro x y hxy
    exact supportProj_mul_supportProj_eq_zero_of_conjTranspose_mul_eq_zero
      (physicalSliceColumns (K x)) (physicalSliceColumns (K y))
      (physicalSliceColumns_conjTranspose_mul_eq_zero K hInj hMPDO hOrth hxy)
  · intro x β α
    exact ⟨physicalSupportProj_mul_physicalSlice (K x) β α,
      physicalSlice_mul_physicalSupportProj_of_isInjective_isMPDO
        (K x) (hInj x) (hMPDO x) β α⟩

/-- Pairwise-annihilating one-site matrices that support every physical slice on both sides
imply BNT layer orthogonality.  No idempotence or self-adjointness of these matrices is required.

Source: arXiv:1606.00608, Theorem 4.9(iv), equation `KxKy=0`, lines 863--868,
and Appendix C.2, equations `AppKxKy=0` and `PjKiPj`, lines 1634--1639 and
1688--1689. -/
theorem isBNTLayerOrthogonal_of_pairwise_orthogonal_twoSided_support
    (K : (x : Fin g) → MPOTensor d (bondDim x))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hPorth : ∀ {x y}, x ≠ y → P x * P y = 0)
    (hSupport : ∀ x (β α : Fin (bondDim x)),
      P x * physicalSlice (K x) β α = physicalSlice (K x) β α ∧
        physicalSlice (K x) β α * P x = physicalSlice (K x) β α) :
    IsBNTLayerOrthogonal K := by
  rw [isBNTLayerOrthogonal_iff_physicalSlice_mul_eq_zero]
  intro x y hxy βy αy βx αx
  calc
    physicalSlice (K y) βy αy * physicalSlice (K x) βx αx =
        (physicalSlice (K y) βy αy * P y) *
          (P x * physicalSlice (K x) βx αx) := by rw [(hSupport y βy αy).2,
            (hSupport x βx αx).1]
    _ = physicalSlice (K y) βy αy * (P y * P x) *
          physicalSlice (K x) βx αx := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPorth hxy.symm, Matrix.mul_zero, Matrix.zero_mul]

/-! ### A square-zero obstruction to a generic support converse -/

namespace BNTLayerOrthogonalityCounterexample

/-- The nonzero square-zero matrix $|0\rangle\langle 1|$ on a two-dimensional physical space. -/
def squareZeroPhysicalMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ if i = 0 ∧ j = 1 then 1 else 0

/-- The chosen physical matrix is nonzero. -/
theorem squareZeroPhysicalMatrix_ne_zero : squareZeroPhysicalMatrix ≠ 0 := by
  intro h
  have hEntry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A 0 1) h
  simp [squareZeroPhysicalMatrix] at hEntry

/-- The chosen physical matrix squares to zero. -/
theorem squareZeroPhysicalMatrix_mul_self :
    squareZeroPhysicalMatrix * squareZeroPhysicalMatrix = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squareZeroPhysicalMatrix, Matrix.mul_apply]

/-- The bond-dimension-one MPO tensor whose sole physical slice is the square-zero matrix. -/
def tensor : MPOTensor 2 1 :=
  fun i j _ _ ↦ squareZeroPhysicalMatrix i j

/-- Two labelled copies of the same square-zero tensor. -/
def family (_x : Fin 2) : MPOTensor 2 1 := tensor

/-- Every physical slice of either labelled copy is the same square-zero matrix. -/
@[simp] theorem physicalSlice_family (x : Fin 2) (β α : Fin 1) :
    physicalSlice (family x) β α = squareZeroPhysicalMatrix := by
  ext i j
  simp [physicalSlice, family, tensor]

/-- The two labelled copies satisfy the raw BNT layer-orthogonality identity. -/
theorem family_isBNTLayerOrthogonal : IsBNTLayerOrthogonal family := by
  rw [isBNTLayerOrthogonal_iff_physicalSlice_mul_eq_zero]
  intro x y _ βy αy βx αx
  rw [physicalSlice_family, physicalSlice_family, squareZeroPhysicalMatrix_mul_self]

/-- The raw layer-orthogonality identity does not, for arbitrary MPO tensors, imply the
existence of pairwise orthogonal one-site projections that fix every sector slice on both
sides.  This statement concerns only that generic converse; it does not address the injectivity
and MPDO hypotheses under which the support construction above applies.

Source comparison: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0` and
`PjKiPj`, lines 1634--1639 and 1688--1689, and Proposition `prop3to4`, lines
1786--1796. -/
theorem no_pairwise_orthogonal_twoSided_support :
    ¬ ∃ P : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x, IsOrthogonalProjection (P x)) ∧
      (∀ {x y}, x ≠ y → P x * P y = 0) ∧
      (∀ x (β α : Fin 1),
        P x * physicalSlice (family x) β α = physicalSlice (family x) β α ∧
          physicalSlice (family x) β α * P x = physicalSlice (family x) β α) := by
  rintro ⟨P, _hP, hPorth, hSupport⟩
  have hSupportZero := (hSupport 0 0 0).1
  have hSupportOne := (hSupport 1 0 0).1
  rw [physicalSlice_family] at hSupportZero hSupportOne
  have hzero : squareZeroPhysicalMatrix = 0 := by
    calc
      squareZeroPhysicalMatrix = P 0 * squareZeroPhysicalMatrix := hSupportZero.symm
      _ = P 0 * (P 1 * squareZeroPhysicalMatrix) := by rw [hSupportOne]
      _ = (P 0 * P 1) * squareZeroPhysicalMatrix := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hPorth (by decide), Matrix.zero_mul]
  exact squareZeroPhysicalMatrix_ne_zero hzero

end BNTLayerOrthogonalityCounterexample

end MPOTensor
