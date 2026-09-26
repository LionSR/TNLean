/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.SuppliedFixedWitnesses
import TNLean.MPS.MPU.ReducedRepresentative

/-!
# Simplicity under support compression

A rectangular bond inclusion with a left inverse preserves the two simplicity
identities in both directions. For support projections `P` and `Q` satisfying
`W i j * P = W i j` and `Q * W i j = W i j`, compression by their reduced
projection also preserves simplicity when the normalized transfer matrix has
rank-one factors. Restriction to orthonormal coordinates on the reduced range
then gives a simple tensor of the reduced bond dimension.

The support and rank-one hypotheses are explicit here. Their derivation after
uniform blocking is a separate part of the index-continuity argument.

## References

Cirac–Pérez-García–Schuch–Verstraete, arXiv:1703.09188, Proposition IV.5,
lines 773–804.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

/-- The doubled matrix associated with a rectangular bond map. -/
private noncomputable def doubledBondMap {D E : ℕ}
    (A : Matrix (Fin E) (Fin D) ℂ) : Matrix (Fin (E * E)) (Fin (D * D)) ℂ :=
  ((A.map (starRingEnd ℂ)) ⊗ₖ A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Rectangular multiplication of bond matrices induces the corresponding
doubled multiplication. Source: CPSV17, Proposition IV.5, lines 773–804. -/
private theorem doubleLayer_rectangularSandwich {d D E : ℕ}
    (W : MPOTensor d D) (A : Matrix (Fin E) (Fin D) ℂ)
    (B : Matrix (Fin D) (Fin E) ℂ) (i j : Fin d) :
    doubleLayerTensor (fun i j ↦ A * W i j * B) i j =
      doubledBondMap A * doubleLayerTensor W i j * doubledBondMap B := by
  simp only [doubleLayerTensor_apply, doubledBondMap,
    Matrix.submatrix_mul_equiv]
  change ((∑ q : Fin d, ((A * W q i * B).map (starRingEnd ℂ)) ⊗ₖ
    (A * W q j * B)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = _
  simp only [Matrix.map_mul, Matrix.mul_kronecker_mul, Matrix.mul_sum, Matrix.sum_mul]
  rfl

/-- A left inverse remains a left inverse on the doubled bond space. -/
private theorem doubledBondMap_mul_eq_one {D E : ℕ}
    (A : Matrix (Fin E) (Fin D) ℂ) (B : Matrix (Fin D) (Fin E) ℂ)
    (hBA : B * A = 1) : doubledBondMap B * doubledBondMap A = 1 := by
  simp only [doubledBondMap, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, ← Matrix.map_mul, hBA]
  simp

/-- A split inclusion of the doubled letters preserves the two simplicity identities.
Source: CPSV17, Definition III.2 and Proposition IV.5, lines 363–374 and 797–804. -/
private theorem isMPUSimple_of_doubleLayer_inclusion {d D E : ℕ}
    {U : MPOTensor d D} {V : MPOTensor d E} (hU : IsMPUSimple U)
    (A : Matrix (Fin (E * E)) (Fin (D * D)) ℂ)
    (B : Matrix (Fin (D * D)) (Fin (E * E)) ℂ)
    (hBA : B * A = 1)
    (hV : ∀ i j, doubleLayerTensor V i j = A * doubleLayerTensor U i j * B) :
    IsMPUSimple V := by
  obtain ⟨a, b, h₁, h₂⟩ := hU
  refine ⟨a ᵥ* B, A *ᵥ b, ?_, ?_⟩
  · simpa only [hV, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA, Matrix.one_mul, Matrix.mul_one] using h₁
  · intro i j k l
    simp only [hV, ← Matrix.mul_vecMulVec, ← Matrix.vecMulVec_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
    simpa only [Matrix.mul_assoc] using congrArg (fun M ↦ A * M * B) (h₂ i j k l)

/-- Removing a split inclusion of the doubled letters preserves simplicity.
Source: CPSV17, Proposition IV.5, restriction to the support, lines 773–804. -/
private theorem isMPUSimple_of_doubleLayer_split_compression {d D E : ℕ}
    {U : MPOTensor d D} {V : MPOTensor d E} (hV : IsMPUSimple V)
    (A : Matrix (Fin (E * E)) (Fin (D * D)) ℂ)
    (B : Matrix (Fin (D * D)) (Fin (E * E)) ℂ)
    (hBA : B * A = 1)
    (hletters : ∀ i j, doubleLayerTensor V i j = A * doubleLayerTensor U i j * B) :
    IsMPUSimple U := by
  obtain ⟨a, b, h₁, h₂⟩ := hV
  refine ⟨a ᵥ* A, B *ᵥ b, ?_, ?_⟩
  · simpa only [hletters, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc] using h₁
  · intro i j k l
    simpa only [hletters, ← Matrix.mul_vecMulVec, ← Matrix.vecMulVec_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA, Matrix.one_mul, Matrix.mul_one] using
      congrArg (fun M ↦ B * M * A) (h₂ i j k l)

/-- A rectangular inclusion with a left inverse preserves simplicity.
Source: CPSV17, Proposition IV.5, lines 773–804. -/
theorem IsMPUSimple.rectangularSandwich {d D E : ℕ}
    {W : MPOTensor d D} (hW : W.IsMPUSimple)
    (A : Matrix (Fin E) (Fin D) ℂ) (B : Matrix (Fin D) (Fin E) ℂ)
    (hBA : B * A = 1) :
    IsMPUSimple (fun i j ↦ A * W i j * B) :=
  isMPUSimple_of_doubleLayer_inclusion hW
    (doubledBondMap A) (doubledBondMap B)
    (doubledBondMap_mul_eq_one A B hBA)
    (doubleLayer_rectangularSandwich W A B)

/-- Removing a rectangular inclusion with a left inverse preserves simplicity.
Source: CPSV17, Proposition IV.5, lines 773–804. -/
theorem isMPUSimple_of_rectangularSandwich {d D E : ℕ}
    (W : MPOTensor d D)
    (A : Matrix (Fin E) (Fin D) ℂ) (B : Matrix (Fin D) (Fin E) ℂ)
    (hBA : B * A = 1)
    (hW : IsMPUSimple (fun i j ↦ A * W i j * B)) :
    W.IsMPUSimple :=
  isMPUSimple_of_doubleLayer_split_compression hW
    (doubledBondMap A) (doubledBondMap B)
    (doubledBondMap_mul_eq_one A B hBA)
    (doubleLayer_rectangularSandwich W A B)

/-- Doubling preserves rectangular matrix multiplication. -/
private theorem doubledBondMap_mul {D E F : ℕ}
    (A : Matrix (Fin F) (Fin E) ℂ) (B : Matrix (Fin E) (Fin D) ℂ) :
    doubledBondMap (A * B) = doubledBondMap A * doubledBondMap B := by
  simp only [doubledBondMap, Matrix.map_mul, Matrix.mul_kronecker_mul,
    Matrix.submatrix_mul_equiv]

/-- Doubling preserves the identity matrix. -/
private theorem doubledBondMap_one (D : ℕ) :
    doubledBondMap (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  simp [doubledBondMap]

/-- An intermediate projection can be removed between matrices with the
specified right and left supports. -/
private theorem mul_projection_mul_of_supports {D : ℕ}
    (X Y P Q H : Matrix (Fin D) (Fin D) ℂ)
    (hXP : X * P = X) (hQY : Q * Y = Y) (hHQ : H * Q = P * Q) :
    X * H * Y = X * Y := by
  have h := congrArg (fun M ↦ X * M * Y) hHQ
  simp only [← Matrix.mul_assoc, hXP] at h
  simpa only [Matrix.mul_assoc, hQY] using h

/-- Compression is multiplicative between letters satisfying the support
insertion identity. -/
private theorem compressed_mul_of_insertion {D : ℕ}
    (X Y H : Matrix (Fin D) (Fin D) ℂ) (hH : H * H = H)
    (hXY : X * H * Y = X * Y) :
    (H * X * H) * (H * Y * H) = H * (X * Y) * H := by
  have h := congrArg (fun M ↦ H * M * H) hXY
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc H H, hH] using h

/-- The two-letter rank-one insertion identity passes through support
compression when insertion of the support projection preserves the three
products involved. -/
private theorem compressed_simple2 {D : ℕ}
    (X Y E H : Matrix (Fin D) (Fin D) ℂ) (hH : H * H = H)
    (hXY : X * H * Y = X * Y) (hXE : X * H * E = X * E)
    (hEY : E * H * Y = E * Y) (h₂ : X * Y = X * E * Y) :
    (H * X * H) * (H * Y * H) =
      (H * X * H) * (H * E * H) * (H * Y * H) := by
  calc
    _ = H * (X * Y) * H := compressed_mul_of_insertion X Y H hH hXY
    _ = H * (X * E * Y) * H := congrArg (fun M ↦ H * M * H) h₂
    _ = (H * (X * E) * H) * (H * Y * H) :=
      (compressed_mul_of_insertion (X * E) Y H hH
        (by simpa only [Matrix.mul_assoc] using congrArg (fun M ↦ X * M) hEY)).symm
    _ = _ := congrArg (fun M ↦ M * (H * Y * H))
      (compressed_mul_of_insertion X E H hH hXE).symm

/-- Right support of the letters induces right support of the double layer. -/
private theorem doubleLayer_mul_support {d D : ℕ}
    (W : MPOTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hWP : ∀ i j, W i j * P = W i j) (i j : Fin d) :
    doubleLayerTensor W i j * doubledBondMap P =
      doubleLayerTensor W i j := by
  simpa only [Matrix.one_mul, hWP, doubledBondMap_one] using
    (doubleLayer_rectangularSandwich W 1 P i j).symm

/-- Left support of the letters induces left support of the double layer. -/
private theorem support_mul_doubleLayer {d D : ℕ}
    (W : MPOTensor d D) (Q : Matrix (Fin D) (Fin D) ℂ)
    (hQW : ∀ i j, Q * W i j = W i j) (i j : Fin d) :
    doubledBondMap Q * doubleLayerTensor W i j =
      doubleLayerTensor W i j := by
  simpa only [Matrix.mul_one, hQW, doubledBondMap_one] using
    (doubleLayer_rectangularSandwich W Q 1 i j).symm

/-- The normalized diagonal inherits a common right support of the letters. -/
private theorem normalizedDiagonal_mul_support {d D : ℕ}
    (W : MPOTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hWP : ∀ i j, W i j * P = W i j) :
    normalizedDiagonal W * P = normalizedDiagonal W := by
  simp only [normalizedDiagonal, contractPhysical,
    Matrix.smul_mul, Matrix.sum_mul, hWP]

/-- The normalized diagonal inherits a common left support of the letters. -/
private theorem support_mul_normalizedDiagonal {d D : ℕ}
    (W : MPOTensor d D) (Q : Matrix (Fin D) (Fin D) ℂ)
    (hQW : ∀ i j, Q * W i j = W i j) :
    Q * normalizedDiagonal W = normalizedDiagonal W := by
  simp only [normalizedDiagonal, contractPhysical,
    Matrix.mul_smul, Matrix.mul_sum, hQW]

/-- The defining support identity of the reduced projection persists on the
doubled bond space. -/
private theorem doubled_reducedProjection_mul_second {D : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P) :
    doubledBondMap (Matrix.reducedProjection P Q) * doubledBondMap Q =
      doubledBondMap P * doubledBondMap Q := by
  simpa only [doubledBondMap_mul] using
    congrArg doubledBondMap (Matrix.reducedProjection_mul_second (Q := Q) hP)

/-- Inserting the reduced support projection between two doubled letters
does not change their product. -/
private theorem doubleLayer_reducedProjection_insertion {d D : ℕ}
    (W : MPOTensor d D) (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j) (i j k l : Fin d) :
    doubleLayerTensor W i j *
        doubledBondMap (Matrix.reducedProjection P Q) *
        doubleLayerTensor W k l =
      doubleLayerTensor W i j * doubleLayerTensor W k l :=
  mul_projection_mul_of_supports _ _ (doubledBondMap P) (doubledBondMap Q) _
    (doubleLayer_mul_support W P hWP i j)
    (support_mul_doubleLayer W Q hQW k l)
    (doubled_reducedProjection_mul_second P Q hP)

/-- Support compression preserves simplicity when the normalized transfer
matrix has rank-one factors and the compressed tensor is an MPU.
Source: CPSV17, Proposition IV.5, lines 773–804. -/
private theorem isMPUSimple_reducedProjection_of_compressed_isMPU {d D : ℕ} [NeZero d]
    (W : MPOTensor d D) (hW : W.IsMPUSimple)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor W) =
      Matrix.vecMulVec ρ Φ)
    (hU : IsMPU
      (fun i j ↦ Matrix.reducedProjection P Q * W i j * Matrix.reducedProjection P Q)) :
    IsMPUSimple
      (fun i j ↦ Matrix.reducedProjection P Q * W i j * Matrix.reducedProjection P Q) := by
  apply hU.isMPUSimple_of_simple2
    (Φ ᵥ* doubledBondMap (Matrix.reducedProjection P Q))
    (doubledBondMap (Matrix.reducedProjection P Q) *ᵥ ρ)
  intro i j k l
  simp only [doubleLayer_rectangularSandwich, ← Matrix.mul_vecMulVec,
    ← Matrix.vecMulVec_mul, ← hE]
  refine compressed_simple2 _ _ _ _ ?_
    (doubleLayer_reducedProjection_insertion W P Q hP hWP hQW i j k l)
    (mul_projection_mul_of_supports _ _ (doubledBondMap P) (doubledBondMap Q) _
      (doubleLayer_mul_support W P hWP i j)
      (support_mul_normalizedDiagonal _ _ (support_mul_doubleLayer W Q hQW))
      (doubled_reducedProjection_mul_second P Q hP))
    (mul_projection_mul_of_supports _ _ (doubledBondMap P) (doubledBondMap Q) _
      (normalizedDiagonal_mul_support _ _ (doubleLayer_mul_support W P hWP))
      (support_mul_doubleLayer W Q hQW k l)
      (doubled_reducedProjection_mul_second P Q hP)) ?_
  · simpa only [doubledBondMap_mul] using
      congrArg doubledBondMap (Matrix.reducedProjection_isOrthogonalProjection P Q).2
  · simpa only [← hE] using
      hW.simple2_of_normalizedDiagonal_pow_eq_vecMulVec ρ Φ 1 Nat.zero_lt_one
        ((pow_one _).trans hE) i j k l

/-- Simplicity of a supported tensor passes to orthonormal coordinates on
its support. Source: CPSV17, Proposition IV.5, lines 773–804. -/
theorem isMPUSimple_supportCoordinates {d D k : ℕ}
    (W : MPOTensor d D) (T : Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1) (hRange : V * Vᴴ = T)
    (hW : IsMPUSimple (fun i j ↦ T * W i j * T)) :
    IsMPUSimple (fun i j ↦ Vᴴ * W i j * V) :=
  isMPUSimple_of_rectangularSandwich (fun i j ↦ Vᴴ * W i j * V) V Vᴴ hV
    (by simpa only [← hRange, Matrix.mul_assoc] using hW)


/-- Support compression of a simple MPU with rank-one normalized transfer
matrix is simple. The compressed tensor is an MPU because support compression
preserves all periodic operators.
Source: CPSV17, Proposition IV.5, lines 773–804. -/
theorem IsMPUSimple.reducedProjection {d D : ℕ} [NeZero d]
    {W : MPOTensor d D} (hW : W.IsMPUSimple)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor W) = Matrix.vecMulVec ρ Φ) :
    IsMPUSimple (virtualSandwich (Matrix.reducedProjection P Q) W
      (Matrix.reducedProjection P Q)) :=
  isMPUSimple_reducedProjection_of_compressed_isMPU W hW P Q hP hWP hQW ρ Φ hE
    (fun N hN ↦ (mpo_virtualSandwich_reducedProjection_eq W P Q hP hWP hQW N).symm ▸
      hW.isMPU N hN)

end MPOTensor
