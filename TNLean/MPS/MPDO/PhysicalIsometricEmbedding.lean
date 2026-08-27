/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.MPDO.BNTLayerOrthogonality
import TNLean.MPS.MPDO.PhysicalSupportSALTransport

/-!
# Isometric embeddings of the physical space of an MPO tensor

This module records the elementary coordinate transport obtained by embedding
the one-site physical space of an MPO tensor isometrically into a larger
space.  On the doubled MPS index, the isometry is the ket matrix tensored with
the conjugate of the bra matrix.

These statements are project-derived coordinate lemmas.  They are used when
placing normal BNT representatives in orthogonal physical sectors; they are
not statements of arXiv:1606.00608.  The source context is the normal-block
decomposition in lines 217--246 and the per-sector reduction in lines
1628--1665 and 1740--1782.

## Main definitions and statements

* `MPOTensor.doubledPhysicalMatrix`: the induced matrix on the doubled
  physical index.
* `MPOTensor.doubledPhysicalMatrix_isometry`: a physical isometry induces an
  isometry on the doubled index.
* `MPOTensor.toMPSTensor_changePhysicalBasis`: exact identification with
  isometric Kraus mixing.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, lines
  217--246, 1628--1665, and 1740--1782 (construction context only)
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

/-! ### The doubled physical isometry -/

/-- The matrix induced on the doubled physical index by a physical coordinate
matrix.  Its ket coefficient is `V i p`, while its bra coefficient is
`star (V j q)`, in the `finProdFinEquiv` convention of `MPOTensor.toMPSTensor`.

This is a project-derived coordinate definition used in the setting of
arXiv:1606.00608, lines 217--246 and 1628--1665; the paper does not state this
definition. -/
def doubledPhysicalMatrix (V : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Fin (e * e)) (Fin (d * d)) ℂ :=
  fun ij pq ↦
    V ij.divNat pq.divNat * star (V ij.modNat pq.modNat)

/-- An isometry of the one-site physical space induces an isometry on the
doubled ket--bra index.

This is project-derived coordinate algebra in the setting of arXiv:1606.00608,
lines 217--246 and 1628--1665, not a result asserted in the paper. -/
theorem doubledPhysicalMatrix_isometry
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    (doubledPhysicalMatrix V)ᴴ * doubledPhysicalMatrix V = 1 := by
  classical
  ext pq rs
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).surjective pq
  obtain ⟨⟨r, s⟩, rfl⟩ :=
    (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).surjective rs
  rw [Matrix.mul_apply, ← Equiv.sum_comp
    (finProdFinEquiv : Fin e × Fin e ≃ Fin (e * e)), Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, doubledPhysicalMatrix,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp_rw [star_mul, star_star]
  have hterm (i j : Fin e) :
      (V j q * star (V i p)) * (V i r * star (V j s)) =
        (star (V i p) * V i r) * (V j q * star (V j s)) := by
    ring
  simp_rw [hterm]
  rw [← Fintype.sum_mul_sum]
  have hpr := congrFun (congrFun hV p) r
  have hsq := congrFun (congrFun hV s) q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hpr hsq
  rw [hpr]
  have hsecond :
      (∑ j : Fin e, V j q * star (V j s)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) s q := by
    simpa only [mul_comm] using hsq
  rw [hsecond]
  simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h₁ : p = r <;> by_cases h₂ : q = s <;>
    simp [h₁, h₂, eq_comm]

/-- Changing the physical basis of an MPO tensor is exactly isometric mixing
of its doubled-index MPS matrices by `doubledPhysicalMatrix`.

This is a project-derived coordinate identity used in the setting of
arXiv:1606.00608, lines 217--246 and 1628--1665; the paper does not state it. -/
theorem toMPSTensor_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (K : MPOTensor d D) :
    (changePhysicalBasis V K).toMPSTensor =
      fun ij ↦ ∑ pq : Fin (d * d), doubledPhysicalMatrix V ij pq • K.toMPSTensor pq := by
  funext ij
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin e × Fin e ≃ Fin (e * e)).surjective ij
  simp only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]
  rw [changePhysicalBasis_apply_eq_sum]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d))]
  apply Finset.sum_congr rfl
  rintro ⟨p, q⟩ _
  simp [doubledPhysicalMatrix]

/-! ### Doubled-index MPS consequences -/

/-- An isometric embedding of the one-site physical space leaves the
doubled-index MPS transfer map unchanged.

This is a project-derived coordinate identity used in the setting of
arXiv:1606.00608, lines 217--246 and 1628--1665; the paper does not state it. -/
theorem transferMap_toMPSTensor_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    Kraus.transferMap (changePhysicalBasis V K).toMPSTensor =
      Kraus.transferMap K.toMPSTensor := by
  rw [toMPSTensor_changePhysicalBasis]
  exact MPSTensor.transferMap_kraus_isometry K.toMPSTensor
    (doubledPhysicalMatrix V) (doubledPhysicalMatrix_isometry V hV)

/-- Isometric physical embedding preserves and reflects one-site
injectivity of the doubled-index MPS tensor.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this equivalence. -/
theorem isInjective_toMPSTensor_changePhysicalBasis_iff
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    Kraus.IsInjective (changePhysicalBasis V K).toMPSTensor ↔
      Kraus.IsInjective K.toMPSTensor := by
  rw [toMPSTensor_changePhysicalBasis]
  exact MPSTensor.isInjective_kraus_isometry_iff K.toMPSTensor
    (doubledPhysicalMatrix V) (doubledPhysicalMatrix_isometry V hV)

/-- An isometric physical embedding preserves left-canonical normalization
of the doubled-index MPS tensor.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this lemma. -/
theorem isLeftCanonical_toMPSTensor_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) (hK : MPSTensor.IsLeftCanonical K.toMPSTensor) :
    MPSTensor.IsLeftCanonical (changePhysicalBasis V K).toMPSTensor := by
  rw [toMPSTensor_changePhysicalBasis]
  exact MPSTensor.isLeftCanonical_kraus_isometry K.toMPSTensor
    (doubledPhysicalMatrix V) (doubledPhysicalMatrix_isometry V hV) hK

/-- Isometric physical embedding preserves and reflects normality of the
doubled-index MPS tensor.

The proof only transports the transfer map and the equivalence between
irreducibility of a Kraus family and of its transfer map; it introduces no
new Perron--Frobenius argument.  This is project-derived coordinate algebra
used for the normal-block construction surrounding arXiv:1606.00608, lines
217--246 and 1628--1665, not a theorem asserted in the paper. -/
theorem isNormalTensor_toMPSTensor_changePhysicalBasis_iff
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    MPSTensor.IsNormalTensor (changePhysicalBasis V K).toMPSTensor ↔
      MPSTensor.IsNormalTensor K.toMPSTensor := by
  have hTransfer := transferMap_toMPSTensor_changePhysicalBasis V hV K
  constructor
  · intro hC
    refine ⟨?_, ?_, ?_⟩
    · apply Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM
      have hIrr := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily
        (changePhysicalBasis V K).toMPSTensor hC.no_invariant_proj
      change IsIrreducibleMap
        (Kraus.transferMap (changePhysicalBasis V K).toMPSTensor) at hIrr
      rw [hTransfer] at hIrr
      exact hIrr
    · rw [← hTransfer]
      exact hC.spectral_radius_one
    · rw [← hTransfer]
      exact hC.primitive_transfer
  · intro hB
    refine ⟨?_, ?_, ?_⟩
    · apply Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM
      have hIrr := Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily
        K.toMPSTensor hB.no_invariant_proj
      change IsIrreducibleMap (Kraus.transferMap K.toMPSTensor) at hIrr
      change IsIrreducibleMap
        (Kraus.transferMap (changePhysicalBasis V K).toMPSTensor)
      rw [hTransfer]
      exact hIrr
    · rw [hTransfer]
      exact hB.spectral_radius_one
    · rw [hTransfer]
      exact hB.primitive_transfer

/-- Applying the same physical-coordinate matrix to two MPO tensors
preserves gauge equivalence of their doubled-index MPS representatives.  No
isometry hypothesis is needed.

This is project-derived coordinate algebra used in the setting of
arXiv:1606.00608, lines 217--246 and 1628--1665; the paper does not state it. -/
theorem gaugeEquiv_toMPSTensor_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) {K L : MPOTensor d D}
    (hKL : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) :
    MPSTensor.GaugeEquiv
      (changePhysicalBasis V K).toMPSTensor
      (changePhysicalBasis V L).toMPSTensor := by
  simp only [toMPSTensor_changePhysicalBasis]
  exact hKL.sum_smul (doubledPhysicalMatrix V)

/-! ### MPO positivity and saturation consequences -/

/-- Applying an arbitrary physical-coordinate matrix preserves the MPDO
positivity condition in the forward direction.

No isometry hypothesis is required: every periodic density operator is
conjugated by the corresponding sitewise physical matrix.  This is a
project-derived coordinate fact used in the setting of arXiv:1606.00608,
lines 1628--1665 and 1740--1782; the paper does not state it. -/
protected theorem IsMPDO.changePhysicalBasis
    (hK : IsMPDO K) (V : Matrix (Fin e) (Fin d) ℂ) :
    IsMPDO (changePhysicalBasis V K) := by
  intro N hN
  rw [← singleKrausMap_sitewisePhysicalMatrix_mpo]
  exact (hK N hN).mul_mul_conjTranspose_same (sitewisePhysicalMatrix V N)

/-- Under an isometric physical embedding, the MPDO condition is equivalent
before and after the embedding.

This is project-derived coordinate algebra used in the setting of
arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper does not state
this equivalence. -/
theorem isMPDO_changePhysicalBasis_iff
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    IsMPDO (changePhysicalBasis V K) ↔ IsMPDO K := by
  constructor
  · exact isMPDO_of_changePhysicalBasis_isMPDO_of_isometry V hV K
  · intro hK
    exact hK.changePhysicalBasis V

/-- Saturation of the area law ascends through an isometric physical
embedding.

The source tensor's positivity, positive-length trace normalization, and the
equalities of neighboring mutual informations are retained.  This is a
project-derived coordinate fact used in the setting of arXiv:1606.00608,
lines 1628--1665 and 1740--1782; the paper does not state it. -/
protected theorem IsSAL.changePhysicalBasis_of_isometry
    (hK : IsSAL K) (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    IsSAL (changePhysicalBasis V K) := by
  obtain ⟨hMpdo, hTrace, hStep⟩ := hK
  let hAmbientMpdo : IsMPDO (changePhysicalBasis V K) :=
    hMpdo.changePhysicalBasis V
  refine ⟨hAmbientMpdo, ?_, ?_⟩
  · intro N hN
    rw [trace_mpo_changePhysicalBasis_of_isometry V hV]
    exact hTrace N hN
  · intro N L hL hLN
    rw [mutualInfoChain_changePhysicalBasis_of_isometry V hV K N L
        (Nat.le_of_lt (hLN.trans_le (Nat.div_le_self N 2)))
        (hMpdo N (by omega)),
      mutualInfoChain_changePhysicalBasis_of_isometry V hV K N (L + 1)
        (hLN.trans_le (Nat.div_le_self N 2)) (hMpdo N (by omega))]
    exact hStep N L hL hLN

/-- Under an isometric physical embedding, saturation of the area law is
equivalent before and after the embedding.

This is project-derived coordinate algebra used in the setting of
arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper does not state
this equivalence. -/
theorem isSAL_changePhysicalBasis_iff
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    IsSAL (changePhysicalBasis V K) ↔ IsSAL K := by
  constructor
  · exact isSAL_of_changePhysicalBasis_isSAL_of_isometry V hV K
  · intro hK
    exact hK.changePhysicalBasis_of_isometry V hV

/-- An isometric physical embedding leaves the one-site physical-trace
transfer matrix unchanged.

This is project-derived coordinate algebra used in the zero-correlation
length setting of arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper
does not state this identity. -/
theorem physTraceTransfer_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    physTraceTransfer (changePhysicalBasis V K) = physTraceTransfer K := by
  ext beta alpha
  simp only [physTraceTransfer, Matrix.sum_apply]
  simp_rw [changePhysicalBasis_apply_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ i : Fin e, ∑ pq : Fin d × Fin d,
        (V i pq.1 * star (V i pq.2)) * K pq.1 pq.2 beta alpha =
        ∑ pq : Fin d × Fin d,
          (∑ i : Fin e, V i pq.1 * star (V i pq.2)) *
            K pq.1 pq.2 beta alpha := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro pq _
              rw [Finset.sum_mul]
    _ = ∑ p : Fin d, K p p beta alpha := by
      have hentry (p q : Fin d) :
          (∑ i : Fin e, V i p * star (V i q)) =
            if p = q then 1 else 0 := by
        have hpq := congrFun (congrFun hV q) p
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.one_apply, mul_comm, eq_comm] using hpq
      rw [Fintype.sum_prod_type]
      simp_rw [hentry]
      simp

/-! ### Canonical one-site physical support -/

/-- The blockwise copy of `Vᴴ` acting on the physical-column component of
`physicalSliceColumns`.  It leaves the two virtual column indices fixed.

This is a project-derived coordinate matrix used in the normal-block setting
of arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper does not state
this definition. -/
noncomputable def physicalSliceColumnCoisometry
    (V : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Fin (D * D * d)) (Fin (D * D * e)) ℂ :=
  fun q r ↦ if q.divNat = r.divNat then star (V r.modNat q.modNat) else 0

/-- If `V` is an isometry, its blockwise action on the stacked physical
columns is a coisometry.

This is project-derived coordinate algebra used in the normal-block setting
of arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper does not state
this lemma. -/
theorem physicalSliceColumnCoisometry_mul_conjTranspose
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    physicalSliceColumnCoisometry (D := D) V *
      (physicalSliceColumnCoisometry (D := D) V)ᴴ = 1 := by
  classical
  ext x y
  obtain ⟨⟨u, p⟩, rfl⟩ :=
    (finProdFinEquiv : Fin (D * D) × Fin d ≃ Fin (D * D * d)).surjective x
  obtain ⟨⟨v, q⟩, rfl⟩ :=
    (finProdFinEquiv : Fin (D * D) × Fin d ≃ Fin (D * D * d)).surjective y
  rw [Matrix.mul_apply, ← Equiv.sum_comp
    (finProdFinEquiv : Fin (D * D) × Fin e ≃ Fin (D * D * e)),
    Fintype.sum_prod_type]
  simp only [physicalSliceColumnCoisometry, Matrix.conjTranspose_apply,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat,
    Matrix.one_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  have hpq :
      (∑ i : Fin e, star (V i p) * V i q) = if p = q then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hV p) q
  by_cases huv : u = v
  · subst v
    simpa [hpq]
  · have hvu : ¬ v = u := fun h ↦ huv h.symm
    simp [huv, hvu]

/-- The stacked physical columns of a physically embedded MPO tensor are
obtained by multiplying the original stacked columns by `V` on the left and
the blockwise copy of `Vᴴ` on the right.

This identity uses the literal `physicalSliceColumns` definition.  It is
project-derived coordinate algebra used in the normal-block setting of
arXiv:1606.00608, lines 1628--1665 and 1740--1782; the paper does not state it. -/
theorem physicalSliceColumns_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (K : MPOTensor d D) :
    physicalSliceColumns (changePhysicalBasis V K) =
      V * physicalSliceColumns K * physicalSliceColumnCoisometry (D := D) V := by
  classical
  ext i r
  obtain ⟨⟨u, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin (D * D) × Fin e ≃ Fin (D * D * e)).surjective r
  simp only [physicalSliceColumns, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, changePhysicalBasis]
  conv_rhs =>
    rw [Matrix.mul_apply, ← Equiv.sum_comp
      (finProdFinEquiv : Fin (D * D) × Fin d ≃ Fin (D * D * d)),
      Fintype.sum_prod_type]
  simp only [physicalSliceColumnCoisometry,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp [Matrix.mul_apply, physicalSliceColumns, physicalSlice]

/-- The joint column support of `V * Y` is the isometric image of the joint
column support of `Y`.

This private helper is project-derived finite-dimensional linear algebra for
the physical-support transport used around arXiv:1606.00608, lines 1628--1665
and 1740--1782; the paper does not state it. -/
private theorem supportProj_left_isometry
    {n m k : ℕ} (V : Matrix (Fin m) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    (Matrix.posSemidef_self_mul_conjTranspose (V * Y)).supportProj =
      V * (Matrix.posSemidef_self_mul_conjTranspose Y).supportProj * Vᴴ := by
  let P := (Matrix.posSemidef_self_mul_conjTranspose Y).supportProj
  let Z := V * Y
  let Q := (Matrix.posSemidef_self_mul_conjTranspose Z).supportProj
  change Q = V * P * Vᴴ
  have hPY : P * Y = Y := by
    simpa [P, Matrix.PosSemidef.supportProj] using
      Matrix.supportProj_mul_conjTranspose_mul_self Y
  have hQZ : Q * Z = Z := by
    simpa [Q, Matrix.PosSemidef.supportProj] using
      Matrix.supportProj_mul_conjTranspose_mul_self Z
  have hPHerm : P.IsHermitian := by
    exact (Matrix.posSemidef_self_mul_conjTranspose Y).supportProj_isHermitian
  have hQHerm : Q.IsHermitian := by
    exact (Matrix.posSemidef_self_mul_conjTranspose Z).supportProj_isHermitian
  have hCandidateHerm : (V * P * Vᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose V hPHerm
  have hCandidateZ : (V * P * Vᴴ) * Z = Z := by
    simp only [Z, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V Y, hV, Matrix.one_mul, hPY]
  obtain ⟨T, hQT⟩ :=
    (Matrix.posSemidef_self_mul_conjTranspose Z).exists_supportProj_eq_mul
  change Q = Z * Zᴴ * T at hQT
  have hCandidateQ : (V * P * Vᴴ) * Q = Q := by
    calc
      (V * P * Vᴴ) * Q =
          (V * P * Vᴴ) * (Z * Zᴴ * T) := by rw [hQT]
      _ = ((V * P * Vᴴ) * Z) * (Zᴴ * T) := by
        simp only [Matrix.mul_assoc]
      _ = Z * (Zᴴ * T) := by rw [hCandidateZ]
      _ = Q := by rw [hQT]; simp only [Matrix.mul_assoc]
  obtain ⟨S, hPS⟩ :=
    (Matrix.posSemidef_self_mul_conjTranspose Y).exists_supportProj_eq_mul
  change P = Y * Yᴴ * S at hPS
  have hCandidateFactor : V * P * Vᴴ = Z * (Yᴴ * S * Vᴴ) := by
    rw [hPS]
    simp only [Z, Matrix.mul_assoc]
  have hQCandidate : Q * (V * P * Vᴴ) = V * P * Vᴴ := by
    rw [hCandidateFactor, ← Matrix.mul_assoc, hQZ]
  have hQCandidateEqQ : Q * (V * P * Vᴴ) = Q := by
    have hAdjoint := congrArg Matrix.conjTranspose hCandidateQ
    simpa only [Matrix.conjTranspose_mul, hQHerm.eq,
      hCandidateHerm.eq] using hAdjoint
  exact hQCandidateEqQ.symm.trans hQCandidate

/-- The Gram matrix of the stacked physical columns transforms by isometric
conjugation under an isometric physical embedding.

The proof uses the literal stacked-column identity and the coisometry on its
column index.  This is project-derived coordinate algebra used in the
normal-block setting of arXiv:1606.00608, lines 1628--1665 and 1740--1782;
the paper does not state it. -/
theorem physicalSliceColumns_mul_conjTranspose_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    physicalSliceColumns (changePhysicalBasis V K) *
        (physicalSliceColumns (changePhysicalBasis V K))ᴴ =
      V * (physicalSliceColumns K * (physicalSliceColumns K)ᴴ) * Vᴴ := by
  let Z := physicalSliceColumns K
  let R := physicalSliceColumnCoisometry (D := D) V
  have hR : R * Rᴴ = 1 :=
    physicalSliceColumnCoisometry_mul_conjTranspose V hV
  rw [physicalSliceColumns_changePhysicalBasis]
  change (V * Z * R) * (V * Z * R)ᴴ = V * (Z * Zᴴ) * Vᴴ
  calc
    (V * Z * R) * (V * Z * R)ᴴ =
        V * Z * (R * Rᴴ) * Zᴴ * Vᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = V * Z * Zᴴ * Vᴴ := by rw [hR]; simp
    _ = V * (Z * Zᴴ) * Vᴴ := by simp only [Matrix.mul_assoc]

/-- The canonical support projection of the stacked physical columns is
transported by isometric conjugation:
`physicalSupportProj (changePhysicalBasis V K) =
V * physicalSupportProj K * Vᴴ`.

This uses the repository's literal `physicalSliceColumns` and
`physicalSupportProj` definitions.  It is a project-derived coordinate fact
used in the normal-block setting of arXiv:1606.00608, lines 1628--1665 and
1740--1782; the paper does not state it. -/
theorem physicalSupportProj_changePhysicalBasis
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (K : MPOTensor d D) :
    physicalSupportProj (changePhysicalBasis V K) =
      V * physicalSupportProj K * Vᴴ := by
  let Z := physicalSliceColumns K
  let Z' := physicalSliceColumns (changePhysicalBasis V K)
  have hGram : Z' * Z'ᴴ = (V * Z) * (V * Z)ᴴ := by
    calc
      Z' * Z'ᴴ = V * (Z * Zᴴ) * Vᴴ :=
        physicalSliceColumns_mul_conjTranspose_changePhysicalBasis V hV K
      _ = (V * Z) * (V * Z)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hSupport :=
    (Matrix.posSemidef_self_mul_conjTranspose Z').supportProj_congr
      (Matrix.posSemidef_self_mul_conjTranspose (V * Z)) hGram
  calc
    physicalSupportProj (changePhysicalBasis V K) =
        (Matrix.posSemidef_self_mul_conjTranspose (V * Z)).supportProj := by
          simpa [physicalSupportProj, Z'] using hSupport
    _ = V * (Matrix.posSemidef_self_mul_conjTranspose Z).supportProj * Vᴴ :=
      supportProj_left_isometry V hV Z
    _ = V * physicalSupportProj K * Vᴴ := by
      simp only [physicalSupportProj, Z]

end MPOTensor
