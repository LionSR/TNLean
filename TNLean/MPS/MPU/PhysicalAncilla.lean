/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalForm

/-!
# Attaching a physical identity ancilla to a matrix product unitary

This file formalizes the local tensor operation
$\mathcal U^{(x)} = \mathcal U \otimes I_x$ from arXiv:1703.09188,
lines 706--724.  It enlarges only the physical alphabet, from \(d\) to \(d x\);
the virtual bond dimension remains \(D\).

## Main definitions

* `MPOTensor.tensorPhysicalId`: attach an identity ancilla at each physical site.
* `MPOTensor.physicalAncillaConfigEquiv`: split every enlarged physical configuration
  into its original and ancilla configurations.
* `MPOTensor.doubledPhysicalAncillaShuffle`: separate the original and ancilla doubled indices.
* `MPOTensor.normalizedDiagonalLift`: adjoin the normalized diagonal ancilla alphabet.
* `MPOTensor.normalizedDiagonalLiftCFIIData`: construct canonical-form-II data for the lift.
* `MPOTensor.tensorPhysicalIdCFIIData`: construct canonical-form-II data after ancilla attachment.

## Main results

* `MPOTensor.mpo_tensorPhysicalId`: the generated MPO is the reindexed Kronecker
  product of the original MPO and the ancilla identity.
* `MPOTensor.IsMPU.tensorPhysicalId`: identity-ancilla attachment preserves the MPU
  property.
* `MPOTensor.transferMap_normalizedFlattening_tensorPhysicalId`: the normalized transfer map is
  unchanged.
* `MPOTensor.hasFullActiveSupport_tensorPhysicalIdCFIIData`: full active support is preserved.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D x : ℕ}

/-- Attach a physical identity ancilla of dimension \(x\) to an MPO tensor, without
changing its virtual bond dimension \(D\).

In coordinates, the enlarged physical indices are pairs `(i, a)` and `(j, b)`, and
$\mathcal U^{(x)}_{(i,a),(j,b);\beta,\alpha}
  = \mathcal U_{i,j;\beta,\alpha}\,\delta_{a,b}$.

Source: arXiv:1703.09188, lines 706--724. -/
def tensorPhysicalId (U : MPOTensor d D) (x : ℕ) : MPOTensor (d * x) D :=
  fun ia jb ↦ if ia.modNat = jb.modNat then U ia.divNat jb.divNat else 0

/-- Coordinate formula for physical identity-ancilla attachment. -/
@[simp] theorem tensorPhysicalId_apply (U : MPOTensor d D) (i j : Fin d)
    (a b : Fin x) (β α : Fin D) :
    tensorPhysicalId U x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) β α =
      U i j β α * if a = b then 1 else 0 := by
  by_cases h : a = b <;> simp [tensorPhysicalId, h]

/-- Each fixed-virtual physical slice is the Kronecker product with the ancilla
identity, reindexed from pairs to the standard `Fin (d * x)` product encoding. -/
theorem physicalSlice_tensorPhysicalId (U : MPOTensor d D) (x : ℕ) (β α : Fin D) :
    physicalSlice (tensorPhysicalId U x) β α =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (physicalSlice U β α ⊗ₖ (1 : Matrix (Fin x) (Fin x) ℂ)) := by
  ext ia jb
  by_cases h : ia.modNat = jb.modNat <;>
    simp [physicalSlice, tensorPhysicalId, Matrix.reindex_apply, h]

/-- Split a sitewise enlarged physical configuration into its original and
ancilla configurations. -/
def physicalAncillaConfigEquiv (N d x : ℕ) :
    (Fin N → Fin (d * x)) ≃ (Fin N → Fin d) × (Fin N → Fin x) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Fin d) (fun _ ↦ Fin x))

private theorem evalWord_tensorPhysicalId (U : MPOTensor d D) (x : ℕ)
    (is js : List (Fin (d * x))) :
    evalWord (tensorPhysicalId U x) is js =
      if is.length = js.length ∧ is.map Fin.modNat = js.map Fin.modNat then
        evalWord U (is.map Fin.divNat) (js.map Fin.divNat)
      else 0 := by
  induction is generalizing js with
  | nil => cases js <;> simp [evalWord]
  | cons i is ih =>
      cases js with
      | nil => simp [evalWord]
      | cons j js =>
          by_cases h : i.modNat = j.modNat
          · simp [evalWord, tensorPhysicalId, h, ih]
          · simp [evalWord, tensorPhysicalId, h]

/-- The closed MPO generated after identity-ancilla attachment is the Kronecker
product of the original closed MPO and the ancilla identity, in the canonical
sitewise product coordinates.

Source: arXiv:1703.09188, lines 706--724. -/
theorem mpo_tensorPhysicalId (U : MPOTensor d D) (x N : ℕ) :
    mpo (tensorPhysicalId U x) N =
      Matrix.reindex (physicalAncillaConfigEquiv N d x).symm
        (physicalAncillaConfigEquiv N d x).symm
        (mpo U N ⊗ₖ (1 : Matrix (Fin N → Fin x) (Fin N → Fin x) ℂ)) := by
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mpo_apply, mpoMatrixEntry]
  rw [evalWord_tensorPhysicalId]
  simp only [List.length_ofFn, true_and, List.map_ofFn]
  by_cases h : (fun c ↦ (σ c).modNat) = (fun c ↦ (τ c).modNat) <;>
    simp [physicalAncillaConfigEquiv, Equiv.arrowCongr, Function.comp_def, h]

/-- Attaching a nonempty physical identity ancilla preserves the matrix product
unitary property.

Source: arXiv:1703.09188, lines 706--724. -/
theorem IsMPU.tensorPhysicalId {U : MPOTensor d D} (hU : IsMPU U)
    (x : ℕ) (_hx : 0 < x) : IsMPU (tensorPhysicalId U x) := by
  intro N hN
  rw [mpo_tensorPhysicalId]
  apply Matrix.reindex_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, hU.mpo_mul_conjTranspose_mpo hN,
    Matrix.one_mul, Matrix.one_kronecker_one]


/-! ## Normalized doubled-index tensor -/

/-- Shuffle the doubled enlarged physical index by
\(((i,a),(j,b))\mapsto((i,j),(a,b))\), with both pairs encoded by
`finProdFinEquiv`.

This makes the original and ancilla doubled indices explicit and fixes their
orientation for identity-ancilla attachment.

Source: arXiv:1703.09188, lines 706--724. -/
private def doubledPhysicalAncillaMiddleShuffle (d x : ℕ) :
    ((Fin d × Fin x) × (Fin d × Fin x)) ≃
      ((Fin d × Fin d) × (Fin x × Fin x)) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv := by rintro ⟨⟨i, a⟩, ⟨j, b⟩⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩; rfl

@[simp] private theorem doubledPhysicalAncillaMiddleShuffle_apply
    (i j : Fin d) (a b : Fin x) :
    doubledPhysicalAncillaMiddleShuffle d x ((i, a), (j, b)) = ((i, j), (a, b)) := rfl

/-- Separate the original and ancilla doubled physical indices by the shuffle
\(((i,a),(j,b))\mapsto((i,j),(a,b))\).

This is the physical relabeling used to identify the normalized flattening and
canonical-form-II data after identity-ancilla attachment. -/
def doubledPhysicalAncillaShuffle (d x : ℕ) :
    Fin ((d * x) * (d * x)) ≃ Fin ((d * d) * (x * x)) :=
  finProdFinEquiv.symm |>.trans <|
    (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans <|
      (doubledPhysicalAncillaMiddleShuffle d x).trans <|
        (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

/-- Coordinate action of the doubled physical-ancilla shuffle. -/
@[simp] theorem doubledPhysicalAncillaShuffle_apply (i j : Fin d) (a b : Fin x) :
    doubledPhysicalAncillaShuffle d x
        (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))) =
      finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (a, b)) := by
  simp [doubledPhysicalAncillaShuffle]

/-- Lift a doubled-index MPS tensor by a normalized diagonal ancilla alphabet.
Only letters \((a,a)\) are nonzero, and each is scaled by \(1/\sqrt{x}\).

The physical alphabet is ordered as \(((i,j),(a,b))\). -/
noncomputable def normalizedDiagonalLift (A : MPSTensor (d * d) D) (x : ℕ) :
    MPSTensor ((d * d) * (x * x)) D := fun k ↦
  let pq := finProdFinEquiv.symm k
  let ab := finProdFinEquiv.symm pq.2
  if ab.1 = ab.2 then ((Real.sqrt x : ℂ)⁻¹) • A pq.1 else 0

/-- Coordinate formula for the normalized diagonal lift. -/
@[simp] theorem normalizedDiagonalLift_apply (A : MPSTensor (d * d) D) (x : ℕ)
    (ij : Fin (d * d)) (a b : Fin x) :
    normalizedDiagonalLift A x (finProdFinEquiv (ij, finProdFinEquiv (a, b))) =
      if a = b then ((Real.sqrt x : ℂ)⁻¹) • A ij else 0 := by
  simp [normalizedDiagonalLift]

/-- A nonempty normalized diagonal ancilla leaves the transfer map unchanged. -/
theorem transferMap_normalizedDiagonalLift (A : MPSTensor (d * d) D)
    (x : ℕ) (hx : 0 < x) :
    MPSTensor.transferMap (normalizedDiagonalLift A x) = MPSTensor.transferMap A := by
  classical
  apply LinearMap.ext
  intro X
  simp only [MPSTensor.transferMap_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  have hscale : (x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1 := by
    have hxR : (0 : ℝ) ≤ x := by positivity
    rw [mul_assoc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hxR]
    simp [hx.ne']
  have hinner (a : Fin x) :
      (∑ b : Fin x,
        normalizedDiagonalLift A x (finProdFinEquiv (ij, finProdFinEquiv (a, b))) * X *
          (normalizedDiagonalLift A x (finProdFinEquiv (ij, finProdFinEquiv (a, b))))ᴴ) =
        ((Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹) • (A ij * X * (A ij)ᴴ) := by
    rw [Finset.sum_eq_single a]
    · simp [normalizedDiagonalLift_apply, Matrix.conjTranspose_smul,
        RCLike.star_def, Complex.conj_ofReal, smul_smul]
    · intro b _ hba
      have hab : a ≠ b := fun h ↦ hba h.symm
      simp [normalizedDiagonalLift_apply, hab]
    · simp
  rw [Finset.sum_congr rfl (fun a _ ↦ hinner a), Finset.sum_const]
  rw [Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hscale' :
      (x : ℂ) * ((Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹) = 1 := by
    simpa [mul_assoc] using hscale
  rw [hscale', one_smul]

/-- A nonempty normalized diagonal lift preserves tensor irreducibility. -/
theorem isIrreducibleTensor_normalizedDiagonalLift
    (A : MPSTensor (d * d) D) (x : ℕ) (hx : 0 < x)
    (hA : MPSTensor.IsIrreducibleTensor A) :
    MPSTensor.IsIrreducibleTensor (normalizedDiagonalLift A x) := by
  classical
  intro hInv
  apply hA
  rcases hInv with ⟨P, hP, hP0, hP1, hLower⟩
  refine ⟨P, hP, hP0, hP1, ?_⟩
  intro ij
  let a : Fin x := ⟨0, hx⟩
  have h := hLower (finProdFinEquiv (ij, finProdFinEquiv (a, a)))
  simp only [normalizedDiagonalLift_apply] at h
  have hsqrt : ((Real.sqrt x : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hx))
  apply (smul_eq_zero.mp ?_).resolve_left hsqrt
  simpa [Matrix.mul_assoc] using h

/-- A nonempty normalized diagonal lift preserves normal tensors. -/
theorem isNormalTensor_normalizedDiagonalLift
    {A : MPSTensor (d * d) D} (hA : MPSTensor.IsNormalTensor A)
    (x : ℕ) (hx : 0 < x) :
    MPSTensor.IsNormalTensor (normalizedDiagonalLift A x) := by
  refine ⟨isIrreducibleTensor_normalizedDiagonalLift A x hx hA.no_invariant_proj, ?_, ?_⟩
  · rw [transferMap_normalizedDiagonalLift A x hx]
    exact hA.spectral_radius_one
  · rw [transferMap_normalizedDiagonalLift A x hx]
    exact hA.primitive_transfer

/-- A nonempty normalized diagonal lift preserves left-canonical normalization. -/
theorem leftCanonical_normalizedDiagonalLift
    (A : MPSTensor (d * d) D) (x : ℕ) (hx : 0 < x)
    (hA : MPSTensor.IsLeftCanonical A) :
    MPSTensor.IsLeftCanonical (normalizedDiagonalLift A x) := by
  classical
  rw [MPSTensor.IsLeftCanonical, ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type]
  apply Eq.trans (Finset.sum_congr rfl fun ij _ ↦ ?_) hA
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  have hscale : (x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1 := by
    have hxR : (0 : ℝ) ≤ x := by positivity
    rw [mul_assoc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hxR]
    simp [hx.ne']
  have hinner (a : Fin x) :
      (∑ b : Fin x,
        (normalizedDiagonalLift A x (finProdFinEquiv (ij, finProdFinEquiv (a, b))))ᴴ *
          normalizedDiagonalLift A x (finProdFinEquiv (ij, finProdFinEquiv (a, b)))) =
        ((Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹) • ((A ij)ᴴ * A ij) := by
    rw [Finset.sum_eq_single a]
    · simp [normalizedDiagonalLift_apply, Matrix.conjTranspose_smul,
        RCLike.star_def, Complex.conj_ofReal, smul_smul]
    · intro b _ hba
      have hab : a ≠ b := fun h ↦ hba h.symm
      simp [normalizedDiagonalLift_apply, hab]
    · simp
  rw [Finset.sum_congr rfl (fun a _ ↦ hinner a), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hscale' :
      (x : ℂ) * ((Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹) = 1 := by
    simpa [mul_assoc] using hscale
  rw [hscale', one_smul]

/-- The normalized flattening after identity-ancilla attachment is the normalized
original flattening with a diagonal ancilla, in the explicit doubled-index shuffle.

Source: arXiv:1703.09188, lines 706--724, together with equation `eq:transfer-op`,
lines 336--340. -/
theorem normalizedFlattening_tensorPhysicalId (U : MPOTensor d D)
    (x : ℕ) (_hx : 0 < x) :
    (tensorPhysicalId U x).normalizedFlattening =
      MPSTensor.reindexPhysical (doubledPhysicalAncillaShuffle d x)
        (normalizedDiagonalLift U.normalizedFlattening x) := by
  funext k
  rcases finProdFinEquiv.surjective k with ⟨⟨ia, jb⟩, rfl⟩
  rcases finProdFinEquiv.surjective ia with ⟨⟨i, a⟩, rfl⟩
  rcases finProdFinEquiv.surjective jb with ⟨⟨j, b⟩, rfl⟩
  rw [show (tensorPhysicalId U x).normalizedFlattening
      (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))) =
        ((Real.sqrt (d * x) : ℂ)⁻¹) •
          tensorPhysicalId U x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) by
      simp [normalizedFlattening, MPOTensor.toMPSTensor]]
  rw [show MPSTensor.reindexPhysical (doubledPhysicalAncillaShuffle d x)
      (normalizedDiagonalLift U.normalizedFlattening x)
      (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))) =
        normalizedDiagonalLift U.normalizedFlattening x
          (finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (a, b))) by
      simp [MPSTensor.reindexPhysical]]
  ext β α
  simp only [Matrix.smul_apply]
  rw [tensorPhysicalId_apply, normalizedDiagonalLift_apply,
    Real.sqrt_mul (by positivity)]
  push_cast
  rw [mul_inv]
  by_cases hab : a = b
  · simp [hab, normalizedFlattening, MPOTensor.toMPSTensor, Matrix.smul_apply,
      mul_assoc, mul_comm]
  · simp [hab]

/-- Lift literal CPSV canonical-form-II data through a nonempty normalized diagonal ancilla.

The retained dimensions, weights, ambient coisometry, and fixed-point matrices are unchanged. Only
physical letters are enlarged, so this does not identify source cuts or compact-SVD factors.

Source: arXiv:1703.09188, lines 706--724; CFII is used as in lines 271--281. -/
noncomputable def normalizedDiagonalLiftCFIIData
    {A : MPSTensor (d * d) D} (data : MPSTensor.CPSVCanonicalFormIIData A)
    (x : ℕ) (hx : 0 < x) :
    MPSTensor.CPSVCanonicalFormIIData (normalizedDiagonalLift A x) where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := data.weights
  blocks := fun k ↦ normalizedDiagonalLift (data.blocks k) x
  blocks_normal := fun k ↦
    isNormalTensor_normalizedDiagonalLift (data.blocks_normal k) x hx
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro q
    rcases finProdFinEquiv.surjective q with ⟨⟨ij, ab⟩, rfl⟩
    rcases finProdFinEquiv.surjective ab with ⟨⟨a, b⟩, rfl⟩
    by_cases hab : a = b
    · subst b
      simp only [normalizedDiagonalLift_apply]
      rw [data.reconstruct ij]
      simp only [MPSTensor.toTensorFromBlocks]
      simp only [normalizedDiagonalLift_apply, ite_eq_left]
      rw [show (fun k ↦ data.weights k • ((Real.sqrt x : ℂ)⁻¹ • data.blocks k ij)) =
          ((Real.sqrt x : ℂ)⁻¹) •
            (fun k ↦ data.weights k • data.blocks k ij) by
        funext k
        simp [smul_smul, mul_comm]]
      rw [Matrix.blockDiagonal'_smul]
      simp [Matrix.submatrix_smul, Matrix.mul_smul, Matrix.smul_mul]
    · simp only [normalizedDiagonalLift_apply, ite_eq_right hab, MPSTensor.toTensorFromBlocks,
        smul_zero]
      rw [show (fun _ : Fin data.r ↦
          (0 : Matrix (Fin (data.dim _)) (Fin (data.dim _)) ℂ)) = 0 by rfl,
        Matrix.blockDiagonal'_zero]
      simp
  blocks_left_canonical := fun k ↦
    leftCanonical_normalizedDiagonalLift (data.blocks k) x hx (data.blocks_left_canonical k)
  blocks_fixed_point := by
    intro k
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ := data.blocks_fixed_point k
    exact ⟨Λ, hΛpos, hΛdiag, by
      rw [transferMap_normalizedDiagonalLift (data.blocks k) x hx]
      exact hΛfix⟩

/-- Full active support is unchanged by the normalized diagonal lift. -/
theorem hasFullActiveSupport_normalizedDiagonalLiftCFIIData
    {A : MPSTensor (d * d) D} (data : MPSTensor.CPSVCanonicalFormIIData A)
    (hfull : data.toCPSVCanonicalFormData.HasFullActiveSupport)
    (x : ℕ) (hx : 0 < x) :
    (normalizedDiagonalLiftCFIIData data x hx).toCPSVCanonicalFormData.HasFullActiveSupport := by
  change ∑ k : data.toCPSVCanonicalFormData.Active, data.dim k.1 = D
  exact hfull

/-- Full active support is preserved when canonical-form-II data are transported across a tensor
identity. -/
private theorem hasFullActiveSupport_castCFIIData
    {d D : ℕ} {A B : MPSTensor d D} (h : A = B)
    (data : MPSTensor.CPSVCanonicalFormIIData B)
    (hfull : data.toCPSVCanonicalFormData.HasFullActiveSupport) :
    (h.symm ▸ data).toCPSVCanonicalFormData.HasFullActiveSupport := by
  subst h
  exact hfull

/-- Construct canonical-form-II data for the normalized flattening after attaching a nonempty
physical identity ancilla.

The construction first uses the normalized diagonal lift and then the explicit doubled-physical
shuffle. It preserves virtual canonical data, but makes no claim that source cuts, ranks, or chosen
compact-SVD factors are unchanged.

Source: arXiv:1703.09188, lines 706--724; CFII is used as in lines 271--281. -/
noncomputable def tensorPhysicalIdCFIIData (U : MPOTensor d D)
    (data : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (x : ℕ) (hx : 0 < x) :
    MPSTensor.CPSVCanonicalFormIIData (tensorPhysicalId U x).normalizedFlattening :=
  (normalizedFlattening_tensorPhysicalId U x hx).symm ▸
    (normalizedDiagonalLiftCFIIData data x hx).reindexPhysical
      (doubledPhysicalAncillaShuffle d x)

/-- Full active support is preserved by physical identity-ancilla attachment.

The active weights and virtual block dimensions are unchanged by the construction.

Source: arXiv:1703.09188, lines 706--724. -/
theorem hasFullActiveSupport_tensorPhysicalIdCFIIData (U : MPOTensor d D)
    (data : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : data.toCPSVCanonicalFormData.HasFullActiveSupport)
    (x : ℕ) (hx : 0 < x) :
    (tensorPhysicalIdCFIIData U data x hx).toCPSVCanonicalFormData.HasFullActiveSupport := by
  let lifted := normalizedDiagonalLiftCFIIData data x hx
  have hlift : lifted.toCPSVCanonicalFormData.HasFullActiveSupport :=
    hasFullActiveSupport_normalizedDiagonalLiftCFIIData data hfull x hx
  let shuffled := lifted.reindexPhysical (doubledPhysicalAncillaShuffle d x)
  have hshuffle : shuffled.toCPSVCanonicalFormData.HasFullActiveSupport :=
    MPSTensor.CPSVCanonicalFormData.hasFullActiveSupport_reindexPhysical
      lifted.toCPSVCanonicalFormData hlift (doubledPhysicalAncillaShuffle d x)
  exact hasFullActiveSupport_castCFIIData
    (normalizedFlattening_tensorPhysicalId U x hx) shuffled hshuffle

/-- Identity-ancilla attachment leaves the transfer map of the normalized
flattening unchanged.

Source: arXiv:1703.09188, lines 706--724 and equation `eq:transfer-op`, lines 336--340. -/
theorem transferMap_normalizedFlattening_tensorPhysicalId (U : MPOTensor d D)
    (x : ℕ) (hx : 0 < x) :
    MPSTensor.transferMap (tensorPhysicalId U x).normalizedFlattening =
      MPSTensor.transferMap U.normalizedFlattening := by
  rw [normalizedFlattening_tensorPhysicalId U x hx,
    MPSTensor.transferMap_reindexPhysical_equiv,
    transferMap_normalizedDiagonalLift U.normalizedFlattening x hx]

end MPOTensor
