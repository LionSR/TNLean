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

## Main results

* `MPOTensor.mpo_tensorPhysicalId`: the generated MPO is the reindexed Kronecker
  product of the original MPO and the ancilla identity.
* `MPOTensor.IsMPU.tensorPhysicalId`: identity-ancilla attachment preserves the MPU
  property.
* `MPOTensor.tensorPhysicalIdCFIIData`: identity-ancilla attachment preserves chosen
  canonical-form-II data and full active support.
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
`((i, a), (j, b)) ↦ ((i, j), (a, b))`, with both pairs encoded by
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

def doubledPhysicalAncillaShuffle (d x : ℕ) :
    Fin ((d * x) * (d * x)) ≃ Fin ((d * d) * (x * x)) :=
  finProdFinEquiv.symm |>.trans <|
    (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans <|
      (doubledPhysicalAncillaMiddleShuffle d x).trans <|
        (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

/-- Lift a doubled-index MPS tensor by a normalized diagonal ancilla alphabet.
Only letters `(a, a)` are nonzero, and each is scaled by `1 / sqrt x`.

The physical alphabet is ordered as `((i, j), (a, b))`. -/
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
  have hsqrt : (Real.sqrt x : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hx)
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
    · simp [normalizedDiagonalLift_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.conjTranspose_smul, RCLike.star_def, map_inv₀, Complex.conj_ofReal,
        smul_smul, mul_comm]
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

/-- The normalized flattening after identity-ancilla attachment is the normalized
original flattening with a diagonal ancilla, in the explicit doubled-index shuffle.

Source: arXiv:1703.09188, lines 706--724, together with equation `eq:transfer-op`,
lines 336--340. -/
theorem normalizedFlattening_tensorPhysicalId (U : MPOTensor d D)
    (x : ℕ) (hx : 0 < x) :
    (tensorPhysicalId U x).normalizedFlattening =
      MPSTensor.reindexPhysical (doubledPhysicalAncillaShuffle d x)
        (normalizedDiagonalLift U.normalizedFlattening x) := by
  funext k
  rcases finProdFinEquiv.surjective k with ⟨⟨ia, jb⟩, rfl⟩
  rcases finProdFinEquiv.surjective ia with ⟨⟨i, a⟩, rfl⟩
  rcases finProdFinEquiv.surjective jb with ⟨⟨j, b⟩, rfl⟩
  simp only [normalizedFlattening, MPSTensor.reindexPhysical,
    doubledPhysicalAncillaShuffle, doubledPhysicalAncillaMiddleShuffle,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.symm_apply_apply,
    MPOTensor.toMPSTensor]
  simp only [Prod.map]
  simp only [finProdFinEquiv.symm_apply_apply]
  change ((Real.sqrt (d * x) : ℂ)⁻¹) •
      tensorPhysicalId U x
        (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))).divNat
        (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))).modNat =
    normalizedDiagonalLift U.normalizedFlattening x
      (finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (a, b)))
  have houter := finProdFinEquiv.symm_apply_apply
    (finProdFinEquiv (i, a), finProdFinEquiv (j, b))
  have hleft := congrArg Prod.fst houter
  have hright := congrArg Prod.snd houter
  change (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))).divNat =
      finProdFinEquiv (i, a) at hleft
  change (finProdFinEquiv (finProdFinEquiv (i, a), finProdFinEquiv (j, b))).modNat =
      finProdFinEquiv (j, b) at hright
  rw [hleft, hright]
  change ((Real.sqrt (d * x) : ℂ)⁻¹) •
      tensorPhysicalId U x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
    normalizedDiagonalLift U.normalizedFlattening x
      (finProdFinEquiv (finProdFinEquiv (i, j), finProdFinEquiv (a, b)))
  rw [tensorPhysicalId_apply, normalizedDiagonalLift_apply,
    Real.sqrt_mul (by positivity)]
  push_cast
  rw [mul_inv]
  by_cases hab : a = b <;> simp [hab, smul_smul, mul_comm]

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
