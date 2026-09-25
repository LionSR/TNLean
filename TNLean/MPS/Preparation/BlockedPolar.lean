/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Preparation.MatrixPolar

/-!
# Polar decomposition of a blocked matrix product state tensor

A tensor `B : MPSTensor n D` is read as the linear map `ℂ^{D²} → ℂ^n` whose matrix is
`(B^i)_{αβ}`, with rows indexed by the physical index `i` and columns by the pair `(α, β)` of
virtual indices. The polar decomposition `B = V P` of that map (`Matrix.polarIso`,
`Matrix.polarPos`) splits `B` into

* a tensor `P` with physical dimension `D²` and bond dimension `D`, whose physical legs carry
  the rows of the positive semidefinite factor, and
* a partial isometry `V : ℂ^{D²} → ℂ^n` acting on the physical leg,

so that `B^i = ∑ₖ V_{ik} P^k`. This file records the consequences used in the log-depth
preparation of matrix product states: the transfer operators of `B` and `P` coincide, and for
`M` blocks of `q` sites of a tensor `A` the periodic `qM`-site state of `A` equals `V^{⊗M}`
applied to the periodic `M`-site state of `P`.

## Main declarations

* `MPSTensor.physicalMatrix` — the tensor as a matrix `ℂ^{D²} → ℂ^n`.
* `MPSTensor.physicalApply` — a matrix acting on the physical leg of a tensor.
* `MPSTensor.transferMap_physicalApply_eq` — `E_{W·A} = E_A` whenever `Wᴴ W` fixes `A`.
* `MPSTensor.mpv_physicalApply` — the periodic state of `W·A` is `W^{⊗N}` applied to that of
  `A`.
* `MPSTensor.polarPosTensor`, `MPSTensor.polarIsoMatrix` — the two polar factors of a tensor.
* `MPSTensor.physicalApply_polarIsoMatrix_polarPosTensor` — `B = V P`.
* `MPSTensor.transferMap_polarPosTensor` — `E_B = E_P` (arXiv:2307.01696, eq. `eq:B_TM`,
  first equality).
* `MPSTensor.mpv_blockedConfigEquiv_eq_sum_polar` — `|φ_N⟩ = (⊗ᵢ Vᵢ) |φ_pos⟩` for `N = qM`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. `eq:B` (the blocked tensor), paragraph
  "Approximation through the fixed-point state" (the polar decomposition `B = V P` and
  eq. `eq:B_TM`), eq. `eq:key_approximation` (the first equality `B = V P` in tensor form),
  and Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors"
  (`B = V P` with `V†V = Π`, and `|φ_N⟩ = (⊗ᵢ Vᵢ) ∑ⱼ βⱼ |v_{pos,j}⟩`).
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {n m D : ℕ}

/-! ### A tensor as a map from the virtual pair space to the physical space -/

/-- The tensor `B` read as the matrix of the linear map `ℂ^{D²} → ℂ^n`, `(i, (α, β)) ↦ B^i_{αβ}`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": the blocked tensor
is interpreted "as a map from the `D²`-dimensional virtual space to the `d^q`-dimensional
physical space". -/
def physicalMatrix (A : MPSTensor n D) : Matrix (Fin n) (Fin D × Fin D) ℂ :=
  fun i p => A i p.1 p.2

/-- The tensor whose physical matrix is `R`. -/
def ofPhysicalMatrix (R : Matrix (Fin n) (Fin D × Fin D) ℂ) : MPSTensor n D :=
  fun i α β => R i (α, β)

@[simp] lemma ofPhysicalMatrix_physicalMatrix (A : MPSTensor n D) :
    ofPhysicalMatrix (physicalMatrix A) = A := rfl

@[simp] lemma physicalMatrix_ofPhysicalMatrix (R : Matrix (Fin n) (Fin D × Fin D) ℂ) :
    physicalMatrix (ofPhysicalMatrix R) = R := rfl

lemma physicalMatrix_injective : Function.Injective (physicalMatrix (n := n) (D := D)) :=
  fun A B h => by rw [← ofPhysicalMatrix_physicalMatrix A, h, ofPhysicalMatrix_physicalMatrix]

/-- An injective tensor (its matrices span the full matrix algebra) has an injective physical
matrix.

arXiv:2307.01696, footnote to "Approximation through the fixed-point state": injectivity of
`B` in the sense of Pérez-García et al. makes `B` an injective map `ℂ^{D²} → ℂ^{d^q}`. -/
theorem injective_physicalMatrix_mulVec_of_isInjective {A : MPSTensor n D}
    (hA : Kraus.IsInjective A) : Function.Injective (physicalMatrix A).mulVec := by
  rw [← LinearMap.coe_mulVecLin, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => ∑ p : Fin D × Fin D, Y p.1 p.2 * x p
      map_add' := fun Y Z => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c Y => by simp [mul_assoc, Finset.mul_sum] }
  have hf : f = 0 := by
    refine LinearMap.ext_on_range hA fun i => ?_
    have := congrFun hx i
    simpa [f, Matrix.mulVec, dotProduct, physicalMatrix] using this
  funext p
  have := LinearMap.congr_fun hf (Matrix.single p.1 p.2 1)
  simpa [f, Matrix.single_apply, Finset.sum_ite_eq', Prod.ext_iff, ite_and] using this

/-! ### Matrices acting on the physical leg -/

/-- The tensor `W · A` obtained by applying `W : ℂ^n → ℂ^m` to the physical leg of `A`:
`(W · A)^i = ∑ₖ W_{ik} A^k`.

arXiv:2307.01696, eq. `eq:key_approximation`: the isometry `V` acts on the physical leg of the
positive part `P`. -/
noncomputable def physicalApply (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D) :
    MPSTensor m D :=
  fun i => ∑ k, W i k • A k

lemma physicalMatrix_physicalApply (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D) :
    physicalMatrix (physicalApply W A) = W * physicalMatrix A := by
  ext i p
  simp [physicalMatrix, physicalApply, Matrix.mul_apply, Matrix.sum_apply]

/-- The transfer operator of `W · A` in terms of the Gram matrix `Wᴴ W`. -/
theorem transferMap_physicalApply_apply (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (physicalApply W A) X =
      ∑ l, (physicalApply (Wᴴ * W) A l) * X * (A l)ᴴ := by
  simp only [Kraus.transferMap_apply, physicalApply, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Finset.sum_mul, Finset.mul_sum, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.conjTranspose_apply, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- If `Wᴴ W` fixes the tensor `A` on its physical leg, then `W · A` and `A` have the same
transfer operator.

arXiv:2307.01696, eq. `eq:B_TM` (first equality) and Supplemental Material, "Proof of Lemma 1
and extension to non-normal tensors": `V†V = Π` and `Π P = P` give `E_{VP} = E_P`. -/
theorem transferMap_physicalApply_eq (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D)
    (hW : physicalApply (Wᴴ * W) A = A) :
    Kraus.transferMap (physicalApply W A) = Kraus.transferMap A := by
  ext1 X
  rw [transferMap_physicalApply_apply, hW, Kraus.transferMap_apply]

/-- Word evaluation of `W · A` along a word of length `N` expands as `W^{⊗N}` applied to the
word evaluations of `A`. -/
theorem evalWord_physicalApply_ofFn (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D) :
    ∀ {N : ℕ} (σ : Fin N → Fin m),
      Kraus.evalWord (physicalApply W A) (List.ofFn σ) =
        ∑ τ : Fin N → Fin n, (∏ j, W (σ j) (τ j)) • Kraus.evalWord A (List.ofFn τ)
  | 0, σ => by simp
  | N + 1, σ => by
    rw [List.ofFn_succ, Kraus.evalWord_cons, evalWord_physicalApply_ofFn W A,
      ← (Fin.consEquiv fun _ : Fin (N + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [physicalApply, Finset.sum_mul, Finset.mul_sum, Fin.consEquiv_apply,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, Kraus.evalWord_cons,
      smul_mul_smul, mul_smul]
    rfl

/-- The periodic state of `W · A` on `N` sites is `W^{⊗N}` applied to the periodic state of
`A`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `|φ_N⟩ = (⊗ᵢ Vᵢ) |φ_pos⟩`. -/
theorem mpv_physicalApply (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D) {N : ℕ}
    (σ : Fin N → Fin m) :
    mpv (physicalApply W A) σ = ∑ τ : Fin N → Fin n, (∏ j, W (σ j) (τ j)) * mpv A τ := by
  simp only [mpv, coeff, evalWord_physicalApply_ofFn, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]

/-! ### The polar factors of a tensor -/

/-- The identification of the `D²` virtual pair indices with `Fin (D * D)`, used as the
physical alphabet of the positive part. -/
def virtualPairEquiv (D : ℕ) : Fin (D * D) ≃ Fin D × Fin D :=
  finProdFinEquiv.symm

/-- The positive factor `P = (Bᴴ B)^{1/2}` of the polar decomposition of a tensor, as a
`D² × D²` matrix.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors": `P : ℂ^{D²} → ℂ^{D²}`. -/
noncomputable def polarPosMatrix (B : MPSTensor n D) : Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  (Matrix.polarPos (physicalMatrix B)).submatrix (virtualPairEquiv D) (virtualPairEquiv D)

/-- The positive factor read as a tensor with physical dimension `D²` and bond dimension `D`:
its `k`-th matrix is the `k`-th row of `P`.

arXiv:2307.01696, eq. `eq:key_approximation` and eq. `eq:phi_pos`: the tensor `P` generating
`|φ_pos⟩`. -/
noncomputable def polarPosTensor (B : MPSTensor n D) : MPSTensor (D * D) D :=
  ofPhysicalMatrix ((Matrix.polarPos (physicalMatrix B)).submatrix (virtualPairEquiv D) id)

/-- The partial isometry `V : ℂ^{D²} → ℂ^n` of the polar decomposition of a tensor.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors". -/
noncomputable def polarIsoMatrix (B : MPSTensor n D) : Matrix (Fin n) (Fin (D * D)) ℂ :=
  (Matrix.polarIso (physicalMatrix B)).submatrix id (virtualPairEquiv D)

/-- The projector `Π` onto the range of the positive factor of a tensor.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors". -/
noncomputable def polarSupportMatrix (B : MPSTensor n D) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  (Matrix.polarSupport (physicalMatrix B)).submatrix (virtualPairEquiv D) (virtualPairEquiv D)

lemma physicalMatrix_polarPosTensor (B : MPSTensor n D) :
    physicalMatrix (polarPosTensor B) =
      (Matrix.polarPos (physicalMatrix B)).submatrix (virtualPairEquiv D) id := rfl

/-- The positive factor is positive semidefinite.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `P` is positive semidefinite. -/
theorem posSemidef_polarPosMatrix (B : MPSTensor n D) : (polarPosMatrix B).PosSemidef :=
  (Matrix.posSemidef_polarPos _).submatrix _

/-- **Polar decomposition of a tensor**: `B^i = ∑ₖ V_{ik} P^k`, that is, `B = V P`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and
eq. `eq:key_approximation` (first equality); Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors". -/
theorem physicalApply_polarIsoMatrix_polarPosTensor (B : MPSTensor n D) :
    physicalApply (polarIsoMatrix B) (polarPosTensor B) = B := by
  apply physicalMatrix_injective
  rw [physicalMatrix_physicalApply, physicalMatrix_polarPosTensor, polarIsoMatrix,
    Matrix.submatrix_mul_equiv, Matrix.polarIso_mul_polarPos]
  rfl

/-- **Polar decomposition of a tensor**, partial-isometry relation: `Vᴴ V = Π`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors": `V†V = Π`. -/
theorem conjTranspose_polarIsoMatrix_mul (B : MPSTensor n D) :
    (polarIsoMatrix B)ᴴ * polarIsoMatrix B = polarSupportMatrix B := by
  rw [polarIsoMatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_polarIso_mul_polarIso, polarSupportMatrix]

/-- The support projector is Hermitian. -/
theorem isHermitian_polarSupportMatrix (B : MPSTensor n D) :
    (polarSupportMatrix B).IsHermitian :=
  (Matrix.isHermitian_polarSupport _).submatrix _

/-- The support projector is idempotent. -/
theorem polarSupportMatrix_mul_self (B : MPSTensor n D) :
    polarSupportMatrix B * polarSupportMatrix B = polarSupportMatrix B := by
  rw [polarSupportMatrix, Matrix.submatrix_mul_equiv, Matrix.polarSupport_mul_polarSupport]

/-- The support projector fixes the positive-part tensor on its physical leg: `Π P = P`. -/
theorem physicalApply_polarSupportMatrix (B : MPSTensor n D) :
    physicalApply (polarSupportMatrix B) (polarPosTensor B) = polarPosTensor B := by
  apply physicalMatrix_injective
  rw [physicalMatrix_physicalApply, physicalMatrix_polarPosTensor, polarSupportMatrix,
    Matrix.submatrix_mul_equiv, Matrix.polarSupport_mul_polarPos]

/-- **Transfer identity** `E_B = E_P`.

arXiv:2307.01696, eq. `eq:B_TM`, first equality (stated there for injective `B`; it holds for
every tensor since `V†V = Π` and `Π P = P`, as in the Supplemental Material, "Proof of
Lemma 1 and extension to non-normal tensors"). -/
theorem transferMap_polarPosTensor (B : MPSTensor n D) :
    Kraus.transferMap (polarPosTensor B) = Kraus.transferMap B := by
  conv_rhs => rw [← physicalApply_polarIsoMatrix_polarPosTensor B]
  rw [transferMap_physicalApply_eq]
  rw [conjTranspose_polarIsoMatrix_mul, physicalApply_polarSupportMatrix]

/-- For an injective tensor, `V` is an isometry, `Vᴴ V = 1`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": for injective `B`,
`V†V = 1_{D²}`. -/
theorem isIsometry_polarIsoMatrix_of_isInjective {B : MPSTensor n D}
    (hB : Kraus.IsInjective B) : (polarIsoMatrix B)ᴴ * polarIsoMatrix B = 1 := by
  rw [conjTranspose_polarIsoMatrix_mul, polarSupportMatrix,
    Matrix.polarSupport_eq_one_of_injective _ (injective_physicalMatrix_mulVec_of_isInjective hB),
    Matrix.submatrix_one_equiv]

/-- For an injective tensor, the positive factor is positive definite.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": for injective `B`,
`P > 0`. -/
theorem posDef_polarPosMatrix_of_isInjective {B : MPSTensor n D}
    (hB : Kraus.IsInjective B) : (polarPosMatrix B).PosDef :=
  (Matrix.posDef_polarPos_of_injective _
    (injective_physicalMatrix_mulVec_of_isInjective hB)).submatrix _

/-! ### Blocked tensors -/

variable {d : ℕ}

/-- **Transfer identity for the blocked tensor**: `E_P = E_B = E_A^q`.

arXiv:2307.01696, text after eq. `eq:B` (`E_B = E_A^q`) and eq. `eq:B_TM` (first equality). -/
theorem transferMap_polarPosTensor_blockTensor (A : MPSTensor d D) (q : ℕ) :
    Kraus.transferMap (polarPosTensor (blockTensor A q)) = Kraus.transferMap A ^ q := by
  rw [transferMap_polarPosTensor, transferMap_blockTensor]

/-- **Polar form of the blocked periodic state**: for `N = qM` sites, the periodic state of
`A` equals `V^{⊗M}` applied to the periodic `M`-site state of the positive-part tensor `P` of
the `q`-site blocked tensor.

arXiv:2307.01696, eq. `eq:B`, eq. `eq:key_approximation` (first equality), and Supplemental
Material, "Proof of Lemma 1 and extension to non-normal tensors":
`|φ_N⟩ = (⊗_{i=1}^{N/q} Vᵢ) |φ_pos⟩` (before normalization). -/
theorem mpv_blockedConfigEquiv_eq_sum_polar (A : MPSTensor d D) (q M : ℕ)
    (σ : Fin M → Fin (blockPhysDim d q)) :
    mpv A (blockedConfigEquiv d M q σ) =
      ∑ τ : Fin M → Fin (D * D),
        (∏ j, polarIsoMatrix (blockTensor A q) (σ j) (τ j)) *
          mpv (polarPosTensor (blockTensor A q)) τ := by
  rw [← mpv_physicalApply, physicalApply_polarIsoMatrix_polarPosTensor]
  simp only [mpv, coeff, ofFn_blockedConfigEquiv, evalWord_blockTensor]

end MPSTensor
