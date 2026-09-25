/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.PolarUniqueness

/-!
# Tree factorization of the isometry of a blocked tensor

For a tensor `A`, put `T₀ = A` and, for `j ≥ 1`, let `B⁽ʲ⁾ = V⁽ʲ⁾ Pⱼ` be the polar
decomposition of the two-site blocked tensor of `Tⱼ₋₁` and let `Tⱼ` be the tensor of `Pⱼ`
(`MPSTensor.polarPosTensor`).  For `q = 2^k` sites this file proves the identity of
arXiv:2307.01696, eq. (16),

  `B_q = (V⁽¹⁾)^{⊗2^{k-1}} (V⁽²⁾)^{⊗2^{k-2}} ⋯ V⁽ᵏ⁾ P_k`,

where `V⁽¹⁾ : ℂ^{D²} → (ℂ^d)^{⊗2}` and `V⁽ʲ⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` for `j ≥ 2`.  The
Kronecker powers act on the regrouping of the `2^k` sites of the block into `2^{k-1}`
neighbouring pairs, then pairs of pairs, and so on.

The product of the layers is a partial isometry whose initial projector is the support
projector of `P_k`.  The key step is that the range of the two-site blocked tensor of `Tⱼ₋₁`
lies in `ran Pⱼ₋₁ ⊗ ran Pⱼ₋₁`, so each layer acts inside the initial space of the next.  By
uniqueness of the polar decomposition (`Matrix.polarIso_eq_of_eq_mul`), the product of the layers
is the isometry `V` of `B_q` and `P_k` is its positive part.

The exponent is indexed from zero: `treeIsoMatrix k A` is the product of the `k + 1` layers for
the block of `2^{k+1}` sites.

## Main declarations

* `MPSTensor.blockKronRect` — the Kronecker power `W^{⊗L}` of a rectangular physical map,
  acting on length-`L` blocks.
* `MPSTensor.blockTensor_rotatePhysical` — blocking commutes with physical maps:
  `(W · C)` blocked `L` times is `W^{⊗L}` applied to `C` blocked `L` times.
* `MPSTensor.treeTensor`, `MPSTensor.treePosTensor`, `MPSTensor.treeIsoMatrix` — the chain
  `Tⱼ`, the last positive part `P_{k+1}`, and the product of the layers.
* `MPSTensor.blockTensor_eq_rotatePhysical_treeIsoMatrix`,
  `MPSTensor.physicalMatrix_blockTensor_eq_treeIsoMatrix_mul` — the tree factorization.
* `MPSTensor.conjTranspose_treeIsoMatrix_mul_self` — the product of the layers is a partial
  isometry with initial projector the support projector of `P_{k+1}`.
* `MPSTensor.polarIsoMatrix_blockTensor_eq_treeIsoMatrix`,
  `MPSTensor.polarPosTensor_blockTensor_eq_treePosTensor` — the layers compose to the polar
  factors of the blocked tensor.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and the paragraph containing it.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {n m p D : ℕ}

/-! ### Kronecker powers of rectangular physical maps -/

/-- The Kronecker power `W^{⊗L}` of a rectangular matrix `W : ℂⁿ → ℂᵐ` acting on length-`L`
blocks: `(W^{⊗L})_{IJ} = ∏ₜ W_{I_t J_t}`.  For square `W` this is `MPSTensor.blockKron`.

arXiv:2307.01696, eq. (16): the layers `(V⁽ʲ⁾)^{⊗2^{k-j}}`. -/
noncomputable def blockKronRect (L : ℕ) (W : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin (blockPhysDim m L)) (Fin (blockPhysDim n L)) ℂ :=
  fun I J => ∏ t : Fin L, W (decodeBlock m L I t) (decodeBlock n L J t)

/-- For a square matrix, `blockKronRect` is `blockKron`. -/
lemma blockKronRect_eq_blockKron (L : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) :
    blockKronRect L P = blockKron L P := rfl

/-- The Kronecker power is multiplicative: `W^{⊗L} W'^{⊗L} = (W W')^{⊗L}`. -/
lemma blockKronRect_mul (L : ℕ) (W : Matrix (Fin m) (Fin n) ℂ) (W' : Matrix (Fin n) (Fin p) ℂ) :
    blockKronRect L W * blockKronRect L W' = blockKronRect L (W * W') := by
  classical
  ext I J
  simp only [blockKronRect, Matrix.mul_apply]
  rw [← Equiv.sum_comp (decodeBlockEquiv n L).symm
    (fun K => (∏ t : Fin L, W (decodeBlock m L I t) (decodeBlock n L K t)) *
      ∏ t : Fin L, W' (decodeBlock n L K t) (decodeBlock p L J t))]
  simp only [decodeBlock_decodeBlockEquiv_symm]
  rw [Finset.prod_univ_sum (t := fun _ : Fin L => (Finset.univ : Finset (Fin n)))
    (f := fun (t : Fin L) (a : Fin n) =>
      W (decodeBlock m L I t) a * W' a (decodeBlock p L J t)),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- The Kronecker power commutes with the conjugate transpose. -/
lemma blockKronRect_conjTranspose (L : ℕ) (W : Matrix (Fin m) (Fin n) ℂ) :
    (blockKronRect L W)ᴴ = blockKronRect L Wᴴ := by
  ext I J
  simp only [Matrix.conjTranspose_apply, blockKronRect, star_prod]

/-- **Blocking commutes with physical maps**: blocking `W · C` over `L` sites gives
`W^{⊗L}` applied to `C` blocked over `L` sites.

arXiv:2307.01696, eq. (16): the layer `(V⁽ʲ⁾)^{⊗2^{k-j}}` acts sitewise on the regrouped
block. -/
theorem blockTensor_rotatePhysical (W : Matrix (Fin m) (Fin n) ℂ) (C : MPSTensor n D)
    (L : ℕ) :
    blockTensor (rotatePhysical W C) L =
      rotatePhysical (blockKronRect L W) (blockTensor C L) := by
  classical
  funext I
  change Kraus.evalWord (rotatePhysical W C) (List.ofFn (decodeBlock m L I)) = _
  rw [evalWord_rotatePhysical_ofFn, rotatePhysical_apply]
  exact (Fintype.sum_equiv (decodeBlockEquiv n L) _ _ fun J => rfl).symm

/-! ### Regrouping a block of `2^{k+2}` sites into pairs -/

/-- The regrouping of a block of `2^{k+2}` sites into `2^{k+1}` neighbouring pairs. -/
noncomputable def pairRegroupEquiv (n k : ℕ) :
    Fin (blockPhysDim n (2 ^ (k + 2))) ≃ Fin (blockPhysDim (blockPhysDim n 2) (2 ^ (k + 1))) :=
  (finCongr (congrArg (blockPhysDim n) (pow_succ' 2 (k + 1)))).trans
    (directIteratedBlockEquiv n 2 (2 ^ (k + 1)))

/-- Rewriting the block length does not change the blocked tensor. -/
private lemma blockTensor_finCongr (A : MPSTensor n D) {L₁ L₂ : ℕ} (h : L₁ = L₂)
    (i : Fin (blockPhysDim n L₁)) :
    blockTensor A L₂ (finCongr (congrArg (blockPhysDim n) h) i) = blockTensor A L₁ i := by
  subst h
  rfl

/-- Blocking `2^{k+2}` sites is blocking `2^{k+1}` pairs of the two-site blocked tensor. -/
theorem blockTensor_pairRegroupEquiv (A : MPSTensor n D) (k : ℕ)
    (i : Fin (blockPhysDim n (2 ^ (k + 2)))) :
    blockTensor (blockTensor A 2) (2 ^ (k + 1)) (pairRegroupEquiv n k i) =
      blockTensor A (2 ^ (k + 2)) i := by
  rw [blockTensor_blockTensor_apply]
  simp only [pairRegroupEquiv, Equiv.trans_apply, directIteratedBlockEquiv_apply,
    iteratedBlockIndex_directToIteratedBlockIndex]
  exact blockTensor_finCongr A _ i

/-! ### The tree of polar decompositions -/

/-- The chain `Tⱼ` of the tree factorization: `T₀ = A`, and `Tⱼ₊₁` is the positive-part tensor
of the two-site blocked tensor of `Tⱼ`.  The physical dimension changes from `n` to `D²` after
the first step, so the chain is valued in tensors of any physical dimension.

arXiv:2307.01696, eq. (16): the tensors whose two-site blocks are decomposed in the successive
layers. -/
noncomputable def treeTensor : ℕ → {n : ℕ} → MPSTensor n D → Σ n' : ℕ, MPSTensor n' D
  | 0, _, A => ⟨_, A⟩
  | k + 1, _, A => treeTensor k (polarPosTensor (blockTensor A 2))

/-- The positive part `P_{k+1}` of the last layer of the tree for a block of `2^{k+1}` sites,
read as a tensor: the positive-part tensor of the two-site blocked tensor of `T_k`.

arXiv:2307.01696, eq. (16): the factor `P_k` (indexed there from one). -/
noncomputable def treePosTensor (k : ℕ) (A : MPSTensor n D) : MPSTensor (D * D) D :=
  polarPosTensor (blockTensor (treeTensor k A).2 2)

/-- The support projector of `P_{k+1}`, the initial projector of the product of the layers. -/
noncomputable def treeSupportMatrix (k : ℕ) (A : MPSTensor n D) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  polarSupportMatrix (blockTensor (treeTensor k A).2 2)

/-- The product of the `k + 1` layers of the tree, a map `ℂ^{D²} → (ℂⁿ)^{⊗2^{k+1}}`:
`V⁽¹⁾` for `k = 0`, and `(V⁽¹⁾)^{⊗2^{k+1}}` composed with the tree of `T₁`, regrouped along
neighbouring pairs, for `k + 1`.  Unfolded, this is
`(V⁽¹⁾)^{⊗2^k} (V⁽²⁾)^{⊗2^{k-1}} ⋯ V⁽ᵏ⁺¹⁾`.

arXiv:2307.01696, eq. (16). -/
noncomputable def treeIsoMatrix :
    (k : ℕ) → {n : ℕ} → MPSTensor n D → Matrix (Fin (blockPhysDim n (2 ^ (k + 1)))) (Fin (D * D)) ℂ
  | 0, _, A => polarIsoMatrix (blockTensor A 2)
  | k + 1, n, A =>
      (blockKronRect (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
        treeIsoMatrix k (polarPosTensor (blockTensor A 2))).submatrix (pairRegroupEquiv n k) id

/-- The first layer of the tree for a block of `2^{k+2}` sites is `(V⁽¹⁾)^{⊗2^{k+1}}`, followed
by the tree of `T₁`. -/
lemma treeIsoMatrix_succ (k : ℕ) (A : MPSTensor n D) :
    treeIsoMatrix (k + 1) A =
      (blockKronRect (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
        treeIsoMatrix k (polarPosTensor (blockTensor A 2))).submatrix (pairRegroupEquiv n k) id :=
  rfl

lemma treePosTensor_succ (k : ℕ) (A : MPSTensor n D) :
    treePosTensor (k + 1) A = treePosTensor k (polarPosTensor (blockTensor A 2)) := rfl

lemma treeSupportMatrix_succ (k : ℕ) (A : MPSTensor n D) :
    treeSupportMatrix (k + 1) A = treeSupportMatrix k (polarPosTensor (blockTensor A 2)) := rfl

/-! ### The factorization -/

/-- **Tree factorization**, tensor form: the tensor `A` blocked over `2^{k+1}` sites is the
product of the `k + 1` layers applied to the physical leg of `P_{k+1}`.

arXiv:2307.01696, eq. (16). -/
theorem blockTensor_eq_rotatePhysical_treeIsoMatrix (k : ℕ) (A : MPSTensor n D) :
    blockTensor A (2 ^ (k + 1)) = rotatePhysical (treeIsoMatrix k A) (treePosTensor k A) := by
  induction k generalizing n with
  | zero => exact (rotatePhysical_polarIsoMatrix_polarPosTensor (blockTensor A 2)).symm
  | succ k ih =>
      have h1 : blockTensor (blockTensor A 2) (2 ^ (k + 1)) =
          rotatePhysical (blockKronRect (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
              treeIsoMatrix k (polarPosTensor (blockTensor A 2)))
            (treePosTensor k (polarPosTensor (blockTensor A 2))) := by
        conv_lhs => rw [← rotatePhysical_polarIsoMatrix_polarPosTensor (blockTensor A 2)]
        rw [blockTensor_rotatePhysical, ih, rotatePhysical_rotatePhysical]
      funext i
      rw [← blockTensor_pairRegroupEquiv, h1]
      rfl

/-- **Tree factorization**, matrix form: `B_{2^{k+1}} = (V⁽¹⁾)^{⊗2^k} ⋯ V⁽ᵏ⁺¹⁾ P_{k+1}` as maps
`ℂ^{D²} → (ℂⁿ)^{⊗2^{k+1}}`.

arXiv:2307.01696, eq. (16). -/
theorem physicalMatrix_blockTensor_eq_treeIsoMatrix_mul (k : ℕ) (A : MPSTensor n D) :
    physicalMatrix (blockTensor A (2 ^ (k + 1))) =
      treeIsoMatrix k A * physicalMatrix (treePosTensor k A) := by
  rw [blockTensor_eq_rotatePhysical_treeIsoMatrix, physicalMatrix_rotatePhysical]

/-! ### The layers are partial isometries -/

/-- Each Kronecker-power layer is a partial isometry: `((V⁽ʲ⁾)^{⊗L})ᴴ (V⁽ʲ⁾)^{⊗L} = Π^{⊗L}`.

arXiv:2307.01696, eq. (16), with the Supplemental Material, "Proof of Lemma 1 and extension to
non-normal tensors" (`V†V = Π`). -/
theorem conjTranspose_blockKronRect_polarIsoMatrix_mul_self (L : ℕ) (B : MPSTensor n D) :
    (blockKronRect L (polarIsoMatrix B))ᴴ * blockKronRect L (polarIsoMatrix B) =
      blockKronRect L (polarSupportMatrix B) := by
  rw [blockKronRect_conjTranspose, blockKronRect_mul,
    conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]

/-- **Range containment**: the tensor `T` of a positive part `P`, blocked over `L` sites, has
its range inside `(ran P)^{⊗L}`, that is, `Π^{⊗L}` fixes its physical matrix.  For `L = 2` this
is the containment `ran B⁽ʲ⁺¹⁾ ⊆ ran Pⱼ ⊗ ran Pⱼ` used in the tree.

arXiv:2307.01696, eq. (16): each layer is applied inside the initial space of the next. -/
theorem blockKronRect_polarSupportMatrix_mul_physicalMatrix_blockTensor (L : ℕ)
    (B : MPSTensor n D) :
    blockKronRect L (polarSupportMatrix B) *
        physicalMatrix (blockTensor (polarPosTensor B) L) =
      physicalMatrix (blockTensor (polarPosTensor B) L) := by
  rw [← physicalMatrix_rotatePhysical, ← blockTensor_rotatePhysical,
    rotatePhysical_polarSupportMatrix]

/-- A matrix annihilating the physical matrix of the positive-part tensor annihilates the
support projector. -/
private lemma mul_polarSupportMatrix_eq_zero {r : ℕ} {Y : Matrix (Fin r) (Fin (D * D)) ℂ}
    (B : MPSTensor n D) (hY : Y * physicalMatrix (polarPosTensor B) = 0) :
    Y * polarSupportMatrix B = 0 := by
  set e := virtualPairEquiv D
  have hY' : Y.submatrix id e.symm * Matrix.polarPos (physicalMatrix B) = 0 := by
    rw [← hY, physicalMatrix_polarPosTensor]
    conv_rhs => rw [show Y = (Y.submatrix id e.symm).submatrix id e by
      simp [Matrix.submatrix_submatrix]]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h := Matrix.mul_eq_zero_of_mul_eq_zero_of_range_le hY'
    (Matrix.range_polarSupport (physicalMatrix B)).le
  rw [polarSupportMatrix]
  conv_lhs => rw [show Y = (Y.submatrix id e.symm).submatrix id e by
    simp [Matrix.submatrix_submatrix]]
  rw [Matrix.submatrix_mul_equiv, h, Matrix.submatrix_zero, Matrix.zero_apply] <;> rfl

/-- **The product of the layers is a partial isometry** whose initial projector is the support
projector of `P_{k+1}`.

arXiv:2307.01696, text after eq. (16): the product of the layers "is a partial isometry with
initial space the range of `P_k`". -/
theorem conjTranspose_treeIsoMatrix_mul_self (k : ℕ) (A : MPSTensor n D) :
    (treeIsoMatrix k A)ᴴ * treeIsoMatrix k A = treeSupportMatrix k A := by
  induction k generalizing n with
  | zero => exact conjTranspose_polarIsoMatrix_mul_polarIsoMatrix (blockTensor A 2)
  | succ k ih =>
      set B := blockTensor A 2
      set T := polarPosTensor B
      set W := treeIsoMatrix k T
      set K := blockKronRect (2 ^ (k + 1)) (polarIsoMatrix B)
      set S := blockKronRect (2 ^ (k + 1)) (polarSupportMatrix B)
      have hWW : Wᴴ * W = treeSupportMatrix k T := ih T
      have hWE : W * treeSupportMatrix k T = W :=
        Matrix.mul_eq_self_of_conjTranspose_mul_self_eq hWW
          (isHermitian_polarSupportMatrix _) (polarSupportMatrix_mul_self _)
      have hX : (S * W - W) * physicalMatrix (treePosTensor k T) = 0 := by
        rw [Matrix.sub_mul, Matrix.mul_assoc, ← physicalMatrix_blockTensor_eq_treeIsoMatrix_mul,
          blockKronRect_polarSupportMatrix_mul_physicalMatrix_blockTensor, sub_self]
      have hXE := mul_polarSupportMatrix_eq_zero _ hX
      have hSW : S * W = W := by
        change (S * W - W) * treeSupportMatrix k T = 0 at hXE
        rw [Matrix.sub_mul, Matrix.mul_assoc, hWE, sub_eq_zero] at hXE
        exact hXE
      rw [treeIsoMatrix_succ, treeSupportMatrix_succ, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ, conjTranspose_blockKronRect_polarIsoMatrix_mul_self,
        hSW, hWW]

/-! ### Identification with the polar decomposition of the blocked tensor -/

/-- The product of the layers, with its columns indexed by virtual pairs. -/
private lemma treeFactorization_uniqueness_data (k : ℕ) (A : MPSTensor n D) :
    let B := blockTensor (treeTensor k A).2 2
    let W := (treeIsoMatrix k A).submatrix id (virtualPairEquiv D).symm
    physicalMatrix (blockTensor A (2 ^ (k + 1))) = W * Matrix.polarPos (physicalMatrix B) ∧
      Wᴴ * W = Matrix.polarSupport (physicalMatrix B) := by
  intro B W
  set e := virtualPairEquiv D
  constructor
  · rw [physicalMatrix_blockTensor_eq_treeIsoMatrix_mul, treePosTensor,
      physicalMatrix_polarPosTensor]
    conv_lhs => rw [show treeIsoMatrix k A = W.submatrix id e by
      simp [W, Matrix.submatrix_submatrix]]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  · have h := conjTranspose_treeIsoMatrix_mul_self k A
    rw [treeSupportMatrix, polarSupportMatrix] at h
    simp only [W, Matrix.conjTranspose_submatrix]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, h, Matrix.submatrix_submatrix]
    simp

/-- **Tree factorization, uniqueness**: the product of the `k + 1` layers is the isometry `V` of
the polar decomposition of `A` blocked over `2^{k+1}` sites.

arXiv:2307.01696, text after eq. (16): the product of the layers is a partial isometry, "so by
uniqueness of the polar decomposition it equals `V`". -/
theorem polarIsoMatrix_blockTensor_eq_treeIsoMatrix (k : ℕ) (A : MPSTensor n D) :
    polarIsoMatrix (blockTensor A (2 ^ (k + 1))) = treeIsoMatrix k A := by
  obtain ⟨hM, hW⟩ := treeFactorization_uniqueness_data k A
  rw [polarIsoMatrix, Matrix.polarIso_eq_of_eq_mul hM (Matrix.posSemidef_polarPos _) hW
    (Matrix.isHermitian_polarSupport _) (Matrix.polarSupport_mul_polarSupport _)
    (Matrix.range_polarSupport _)]
  simp [Matrix.submatrix_submatrix]

/-- **Tree factorization, uniqueness**: the positive part of `A` blocked over `2^{k+1}` sites is
the positive part `P_{k+1}` of the last layer of the tree.

arXiv:2307.01696, text after eq. (16): `P_k = P`. -/
theorem polarPosTensor_blockTensor_eq_treePosTensor (k : ℕ) (A : MPSTensor n D) :
    polarPosTensor (blockTensor A (2 ^ (k + 1))) = treePosTensor k A := by
  obtain ⟨hM, hW⟩ := treeFactorization_uniqueness_data k A
  rw [polarPosTensor, Matrix.polarPos_eq_of_eq_mul hM (Matrix.posSemidef_polarPos _) hW
    (Matrix.isHermitian_polarSupport _) (Matrix.polarSupport_mul_polarSupport _)
    (Matrix.range_polarSupport _)]
  rfl

end MPSTensor
