/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure
import TNLean.MPS.Preparation.BlockedPolar

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

The key step is that the range of the two-site blocked tensor of `Tⱼ₋₁` lies in
`ran Pⱼ₋₁ ⊗ ran Pⱼ₋₁`, so each layer `K` acts inside its initial space: `Kᴴ K` fixes the tensor
it is applied to.  Then `K M` has the positive part and the support projector of `M`, and its
partial isometry is `K` times that of `M` (`MPSTensor.polarIsoMatrix_rotatePhysical`).  By
induction on the depth, the product of the layers is the isometry `V` of `B_q`, `P_k` is its
positive part, and the product of the layers is a partial isometry whose initial projector is
the support projector of `P_k`.

The exponent is indexed from zero: `treeIsoMatrix k A` is the product of the `k + 1` layers for
the block of `2^{k+1}` sites.

## Main declarations

* `MPSTensor.blockKron` (from `TNLean.MPS.Core.Blocking`) — the Kronecker power `W^{⊗L}` of a
  rectangular physical map, acting on length-`L` blocks.
* `MPSTensor.blockTensor_rotatePhysical` (from `TNLean.MPS.Core.Blocking`) — blocking commutes
  with physical maps: `(W · C)` blocked `L` times is `W^{⊗L}` applied to `C` blocked `L` times.
* `MPSTensor.pairPosTensor`, `MPSTensor.treeLayers` — positive-part iteration and its layers.
* `MPSTensor.treeTensor`, `MPSTensor.treePosTensor`, `MPSTensor.treeIsoMatrix` — the chain
  `Tⱼ`, the last positive part `P_{k+1}`, and the product of the layers.
* `MPSTensor.blockTensor_eq_rotatePhysical_treeIsoMatrix`,
  `MPSTensor.physicalMatrix_blockTensor_eq_treeIsoMatrix_mul` — the tree factorization.
* `MPSTensor.conjTranspose_treeIsoMatrix_mul_self` — the product of the layers is a partial
  isometry with initial projector the support projector of `P_{k+1}`.
* `MPSTensor.polarIsoMatrix_blockTensor_eq_treeIsoMatrix`,
  `MPSTensor.polarPosTensor_blockTensor_eq_treePosTensor`,
  `MPSTensor.polarSupportMatrix_blockTensor_eq_treeSupportMatrix` — the layers compose to the
  polar factors of the blocked tensor.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and the paragraph containing it.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {n m D : ℕ}

/-- The positive-part tensor `T₁` of the two-site blocked tensor of `A`, the tensor whose
two-site blocks are decomposed in the next layer of eq. (16) of arXiv:2307.01696. -/
noncomputable def pairPosTensor (A : MPSTensor n D) : MPSTensor (D * D) D :=
  polarPosTensor (blockTensor A 2)

/-- The coarse layers `V⁽²⁾, …, V⁽ᵏ⁺¹⁾` of the tree-RG circuit for a block of `2^{k+1}` sites:
`V⁽ʲ⁺²⁾` is the isometric factor of the two-site blocked tensor of `T_{j+1}`.

arXiv:2307.01696, eq. (16). -/
noncomputable def treeLayers (k : ℕ) (A : MPSTensor n D) :
    Fin k → Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ :=
  fun j => polarIsoMatrix
    (blockTensor ((pairPosTensor : MPSTensor (D * D) D → MPSTensor (D * D) D)^[j]
      (pairPosTensor A)) 2)

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
  exact blockTensor_finCongr A (pow_succ' 2 (k + 1)) i

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
      (blockKron (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
        treeIsoMatrix k (polarPosTensor (blockTensor A 2))).submatrix (pairRegroupEquiv n k) id

/-- The first layer of the tree for a block of `2^{k+2}` sites is `(V⁽¹⁾)^{⊗2^{k+1}}`, followed
by the tree of `T₁`. -/
lemma treeIsoMatrix_succ (k : ℕ) (A : MPSTensor n D) :
    treeIsoMatrix (k + 1) A =
      (blockKron (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
        treeIsoMatrix k (polarPosTensor (blockTensor A 2))).submatrix (pairRegroupEquiv n k) id :=
  rfl

lemma treePosTensor_succ (k : ℕ) (A : MPSTensor n D) :
    treePosTensor (k + 1) A = treePosTensor k (polarPosTensor (blockTensor A 2)) := rfl

lemma treeSupportMatrix_succ (k : ℕ) (A : MPSTensor n D) :
    treeSupportMatrix (k + 1) A = treeSupportMatrix k (polarPosTensor (blockTensor A 2)) := rfl

/-! ### The layers are partial isometries -/

/-- Each Kronecker-power layer is a partial isometry: `((V⁽ʲ⁾)^{⊗L})ᴴ (V⁽ʲ⁾)^{⊗L} = Π^{⊗L}`.

arXiv:2307.01696, eq. (16), with the Supplemental Material, "Proof of Lemma 1 and extension to
non-normal tensors" (`V†V = Π`). -/
theorem conjTranspose_blockKron_polarIsoMatrix_mul_self (L : ℕ) (B : MPSTensor n D) :
    (blockKron L (polarIsoMatrix B))ᴴ * blockKron L (polarIsoMatrix B) =
      blockKron L (polarSupportMatrix B) := by
  rw [blockKron_conjTranspose, ← blockKron_mul,
    conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]

/-- **Range containment**: the tensor `T` of a positive part `P`, blocked over `L` sites, has
its range inside `(ran P)^{⊗L}`, that is, `Π^{⊗L}` fixes its physical matrix.  For `L = 2` this
is the containment `ran B⁽ʲ⁺¹⁾ ⊆ ran Pⱼ ⊗ ran Pⱼ` used in the tree.

arXiv:2307.01696, eq. (16): each layer is applied inside the initial space of the next. -/
theorem blockKron_polarSupportMatrix_mul_physicalMatrix_blockTensor (L : ℕ)
    (B : MPSTensor n D) :
    blockKron L (polarSupportMatrix B) *
        physicalMatrix (blockTensor (polarPosTensor B) L) =
      physicalMatrix (blockTensor (polarPosTensor B) L) := by
  rw [← physicalMatrix_rotatePhysical, ← blockTensor_rotatePhysical,
    rotatePhysical_polarSupportMatrix]

/-- The first layer `(V⁽¹⁾)^{⊗L}` acts inside its initial space on the blocked tensor of `T₁`:
its Gram matrix fixes that tensor. -/
private lemma rotatePhysical_blockKron_gram_blockTensor (L : ℕ) (B : MPSTensor n D) :
    rotatePhysical ((blockKron L (polarIsoMatrix B))ᴴ * blockKron L (polarIsoMatrix B))
      (blockTensor (polarPosTensor B) L) = blockTensor (polarPosTensor B) L := by
  apply physicalMatrix_injective
  rw [physicalMatrix_rotatePhysical, conjTranspose_blockKron_polarIsoMatrix_mul_self,
    blockKron_polarSupportMatrix_mul_physicalMatrix_blockTensor]

/-- A block of `2^{k+2}` sites is the first layer `(V⁽¹⁾)^{⊗2^{k+1}}` applied to the blocked
tensor of `T₁`, regrouped along neighbouring pairs. -/
private lemma blockTensor_two_pow_add_two (k : ℕ) (A : MPSTensor n D) :
    blockTensor A (2 ^ (k + 1 + 1)) = fun i =>
      rotatePhysical (blockKron (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)))
        (blockTensor (polarPosTensor (blockTensor A 2)) (2 ^ (k + 1)))
        (pairRegroupEquiv n k i) := by
  funext i
  rw [← blockTensor_rotatePhysical, rotatePhysical_polarIsoMatrix_polarPosTensor]
  exact (blockTensor_pairRegroupEquiv A k i).symm

/-! ### Identification with the polar decomposition of the blocked tensor -/

/-- **Tree factorization, uniqueness**: the product of the `k + 1` layers is the isometry `V` of
the polar decomposition of `A` blocked over `2^{k+1}` sites.

arXiv:2307.01696, eq. (16) and the sentence before it: the tree layers act "to the same
effect" as blocking directly. The identification of the product of the layers with `V` is left
implicit in the source; here each layer acts inside its initial space, so it composes with the
isometry of the next (`MPSTensor.polarIsoMatrix_rotatePhysical`). -/
theorem polarIsoMatrix_blockTensor_eq_treeIsoMatrix (k : ℕ) (A : MPSTensor n D) :
    polarIsoMatrix (blockTensor A (2 ^ (k + 1))) = treeIsoMatrix k A := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [blockTensor_two_pow_add_two, polarIsoMatrix_comp_equiv,
        polarIsoMatrix_rotatePhysical (rotatePhysical_blockKron_gram_blockTensor _ _), ih,
        treeIsoMatrix_succ]

/-- **Tree factorization, uniqueness**: the positive part of `A` blocked over `2^{k+1}` sites is
the positive part `P_{k+1}` of the last layer of the tree.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"); the equality of
the positive parts is left implicit in the source. -/
theorem polarPosTensor_blockTensor_eq_treePosTensor (k : ℕ) (A : MPSTensor n D) :
    polarPosTensor (blockTensor A (2 ^ (k + 1))) = treePosTensor k A := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [blockTensor_two_pow_add_two, polarPosTensor_comp_equiv,
        polarPosTensor_rotatePhysical (rotatePhysical_blockKron_gram_blockTensor _ _), ih,
        treePosTensor_succ]

/-- **Tree factorization, uniqueness**: the support projector of `A` blocked over `2^{k+1}` sites
is the support projector of the positive part `P_{k+1}` of the last layer of the tree.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"), with the
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors" (`V†V = Π`). -/
theorem polarSupportMatrix_blockTensor_eq_treeSupportMatrix (k : ℕ) (A : MPSTensor n D) :
    polarSupportMatrix (blockTensor A (2 ^ (k + 1))) = treeSupportMatrix k A := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [blockTensor_two_pow_add_two, polarSupportMatrix_comp_equiv,
        polarSupportMatrix_rotatePhysical (rotatePhysical_blockKron_gram_blockTensor _ _), ih,
        treeSupportMatrix_succ]

/-! ### The factorization -/

/-- **Tree factorization**, tensor form: the tensor `A` blocked over `2^{k+1}` sites is the
product of the `k + 1` layers applied to the physical leg of `P_{k+1}`.

arXiv:2307.01696, eq. (16). -/
theorem blockTensor_eq_rotatePhysical_treeIsoMatrix (k : ℕ) (A : MPSTensor n D) :
    blockTensor A (2 ^ (k + 1)) = rotatePhysical (treeIsoMatrix k A) (treePosTensor k A) := by
  rw [← polarIsoMatrix_blockTensor_eq_treeIsoMatrix, ← polarPosTensor_blockTensor_eq_treePosTensor,
    rotatePhysical_polarIsoMatrix_polarPosTensor]

/-- **Tree factorization**, matrix form: `B_{2^{k+1}} = (V⁽¹⁾)^{⊗2^k} ⋯ V⁽ᵏ⁺¹⁾ P_{k+1}` as maps
`ℂ^{D²} → (ℂⁿ)^{⊗2^{k+1}}`.

arXiv:2307.01696, eq. (16). -/
theorem physicalMatrix_blockTensor_eq_treeIsoMatrix_mul (k : ℕ) (A : MPSTensor n D) :
    physicalMatrix (blockTensor A (2 ^ (k + 1))) =
      treeIsoMatrix k A * physicalMatrix (treePosTensor k A) := by
  rw [blockTensor_eq_rotatePhysical_treeIsoMatrix, physicalMatrix_rotatePhysical]

/-- **The product of the layers is a partial isometry** whose initial projector is the support
projector of `P_{k+1}`.

Supplied step for arXiv:2307.01696, eq. (16), which the source leaves implicit; it is the
tree analogue of `V†V = Π` for `Π` the projector onto the image of `P` (arXiv:2307.01696,
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors"). -/
theorem conjTranspose_treeIsoMatrix_mul_self (k : ℕ) (A : MPSTensor n D) :
    (treeIsoMatrix k A)ᴴ * treeIsoMatrix k A = treeSupportMatrix k A := by
  rw [← polarIsoMatrix_blockTensor_eq_treeIsoMatrix,
    ← polarSupportMatrix_blockTensor_eq_treeSupportMatrix,
    conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]

end MPSTensor
