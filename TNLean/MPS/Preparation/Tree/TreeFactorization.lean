/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.BlockingInfrastructure
import TNLean.MPS.Tensor.Physical.BlockedPolar

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

* `MPSTensor.blockKron` (from `TNLean.MPS.Tensor.Physical.Blocking`) — the Kronecker power
  `W^{⊗L}` of a rectangular physical map, acting on length-`L` blocks.
* `MPSTensor.block_rotatePhysical` (from `TNLean.MPS.Tensor.Physical.Blocking`) — blocking commutes
  with physical maps: `(W · C)` blocked `L` times is `W^{⊗L}` applied to `C` blocked `L` times.
* `MPSTensor.pairPosTensor`, `MPSTensor.treeLayers` — positive-part iteration and its layers.
* `MPSTensor.treePosTensor`, `MPSTensor.treeIsoMatrix` — the last positive part `P_{k+1}` of
  the chain `Tⱼ`, and the product of the layers.
* `MPSTensor.block_eq_rotatePhysical_treeIsoMatrix`,
  `MPSTensor.physicalMatrix_block_eq_treeIsoMatrix_mul` — the tree factorization.
* `MPSTensor.conjTranspose_treeIsoMatrix_mul_self` — the product of the layers is a partial
  isometry with initial projector the support projector of `P_{k+1}`.
* `MPSTensor.polarIsoMatrix_block_eq_treeIsoMatrix`,
  `MPSTensor.polarPosTensor_block_eq_treePosTensor`,
  `MPSTensor.polarSupportMatrix_block_eq_treeSupportMatrix` — the layers compose to the
  polar factors of the blocked tensor.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and the paragraph containing it.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {α : Type} [Fintype α] {D : ℕ}

/-- The positive-part tensor `T₁` of the two-site blocked tensor of `A`, the tensor whose
two-site blocks are decomposed in the next layer of eq. (16) of arXiv:2307.01696. -/
noncomputable def pairPosTensor (A : MPTensor α (Fin D)) : MPSTensor (D * D) D :=
  polarPosTensor (Kraus.block A 2)

/-- The coarse layers `V⁽²⁾, …, V⁽ᵏ⁺¹⁾` of the tree-RG circuit for a block of `2^{k+1}` sites:
`V⁽ʲ⁺²⁾` is the isometric factor of the two-site blocked tensor of `T_{j+1}`.

arXiv:2307.01696, eq. (16). -/
noncomputable def treeLayers (k : ℕ) (A : MPTensor α (Fin D)) :
    Fin k → Matrix (Fin 2 → Fin (D * D)) (Fin (D * D)) ℂ :=
  fun j => polarIsoMatrix
    (Kraus.block ((pairPosTensor : MPSTensor (D * D) D → MPSTensor (D * D) D)^[j]
      (pairPosTensor A)) 2)

/-! ### Regrouping a block of `2^{k+2}` sites into pairs -/

/-- The regrouping of a block of `2^{k+2}` sites into `2^{k+1}` neighbouring pairs. -/
noncomputable def pairRegroupEquiv (α : Type) (k : ℕ) :
    (Fin (2 ^ (k + 2)) → α) ≃ (Fin (2 ^ (k + 1)) → Fin 2 → α) :=
  (Equiv.arrowCongr (finCongr (pow_succ 2 (k + 1))) (Equiv.refl α)).trans
    (Kraus.blockConfigEquiv α (2 ^ (k + 1)) 2).symm

/-- Blocking `2^{k+2}` sites is blocking `2^{k+1}` pairs of the two-site blocked tensor. -/
theorem block_pairRegroupEquiv (A : MPTensor α (Fin D)) (k : ℕ) (i : Fin (2 ^ (k + 2)) → α) :
    Kraus.block (Kraus.block A 2) (2 ^ (k + 1)) (pairRegroupEquiv α k i) =
      Kraus.block A (2 ^ (k + 2)) i := by
  rw [Kraus.block_apply, Kraus.evalWord_block, ← Kraus.ofFn_blockConfigEquiv, pairRegroupEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply, Kraus.block_apply]
  exact congrArg _ (List.ofFn_congr (pow_succ 2 (k + 1)) i).symm

/-! ### The tree of polar decompositions -/

/-- The positive part `P_{k+1}` of the last layer of the tree for a block of `2^{k+1}` sites,
read as a tensor. Along the chain `T₀ = A`, `Tⱼ₊₁` the positive-part tensor of the two-site
blocked tensor of `Tⱼ`, it is the positive-part tensor of the two-site blocked tensor of `T_k`.
The physical alphabet changes from `α` to `Fin (D * D)` after the first step.

arXiv:2307.01696, eq. (16): the tensors whose two-site blocks are decomposed in the successive
layers, and the factor `P_k` (indexed there from one). -/
noncomputable def treePosTensor :
    (k : ℕ) → {α : Type} → [Fintype α] → MPTensor α (Fin D) → MPSTensor (D * D) D
  | 0, _, _, A => polarPosTensor (Kraus.block A 2)
  | k + 1, _, _, A => treePosTensor k (polarPosTensor (Kraus.block A 2))

/-- The support projector of `P_{k+1}`, the initial projector of the product of the layers. -/
noncomputable def treeSupportMatrix :
    (k : ℕ) → {α : Type} → [Fintype α] → MPTensor α (Fin D) → Matrix (Fin (D * D)) (Fin (D * D)) ℂ
  | 0, _, _, A => polarSupportMatrix (Kraus.block A 2)
  | k + 1, _, _, A => treeSupportMatrix k (polarPosTensor (Kraus.block A 2))

/-- The product of the `k + 1` layers of the tree, a map `ℂ^{D²} → (ℂ^α)^{⊗2^{k+1}}`:
`V⁽¹⁾` for `k = 0`, and `(V⁽¹⁾)^{⊗2^{k+1}}` composed with the tree of `T₁`, regrouped along
neighbouring pairs, for `k + 1`.  Unfolded, this is
`(V⁽¹⁾)^{⊗2^k} (V⁽²⁾)^{⊗2^{k-1}} ⋯ V⁽ᵏ⁺¹⁾`.

arXiv:2307.01696, eq. (16). -/
noncomputable def treeIsoMatrix :
    (k : ℕ) → {α : Type} → [Fintype α] → MPTensor α (Fin D) →
      Matrix (Fin (2 ^ (k + 1)) → α) (Fin (D * D)) ℂ
  | 0, _, _, A => polarIsoMatrix (Kraus.block A 2)
  | k + 1, α, _, A =>
      (blockKron (2 ^ (k + 1)) (polarIsoMatrix (Kraus.block A 2)) *
        treeIsoMatrix k (polarPosTensor (Kraus.block A 2))).submatrix (pairRegroupEquiv α k) id

/-- The first layer of the tree for a block of `2^{k+2}` sites is `(V⁽¹⁾)^{⊗2^{k+1}}`, followed
by the tree of `T₁`. -/
lemma treeIsoMatrix_succ (k : ℕ) (A : MPTensor α (Fin D)) :
    treeIsoMatrix (k + 1) A =
      (blockKron (2 ^ (k + 1)) (polarIsoMatrix (Kraus.block A 2)) *
        treeIsoMatrix k (polarPosTensor (Kraus.block A 2))).submatrix (pairRegroupEquiv α k) id :=
  rfl

lemma treePosTensor_succ (k : ℕ) (A : MPTensor α (Fin D)) :
    treePosTensor (k + 1) A = treePosTensor k (polarPosTensor (Kraus.block A 2)) := rfl

lemma treeSupportMatrix_succ (k : ℕ) (A : MPTensor α (Fin D)) :
    treeSupportMatrix (k + 1) A = treeSupportMatrix k (polarPosTensor (Kraus.block A 2)) := rfl

/-! ### The layers are partial isometries -/

/-- Each Kronecker-power layer is a partial isometry: `((V⁽ʲ⁾)^{⊗L})ᴴ (V⁽ʲ⁾)^{⊗L} = Π^{⊗L}`.

arXiv:2307.01696, eq. (16), with the Supplemental Material, "Proof of Lemma 1 and extension to
non-normal tensors" (`V†V = Π`). -/
theorem conjTranspose_blockKron_polarIsoMatrix_mul_self (L : ℕ) (B : MPTensor α (Fin D)) :
    (blockKron L (polarIsoMatrix B))ᴴ * blockKron L (polarIsoMatrix B) =
      blockKron L (polarSupportMatrix B) := by
  rw [blockKron_conjTranspose, ← blockKron_mul,
    conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]

/-- **Range containment**: the tensor `T` of a positive part `P`, blocked over `L` sites, has
its range inside `(ran P)^{⊗L}`, that is, `Π^{⊗L}` fixes its physical matrix.  For `L = 2` this
is the containment `ran B⁽ʲ⁺¹⁾ ⊆ ran Pⱼ ⊗ ran Pⱼ` used in the tree.

arXiv:2307.01696, eq. (16): each layer is applied inside the initial space of the next. -/
theorem blockKron_polarSupportMatrix_mul_physicalMatrix_block (L : ℕ)
    (B : MPTensor α (Fin D)) :
    blockKron L (polarSupportMatrix B) *
        physicalMatrix (Kraus.block (polarPosTensor B) L) =
      physicalMatrix (Kraus.block (polarPosTensor B) L) := by
  rw [← physicalMatrix_rotatePhysical, ← block_rotatePhysical,
    rotatePhysical_polarSupportMatrix]

/-- The first layer `(V⁽¹⁾)^{⊗L}` acts inside its initial space on the blocked tensor of `T₁`:
its Gram matrix fixes that tensor. -/
private lemma rotatePhysical_blockKron_gram_block (L : ℕ) (B : MPTensor α (Fin D)) :
    rotatePhysical ((blockKron L (polarIsoMatrix B))ᴴ * blockKron L (polarIsoMatrix B))
      (Kraus.block (polarPosTensor B) L) = Kraus.block (polarPosTensor B) L := by
  apply physicalMatrix_injective
  rw [physicalMatrix_rotatePhysical, conjTranspose_blockKron_polarIsoMatrix_mul_self,
    blockKron_polarSupportMatrix_mul_physicalMatrix_block]

/-- A block of `2^{k+2}` sites is the first layer `(V⁽¹⁾)^{⊗2^{k+1}}` applied to the blocked
tensor of `T₁`, regrouped along neighbouring pairs. -/
private lemma block_two_pow_add_two (k : ℕ) (A : MPTensor α (Fin D)) :
    Kraus.block A (2 ^ (k + 1 + 1)) = fun i =>
      rotatePhysical (blockKron (2 ^ (k + 1)) (polarIsoMatrix (Kraus.block A 2)))
        (Kraus.block (polarPosTensor (Kraus.block A 2)) (2 ^ (k + 1)))
        (pairRegroupEquiv α k i) := by
  funext i
  rw [← block_rotatePhysical, rotatePhysical_polarIsoMatrix_polarPosTensor]
  exact (block_pairRegroupEquiv A k i).symm

/-! ### Identification with the polar decomposition of the blocked tensor -/

/-- **Tree factorization, uniqueness**: the product of the `k + 1` layers is the isometry `V` of
the polar decomposition of `A` blocked over `2^{k+1}` sites.

arXiv:2307.01696, eq. (16) and the sentence before it: the tree layers act "to the same
effect" as blocking directly. The identification of the product of the layers with `V` is left
implicit in the source; here each layer acts inside its initial space, so it composes with the
isometry of the next (`MPSTensor.polarIsoMatrix_rotatePhysical`). -/
theorem polarIsoMatrix_block_eq_treeIsoMatrix (k : ℕ) (A : MPTensor α (Fin D)) :
    polarIsoMatrix (Kraus.block A (2 ^ (k + 1))) = treeIsoMatrix k A := by
  induction k generalizing α with
  | zero => rfl
  | succ k ih =>
      rw [block_two_pow_add_two, polarIsoMatrix_comp_equiv,
        polarIsoMatrix_rotatePhysical (rotatePhysical_blockKron_gram_block _ _), ih,
        treeIsoMatrix_succ]

/-- **Tree factorization, uniqueness**: the positive part of `A` blocked over `2^{k+1}` sites is
the positive part `P_{k+1}` of the last layer of the tree.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"); the equality of
the positive parts is left implicit in the source. -/
theorem polarPosTensor_block_eq_treePosTensor (k : ℕ) (A : MPTensor α (Fin D)) :
    polarPosTensor (Kraus.block A (2 ^ (k + 1))) = treePosTensor k A := by
  induction k generalizing α with
  | zero => rfl
  | succ k ih =>
      rw [block_two_pow_add_two, polarPosTensor_comp_equiv,
        polarPosTensor_rotatePhysical (rotatePhysical_blockKron_gram_block _ _), ih,
        treePosTensor_succ]

/-- **Tree factorization, uniqueness**: the support projector of `A` blocked over `2^{k+1}` sites
is the support projector of the positive part `P_{k+1}` of the last layer of the tree.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"), with the
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors" (`V†V = Π`). -/
theorem polarSupportMatrix_block_eq_treeSupportMatrix (k : ℕ) (A : MPTensor α (Fin D)) :
    polarSupportMatrix (Kraus.block A (2 ^ (k + 1))) = treeSupportMatrix k A := by
  induction k generalizing α with
  | zero => rfl
  | succ k ih =>
      rw [block_two_pow_add_two, polarSupportMatrix_comp_equiv,
        polarSupportMatrix_rotatePhysical (rotatePhysical_blockKron_gram_block _ _), ih,
        treeSupportMatrix_succ]

/-! ### The factorization -/

/-- **Tree factorization**, tensor form: the tensor `A` blocked over `2^{k+1}` sites is the
product of the `k + 1` layers applied to the physical leg of `P_{k+1}`.

arXiv:2307.01696, eq. (16). -/
theorem block_eq_rotatePhysical_treeIsoMatrix (k : ℕ) (A : MPTensor α (Fin D)) :
    Kraus.block A (2 ^ (k + 1)) = rotatePhysical (treeIsoMatrix k A) (treePosTensor k A) := by
  rw [← polarIsoMatrix_block_eq_treeIsoMatrix, ← polarPosTensor_block_eq_treePosTensor,
    rotatePhysical_polarIsoMatrix_polarPosTensor]

/-- **Tree factorization**, matrix form: `B_{2^{k+1}} = (V⁽¹⁾)^{⊗2^k} ⋯ V⁽ᵏ⁺¹⁾ P_{k+1}` as maps
`ℂ^{D²} → (ℂ^α)^{⊗2^{k+1}}`.

arXiv:2307.01696, eq. (16). -/
theorem physicalMatrix_block_eq_treeIsoMatrix_mul (k : ℕ) (A : MPTensor α (Fin D)) :
    physicalMatrix (Kraus.block A (2 ^ (k + 1))) =
      treeIsoMatrix k A * physicalMatrix (treePosTensor k A) := by
  rw [block_eq_rotatePhysical_treeIsoMatrix, physicalMatrix_rotatePhysical]

/-- **The product of the layers is a partial isometry** whose initial projector is the support
projector of `P_{k+1}`.

Supplied step for arXiv:2307.01696, eq. (16), which the source leaves implicit; it is the
tree analogue of `V†V = Π` for `Π` the projector onto the image of `P` (arXiv:2307.01696,
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors"). -/
theorem conjTranspose_treeIsoMatrix_mul_self (k : ℕ) (A : MPTensor α (Fin D)) :
    (treeIsoMatrix k A)ᴴ * treeIsoMatrix k A = treeSupportMatrix k A := by
  rw [← polarIsoMatrix_block_eq_treeIsoMatrix,
    ← polarSupportMatrix_block_eq_treeSupportMatrix,
    conjTranspose_polarIsoMatrix_mul_polarIsoMatrix]

end MPSTensor
