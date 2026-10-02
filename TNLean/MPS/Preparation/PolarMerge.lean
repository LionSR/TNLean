/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.PolarUniqueness

/-!
# The isometry of a block of unequal halves

The tree-RG circuit of arXiv:2307.01696, eq. (16), writes the isometry `V` of the polar
decomposition `B_q = V P` of a blocked tensor as a tree of isometries, each of which maps the
virtual space `ℂ^{D²}` of a block to those of its two halves. For blocks of `2^{k+1}` sites, cut
into equal halves, this is `MPSTensor.polarIsoMatrix_blockTensor_eq_treeIsoMatrix`. This file
proves the step of the tree for two halves of any lengths `n₁` and `n₂`: if `B_{n₁} = V₁ P₁` and
`B_{n₂} = V₂ P₂`, then

  `V_{n₁+n₂} = (V₁ ⊗ V₂) W`,

where `W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` is the partial isometry of the polar decomposition of the
tensor `(a, b) ↦ P₁^a P₂^b` of two neighbouring sites carrying the positive parts
(`MPSPreparation.cfgPolarIso_append`), and that tensor has the positive part of `B_{n₁+n₂}`
(`MPSPreparation.polarPosTensor_blockTensor_add`). No injectivity is assumed: the initial
projector `Π₁ ⊗ Π₂` of `V₁ ⊗ V₂` fixes the tensor of the positive parts, so `V₁ ⊗ V₂` composes
with its partial isometry (`MPSTensor.polarIsoMatrix_rotatePhysical`). For halves of equal
lengths, `W` is the layer of the tree (`MPSPreparation.mergeIso_self`).

The isometries are read on configurations of the sites of a block
(`MPSPreparation.cfgPolarIso`), which is how the circuits act on them.

## Main definitions

* `MPSPreparation.pairProductTensor` — the tensor `(a, b) ↦ X^a Y^b` of two neighbouring sites.
* `MPSPreparation.cfgPolarIso` — the isometry `V_n` of `A` blocked over `n` sites, on
  configurations.
* `MPSPreparation.mergeIso` — the isometry `W` joining blocks of `n₁` and `n₂` sites.

## Main results

* `MPSPreparation.cfgPolarIso_append`, `MPSPreparation.cfgPolarIso_split` —
  `V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`, for every tensor.
* `MPSPreparation.polarPosTensor_blockTensor_add` — `P_{n₁+n₂}` is the positive part of the
  tensor `(a, b) ↦ P₁^a P₂^b`.
* `MPSPreparation.pairProductTensor_self`, `MPSPreparation.mergeIso_self` — for halves of equal
  lengths, `W` is the isometry of the two-site blocked tensor of `P_n`.
* `MPSPreparation.isIsometry_mergeIso` — `W` is an isometry when `A` blocked over `n₁ + n₂`
  sites is injective.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16), and the paragraph "Approximation
  through the fixed-point state" (the polar decomposition `B = V P`).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d D : ℕ}

/-! ### Two neighbouring sites carrying different tensors -/

/-- The tensor of two neighbouring sites carrying `X` and `Y`: `(a, b) ↦ X^a Y^b`. For `X = Y`
it is the two-site blocked tensor of `X`. -/
noncomputable def pairProductTensor {κ : ℕ} (X Y : MPSTensor κ D) :
    MPSTensor (blockPhysDim κ 2) D :=
  fun e => X (decodeBlock κ 2 e 0) * Y (decodeBlock κ 2 e 1)

/-- The isometry `V_n` of the polar decomposition of `A` blocked over `n` sites, read on the
configurations of the `n` sites: `⟨τ| V_n |x⟩`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": `B = V P` with
`V : ℂ^{D²} → ℂ^{d^q}`. -/
noncomputable def cfgPolarIso (A : MPSTensor d D) (n : ℕ) : Matrix (Cfg d n) (Fin (D * D)) ℂ :=
  fun τ x => polarIsoMatrix (blockTensor A n) ((decodeBlockEquiv d n).symm τ) x

/-- The isometry `W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` joining a block of `n₁` sites to the block of
`n₂` sites after it: the partial isometry of the polar decomposition of the tensor
`(a, b) ↦ P₁^a P₂^b`, with `P₁` and `P₂` the positive parts of `A` blocked over `n₁` and `n₂` sites.

arXiv:2307.01696, eq. (16): the isometries `V⁽ʲ⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` of the tree, here
for halves of unequal lengths. -/
noncomputable def mergeIso (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ :=
  polarIsoMatrix (pairProductTensor (polarPosTensor (blockTensor A n₁))
    (polarPosTensor (blockTensor A n₂)))

/-- For an injective blocked tensor, `V_n` is an isometry. -/
theorem isIsometry_cfgPolarIso (A : MPSTensor d D) {n : ℕ}
    (h : Kraus.IsInjective (blockTensor A n)) : (cfgPolarIso A n).IsIsometry := by
  have hV := isIsometry_polarIsoMatrix_of_isInjective h
  have he : cfgPolarIso A n =
      (polarIsoMatrix (blockTensor A n)).submatrix (decodeBlockEquiv d n).symm id := rfl
  rw [Matrix.IsIsometry, he, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    show (polarIsoMatrix (blockTensor A n))ᴴ * polarIsoMatrix (blockTensor A n) = 1 from hV,
    Matrix.submatrix_id_id]

/-! ### Blocking two halves -/

/-- A block of `n₁ + n₂` sites carries the product of the blocked tensors of its halves. -/
theorem blockTensor_add_apply (A : MPSTensor d D) (n₁ n₂ : ℕ) (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) :
    blockTensor A (n₁ + n₂) ((decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂)) =
      blockTensor A n₁ ((decodeBlockEquiv d n₁).symm τ₁) *
        blockTensor A n₂ ((decodeBlockEquiv d n₂).symm τ₂) := by
  simp only [blockTensor, Kraus.blockTensor, Kraus.wordOfBlock,
    Kraus.decodeBlock_decodeBlockEquiv_symm, List.ofFn_fin_append, Kraus.evalWord_append]

/-- The equivalence of the configurations of a block with the pairs of configurations of its
halves, read on blocked indices. -/
private noncomputable def splitEquiv (d n₁ n₂ : ℕ) :
    Fin (blockPhysDim d (n₁ + n₂)) ≃ Fin (blockPhysDim d n₁) × Fin (blockPhysDim d n₂) :=
  ((decodeBlockEquiv d (n₁ + n₂)).trans (Fin.appendEquiv n₁ n₂).symm).trans
    (Equiv.prodCongr (decodeBlockEquiv d n₁).symm (decodeBlockEquiv d n₂).symm)

/-- The pairs of indices of `ℂ^{D²} ⊗ ℂ^{D²}`, read on two-site blocked indices. -/
private noncomputable def pairEquiv (κ : ℕ) : Fin (blockPhysDim κ 2) ≃ Fin κ × Fin κ :=
  (decodeBlockEquiv κ 2).trans (piFinTwoEquiv fun _ => Fin κ)

private theorem splitEquiv_symm_apply (n₁ n₂ : ℕ) (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) :
    (splitEquiv d n₁ n₂).symm ((decodeBlockEquiv d n₁).symm τ₁, (decodeBlockEquiv d n₂).symm τ₂) =
      (decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂) := by
  simp [splitEquiv, Fin.appendEquiv]

private theorem blockTensor_splitEquiv (A : MPSTensor d D) (n₁ n₂ : ℕ)
    (I : Fin (blockPhysDim d (n₁ + n₂))) :
    blockTensor A (n₁ + n₂) I =
      blockTensor A n₁ (splitEquiv d n₁ n₂ I).1 * blockTensor A n₂ (splitEquiv d n₁ n₂ I).2 := by
  obtain ⟨⟨I₁, I₂⟩, rfl⟩ := (splitEquiv d n₁ n₂).symm.surjective I
  obtain ⟨τ₁, rfl⟩ := (decodeBlockEquiv d n₁).symm.surjective I₁
  obtain ⟨τ₂, rfl⟩ := (decodeBlockEquiv d n₂).symm.surjective I₂
  rw [Equiv.apply_symm_apply, splitEquiv_symm_apply, blockTensor_add_apply]

private theorem pairEquiv_fst {κ : ℕ} (e : Fin (blockPhysDim κ 2)) :
    (pairEquiv κ e).1 = decodeBlock κ 2 e 0 := rfl

private theorem pairEquiv_snd {κ : ℕ} (e : Fin (blockPhysDim κ 2)) :
    (pairEquiv κ e).2 = decodeBlock κ 2 e 1 := rfl

/-- A tensor read through its polar decomposition: `B^a = ∑_y ⟨a|V|y⟩ P^y`. -/
private theorem eq_sum_polarIsoMatrix_smul {m : ℕ} (B : MPSTensor m D) (a : Fin m) :
    B a = ∑ y, polarIsoMatrix B a y • polarPosTensor B y := by
  conv_lhs => rw [← rotatePhysical_polarIsoMatrix_polarPosTensor B]
  rfl

/-- The Kronecker product `V₁ ⊗ V₂` of maps into the halves of a block, read on blocked
indices. -/
private noncomputable def splitKron {κ n₁ n₂ : ℕ} (V₁ : Matrix (Fin (blockPhysDim d n₁)) (Fin κ) ℂ)
    (V₂ : Matrix (Fin (blockPhysDim d n₂)) (Fin κ) ℂ) :
    Matrix (Fin (blockPhysDim d (n₁ + n₂))) (Fin (blockPhysDim κ 2)) ℂ :=
  fun I e => V₁ (splitEquiv d n₁ n₂ I).1 (pairEquiv κ e).1 *
    V₂ (splitEquiv d n₁ n₂ I).2 (pairEquiv κ e).2

/-- The Kronecker product `E₁ ⊗ E₂` of two square matrices, read on two-site blocked
indices. -/
private noncomputable def pairKron {κ : ℕ} (E₁ E₂ : Matrix (Fin κ) (Fin κ) ℂ) :
    Matrix (Fin (blockPhysDim κ 2)) (Fin (blockPhysDim κ 2)) ℂ :=
  fun e e' => E₁ (pairEquiv κ e).1 (pairEquiv κ e').1 * E₂ (pairEquiv κ e).2 (pairEquiv κ e').2

/-- `(V₁ ⊗ V₂)ᴴ (V₁ ⊗ V₂) = V₁ᴴ V₁ ⊗ V₂ᴴ V₂`. -/
private theorem conjTranspose_splitKron_mul_self {κ n₁ n₂ : ℕ}
    (V₁ : Matrix (Fin (blockPhysDim d n₁)) (Fin κ) ℂ)
    (V₂ : Matrix (Fin (blockPhysDim d n₂)) (Fin κ) ℂ) :
    (splitKron V₁ V₂)ᴴ * splitKron V₁ V₂ = pairKron (V₁ᴴ * V₁) (V₂ᴴ * V₂) := by
  ext e e'
  simp only [Matrix.mul_apply, conjTranspose_apply, pairKron]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (splitEquiv d n₁ n₂) _ _ fun I => ?_
  simp only [splitKron, star_mul']
  ring

/-- `E₁ ⊗ E₂` acts on the tensor `(a, b) ↦ X^a Y^b` factor by factor. -/
private theorem rotatePhysical_pairKron_pairProductTensor {κ : ℕ}
    (E₁ E₂ : Matrix (Fin κ) (Fin κ) ℂ) (X Y : MPSTensor κ D) :
    rotatePhysical (pairKron E₁ E₂) (pairProductTensor X Y) =
      pairProductTensor (rotatePhysical E₁ X) (rotatePhysical E₂ Y) := by
  funext e
  simp only [rotatePhysical_apply, pairProductTensor, ← pairEquiv_fst, ← pairEquiv_snd]
  rw [Finset.sum_mul_sum, ← (pairEquiv κ).symm.sum_comp, Fintype.sum_prod_type]
  simp only [pairKron, Equiv.apply_symm_apply, smul_mul_smul_comm]

/-- `B_{n₁+n₂} = (V₁ ⊗ V₂) C`, with `C` the tensor `(a, b) ↦ P₁^a P₂^b`. -/
private theorem physicalMatrix_blockTensor_add (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    physicalMatrix (blockTensor A (n₁ + n₂)) =
      splitKron (polarIsoMatrix (blockTensor A n₁)) (polarIsoMatrix (blockTensor A n₂)) *
        physicalMatrix (pairProductTensor (polarPosTensor (blockTensor A n₁))
          (polarPosTensor (blockTensor A n₂))) := by
  ext I ⟨α, β⟩
  simp only [physicalMatrix, Matrix.mul_apply]
  rw [blockTensor_splitEquiv, eq_sum_polarIsoMatrix_smul (blockTensor A n₁),
    eq_sum_polarIsoMatrix_smul (blockTensor A n₂), Finset.sum_mul_sum,
    ← (pairEquiv (D * D)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply, smul_mul_smul_comm, Matrix.smul_apply, smul_eq_mul, splitKron,
    Equiv.apply_symm_apply, pairProductTensor, ← pairEquiv_fst, ← pairEquiv_snd]

/-- `B_{n₁+n₂} = (V₁ ⊗ V₂) · C`, with `C` the tensor `(a, b) ↦ P₁^a P₂^b`, and
`(V₁ ⊗ V₂)ᴴ (V₁ ⊗ V₂)` fixes `C`; so `V_{n₁+n₂} = (V₁ ⊗ V₂) W` and `C` has the positive part
of `B_{n₁+n₂}`. -/
private theorem blockTensor_add_eq_rotatePhysical (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    blockTensor A (n₁ + n₂) =
        rotatePhysical
          (splitKron (polarIsoMatrix (blockTensor A n₁)) (polarIsoMatrix (blockTensor A n₂)))
          (pairProductTensor (polarPosTensor (blockTensor A n₁))
            (polarPosTensor (blockTensor A n₂))) ∧
      rotatePhysical
          ((splitKron (polarIsoMatrix (blockTensor A n₁)) (polarIsoMatrix (blockTensor A n₂)))ᴴ *
            splitKron (polarIsoMatrix (blockTensor A n₁)) (polarIsoMatrix (blockTensor A n₂)))
          (pairProductTensor (polarPosTensor (blockTensor A n₁))
            (polarPosTensor (blockTensor A n₂))) =
        pairProductTensor (polarPosTensor (blockTensor A n₁))
          (polarPosTensor (blockTensor A n₂)) := by
  refine ⟨physicalMatrix_injective ?_, ?_⟩
  · rw [physicalMatrix_rotatePhysical]
    exact physicalMatrix_blockTensor_add A n₁ n₂
  · rw [conjTranspose_splitKron_mul_self, rotatePhysical_pairKron_pairProductTensor,
      conjTranspose_polarIsoMatrix_mul_polarIsoMatrix,
      conjTranspose_polarIsoMatrix_mul_polarIsoMatrix, rotatePhysical_polarSupportMatrix,
      rotatePhysical_polarSupportMatrix]

/-- **The isometry of a block of unequal halves** (arXiv:2307.01696, eq. (16), for halves of
lengths `n₁` and `n₂`): `V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`, with `W = mergeIso A n₁ n₂`:

  `⟨τ₁ τ₂| V_{n₁+n₂} |x⟩ = ∑ₑ ⟨τ₁| V_{n₁} |e₀⟩ ⟨τ₂| V_{n₂} |e₁⟩ ⟨e₀ e₁| W |x⟩`.

No injectivity is assumed. The proof writes `B_{n₁+n₂} = (V₁ ⊗ V₂) C`, with `C` the tensor
`(a, b) ↦ P₁^a P₂^b`. The initial projector `Π₁ ⊗ Π₂` of `V₁ ⊗ V₂` fixes `C`, so the partial
isometry of `B_{n₁+n₂}` is `V₁ ⊗ V₂` times that of `C` (`MPSTensor.polarIsoMatrix_rotatePhysical`).
The source leaves this identification implicit ("to the same effect"); its footnote to "The
sequential-RG circuit" states that the derivation holds for non-injective tensors. -/
theorem cfgPolarIso_append (A : MPSTensor d D) {n₁ n₂ : ℕ} (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂)
    (x : Fin (D * D)) :
    cfgPolarIso A (n₁ + n₂) (Fin.append τ₁ τ₂) x =
      ∑ e, cfgPolarIso A n₁ τ₁ (decodeBlock _ 2 e 0) * cfgPolarIso A n₂ τ₂ (decodeBlock _ 2 e 1) *
        mergeIso A n₁ n₂ e x := by
  obtain ⟨hB, hfix⟩ := blockTensor_add_eq_rotatePhysical A n₁ n₂
  have hiso := congrFun (congrFun (congrArg polarIsoMatrix hB)
    ((decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂))) x
  rw [polarIsoMatrix_rotatePhysical hfix, Matrix.mul_apply] at hiso
  refine hiso.trans ?_
  have hσ : splitEquiv d n₁ n₂ ((decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂)) =
      ((decodeBlockEquiv d n₁).symm τ₁, (decodeBlockEquiv d n₂).symm τ₂) := by
    rw [← splitEquiv_symm_apply, Equiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [splitKron, hσ, pairEquiv_fst, pairEquiv_snd]
  rfl

/-- **The isometry of a block of unequal halves**, for a block of `n = n₁ + n₂` sites:
`cfgPolarIso_append` with the halves read off a configuration `τ` of the block. -/
theorem cfgPolarIso_split (A : MPSTensor d D) {n₁ n₂ n : ℕ} (hn : n₁ + n₂ = n)
    (τ : Cfg d n) (x : Fin (D * D)) :
    cfgPolarIso A n τ x =
      ∑ e, cfgPolarIso A n₁ (fun i => τ ⟨i.val, by omega⟩) (decodeBlock _ 2 e 0) *
        cfgPolarIso A n₂ (fun i => τ ⟨n₁ + i.val, by omega⟩) (decodeBlock _ 2 e 1) *
          mergeIso A n₁ n₂ e x := by
  subst hn
  have hτ : Fin.append (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
      (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) = τ := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  have h := cfgPolarIso_append A (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
    (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) x
  rwa [hτ] at h

/-- **The positive part of a block of unequal halves**: the positive part of `A` blocked over
`n₁ + n₂` sites is the positive part of the tensor `(a, b) ↦ P₁^a P₂^b` of the positive parts of
its halves. No injectivity is assumed.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"), for halves of
unequal lengths. -/
theorem polarPosTensor_blockTensor_add (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    polarPosTensor (blockTensor A (n₁ + n₂)) =
      polarPosTensor (pairProductTensor (polarPosTensor (blockTensor A n₁))
        (polarPosTensor (blockTensor A n₂))) := by
  obtain ⟨hB, hfix⟩ := blockTensor_add_eq_rotatePhysical A n₁ n₂
  rw [hB, polarPosTensor_rotatePhysical hfix]

/-- On two neighbouring sites carrying the same tensor, `(a, b) ↦ X^a X^b` is the two-site
blocked tensor of `X`. -/
theorem pairProductTensor_self {κ : ℕ} (X : MPSTensor κ D) :
    pairProductTensor X X = blockTensor X 2 := by
  funext e
  simp [pairProductTensor, blockTensor, Kraus.blockTensor, Kraus.wordOfBlock, List.ofFn_succ]

/-- **Halves of equal lengths**: joining two blocks of `n` sites, `W` is the isometry of the
two-site blocked tensor of the positive part `P_n`, the layer `V⁽ʲ⁾` of arXiv:2307.01696,
eq. (16). -/
theorem mergeIso_self (A : MPSTensor d D) (n : ℕ) :
    mergeIso A n n = polarIsoMatrix (blockTensor (polarPosTensor (blockTensor A n)) 2) := by
  rw [mergeIso, pairProductTensor_self]

/-- If `A` blocked over `n₁ + n₂` sites is injective, so is the tensor `(a, b) ↦ P₁^a P₂^b` of
the positive parts of its halves: its matrices span those of the blocked tensor. -/
theorem isInjective_pairProductTensor (A : MPSTensor d D) {n₁ n₂ : ℕ}
    (h : Kraus.IsInjective (blockTensor A (n₁ + n₂))) :
    Kraus.IsInjective (pairProductTensor (polarPosTensor (blockTensor A n₁))
      (polarPosTensor (blockTensor A n₂))) := by
  classical
  refine eq_top_iff.mpr (h.symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨I, rfl⟩
  rw [SetLike.mem_coe, blockTensor_splitEquiv, eq_sum_polarIsoMatrix_smul (blockTensor A n₁),
    eq_sum_polarIsoMatrix_smul (blockTensor A n₂), Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun y₁ _ => Submodule.sum_mem _ fun y₂ _ => ?_
  rw [smul_mul_smul_comm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(pairEquiv (D * D)).symm (y₁, y₂), ?_⟩)
  simp [pairProductTensor, pairEquiv, piFinTwoEquiv]

/-- The isometry `W` joining two blocks is an isometry when `A` blocked over the joined block is
injective. -/
theorem isIsometry_mergeIso (A : MPSTensor d D) {n₁ n₂ : ℕ}
    (h : Kraus.IsInjective (blockTensor A (n₁ + n₂))) : (mergeIso A n₁ n₂).IsIsometry :=
  isIsometry_polarIsoMatrix_of_isInjective (isInjective_pairProductTensor A h)

end MPSPreparation
