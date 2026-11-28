/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Overlap
import TNLean.MPS.Tensor.Physical.BlockedPolar
import TNLean.MPS.Preparation.Tree.TreeFactorization
import TNLean.MPS.Preparation.Tree.IsometryTree

/-!
# The partial isometry of a block of unequal halves

The tree-RG circuit of arXiv:2307.01696, eq. (16), writes the partial isometry `V` of the polar
decomposition `B_q = V P` of a blocked tensor as a tree of partial isometries, each of which maps
the virtual space `ℂ^{D²}` of a block to those of its two halves. For blocks of `2^{k+1}` sites, cut
into equal halves, this is `MPSTensor.polarIsoMatrix_block_eq_treeIsoMatrix`. This file
proves the step of the tree for two halves of any lengths `n₁` and `n₂`: if `B_{n₁} = V₁ P₁` and
`B_{n₂} = V₂ P₂`, then

  `V_{n₁+n₂} = (V₁ ⊗ V₂) W`,

where `W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` is the partial isometry of the polar decomposition of the
tensor `(a, b) ↦ P₁^a P₂^b` of two neighbouring sites carrying the positive parts
(`MPSPreparation.polarIsoMatrix_block_append`), and that tensor has the positive part of `B_{n₁+n₂}`
(`MPSPreparation.polarPosTensor_block_add`). No injectivity is assumed: the initial
projector `Π₁ ⊗ Π₂` of `V₁ ⊗ V₂` fixes the tensor of the positive parts, so `V₁ ⊗ V₂` composes
with its partial isometry (`MPSTensor.polarIsoMatrix_rotatePhysical`). For halves of equal
lengths, `W` is the partial isometry of the two-site blocked tensor of `P_n`
(`MPSPreparation.mergeIso_self`); for halves of `2^{j+1}` sites this is the layer `V⁽ʲ⁺²⁾` of
the tree (`MPSPreparation.mergeIso_two_pow`).

The blocked tensor `Kraus.block A n` is indexed by the configurations of the sites of the
block, so its partial isometry is read on them, which is how the circuits act on it.

## Main definitions

* `MPSPreparation.pairProductTensor` — the tensor `(a, b) ↦ X^a Y^b` of two neighbouring sites.
* `MPSPreparation.mergeIso` — the partial isometry `W` joining blocks of `n₁` and `n₂` sites.

## Main results

* `MPSPreparation.polarIsoMatrix_block_append`, `MPSPreparation.polarIsoMatrix_block_split` —
  `V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`, for every tensor.
* `MPSPreparation.polarPosTensor_block_add` — `P_{n₁+n₂}` is the positive part of the
  tensor `(a, b) ↦ P₁^a P₂^b`.
* `MPSPreparation.pairProductTensor_self`, `MPSPreparation.mergeIso_self` — for halves of equal
  lengths, `W` is the partial isometry of the two-site blocked tensor of `P_n`.
* `MPSPreparation.polarPosTensor_block_two_pow`, `MPSPreparation.mergeIso_two_pow` —
  for halves of `2^{j+1}` sites, `W` is the layer `V⁽ʲ⁺²⁾` of the tree of eq. (16).
* `MPSPreparation.isIsometry_mergeIso` — `W` is an isometry when `A` blocked over `n₁ + n₂`
  sites is injective.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16), and the paragraph "Approximation
  through the fixed-point state" (the polar decomposition `B = V P`).

## Polar isometries as trees of uniformly bounded leaves

Suppose all blocks of length at least `s` are injective. A block of any length `n`
between `2^h s` and `2^h c` has a binary tree of `h` coarse layers, with every physical
leaf between `s` and `c` sites. Repeatedly split a block into its floor and ceiling
halves. The polar-merge identity identifies the resulting tree with the polar
isometry of the original block. Vertex tensors may differ even at the same depth.

This extends the tree in arXiv:2307.01696, eq. (16), to unequal block lengths;
the physical leaf bound is independent of the total length and the requested accuracy.
-/

section

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d D : ℕ}

/-! ### Two neighbouring sites carrying different tensors -/

/-- The tensor of two neighbouring sites carrying `X` and `Y`: `(a, b) ↦ X^a Y^b`. For `X = Y`
it is the two-site blocked tensor of `X`. -/
noncomputable def pairProductTensor {κ : ℕ} (X Y : MPSTensor κ D) :
    MPTensor (Fin 2 → Fin κ) (Fin D) :=
  fun e => X (e 0) * Y (e 1)

/-- The partial isometry `W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` joining a block of `n₁` sites to the
block of `n₂` sites after it: the partial isometry of the polar decomposition of the tensor
`(a, b) ↦ P₁^a P₂^b`, with `P₁` and `P₂` the positive parts of `A` blocked over `n₁` and `n₂` sites.

arXiv:2307.01696, eq. (16): the isometries `V⁽ʲ⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` of the tree, here
for halves of unequal lengths. -/
noncomputable def mergeIso (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    Matrix (Fin 2 → Fin (D * D)) (Fin (D * D)) ℂ :=
  polarIsoMatrix (pairProductTensor (polarPosTensor (Kraus.block A n₁))
    (polarPosTensor (Kraus.block A n₂)))

/-! ### Blocking two halves -/

/-- A block of `n₁ + n₂` sites carries the product of the blocked tensors of its halves. -/
theorem block_add_apply (A : MPSTensor d D) (n₁ n₂ : ℕ) (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) :
    Kraus.block A (n₁ + n₂) (Fin.append τ₁ τ₂) =
      Kraus.block A n₁ τ₁ * Kraus.block A n₂ τ₂ := by
  simp only [Kraus.block_apply, List.ofFn_fin_append, Kraus.evalWord_append]

/-- The equivalence of the configurations of a block with the pairs of configurations of its
halves. -/
private noncomputable def splitEquiv (d n₁ n₂ : ℕ) :
    (Fin (n₁ + n₂) → Fin d) ≃ (Fin n₁ → Fin d) × (Fin n₂ → Fin d) :=
  (Fin.appendEquiv n₁ n₂).symm

/-- The pairs of indices of `ℂ^{D²} ⊗ ℂ^{D²}`, read on two-site configurations. -/
private noncomputable def pairEquiv (κ : ℕ) : (Fin 2 → Fin κ) ≃ Fin κ × Fin κ :=
  piFinTwoEquiv fun _ => Fin κ

private theorem splitEquiv_symm_apply (n₁ n₂ : ℕ) (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) :
    (splitEquiv d n₁ n₂).symm (τ₁, τ₂) = Fin.append τ₁ τ₂ := by
  simp [splitEquiv, Fin.appendEquiv]

private theorem block_splitEquiv (A : MPSTensor d D) (n₁ n₂ : ℕ)
    (I : (Fin (n₁ + n₂) → Fin d)) :
    Kraus.block A (n₁ + n₂) I =
      Kraus.block A n₁ (splitEquiv d n₁ n₂ I).1 * Kraus.block A n₂ (splitEquiv d n₁ n₂ I).2 := by
  obtain ⟨⟨τ₁, τ₂⟩, rfl⟩ := (splitEquiv d n₁ n₂).symm.surjective I
  rw [Equiv.apply_symm_apply, splitEquiv_symm_apply, block_add_apply]

private theorem pairEquiv_fst {κ : ℕ} (e : (Fin 2 → Fin κ)) :
    (pairEquiv κ e).1 = e 0 := rfl

private theorem pairEquiv_snd {κ : ℕ} (e : (Fin 2 → Fin κ)) :
    (pairEquiv κ e).2 = e 1 := rfl

/-- A tensor read through its polar decomposition: `B^a = ∑_y ⟨a|V|y⟩ P^y`. -/
private theorem eq_sum_polarIsoMatrix_smul {m : ℕ} (B : MPSTensor m D) (a : Fin m) :
    B a = ∑ y, polarIsoMatrix B a y • polarPosTensor B y := by
  conv_lhs => rw [← rotatePhysical_polarIsoMatrix_polarPosTensor B]
  rfl

/-- The Kronecker product `V₁ ⊗ V₂` of maps into the halves of a block, read on blocked
indices. -/
private noncomputable def splitKron {κ n₁ n₂ : ℕ} (V₁ : Matrix (Fin n₁ → Fin d) (Fin κ) ℂ)
    (V₂ : Matrix (Fin n₂ → Fin d) (Fin κ) ℂ) :
    Matrix (Fin (n₁ + n₂) → Fin d) (Fin 2 → Fin κ) ℂ :=
  fun I e => V₁ (splitEquiv d n₁ n₂ I).1 (pairEquiv κ e).1 *
    V₂ (splitEquiv d n₁ n₂ I).2 (pairEquiv κ e).2

/-- The Kronecker product `E₁ ⊗ E₂` of two square matrices, read on two-site blocked
indices. -/
private noncomputable def pairKron {κ : ℕ} (E₁ E₂ : Matrix (Fin κ) (Fin κ) ℂ) :
    Matrix (Fin 2 → Fin κ) (Fin 2 → Fin κ) ℂ :=
  fun e e' => E₁ (pairEquiv κ e).1 (pairEquiv κ e').1 * E₂ (pairEquiv κ e).2 (pairEquiv κ e').2

/-- `(V₁ ⊗ V₂)ᴴ (V₁ ⊗ V₂) = V₁ᴴ V₁ ⊗ V₂ᴴ V₂`. -/
private theorem conjTranspose_splitKron_mul_self {κ n₁ n₂ : ℕ}
    (V₁ : Matrix (Fin n₁ → Fin d) (Fin κ) ℂ)
    (V₂ : Matrix (Fin n₂ → Fin d) (Fin κ) ℂ) :
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
private theorem physicalMatrix_block_add (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    physicalMatrix (Kraus.block A (n₁ + n₂)) =
      splitKron (polarIsoMatrix (Kraus.block A n₁)) (polarIsoMatrix (Kraus.block A n₂)) *
        physicalMatrix (pairProductTensor (polarPosTensor (Kraus.block A n₁))
          (polarPosTensor (Kraus.block A n₂))) := by
  ext I ⟨α, β⟩
  simp only [physicalMatrix, Matrix.mul_apply]
  rw [block_splitEquiv, eq_sum_polarIsoMatrix_smul (Kraus.block A n₁),
    eq_sum_polarIsoMatrix_smul (Kraus.block A n₂), Finset.sum_mul_sum,
    ← (pairEquiv (D * D)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.sum_apply, smul_mul_smul_comm, Matrix.smul_apply, smul_eq_mul, splitKron,
    Equiv.apply_symm_apply, pairProductTensor, ← pairEquiv_fst, ← pairEquiv_snd]

/-- `B_{n₁+n₂} = (V₁ ⊗ V₂) · C`, with `C` the tensor `(a, b) ↦ P₁^a P₂^b`, and
`(V₁ ⊗ V₂)ᴴ (V₁ ⊗ V₂)` fixes `C`; so `V_{n₁+n₂} = (V₁ ⊗ V₂) W` and `C` has the positive part
of `B_{n₁+n₂}`. -/
private theorem block_add_eq_rotatePhysical (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    Kraus.block A (n₁ + n₂) =
        rotatePhysical
          (splitKron (polarIsoMatrix (Kraus.block A n₁)) (polarIsoMatrix (Kraus.block A n₂)))
          (pairProductTensor (polarPosTensor (Kraus.block A n₁))
            (polarPosTensor (Kraus.block A n₂))) ∧
      rotatePhysical
          ((splitKron (polarIsoMatrix (Kraus.block A n₁)) (polarIsoMatrix (Kraus.block A n₂)))ᴴ *
            splitKron (polarIsoMatrix (Kraus.block A n₁)) (polarIsoMatrix (Kraus.block A n₂)))
          (pairProductTensor (polarPosTensor (Kraus.block A n₁))
            (polarPosTensor (Kraus.block A n₂))) =
        pairProductTensor (polarPosTensor (Kraus.block A n₁))
          (polarPosTensor (Kraus.block A n₂)) := by
  refine ⟨physicalMatrix_injective ?_, ?_⟩
  · rw [physicalMatrix_rotatePhysical]
    exact physicalMatrix_block_add A n₁ n₂
  · rw [conjTranspose_splitKron_mul_self, rotatePhysical_pairKron_pairProductTensor,
      conjTranspose_polarIsoMatrix_mul_polarIsoMatrix,
      conjTranspose_polarIsoMatrix_mul_polarIsoMatrix, rotatePhysical_polarSupportMatrix,
      rotatePhysical_polarSupportMatrix]

/-- **The partial isometry of a block of unequal halves** (arXiv:2307.01696, eq. (16), for halves of
lengths `n₁` and `n₂`): `V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`, with `W = mergeIso A n₁ n₂`:

  `⟨τ₁ τ₂| V_{n₁+n₂} |x⟩ = ∑ₑ ⟨τ₁| V_{n₁} |e₀⟩ ⟨τ₂| V_{n₂} |e₁⟩ ⟨e₀ e₁| W |x⟩`.

No injectivity is assumed. The proof writes `B_{n₁+n₂} = (V₁ ⊗ V₂) C`, with `C` the tensor
`(a, b) ↦ P₁^a P₂^b`. The initial projector `Π₁ ⊗ Π₂` of `V₁ ⊗ V₂` fixes `C`, so the partial
isometry of `B_{n₁+n₂}` is `V₁ ⊗ V₂` times that of `C` (`MPSTensor.polarIsoMatrix_rotatePhysical`).
The source leaves this identification implicit ("to the same effect"); its footnote to "The
sequential-RG circuit" states that the derivation holds for non-injective tensors. -/
theorem polarIsoMatrix_block_append (A : MPSTensor d D) {n₁ n₂ : ℕ} (τ₁ : Cfg d n₁)
    (τ₂ : Cfg d n₂) (x : Fin (D * D)) :
    polarIsoMatrix (Kraus.block A (n₁ + n₂)) (Fin.append τ₁ τ₂) x =
      ∑ e, polarIsoMatrix (Kraus.block A n₁) τ₁ (e 0) *
        polarIsoMatrix (Kraus.block A n₂) τ₂ (e 1) * mergeIso A n₁ n₂ e x := by
  obtain ⟨hB, hfix⟩ := block_add_eq_rotatePhysical A n₁ n₂
  have hiso := congrFun (congrFun (congrArg polarIsoMatrix hB)
    (Fin.append τ₁ τ₂)) x
  rw [polarIsoMatrix_rotatePhysical hfix, Matrix.mul_apply] at hiso
  refine hiso.trans ?_
  have hσ : splitEquiv d n₁ n₂ (Fin.append τ₁ τ₂) =
      (τ₁, τ₂) := by
    rw [← splitEquiv_symm_apply, Equiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [splitKron, hσ, pairEquiv_fst, pairEquiv_snd]
  rfl

/-- **The partial isometry of a block of unequal halves**, for a block of `n = n₁ + n₂` sites:
`polarIsoMatrix_block_append` with the halves read off a configuration `τ` of the block. -/
theorem polarIsoMatrix_block_split (A : MPSTensor d D) {n₁ n₂ n : ℕ} (hn : n₁ + n₂ = n)
    (τ : Cfg d n) (x : Fin (D * D)) :
    polarIsoMatrix (Kraus.block A n) τ x =
      ∑ e, polarIsoMatrix (Kraus.block A n₁) (fun i => τ ⟨i.val, by omega⟩) (e 0) *
        polarIsoMatrix (Kraus.block A n₂) (fun i => τ ⟨n₁ + i.val, by omega⟩) (e 1) *
          mergeIso A n₁ n₂ e x := by
  subst hn
  have hτ : Fin.append (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
      (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) = τ := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  have h := polarIsoMatrix_block_append A (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
    (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) x
  rwa [hτ] at h

/-- **The positive part of a block of unequal halves**: the positive part of `A` blocked over
`n₁ + n₂` sites is the positive part of the tensor `(a, b) ↦ P₁^a P₂^b` of the positive parts of
its halves. No injectivity is assumed.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"), for halves of
unequal lengths. -/
theorem polarPosTensor_block_add (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    polarPosTensor (Kraus.block A (n₁ + n₂)) =
      polarPosTensor (pairProductTensor (polarPosTensor (Kraus.block A n₁))
        (polarPosTensor (Kraus.block A n₂))) := by
  obtain ⟨hB, hfix⟩ := block_add_eq_rotatePhysical A n₁ n₂
  rw [hB, polarPosTensor_rotatePhysical hfix]

/-- On two neighbouring sites carrying the same tensor, `(a, b) ↦ X^a X^b` is the two-site
blocked tensor of `X`. -/
theorem pairProductTensor_self {κ : ℕ} (X : MPSTensor κ D) :
    pairProductTensor X X = Kraus.block X 2 := by
  funext e
  simp [pairProductTensor, Kraus.block_apply, List.ofFn_succ]

/-- **Halves of equal lengths**: joining two blocks of `n` sites, `W` is the partial isometry
of the two-site blocked tensor of the positive part `P_n`. For `n = 2^{j+1}` this is the layer
`V⁽ʲ⁺²⁾` of arXiv:2307.01696, eq. (16) (`mergeIso_two_pow`). -/
theorem mergeIso_self (A : MPSTensor d D) (n : ℕ) :
    mergeIso A n n = polarIsoMatrix (Kraus.block (polarPosTensor (Kraus.block A n)) 2) := by
  rw [mergeIso, pairProductTensor_self]

/-- If `A` blocked over `n₁ + n₂` sites is injective, so is the tensor `(a, b) ↦ P₁^a P₂^b` of
the positive parts of its halves: its matrices span those of the blocked tensor. -/
theorem isInjective_pairProductTensor (A : MPSTensor d D) {n₁ n₂ : ℕ}
    (h : Kraus.IsInjective (Kraus.block A (n₁ + n₂))) :
    Kraus.IsInjective (pairProductTensor (polarPosTensor (Kraus.block A n₁))
      (polarPosTensor (Kraus.block A n₂))) := by
  classical
  refine eq_top_iff.mpr (h.symm.le.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨I, rfl⟩
  rw [SetLike.mem_coe, block_splitEquiv, eq_sum_polarIsoMatrix_smul (Kraus.block A n₁),
    eq_sum_polarIsoMatrix_smul (Kraus.block A n₂), Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun y₁ _ => Submodule.sum_mem _ fun y₂ _ => ?_
  rw [smul_mul_smul_comm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(pairEquiv (D * D)).symm (y₁, y₂), ?_⟩)
  simp [pairProductTensor, pairEquiv, piFinTwoEquiv]

/-- The partial isometry `W` joining two blocks is an isometry when `A` blocked over the joined
block is injective. -/
theorem isIsometry_mergeIso (A : MPSTensor d D) {n₁ n₂ : ℕ}
    (h : Kraus.IsInjective (Kraus.block A (n₁ + n₂))) : (mergeIso A n₁ n₂).IsIsometry :=
  isIsometry_polarIsoMatrix_of_isInjective (isInjective_pairProductTensor A h)

/-- **The positive parts along the tree**: the positive part `P_{2^{j+1}}` of `A` blocked over
`2^{j+1}` sites is the tensor `T_{j+1}` of the tree, obtained by taking `j + 1` times the positive
part of the two-site blocked tensor. Each step is `polarPosTensor_block_add` for halves of
equal lengths.

arXiv:2307.01696, eq. (16) and the sentence before it ("to the same effect"). -/
theorem polarPosTensor_block_two_pow (A : MPSTensor d D) (j : ℕ) :
    polarPosTensor (Kraus.block A (2 ^ (j + 1))) =
      (pairPosTensor : MPSTensor (D * D) D → MPSTensor (D * D) D)^[j] (pairPosTensor A) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ← ih,
        show 2 ^ (j + 1 + 1) = 2 ^ (j + 1) + 2 ^ (j + 1) by ring, polarPosTensor_block_add,
        pairProductTensor_self]
      rfl

/-- **The layers of the tree as merges**: for halves of `2^{j+1}` sites, `W` is the layer
`V⁽ʲ⁺²⁾` of the tree-RG circuit, the partial isometry of the two-site blocked tensor of
`T_{j+1}`.

arXiv:2307.01696, eq. (16). -/
theorem mergeIso_two_pow (A : MPSTensor d D) {k : ℕ} (j : Fin k) :
    mergeIso A (2 ^ (j.val + 1)) (2 ^ (j.val + 1)) = treeLayers k A j := by
  rw [mergeIso_self, polarPosTensor_block_two_pow]
  rfl

end MPSPreparation

end

section

open Matrix MPSTensor

namespace MPSPreparation

/-- **A bounded-leaf polar tree for an arbitrary block length.** If every block of length
at least `s > 0` is injective and `2^h s ≤ n ≤ 2^h c`, the polar isometry of the block
has an `h`-layer binary tree whose leaves have at most `c` sites.

Source: arXiv:2307.01696, eq. (16), using the polar merge identity for unequal halves. -/
theorem exists_isometryTree_matrix_eq_polarIsoMatrix_block {d D s : ℕ} (A : MPSTensor d D)
    (hs : 0 < s) (hinj : ∀ m, s ≤ m → Kraus.IsInjective (Kraus.block A m))
    (h n c : ℕ) (hlower : 2 ^ h * s ≤ n) (hupper : n ≤ 2 ^ h * c) :
    ∃ T : IsometryTree d (D * D) c h n, T.matrix = polarIsoMatrix (Kraus.block A n) := by
  induction h generalizing n with
  | zero =>
    have hsn : s ≤ n := by simpa using hlower
    exact ⟨.leaf (polarIsoMatrix (Kraus.block A n))
      (isIsometry_polarIsoMatrix_of_isInjective (hinj n hsn))
      (hs.trans_le hsn) (by simpa using hupper), rfl⟩
  | succ h ih =>
    have hlo : 2 * (2 ^ h * s) ≤ n := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlower
    have hhi : n ≤ 2 * (2 ^ h * c) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hupper
    have hsum : n / 2 + (n - n / 2) = n := by omega
    obtain ⟨T₁, hT₁⟩ := ih (n / 2) (by omega) (by omega)
    obtain ⟨T₂, hT₂⟩ := ih (n - n / 2) (by omega) (by omega)
    have hsn : s ≤ n :=
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (h + 1))).trans hlower
    have hW : (mergeIso A (n / 2) (n - n / 2)).IsIsometry := by
      apply isIsometry_mergeIso A
      rw [hsum]
      exact hinj n hsn
    refine ⟨(IsometryTree.fork T₁ T₂ (mergeIso A (n / 2) (n - n / 2)) hW).cast hsum, ?_⟩
    ext τ x
    rw [IsometryTree.matrix_cast, IsometryTree.matrix_fork_apply, hT₁, hT₂]
    exact (polarIsoMatrix_block_split A hsum τ x).symm

end MPSPreparation

end
