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
`B_{n₂} = V₂ P₂` are injective, then

  `V_{n₁+n₂} = (V₁ ⊗ V₂) W`,

where `W : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` is the isometry of the polar decomposition of the tensor
`(a, b) ↦ P₁^a P₂^b` of two neighbouring sites carrying the positive parts
(`MPSPreparation.cfgPolarIso_append`). The proof is uniqueness of the polar decomposition
(`Matrix.polarIso_eq_of_eq_mul`), as for blocks of equal halves.

The isometries are read on configurations of the sites of a block
(`MPSPreparation.cfgPolarIso`), which is how the circuits act on them.

## Main definitions

* `MPSPreparation.pairProductTensor` — the tensor `(a, b) ↦ X^a Y^b` of two neighbouring sites.
* `MPSPreparation.cfgPolarIso` — the isometry `V_n` of `A` blocked over `n` sites, on
  configurations.
* `MPSPreparation.mergeIso` — the isometry `W` joining blocks of `n₁` and `n₂` sites.

## Main results

* `MPSPreparation.cfgPolarIso_append`, `MPSPreparation.cfgPolarIso_split` —
  `V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`.
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
`n₂` sites after it: the isometry of the polar decomposition of the tensor `(a, b) ↦ P₁^a P₂^b`,
with `P₁` and `P₂` the positive parts of `A` blocked over `n₁` and `n₂` sites.

arXiv:2307.01696, eq. (16): the isometries `V⁽ʲ⁾ : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` of the tree, here
for halves of unequal lengths. -/
noncomputable def mergeIso (A : MPSTensor d D) (n₁ n₂ : ℕ) :
    Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ :=
  polarIsoMatrix (pairProductTensor (polarPosTensor (blockTensor A n₁))
    (polarPosTensor (blockTensor A n₂)))

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

private theorem conjTranspose_splitKron_mul_self {κ n₁ n₂ : ℕ}
    {V₁ : Matrix (Fin (blockPhysDim d n₁)) (Fin κ) ℂ}
    {V₂ : Matrix (Fin (blockPhysDim d n₂)) (Fin κ) ℂ} (hV₁ : V₁.IsIsometry)
    (hV₂ : V₂.IsIsometry) : (splitKron V₁ V₂)ᴴ * splitKron V₁ V₂ = 1 := by
  classical
  ext e e'
  set u := (pairEquiv κ e).1
  set v := (pairEquiv κ e).2
  set u' := (pairEquiv κ e').1
  set v' := (pairEquiv κ e').2
  have h₁ := congrFun (congrFun hV₁ u) u'
  have h₂ := congrFun (congrFun hV₂ v) v'
  rw [Matrix.mul_apply] at h₁ h₂ ⊢
  simp only [conjTranspose_apply] at h₁ h₂ ⊢
  have hsum : ∑ I, star (splitKron V₁ V₂ I e) * splitKron V₁ V₂ I e' =
      (∑ a, star (V₁ a u) * V₁ a u') * ∑ b, star (V₂ b v) * V₂ b v' := by
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (splitEquiv d n₁ n₂) _ _ fun I => ?_
    simp only [splitKron, star_mul']
    ring
  rw [hsum, h₁, h₂, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : e = e'
  · subst h; simp [u, u', v, v']
  · have hne : (u, v) ≠ (u', v') := fun hc => h ((pairEquiv κ).injective (by
      simpa [u, v, u', v'] using hc))
    rw [ite_eq_right_iff.mpr fun h' => absurd h' h]
    by_cases hu : u = u'
    · have hv : v ≠ v' := fun hv => hne (by rw [hu, hv])
      rw [ite_eq_right_iff.mpr fun h' => absurd h' hv, mul_zero]
    · rw [ite_eq_right_iff.mpr fun h' => absurd h' hu, zero_mul]

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

/-- **The isometry of a block of unequal halves** (arXiv:2307.01696, eq. (16), for halves of
lengths `n₁` and `n₂`). If `A` blocked over `n₁` and over `n₂` sites is injective, then
`V_{n₁+n₂} = (V_{n₁} ⊗ V_{n₂}) W`, with `W = mergeIso A n₁ n₂`:

  `⟨τ₁ τ₂| V_{n₁+n₂} |x⟩ = ∑ₑ ⟨τ₁| V_{n₁} |e₀⟩ ⟨τ₂| V_{n₂} |e₁⟩ ⟨e₀ e₁| W |x⟩`.

The proof writes `B_{n₁+n₂} = (V₁ ⊗ V₂) W Q`, with `Q` the positive part of the tensor
`(a, b) ↦ P₁^a P₂^b`, and identifies `(V₁ ⊗ V₂) W` with `V_{n₁+n₂}` by uniqueness of the polar
decomposition; the source leaves this identification implicit ("to the same effect"). -/
theorem cfgPolarIso_append (A : MPSTensor d D) {n₁ n₂ : ℕ}
    (h₁ : Kraus.IsInjective (blockTensor A n₁)) (h₂ : Kraus.IsInjective (blockTensor A n₂))
    (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) (x : Fin (D * D)) :
    cfgPolarIso A (n₁ + n₂) (Fin.append τ₁ τ₂) x =
      ∑ e, cfgPolarIso A n₁ τ₁ (decodeBlock _ 2 e 0) * cfgPolarIso A n₂ τ₂ (decodeBlock _ 2 e 1) *
        mergeIso A n₁ n₂ e x := by
  classical
  set C := pairProductTensor (polarPosTensor (blockTensor A n₁))
    (polarPosTensor (blockTensor A n₂))
  set K := splitKron (polarIsoMatrix (blockTensor A n₁)) (polarIsoMatrix (blockTensor A n₂))
  have hK : Kᴴ * K = 1 := conjTranspose_splitKron_mul_self
    (isIsometry_polarIsoMatrix_of_isInjective h₁) (isIsometry_polarIsoMatrix_of_isInjective h₂)
  have hM : physicalMatrix (blockTensor A (n₁ + n₂)) =
      (K * Matrix.polarIso (physicalMatrix C)) * Matrix.polarPos (physicalMatrix C) := by
    rw [Matrix.mul_assoc, Matrix.polarIso_mul_polarPos]
    exact physicalMatrix_blockTensor_add A n₁ n₂
  have hW : (K * Matrix.polarIso (physicalMatrix C))ᴴ * (K * Matrix.polarIso (physicalMatrix C)) =
      Matrix.polarSupport (physicalMatrix C) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ, hK, Matrix.one_mul,
      Matrix.conjTranspose_polarIso_mul_polarIso]
  have hiso := Matrix.polarIso_eq_of_eq_mul hM (Matrix.posSemidef_polarPos _) hW
    (Matrix.isHermitian_polarSupport _) (Matrix.polarSupport_mul_polarSupport _)
    (Matrix.range_polarSupport _)
  have hx := congrFun (congrFun hiso ((decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂)))
    (virtualPairEquiv D x)
  rw [Matrix.mul_apply] at hx
  refine hx.trans ?_
  have hσ : splitEquiv d n₁ n₂ ((decodeBlockEquiv d (n₁ + n₂)).symm (Fin.append τ₁ τ₂)) =
      ((decodeBlockEquiv d n₁).symm τ₁, (decodeBlockEquiv d n₂).symm τ₂) := by
    rw [← splitEquiv_symm_apply, Equiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [K, splitKron, hσ, pairEquiv_fst, pairEquiv_snd]
  rfl

/-- **The isometry of a block of unequal halves**, for a block of `n = n₁ + n₂` sites:
`cfgPolarIso_append` with the halves read off a configuration `τ` of the block. -/
theorem cfgPolarIso_split (A : MPSTensor d D) {n₁ n₂ n : ℕ} (hn : n₁ + n₂ = n)
    (h₁ : Kraus.IsInjective (blockTensor A n₁)) (h₂ : Kraus.IsInjective (blockTensor A n₂))
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
  have h := cfgPolarIso_append A h₁ h₂ (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
    (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) x
  rwa [hτ] at h

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
