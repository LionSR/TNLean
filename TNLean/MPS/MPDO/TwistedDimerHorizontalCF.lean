/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.PEquiv
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.TwistedDimer

/-!
# The horizontal canonical form of the twisted quantum dimer

**Scope: one-site literal canonical form.** The doubled-index tensor of the
$\mathbb Z_2$-twisted quantum dimer `T` of `TNLean.MPS.MPDO.TwistedDimer` (a
project example, not a tensor stated in the source) is written in the literal
canonical form of arXiv:1606.00608, Section 2.3, lines 214--245 and eq.
`II_CF1`. The two retained normal tensors are the displayed horizontal blocks
`block 0`, `block 1` of bond dimension four, each rescaled by $8/5$ so that
its ket-against-bra letters resolve the identity; both carry the weight
$\mu = 5/8$. The ambient coisometry is the permutation of the bond index
$(p, p', k)$ into the block label $k$ followed by the block bond index
$(p, p')$.

Only the one-site statement is made here. Blocking, the resulting BNT sector
presentation, and non-simplicity of the tensor are treated in
`TNLean.MPS.MPDO.TwistedDimerNotSimple`.

## Main results

* `normalizedBlock_toMPSTensor_isInjective` — the letters of each rescaled
  block span the full bond matrix algebra;
* `normalizedBlock_isLeftCanonical` — the ket-against-bra letters of each
  rescaled block resolve the identity;
* `normalizedBlock_isNormalTensor` — each rescaled block is a normal tensor;
* `canonicalFormData` — the literal canonical-form data of the doubled-index
  tensor with the two rescaled blocks and the weight $5/8$;
* `physTraceTransfer_normalizedBlock_one` — the rescaled block $k = 1$ has
  vanishing physical-trace transfer.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 2.3, lines 214--245 and eq. `II_CF1` (project example, not a
  tensor stated in the source)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### The rescaled horizontal blocks -/

/-- The horizontal block `k` of the twisted dimer rescaled by $8/5$: the
letter at the pair `(i, j)` is the matrix unit of `block k` with coefficient
$\tfrac85\,$`coef k i j`. The rescaling makes the ket-against-bra letters
resolve the identity (`normalizedBlock_isLeftCanonical`), which is the
spectral normalization of arXiv:1606.00608, lines 224--235, for this project
example. -/
def normalizedBlock (k : Fin 2) : MPOTensor 8 4 := fun i j => (8 / 5 : ℂ) • block k i j

lemma normalizedBlock_apply (k : Fin 2) (i j : Fin 8) :
    normalizedBlock k i j =
      Matrix.single (finProdFinEquiv (bitL i, bitL j)) (finProdFinEquiv (bitR i, bitR j))
        ((8 / 5 : ℂ) * coef k i j) := by
  simp [normalizedBlock, block]

/-- The doubled-index letter at `finProdFinEquiv (i, j)` is the MPO letter at `(i, j)`. -/
lemma toMPSTensor_apply_finProdFinEquiv {d D : ℕ} (M : MPOTensor d D) (i j : Fin d) :
    M.toMPSTensor (finProdFinEquiv (i, j)) = M i j := by
  unfold MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- At flag value zero every coefficient of a block is nonzero: it is one of
$\tfrac14$ and $\tfrac3{16}$. -/
lemma coef_flag_zero_ne_zero (k p q p' q' : Fin 2) :
    coef k (physIdx p q 0) (physIdx p' q' 0) ≠ 0 := by
  rw [coef_physIdx, ite_eq_left rfl]
  fin_cases k <;> fin_cases p <;> fin_cases p' <;> norm_num [Cmat, tau, cDiag_eq, cOff_eq]

/-- **The letters of a horizontal block span the bond matrix algebra.** The
matrix unit at the bond pair $((p,p'),(q,q'))$ is a nonzero multiple of the
letter at the physical pair $((p,q,0),(p',q',0))$. -/
theorem block_toMPSTensor_isInjective (k : Fin 2) :
    Kraus.IsInjective (block k).toMPSTensor := by
  unfold Kraus.IsInjective
  apply le_antisymm le_top
  rw [← (Matrix.stdBasis ℂ (Fin 4) (Fin 4)).span_eq]
  apply Submodule.span_le.mpr
  rintro M ⟨⟨a, b⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single]
  obtain ⟨p, p', rfl⟩ : ∃ p p', a = finProdFinEquiv (p, p') :=
    ⟨((finProdFinEquiv (m := 2) (n := 2)).symm a).1,
      ((finProdFinEquiv (m := 2) (n := 2)).symm a).2, by simp⟩
  obtain ⟨q, q', rfl⟩ : ∃ q q', b = finProdFinEquiv (q, q') :=
    ⟨((finProdFinEquiv (m := 2) (n := 2)).symm b).1,
      ((finProdFinEquiv (m := 2) (n := 2)).symm b).2, by simp⟩
  have hmem : block k (physIdx p q 0) (physIdx p' q' 0) ∈
      Submodule.span ℂ (Set.range (block k).toMPSTensor) := by
    rw [← toMPSTensor_apply_finProdFinEquiv (block k)]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hblock : block k (physIdx p q 0) (physIdx p' q' 0) =
      coef k (physIdx p q 0) (physIdx p' q' 0) •
        Matrix.single (finProdFinEquiv (p, p')) (finProdFinEquiv (q, q')) (1 : ℂ) := by
    simp [block]
  rw [hblock] at hmem
  have hscaled := Submodule.smul_mem _ (coef k (physIdx p q 0) (physIdx p' q' 0))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ (coef_flag_zero_ne_zero k p q p' q'), one_smul] at hscaled

/-- The letters of a rescaled block span the bond matrix algebra. -/
theorem normalizedBlock_toMPSTensor_isInjective (k : Fin 2) :
    Kraus.IsInjective (normalizedBlock k).toMPSTensor := by
  have h : (normalizedBlock k).toMPSTensor = fun v => (8 / 5 : ℂ) • (block k).toMPSTensor v := rfl
  rw [h]
  exact (block_toMPSTensor_isInjective k).smul (by norm_num)

/-! ### The ket-against-bra letters resolve the identity -/

/-- Every coefficient of the twisted dimer is real. -/
lemma star_coef (k : Fin 2) (i j : Fin 8) : star (coef k i j) = coef k i j := by
  unfold coef
  split_ifs <;> simp [Complex.conj_ofReal]

/-- The ket-against-bra product of one letter of a rescaled block is the
matrix unit at the right bits with the squared coefficient. -/
lemma conjTranspose_mul_self_normalizedBlock (k : Fin 2) (i j : Fin 8) :
    (normalizedBlock k i j)ᴴ * normalizedBlock k i j =
      Matrix.single (finProdFinEquiv (bitR i, bitR j)) (finProdFinEquiv (bitR i, bitR j))
        (((8 / 5 : ℂ) * coef k i j) ^ 2) := by
  rw [normalizedBlock_apply, Matrix.conjTranspose_single, Matrix.single_mul_single_same,
    star_mul', star_coef, sq]
  have h : star (8 / 5 : ℂ) = 8 / 5 := by simp
  rw [h]

/-- The bit encoding of the physical index with the right bit first. -/
def rightBitEquiv : Fin 2 × (Fin 2 × Fin 2) ≃ Fin 8 where
  toFun x := physIdx x.2.1 x.1 x.2.2
  invFun i := (bitR i, (bitL i, bitF i))
  left_inv := by rintro ⟨r, l, f⟩; simp
  right_inv i := physIdx_bits i

/-- A finite sum of matrix units at one position is the matrix unit of the sum. -/
lemma sum_single_eq_single_sum {ι m n : Type*} [DecidableEq m] [DecidableEq n]
    (s : Finset ι) (a : m) (b : n) (c : ι → ℂ) :
    ∑ x ∈ s, Matrix.single a b (c x) = Matrix.single a b (∑ x ∈ s, c x) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j <;> simp [h]

/-- For fixed right bits, the squared rescaled coefficients sum to one:
$\tfrac{64}{25}\cdot 2 \cdot \tfrac14\,(2\,C_k[0,0]^2 + 2\,C_k[0,1]^2) = 1$. -/
lemma sum_normalizedCoef_sq (k r r' : Fin 2) :
    ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2,
      ((8 / 5 : ℂ) * coef k (physIdx x.1 r x.2) (physIdx y.1 r' y.2)) ^ 2 = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, coef_physIdx]
  fin_cases k <;> norm_num [Cmat, tau, cDiag_eq, cOff_eq]

/-- **The ket-against-bra letters of a rescaled block resolve the identity.**
Grouping the letters by the right bits of their two physical indices, the
matrix units at $((r,r'),(r,r'))$ carry the coefficient sum of
`sum_normalizedCoef_sq`. -/
theorem normalizedBlock_isLeftCanonical (k : Fin 2) :
    MPSTensor.IsLeftCanonical (normalizedBlock k).toMPSTensor := by
  let c : Fin 8 → Fin 8 → ℂ := fun i j => ((8 / 5 : ℂ) * coef k i j) ^ 2
  have hterm : ∀ i j : Fin 8,
      ((normalizedBlock k).toMPSTensor (finProdFinEquiv (i, j)))ᴴ *
        (normalizedBlock k).toMPSTensor (finProdFinEquiv (i, j)) =
      Matrix.single (finProdFinEquiv (bitR i, bitR j)) (finProdFinEquiv (bitR i, bitR j))
        (c i j) := by
    intro i j
    rw [toMPSTensor_apply_finProdFinEquiv, conjTranspose_mul_self_normalizedBlock]
  change ∑ v : Fin (8 * 8),
    ((normalizedBlock k).toMPSTensor v)ᴴ * (normalizedBlock k).toMPSTensor v = 1
  rw [← (finProdFinEquiv : Fin 8 × Fin 8 ≃ Fin (8 * 8)).sum_comp, Fintype.sum_prod_type]
  simp only [hterm]
  rw [← rightBitEquiv.sum_comp, Fintype.sum_prod_type]
  have hrow : ∀ (r : Fin 2) (x : Fin 2 × Fin 2),
      ∑ j : Fin 8, Matrix.single (finProdFinEquiv (bitR (rightBitEquiv (r, x)), bitR j))
        (finProdFinEquiv (bitR (rightBitEquiv (r, x)), bitR j)) (c (rightBitEquiv (r, x)) j) =
      ∑ r' : Fin 2, Matrix.single (finProdFinEquiv (r, r')) (finProdFinEquiv (r, r'))
        (∑ y : Fin 2 × Fin 2, c (physIdx x.1 r x.2) (physIdx y.1 r' y.2)) := by
    intro r x
    rw [← rightBitEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [rightBitEquiv, Equiv.coe_fn_mk, bitR_physIdx]
    exact Finset.sum_congr rfl fun r' _ => sum_single_eq_single_sum _ _ _ _
  simp only [hrow]
  have hswap : ∀ r : Fin 2,
      ∑ x : Fin 2 × Fin 2, ∑ r' : Fin 2,
        Matrix.single (finProdFinEquiv (r, r')) (finProdFinEquiv (r, r'))
          (∑ y : Fin 2 × Fin 2, c (physIdx x.1 r x.2) (physIdx y.1 r' y.2)) =
      ∑ r' : Fin 2, Matrix.single (finProdFinEquiv (r, r')) (finProdFinEquiv (r, r')) (1 : ℂ) := by
    intro r
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [sum_single_eq_single_sum]
    congr 1
    exact sum_normalizedCoef_sq k r r'
  simp only [hswap]
  calc ∑ r : Fin 2, ∑ r' : Fin 2,
        Matrix.single (finProdFinEquiv (r, r')) (finProdFinEquiv (r, r')) (1 : ℂ)
      = ∑ x : Fin 2 × Fin 2, Matrix.single (finProdFinEquiv x) (finProdFinEquiv x) (1 : ℂ) :=
        (Fintype.sum_prod_type
          (fun x : Fin 2 × Fin 2 => Matrix.single (finProdFinEquiv x) (finProdFinEquiv x)
            (1 : ℂ))).symm
    _ = ∑ a : Fin 4, Matrix.single a a (1 : ℂ) :=
        finProdFinEquiv.sum_comp (fun a => Matrix.single a a (1 : ℂ))
    _ = 1 := Matrix.sum_single_one

/-- **Each rescaled horizontal block is a normal tensor** in the sense of
arXiv:1606.00608, lines 224--235: its letters span the bond matrix algebra and
its ket-against-bra letters resolve the identity. -/
theorem normalizedBlock_isNormalTensor (k : Fin 2) :
    MPSTensor.IsNormalTensor (normalizedBlock k).toMPSTensor :=
  MPSTensor.isNormalTensor_of_isNormal_leftCanonical _
    (normalizedBlock_toMPSTensor_isInjective k).isNormal (normalizedBlock_isLeftCanonical k)

/-- The physical-trace transfer of the rescaled block $k = 1$ vanishes, as it
does for the displayed block (`physTraceTransfer_block_one`). -/
theorem physTraceTransfer_normalizedBlock_one : physTraceTransfer (normalizedBlock 1) = 0 := by
  have h : physTraceTransfer (normalizedBlock 1) = (8 / 5 : ℂ) • physTraceTransfer (block 1) := by
    unfold physTraceTransfer normalizedBlock
    rw [Finset.smul_sum]
  rw [h, physTraceTransfer_block_one, smul_zero]

/-! ### The ambient coisometry -/

/-- The bond index `(p, p', k)` of the tensor read as the block label `k`
together with the block bond index `(p, p')`. -/
def blockBondEquiv : (Σ _k : Fin 2, Fin 4) ≃ Fin 8 where
  toFun x := physIdx ((finProdFinEquiv (m := 2) (n := 2)).symm x.2).1
    ((finProdFinEquiv (m := 2) (n := 2)).symm x.2).2 x.1
  invFun b := ⟨bitF b, finProdFinEquiv (bitL b, bitR b)⟩
  left_inv := by rintro ⟨k, a⟩; simp
  right_inv b := by simp [physIdx_bits]

/-- The flattened retained bond index against the ambient bond index. -/
def retainedBondEquiv : Fin (∑ _k : Fin 2, 4) ≃ Fin 8 :=
  finSigmaFinEquiv.symm.trans blockBondEquiv

/-- The ambient coisometry of the literal canonical form: the permutation
matrix of `retainedBondEquiv`. -/
def ambientCoisometry : Matrix (Fin (∑ _k : Fin 2, 4)) (Fin 8) ℂ :=
  retainedBondEquiv.toPEquiv.toMatrix

/-- The conjugate transpose of a permutation matrix is the permutation matrix
of the inverse permutation. -/
lemma conjTranspose_toMatrix_toPEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) :
    (e.toPEquiv.toMatrix : Matrix α β ℂ)ᴴ = e.symm.toPEquiv.toMatrix := by
  rw [Equiv.toPEquiv_symm, PEquiv.toMatrix_symm]
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

lemma ambientCoisometry_mul_conjTranspose :
    (ambientCoisometry * ambientCoisometryᴴ :
      Matrix (Fin (∑ _k : Fin 2, 4)) (Fin (∑ _k : Fin 2, 4)) ℂ) = 1 := by
  rw [ambientCoisometry, conjTranspose_toMatrix_toPEquiv, ← PEquiv.toMatrix_trans,
    ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- Conjugating by the ambient coisometry permutes the bond indices. -/
lemma conjTranspose_mul_mul_ambientCoisometry
    (Y : Matrix (Fin (∑ _k : Fin 2, 4)) (Fin (∑ _k : Fin 2, 4)) ℂ) :
    ambientCoisometryᴴ * Y * ambientCoisometry =
      Y.submatrix retainedBondEquiv.symm retainedBondEquiv.symm := by
  rw [ambientCoisometry, conjTranspose_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

lemma finSigmaFinEquiv_symm_retainedBondEquiv_symm (p p' k : Fin 2) :
    finSigmaFinEquiv.symm (retainedBondEquiv.symm (physIdx p p' k)) =
      ⟨k, finProdFinEquiv (p, p')⟩ := by
  simp [retainedBondEquiv, blockBondEquiv]

/-- **Reconstruction of the doubled-index tensor** from the weighted direct
sum of the two rescaled blocks: the bond matrix at the bond pair
$((p,p',k),(q,q',k'))$ is the block-`k` entry when $k = k'$ and zero
otherwise, exactly as in `T_apply_blocks`. -/
theorem toMPSTensor_T_reconstruct (i : Fin (8 * 8)) :
    T.toMPSTensor i =
      ambientCoisometryᴴ *
        MPSTensor.toTensorFromBlocks (d := 8 * 8) (fun _ : Fin 2 => (5 / 8 : ℂ))
          (fun k => (normalizedBlock k).toMPSTensor) i *
        ambientCoisometry := by
  rw [conjTranspose_mul_mul_ambientCoisometry]
  ext b b'
  obtain ⟨p, p', k, rfl⟩ : ∃ p p' k, b = physIdx p p' k := ⟨_, _, _, (physIdx_bits b).symm⟩
  obtain ⟨q, q', k', rfl⟩ : ∃ q q' k', b' = physIdx q q' k' :=
    ⟨_, _, _, (physIdx_bits b').symm⟩
  simp only [MPSTensor.toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSigmaFinEquiv_symm_retainedBondEquiv_symm]
  change T i.divNat i.modNat (physIdx p p' k) (physIdx q q' k') = _
  rw [T_apply_blocks]
  by_cases hk : k = k'
  · subst hk
    rw [ite_eq_left rfl, Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.smul_apply, smul_eq_mul, MPOTensor.toMPSTensor, normalizedBlock]
    ring
  · rw [ite_eq_right hk, Matrix.blockDiagonal'_apply_ne _ _ _ hk]

/-- **The literal canonical form of the doubled-index twisted dimer.** Two
retained normal blocks of bond dimension four, namely the rescaled horizontal
blocks, both with weight $5/8$, and the bond permutation `ambientCoisometry`.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`
(project example). -/
def canonicalFormData : MPSTensor.CPSVCanonicalFormData T.toMPSTensor where
  r := 2
  dim := fun _ => 4
  dim_pos := fun _ => by norm_num
  weights := fun _ => (5 / 8 : ℂ)
  weights_ne_zero := fun _ => by norm_num
  blocks := fun k => (normalizedBlock k).toMPSTensor
  blocks_normal := normalizedBlock_isNormalTensor
  total_dim_le := by simp
  ambient_coisometry := ambientCoisometry
  coisometric := ambientCoisometry_mul_conjTranspose
  reconstruct := toMPSTensor_T_reconstruct

/-- The doubled-index twisted dimer is in literal canonical form.

Source: arXiv:1606.00608, Section 2.3, lines 214--245 and eq. `II_CF1`
(project example). -/
theorem T_toMPSTensor_isCPSVCanonicalForm : MPSTensor.IsCPSVCanonicalForm T.toMPSTensor :=
  ⟨canonicalFormData⟩

end MPOTensor.TwistedDimer
