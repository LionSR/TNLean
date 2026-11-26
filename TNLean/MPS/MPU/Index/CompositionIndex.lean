/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Transfer.ReductionExistence
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.OperatorProduct.MPOProduct
import TNLean.MPS.MPU.Simple.RectangularSourceRanks
import TNLean.MPS.MPU.Index.RepresentativeIndex
import TNLean.MPS.Operator.Unitary.StandardForm
import TNLean.MPS.CanonicalForm.SimpleMPU.SimpleBlocking
import QICLean.Algebra.Combinatorics.FinSumPermutation

/-!
# Additivity of the matrix product unitary index under composition

After a common positive blocking, let the two input tensors be simple and
write their source ranks as $r,\ell$ and $r',\ell'$. The four-site composition
bounds give $r''\le d^2rr'$ and $\ell''\le d^2\ell\ell'$ for a reduced canonical
representative. Its rank product is $r''\ell''=d^8$, equal to the product of
the bounds. Both bounds are therefore equalities, and their common factor
cancels in the logarithmic index.

Rectangular reduction is used only to decrease source ranks. No equality
between the raw source ranks and the ranks of a reduced tensor is assumed.

It also contains the following results.

* `MPOTensor.rightRank_blockTensor_mulTensor_four_le`,
  `MPOTensor.leftRank_blockTensor_mulTensor_four_le`: source-rank bounds for composition.

## References

* CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824–845.
-/

section CompositionRanks

/-!
## Source-rank bounds for composition

This file proves the four-site source-rank bounds used in the composition part
of the Matrix Product Unitary index theorem. The argument is algebraic: the
two-site factorizations through the paper gates of the two factors give a
factorization of each source cut of the four-site product tensor through the
legs crossed by the paper's diagonal cut.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D₁ D₂ : ℕ}

/-- The left local factor in the $v$--$Y_1$--$Y_2$ factorization of the
first two-site source cut.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `vdagger`, lines 525--543,
as used in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private noncomputable def rightBlockLeft (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin (d * d) × Fin D₁) (Fin d × Fin r[U]) ℂ :=
  fun (I, b) (j₂, r) => ∑ l : Fin ℓ[U],
    SourceFactors.sourceV U S (finProdFinEquiv.symm I) (r, l) * S.Y₂ l (j₂, b)

/-- The right local factor in the $v$--$Y_1$--$Y_2$ factorization of the
first two-site source cut.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `vdagger`, lines 525--543,
as used in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private noncomputable def rightBlockRight (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin r[U]) (Fin D₁ × Fin (d * d)) ℂ :=
  fun (j₂, r) (a, J) =>
    if j₂ = (finProdFinEquiv.symm J).2 then
      S.Y₁ r (a, (finProdFinEquiv.symm J).1) else 0

/-- The two-site first source cut factors through a space of dimension $d r[U]$.
This is the coordinate factorization obtained from the paper gate $v$.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `vdagger`, lines 525--543,
as used in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private theorem sourceCutM₁_blockTwo_factorization (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    sourceCutM₁ (blockTwo U) = rightBlockLeft U S * rightBlockRight U S := by
  ext ⟨I, b⟩ ⟨a, J⟩
  classical
  simp only [sourceCutM₁_apply, Matrix.mul_apply, rightBlockLeft, rightBlockRight]
  rw [SourceFactors.blockTwo_apply_eq_sum_sourceV_mul_Y₁_mul_Y₂ U S I J a b,
    Fintype.sum_prod_type, Finset.sum_eq_single (finProdFinEquiv.symm J).2]
  · simp only [ite_true, Finset.sum_mul]
    refine Finset.sum_congr₂ fun r _ l _ ↦ ?_
    ring
  · intro x _ hx
    simp only [hx, ite_false, mul_zero, Finset.sum_const_zero]
  · simp

/-- The left local factor in the $X_2$--$u$--$X_1$ factorization of the
second two-site source cut.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `uu`, lines 525--543, as used
in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private noncomputable def leftBlockLeft (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin D₁ × Fin (d * d)) (Fin d × Fin ℓ[U]) ℂ :=
  fun (a, I) (i₂, l) =>
    if i₂ = (finProdFinEquiv.symm I).2 then
      S.X₂ (a, (finProdFinEquiv.symm I).1) l else 0

/-- The right local factor in the $X_2$--$u$--$X_1$ factorization of the
second two-site source cut.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `uu`, lines 525--543, as used
in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private noncomputable def leftBlockRight (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    Matrix (Fin d × Fin ℓ[U]) (Fin (d * d) × Fin D₁) ℂ :=
  fun (i₂, l) (J, b) => ∑ r : Fin r[U],
    SourceFactors.sourceU U S (l, r) (finProdFinEquiv.symm J) * S.X₁ (i₂, b) r

/-- The two-site second source cut factors through a space of dimension $d\ell[U]$.
This is the coordinate factorization obtained from the paper gate $u$.

Source: CPSV17 equations `SVDforms2`, `uuvv`, and `uu`, lines 525--543, as used
in the proof of Theorem `IndexTh` (ii), lines 833--845. -/
private theorem sourceCutM₂_blockTwo_factorization (U : MPOTensor d D₁)
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} (S : SourceFactors U ρ) :
    sourceCutM₂ (blockTwo U) = leftBlockLeft U S * leftBlockRight U S := by
  ext ⟨a, I⟩ ⟨J, b⟩
  classical
  simp only [sourceCutM₂_apply, Matrix.mul_apply, leftBlockLeft, leftBlockRight]
  rw [SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁ U S I J a b,
    Fintype.sum_prod_type, Finset.sum_eq_single (finProdFinEquiv.symm I).2]
  · simp only [ite_true, Finset.mul_sum]
    ring_nf
  · intro x _ hx
    simp only [hx, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

section GenericCut

variable {q E₁ E₂ : ℕ} {ι₁ ι₂ : Type*}
variable [Fintype ι₁] [Fintype ι₂]

private def eightCutEquiv (A B C D E F G H : Type*) :
    (A × (B × (C × (D × (E × (F × (G × H))))))) ≃
      (H × (D × (A × (C × (E × (F × (G × B))))))) where
  toFun x := (x.2.2.2.2.2.2.2,
    (x.2.2.2.1, (x.1, (x.2.2.1, (x.2.2.2.2.1,
      (x.2.2.2.2.2.1, (x.2.2.2.2.2.2.1, x.2.1)))))))
  invFun x := (x.2.2.1,
    (x.2.2.2.2.2.2.2, (x.2.2.2.1, (x.2.1,
      (x.2.2.2.2.1, (x.2.2.2.2.2.1, (x.2.2.2.2.2.2.1, x.1)))))))
  left_inv x := by rcases x with ⟨a, b, c, d, e, f, g, h⟩; rfl
  right_inv x := by rcases x with ⟨h, d, a, c, e, f, g, b⟩; rfl

private theorem sum_eight_cut_shuffle
    {A B C D E F G H : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] [Fintype G] [Fintype H]
    (φ : A → B → C → D → E → F → G → H → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ h, φ a b c d e f g h) =
      ∑ h, ∑ d, ∑ a, ∑ c, ∑ e, ∑ f, ∑ g, ∑ b, φ a b c d e f g h := by
  calc
    _ = ∑ x : A × (B × (C × (D × (E × (F × (G × H)))))),
        φ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
          x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ x : H × (D × (A × (C × (E × (F × (G × B)))))),
        φ x.2.2.1 x.2.2.2.2.2.2.2 x.2.2.2.1 x.2.1 x.2.2.2.2.1
          x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.1 := by
      apply Fintype.sum_equiv (eightCutEquiv A B C D E F G H)
      intro x
      rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Expand the product of four two-factor finite sums over the eight indices `X`, `Y`,
`J`, `K`, `T₁`, `T₂`, `S₁`, `S₂`, permute them by `sum_eight_cut_shuffle`, and
reassemble the result into the `T₁ × S₂` cut factorization used below. -/
private theorem sum_eight_cut_factorization
    {X Y J K T₁ T₂ S₁ S₂ : Type*}
    [Fintype X] [Fintype Y] [Fintype J] [Fintype K]
    [Fintype T₁] [Fintype T₂] [Fintype S₁] [Fintype S₂]
    (a : J → T₁ → ℂ) (b : T₁ → X → ℂ)
    (c : T₂ → ℂ) (d : T₂ → J → Y → ℂ)
    (e : X → K → S₁ → ℂ) (f : S₁ → ℂ)
    (g : Y → S₂ → ℂ) (h : S₂ → K → ℂ) :
    (∑ x, ∑ y,
      (∑ j, (∑ t₁, a j t₁ * b t₁ x) * ∑ t₂, c t₂ * d t₂ j y) *
        ∑ k, (∑ s₁, e x k s₁ * f s₁) * ∑ s₂, g y s₂ * h s₂ k) =
      ∑ ts : T₁ × S₂,
        (∑ j, a j ts.1 * ∑ t₂, ∑ y, c t₂ * d t₂ j y * g y ts.2) *
          ∑ x, ∑ k, ∑ s₁, b ts.1 x * e x k s₁ * f s₁ * h ts.2 k := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [sum_eight_cut_shuffle]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  refine Finset.sum_congr rfl fun s₂ _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun s₁ _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  ac_rfl

/-- The left rectangular factor of the generic four-site product cut.
Instantiated at the first source cuts of the two composed tensors it is the
Chapter 28 matrix $A_{1,4}$, and at their second source cuts it is $A_{2,4}$.
The rank argument uses this factorization of an arbitrary source cut, not a
particular choice of source factors.

Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 837--845. -/
private noncomputable def compositionCutLeft
    (L₁ : Matrix (Fin E₁ × Fin q) ι₁ ℂ)
    (R₂ : Matrix ι₂ (Fin q × Fin E₂) ℂ)
    (L₂ : Matrix (Fin E₂ × Fin q) ι₂ ℂ) :
    Matrix (Fin (E₁ * E₂) × Fin (q * q)) (ι₁ × ι₂) ℂ :=
  fun (ac, K) rs =>
    let a := (finProdFinEquiv.symm ac).1
    let c := (finProdFinEquiv.symm ac).2
    let K₁ := (finProdFinEquiv.symm K).1
    let K₂ := (finProdFinEquiv.symm K).2
    ∑ J : Fin q, L₁ (a, J) rs.1 *
      ∑ t : ι₂, ∑ y : Fin E₂,
        L₂ (c, K₁) t * R₂ t (J, y) * L₂ (y, K₂) rs.2

/-- The right rectangular factor of the generic four-site product cut.
Instantiated at the first source cuts of the two composed tensors it is the
Chapter 28 matrix $B_{1,4}$, and at their second source cuts it is $B_{2,4}$.
The rank argument uses this factorization of an arbitrary source cut, not a
particular choice of source factors.

Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 837--845. -/
private noncomputable def compositionCutRight
    (R₁ : Matrix ι₁ (Fin q × Fin E₁) ℂ)
    (L₁ : Matrix (Fin E₁ × Fin q) ι₁ ℂ)
    (R₂ : Matrix ι₂ (Fin q × Fin E₂) ℂ) :
    Matrix (ι₁ × ι₂) (Fin (q * q) × Fin (E₁ * E₂)) ℂ :=
  fun rs (I, ef) =>
    let e := (finProdFinEquiv.symm ef).1
    let f := (finProdFinEquiv.symm ef).2
    let I₁ := (finProdFinEquiv.symm I).1
    let I₂ := (finProdFinEquiv.symm I).2
    ∑ x : Fin E₁, ∑ J : Fin q, ∑ t : ι₁,
      R₁ rs.1 (I₁, x) * L₁ (x, J) t * R₁ t (I₂, e) * R₂ rs.2 (J, f)

/-- The first source cut of a two-site-blocked product factors through the two local
first-cut factorizations.

Source: CPSV17 source cut `II_SVD`, lines 458--477, and the composition proof
of Theorem `IndexTh` (ii), lines 833--845. -/
private theorem sourceCutM₁_blockTwo_mulTensor_factorization
    (A : MPOTensor q E₁) (B : MPOTensor q E₂)
    (L₁ : Matrix (Fin q × Fin E₁) ι₁ ℂ)
    (R₁ : Matrix ι₁ (Fin E₁ × Fin q) ℂ)
    (L₂ : Matrix (Fin q × Fin E₂) ι₂ ℂ)
    (R₂ : Matrix ι₂ (Fin E₂ × Fin q) ℂ)
    (h₁ : sourceCutM₁ A = L₁ * R₁) (h₂ : sourceCutM₁ B = L₂ * R₂) :
    sourceCutM₁ (blockTwo (mulTensor A B)) =
      (compositionCutRight L₁.transpose R₁.transpose L₂.transpose).transpose *
        (compositionCutLeft R₁.transpose L₂.transpose R₂.transpose).transpose := by
  classical
  apply Matrix.transpose_injective
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hA (i j : Fin q) (a b : Fin E₁) :
      A (i, j) a b = ∑ t : ι₁, R₁.transpose (a, j) t * L₁.transpose t (i, b) := by
    have h := congrArg (fun M => M (i, b) (a, j)) h₁
    simpa only [sourceCutM₁_apply, Matrix.mul_apply, Matrix.transpose_apply,
      mul_comm] using h
  have hB (i j : Fin q) (a b : Fin E₂) :
      B (i, j) a b = ∑ t : ι₂, R₂.transpose (a, j) t * L₂.transpose t (i, b) := by
    have h := congrArg (fun M => M (i, b) (a, j)) h₂
    simpa only [sourceCutM₁_apply, Matrix.mul_apply, Matrix.transpose_apply,
      mul_comm] using h
  ext ⟨ac, K⟩ ⟨I, ef⟩
  rcases finProdFinEquiv.surjective ac with ⟨⟨a, c⟩, rfl⟩
  rcases finProdFinEquiv.surjective ef with ⟨⟨e, f⟩, rfl⟩
  rcases finProdFinEquiv.surjective K with ⟨⟨K₁, K₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective I with ⟨⟨I₁, I₂⟩, rfl⟩
  simp only [Matrix.transpose_apply, sourceCutM₁_apply, blockTwo_apply, Matrix.mul_apply,
    compositionCutLeft, compositionCutRight, Equiv.symm_apply_apply,
    mulTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  simp_rw [hA, hB]
  exact sum_eight_cut_factorization
    (fun j t₁ ↦ R₁.transpose (a, j) t₁)
    (fun t₁ x ↦ L₁.transpose t₁ (I₁, x))
    (fun t₂ ↦ R₂.transpose (c, K₁) t₂)
    (fun t₂ j y ↦ L₂.transpose t₂ (j, y))
    (fun x k s₁ ↦ R₁.transpose (x, k) s₁)
    (fun s₁ ↦ L₁.transpose s₁ (I₂, e))
    (fun y s₂ ↦ R₂.transpose (y, K₂) s₂)
    (fun s₂ k ↦ L₂.transpose s₂ (k, f))

end GenericCut

private def pairPhysicalEquiv {d e : ℕ} (σ : Fin d ≃ Fin e) :
    Fin (d * d) ≃ Fin (e * e) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodCongr σ σ).trans finProdFinEquiv)

private theorem mulTensor_reindexPhysical {d' : ℕ} (σ : Fin d' ≃ Fin d)
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    mulTensor (reindexPhysical σ U) (reindexPhysical σ V) =
      reindexPhysical σ (mulTensor U V) := by
  classical
  ext ⟨i, k⟩ x y
  simp only [mulTensor_apply, reindexPhysical, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [← Equiv.sum_comp σ]

private theorem blockTwo_reindexPhysical {d' : ℕ} (σ : Fin d' ≃ Fin d)
    (U : MPOTensor d D₁) :
    blockTwo (reindexPhysical σ U) =
      reindexPhysical (pairPhysicalEquiv σ) (blockTwo U) := by
  funext ⟨I, J⟩
  simp [blockTwo_apply, reindexPhysical, pairPhysicalEquiv]

private theorem rightRank_blockTwo_mulTensor_reindexPhysical {d' : ℕ}
    (σ : Fin d' ≃ Fin d) (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    r[blockTwo (mulTensor (reindexPhysical σ U) (reindexPhysical σ V))] =
      r[blockTwo (mulTensor U V)] := by
  rw [mulTensor_reindexPhysical, blockTwo_reindexPhysical,
    rightRank_reindexPhysical]

private theorem leftRank_blockTwo_mulTensor_reindexPhysical {d' : ℕ}
    (σ : Fin d' ≃ Fin d) (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    ℓ[blockTwo (mulTensor (reindexPhysical σ U) (reindexPhysical σ V))] =
      ℓ[blockTwo (mulTensor U V)] := by
  rw [mulTensor_reindexPhysical, blockTwo_reindexPhysical,
    leftRank_reindexPhysical]

private theorem rightRank_blockTwo_eq_blockTensor_two (U : MPOTensor d D₁) :
    r[blockTwo U] = r[blockTensor U 2] := by
  have h : blockTwo U = reindexPhysical (twoSiteBlockEquiv d) (blockTensor U 2) :=
    blockTwo_eq_blockTensor_reindex U
  rw [h, rightRank_reindexPhysical]

private theorem leftRank_blockTwo_eq_blockTensor_two (U : MPOTensor d D₁) :
    ℓ[blockTwo U] = ℓ[blockTensor U 2] := by
  have h : blockTwo U = reindexPhysical (twoSiteBlockEquiv d) (blockTensor U 2) :=
    blockTwo_eq_blockTensor_reindex U
  rw [h, leftRank_reindexPhysical]

private theorem rightRank_blockTwo_mulTensor_blockTwo_le
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    r[blockTwo (mulTensor (blockTwo U) (blockTwo V))] ≤
      d ^ 2 * r[U] * r[V] := by
  let Sᵤ := sourceFactors U (1 : Matrix (Fin D₁) (Fin D₁) ℂ) Matrix.PosDef.one
  let Sᵥ := sourceFactors V (1 : Matrix (Fin D₂) (Fin D₂) ℂ) Matrix.PosDef.one
  rw [rightRank,
    sourceCutM₁_blockTwo_mulTensor_factorization (blockTwo U) (blockTwo V)
      (rightBlockLeft U Sᵤ) (rightBlockRight U Sᵤ)
      (rightBlockLeft V Sᵥ) (rightBlockRight V Sᵥ)
      (sourceCutM₁_blockTwo_factorization U Sᵤ)
      (sourceCutM₁_blockTwo_factorization V Sᵥ)]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  calc
    _ ≤ Fintype.card ((Fin d × Fin r[U]) × (Fin d × Fin r[V])) :=
      Matrix.rank_le_card_width _
    _ = d ^ 2 * r[U] * r[V] := by simp [pow_two]; ring

private theorem rightRank_reindexBond {D' : ℕ} (e : Fin D' ≃ Fin D₁)
    (U : MPOTensor d D₁) : r[reindexBond e U] = r[U] := by
  rw [rightRank]
  change (Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin d)) e.symm)
    (Equiv.prodCongr e.symm (Equiv.refl (Fin d))) (sourceCutM₁ U)).rank = _
  rw [Matrix.rank_reindex]
  rfl

private theorem reindexBond_blockTwo {D' : ℕ} (e : Fin D' ≃ Fin D₁)
    (U : MPOTensor d D₁) :
    reindexBond e (blockTwo U) = blockTwo (reindexBond e U) := by
  classical
  ext ⟨I, J⟩ a b
  simp only [reindexBond, blockTwo_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp e]

private def physicalFlip (U : MPOTensor d D₁) : MPOTensor d D₁ :=
  fun (i, j) => U (j, i)

private theorem rightRank_physicalFlip (U : MPOTensor d D₁) :
    r[physicalFlip U] = ℓ[U] := by
  change (sourceCutM₂ U).transpose.rank = (sourceCutM₂ U).rank
  exact Matrix.rank_transpose (sourceCutM₂ U)

private theorem blockTwo_physicalFlip (U : MPOTensor d D₁) :
    blockTwo (physicalFlip U) = physicalFlip (blockTwo U) := by
  rfl

private theorem mulTensor_physicalFlip_swap
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    mulTensor (physicalFlip V) (physicalFlip U) =
      reindexBond (productBondSwapEquiv D₂ D₁) (physicalFlip (mulTensor U V)) := by
  classical
  ext ⟨i, k⟩ x y
  simp only [mulTensor_apply, physicalFlip, reindexBond, productBondSwapEquiv,
    Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  rcases hx : finProdFinEquiv.symm x with ⟨v₁, u₁⟩
  rcases hy : finProdFinEquiv.symm y with ⟨v₂, u₂⟩
  simp only [Prod.swap_prod_mk]
  ring

/-- Swapping the physical input and output indices sends the first source cut to the
transpose of the second source cut.

Source: CPSV17 source cuts `II_SVD`, lines 458--477. -/
private theorem sourceCutM₁_physicalFlip (U : MPOTensor d D₁) :
    sourceCutM₁ (physicalFlip U) = (sourceCutM₂ U).transpose := by
  rfl

private theorem leftRank_blockTwo_mulTensor_blockTwo_le
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    ℓ[blockTwo (mulTensor (blockTwo U) (blockTwo V))] ≤
      d ^ 2 * ℓ[U] * ℓ[V] := by
  let Sᵤ := sourceFactors U (1 : Matrix (Fin D₁) (Fin D₁) ℂ) Matrix.PosDef.one
  let Sᵥ := sourceFactors V (1 : Matrix (Fin D₂) (Fin D₂) ℂ) Matrix.PosDef.one
  have hU : sourceCutM₁ (physicalFlip (blockTwo U)) =
      (leftBlockRight U Sᵤ).transpose * (leftBlockLeft U Sᵤ).transpose := by
    rw [sourceCutM₁_physicalFlip, sourceCutM₂_blockTwo_factorization,
      Matrix.transpose_mul]
  have hV : sourceCutM₁ (physicalFlip (blockTwo V)) =
      (leftBlockRight V Sᵥ).transpose * (leftBlockLeft V Sᵥ).transpose := by
    rw [sourceCutM₁_physicalFlip, sourceCutM₂_blockTwo_factorization,
      Matrix.transpose_mul]
  have hfactor := sourceCutM₁_blockTwo_mulTensor_factorization
    (physicalFlip (blockTwo V)) (physicalFlip (blockTwo U))
    (leftBlockRight V Sᵥ).transpose (leftBlockLeft V Sᵥ).transpose
    (leftBlockRight U Sᵤ).transpose (leftBlockLeft U Sᵤ).transpose hV hU
  have hrank :
      r[blockTwo
        (mulTensor (physicalFlip (blockTwo V)) (physicalFlip (blockTwo U)))] ≤
        d ^ 2 * ℓ[V] * ℓ[U] := by
    rw [rightRank, hfactor]
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    calc
      _ ≤ Fintype.card ((Fin d × Fin ℓ[V]) × (Fin d × Fin ℓ[U])) :=
        Matrix.rank_le_card_width _
      _ = d ^ 2 * ℓ[V] * ℓ[U] := by simp [pow_two]; ring
  have heq :
      r[blockTwo
        (mulTensor (physicalFlip (blockTwo V)) (physicalFlip (blockTwo U)))] =
        ℓ[blockTwo (mulTensor (blockTwo U) (blockTwo V))] := by
    rw [mulTensor_physicalFlip_swap, ← reindexBond_blockTwo,
      rightRank_reindexBond, blockTwo_physicalFlip, rightRank_physicalFlip]
  rw [← heq]
  exact hrank.trans_eq (by ring)

/-- The right source rank of the four-site block of a product tensor is bounded
by the two right source ranks and the two physical legs crossed by the cut.

Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 837--845. -/
theorem rightRank_blockTensor_mulTensor_four_le
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    r[blockTensor (mulTensor U V) 4] ≤ d ^ 2 * r[U] * r[V] := by
  let C := mulTensor U V
  have hIter :
      r[blockTensor C 4] = r[blockTensor (blockTensor C 2) 2] := by
    have h := reindexPhysical_blockTensor_blockTensor C 2 2
    change reindexPhysical (MPSTensor.directIteratedBlockEquiv d 2 2)
        (blockTensor (blockTensor C 2) 2) = blockTensor C 4 at h
    rw [← h, rightRank_reindexPhysical]
  rw [hIter, blockTensor_mulTensor U V]
  rw [← rightRank_blockTwo_eq_blockTensor_two
    (mulTensor (blockTensor U 2) (blockTensor V 2))]
  rw [← rightRank_blockTwo_mulTensor_reindexPhysical (twoSiteBlockEquiv d)
    (blockTensor U 2) (blockTensor V 2)]
  have hU : reindexPhysical (twoSiteBlockEquiv d) (blockTensor U 2) = blockTwo U :=
    (blockTwo_eq_blockTensor_reindex U).symm
  have hV : reindexPhysical (twoSiteBlockEquiv d) (blockTensor V 2) = blockTwo V :=
    (blockTwo_eq_blockTensor_reindex V).symm
  rw [hU, hV]
  exact rightRank_blockTwo_mulTensor_blockTwo_le U V

/-- The left source rank of the four-site block of a product tensor is bounded
by the two left source ranks and the two physical legs crossed by the reflected
cut.  The reflected local factorization keeps the physical order `(j₂, j₁)`
and source order `(r, l)` explicit.

Source: arXiv:1703.09188, Theorem `IndexTh` (ii), lines 837--845. -/
theorem leftRank_blockTensor_mulTensor_four_le
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    ℓ[blockTensor (mulTensor U V) 4] ≤ d ^ 2 * ℓ[U] * ℓ[V] := by
  let C := mulTensor U V
  have hIter :
      ℓ[blockTensor C 4] = ℓ[blockTensor (blockTensor C 2) 2] := by
    have h := reindexPhysical_blockTensor_blockTensor C 2 2
    change reindexPhysical (MPSTensor.directIteratedBlockEquiv d 2 2)
        (blockTensor (blockTensor C 2) 2) = blockTensor C 4 at h
    rw [← h, leftRank_reindexPhysical]
  rw [hIter, blockTensor_mulTensor U V]
  rw [← leftRank_blockTwo_eq_blockTensor_two
    (mulTensor (blockTensor U 2) (blockTensor V 2))]
  rw [← leftRank_blockTwo_mulTensor_reindexPhysical (twoSiteBlockEquiv d)
    (blockTensor U 2) (blockTensor V 2)]
  have hU : reindexPhysical (twoSiteBlockEquiv d) (blockTensor U 2) = blockTwo U :=
    (blockTwo_eq_blockTensor_reindex U).symm
  have hV : reindexPhysical (twoSiteBlockEquiv d) (blockTensor V 2) = blockTwo V :=
    (blockTwo_eq_blockTensor_reindex V).symm
  rw [hU, hV]
  exact leftRank_blockTwo_mulTensor_blockTwo_le U V

end MPOTensor

end CompositionRanks

section CompositionIndex

namespace MPOTensor

/-- The four-site composition rank bounds are equalities after reduction to a
simple canonical representative. CPSV17, arXiv:1703.09188, Theorem
`IndexTh` (ii), lines 830–845. -/
theorem IsMPUCanonicalFormII.compositionRanks_of_isReduction
    {d D₁ D₂ E : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    {R : MPOTensor d E}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hR : IsMPUCanonicalFormII R)
    (hSU : IsMPUSimple U) (hSV : IsMPUSimple V)
    (hSR : IsMPUSimple (MPOTensor.blockTensor R 4))
    {A : Matrix (Fin E) (Fin (D₁ * D₂)) ℂ}
    {B : Matrix (Fin (D₁ * D₂)) (Fin E) ℂ}
    (hred : MPTensor.IsReduction (mulTensor U V).toMPSTensor R.toMPSTensor A B) :
    r[MPOTensor.blockTensor R 4] = d ^ 2 * r[U] * r[V] ∧
      ℓ[MPOTensor.blockTensor R 4] = d ^ 2 * ℓ[U] * ℓ[V] := by
  apply eq_and_eq_of_pos_of_le_of_mul_le_mul
    (hR.sourceRanks_blockTensor_pos (by decide) hSR).1
    (hR.sourceRanks_blockTensor_pos (by decide) hSR).2
    ((rightRank_blockTensor_le_of_isReduction hred 4).trans
      (rightRank_blockTensor_mulTensor_four_le U V))
    ((leftRank_blockTensor_le_of_isReduction hred 4).trans
      (leftRank_blockTensor_mulTensor_four_le U V))
  rw [hR.rightRank_mul_leftRank_blockTensor (by decide) hSR]
  have hprod : d ^ 2 * r[U] * r[V] * (d ^ 2 * ℓ[U] * ℓ[V]) =
      d ^ 4 * (r[U] * ℓ[U]) * (r[V] * ℓ[V]) := by ring
  have hprodU : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 1 2).mp hSU
  have hprodV : r[V] * ℓ[V] = d * d := (hV.isMPUSimple_tfae.out 1 2).mp hSV
  rw [hprod, hprodU, hprodV]
  exact le_of_eq (by ring)

/-- Equality of all positive-length periodic operators gives a rectangular
reduction to a canonical-form-II tensor. The target is normal after removing
the normalization scalar; apply the normal-target reduction theorem.
CPSV17, canonical-form discussion, lines 319–356. -/
theorem exists_isReduction_of_mpo_eq_cfii
    {d D E : ℕ} {U : MPOTensor d D} {V : MPOTensor d E}
    (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 0 < N → mpo U N = mpo V N) :
    ∃ (A : Matrix (Fin E) (Fin D) ℂ)
      (B : Matrix (Fin D) (Fin E) ℂ),
      MPTensor.IsReduction U.toMPSTensor V.toMPSTensor A B := by
  let _ : NeZero d := hV.neZero_phys
  let _ : NeZero E := hV.neZero_bond
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast NeZero.pos d)
  have hζ : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 := inv_ne_zero hsqrt
  have hNormalNorm : Kraus.IsNormal V.normalizedFlattening :=
    hV.isNormalTensor_normalizedFlattening.isNormal
  have hNormalRaw : Kraus.IsNormal V.toMPSTensor := by
    apply (MPSTensor.isNormal_smul_iff hζ V.toMPSTensor).mp
    exact hNormalNorm
  have hSame : MPTensor.SameMPV₂Pos U.toMPSTensor V.toMPSTensor := by
    intro N hN σ
    rw [mpv_toMPSTensor, mpv_toMPSTensor, hEq N hN]
  exact MPSTensor.exists_isReduction_of_isNormal_of_sameMPV₂Pos
    V.toMPSTensor U.toMPSTensor hNormalRaw hSame

/-- A canonical representative of a composition has the sum of the indices
of its canonical factors. CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii),
lines 830–845. -/
theorem IsMPUCanonicalFormII.index_eq_add_of_mpo_eq_mulTensor
    {d D₁ D₂ E : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    {R : MPOTensor d E}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hR : IsMPUCanonicalFormII R)
    (hMpo : ∀ N : ℕ, 0 < N → mpo R N = mpo (mulTensor U V) N) :
    hR.index = hU.index + hV.index := by
  obtain ⟨A, B, hred⟩ := exists_isReduction_of_mpo_eq_cfii hR
    (fun N hN => (hMpo N hN).symm)
  obtain ⟨k, hcommon⟩ :=
    letI := hU.neZero_phys
    letI := hU.neZero_bond
    letI := hV.neZero_bond
    letI := hR.neZero_bond
    hU.isMPU.exists_common_blockTensor_isMPUSimple_three hV.isMPU hR.isMPU
  have hredK : MPTensor.IsReduction
      (mulTensor (MPOTensor.blockTensor U k)
        (MPOTensor.blockTensor V k)).toMPSTensor
      (MPOTensor.blockTensor R k).toMPSTensor A B := by
    rw [← blockTensor_mulTensor]
    simpa only [toMPSTensor_blockTensor] using
      (hred.blockTensor k).reindexPhysical
        (blockedDoubledIndexEquiv d k)
  have hRanks := (hU.blockTensor k hcommon.1).compositionRanks_of_isReduction
    (hV.blockTensor k hcommon.1)
    (hR.blockTensor k hcommon.1)
    hcommon.2.1 hcommon.2.2.1
    (hcommon.2.2.2.blockTensor 4 (by decide)) hredK
  have hValue :=
    let hu := hU.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.1
    let hv := hV.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.2.1
    let hr := (hR.blockTensor k hcommon.1).sourceRanks_blockTensor_pos
      (by decide) (hcommon.2.2.2.blockTensor 4 (by decide))
    letI := (hU.blockTensor k hcommon.1).neZero_phys
    sourceIndexValue_eq_add_of_common_rank_product
      (MPOTensor.blockTensor U k)
      (MPOTensor.blockTensor V k)
      (MPOTensor.blockTensor (MPOTensor.blockTensor R k) 4)
      (Kraus.blockPhysDim d k ^ 2)
      (pow_pos (NeZero.pos _) _) hu.1 hu.2 hv.1 hv.2 hr.1 hr.2 hRanks.1 hRanks.2
  simpa only [
    (hR.blockTensor k hcommon.1).sourceIndexValue_eq_index
      (by decide) (hcommon.2.2.2.blockTensor 4 (by decide)),
    hR.index_blockTensor k hcommon.1,
    hU.sourceIndexValue_eq_index hcommon.1 hcommon.2.1,
    hV.sourceIndexValue_eq_index hcommon.1 hcommon.2.2.1] using hValue

/-- The index is additive under composition of positive-dimensional MPUs.
No choice of blocking length or canonical representative occurs in the
statement. CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824–845. -/
theorem IsMPU.index_mulTensor
    {d D₁ D₂ : ℕ} [NeZero d] [NeZero D₁] [NeZero D₂]
    {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPU U) (hV : IsMPU V) :
    (hU.mulTensor hV).index = hU.index + hV.index := by
  obtain ⟨E, hE, R, hR, _, hMpo⟩ :=
    (hU.mulTensor hV).exists_reduced_cfii_representative
  obtain ⟨⟨EU, _, Ured, hUred, _, hMpoU⟩, ⟨EV, _, Vred, hVred, _, hMpoV⟩⟩ :=
    And.intro hU.exists_reduced_cfii_representative hV.exists_reduced_cfii_representative
  rw [(hU.mulTensor hV).index_eq_canonical_representative hR hMpo,
    hU.index_eq_canonical_representative hUred hMpoU,
    hV.index_eq_canonical_representative hVred hMpoV]
  apply hUred.index_eq_add_of_mpo_eq_mulTensor hVred hR
  intro N hN
  rw [hMpo N hN, mpo_mulTensor, mpo_mulTensor, hMpoU N hN, hMpoV N hN]

end MPOTensor

end CompositionIndex
