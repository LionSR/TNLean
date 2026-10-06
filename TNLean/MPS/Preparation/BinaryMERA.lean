/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.FixedPointPairState
import TNLean.MPS.Preparation.TreeFactorization
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# Binary finite-range MERA and polar tree layers

The algebraic network of arXiv:2307.01696, eq. (16) and "Connection to MERA":
a binary tree of isometries above a layer of unitary pair preparations. Its state has unit
norm. The polar factors provide its isometries once the two-site blocked tensor is injective.
No convergence rate or approximation-error estimate is used here.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSTensor

variable {n D : ℕ}

/-! ### Binary trees of layers -/

/-- The map `ℂ^χ → (ℂⁿ)^{⊗2^{k+1}}` of a binary tree with `k + 1` layers: the finest layer
`W : ℂ^χ → ℂⁿ ⊗ ℂⁿ` and the coarser layers `V 0, …, V (k-1) : ℂ^χ → ℂ^χ ⊗ ℂ^χ`, ordered from
fine to coarse. For `k + 1` it is `W^{⊗2^{k+1}}` composed with the tree of the coarser layers,
regrouped along neighbouring pairs; unfolded, `W^{⊗2^k} (V 0)^{⊗2^{k-1}} ⋯ V (k-1)`.

arXiv:2307.01696, eq. (16), and paragraph "Connection to MERA": the isometries of the tree. -/
noncomputable def binaryTreeMatrix {χ : ℕ} :
    (k : ℕ) → {n : ℕ} → Matrix (Fin (blockPhysDim n 2)) (Fin χ) ℂ →
      (Fin k → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ) →
      Matrix (Fin (blockPhysDim n (2 ^ (k + 1)))) (Fin χ) ℂ
  | 0, _, W, _ => W
  | k + 1, n, W, V =>
      (blockKron (2 ^ (k + 1)) W * binaryTreeMatrix k (V 0) (Fin.tail V)).submatrix
        (pairRegroupEquiv n k) id

/-- A binary tree of isometries is an isometry. -/
theorem isIsometry_binaryTreeMatrix {χ : ℕ} (k : ℕ) {n : ℕ}
    {W : Matrix (Fin (blockPhysDim n 2)) (Fin χ) ℂ}
    {V : Fin k → Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ} (hW : W.IsIsometry)
    (hV : ∀ j, (V j).IsIsometry) : (binaryTreeMatrix k W V).IsIsometry := by
  induction k generalizing n with
  | zero => exact hW
  | succ k ih =>
      have h : (binaryTreeMatrix k (V 0) (Fin.tail V)).IsIsometry :=
        ih (hV 0) fun j => hV j.succ
      rw [Matrix.IsIsometry] at hW h ⊢
      change ((blockKron (2 ^ (k + 1)) W * binaryTreeMatrix k (V 0) (Fin.tail V)).submatrix
        (pairRegroupEquiv n k) id)ᴴ * (blockKron (2 ^ (k + 1)) W *
          binaryTreeMatrix k (V 0) (Fin.tail V)).submatrix (pairRegroupEquiv n k) id = 1
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
        Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (blockKron _ W)ᴴ,
        blockKron_conjTranspose, ← blockKron_mul, hW, blockKron_one, Matrix.one_mul, h]

/-! ### The layers of the tree-RG circuit -/

/-- The binary tree of the layers `V⁽¹⁾, …, V⁽ᵏ⁺¹⁾` is the product of the layers of eq. (16)
of arXiv:2307.01696 (`treeIsoMatrix`). -/
theorem binaryTreeMatrix_treeLayers (k : ℕ) (A : MPSTensor n D) :
    binaryTreeMatrix k (polarIsoMatrix (blockTensor A 2)) (treeLayers k A) =
      treeIsoMatrix k A := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      have htail : Fin.tail (treeLayers (k + 1) A) = treeLayers k (pairPosTensor A) := by
        funext j
        simp only [Fin.tail, treeLayers, Fin.val_succ, Function.iterate_succ_apply]
      change (blockKron (2 ^ (k + 1)) (polarIsoMatrix (blockTensor A 2)) *
          binaryTreeMatrix k (polarIsoMatrix (blockTensor (pairPosTensor A) 2))
            (Fin.tail (treeLayers (k + 1) A))).submatrix (pairRegroupEquiv n k) id = _
      rw [htail, ih]
      rfl

/-! ### Injectivity of the layers -/

/-- If the physical rotation `W · Y` of a tensor is injective, so is `Y`: the matrices of
`W · Y` are combinations of those of `Y`. -/
theorem isInjective_of_isInjective_rotatePhysical {m : ℕ} (W : Matrix (Fin m) (Fin n) ℂ)
    {Y : MPSTensor n D} (h : Kraus.IsInjective (rotatePhysical W Y)) : Kraus.IsInjective Y := by
  refine eq_top_iff.2 (h.symm.le.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨i, rfl⟩
  rw [rotatePhysical_apply]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The two-site blocked tensor of an injective tensor is injective. -/
theorem isInjective_blockTensor_two {B : MPSTensor n D} (h : Kraus.IsInjective B) :
    Kraus.IsInjective (blockTensor B 2) :=
  (isNBlkInjective_iff_blockTensor_isInjective B 2).1
    (isNBlkInjective_of_le zero_lt_one (Kraus.isNBlkInjective_one_of_isInjective h) one_le_two)

/-- If the two-site blocked tensor of `A` is injective, so is that of `T₁`: blocking
`B₂ = V⁽¹⁾ T₁` twice gives `(V⁽¹⁾)^{⊗2}` applied to `T₁` blocked twice. -/
theorem isInjective_blockTensor_pairPosTensor {A : MPSTensor n D}
    (h : Kraus.IsInjective (blockTensor A 2)) :
    Kraus.IsInjective (blockTensor (pairPosTensor A) 2) := by
  have h4 := isInjective_blockTensor_two h
  rw [← rotatePhysical_polarIsoMatrix_polarPosTensor (blockTensor A 2),
    blockTensor_rotatePhysical] at h4
  exact isInjective_of_isInjective_rotatePhysical _ h4

/-- If the two-site blocked tensor of `A` is injective, every coarse layer `V⁽ʲ⁺²⁾` is the
isometric factor of an injective tensor. -/
theorem isInjective_blockTensor_iterate_pairPosTensor {A : MPSTensor n D}
    (h : Kraus.IsInjective (blockTensor A 2)) (j : ℕ) :
    Kraus.IsInjective (blockTensor
      ((pairPosTensor : MPSTensor (D * D) D → MPSTensor (D * D) D)^[j] (pairPosTensor A)) 2) := by
  induction j with
  | zero => exact isInjective_blockTensor_pairPosTensor h
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact isInjective_blockTensor_pairPosTensor ih

/-- If the two-site blocked tensor of `A` is injective, every coarse layer of the tree-RG
circuit is an isometry `ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}`.

arXiv:2307.01696, paragraph "The tree-RG circuit": "each layer but the lowest consists of
isometries from dimension $D^2$ to $D^4$". -/
theorem isIsometry_treeLayers {A : MPSTensor n D} (h : Kraus.IsInjective (blockTensor A 2))
    (k : ℕ) (j : Fin k) : (treeLayers k A j).IsIsometry :=
  isIsometry_polarIsoMatrix_of_isInjective (isInjective_blockTensor_iterate_pairPosTensor h j)

end MPSTensor

namespace MPSPreparation

open MPSTensor

variable {d n D k : ℕ}

/-! ### A binary finite-range MERA -/

/-- A **binary finite-range MERA** with `k + 1` isometry layers and bond dimension `D²`, on a
ring whose top sites carry `ℂ^{D²} = L ⊗ R`.

* `disentangler` is the unitary `u` on `ℂ^D ⊗ ℂ^D` of the first (top) layer, applied to
  `|0⟩|0⟩` on every pair `R_i L_{i+1}` of neighbouring bond legs;
* `coarseIso j : ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}`, `j < k`, are the isometries of the coarse layers,
  ordered from fine to coarse, and `fineIso : ℂ^{D²} → ℂⁿ ⊗ ℂⁿ` is the isometry of the finest
  layer. Each is copied on every site of its layer.

The disentanglers of the lower layers are the identity.

arXiv:2307.01696, paragraph "Connection to MERA": the isometries `V⁽ʲ⁾` are the isometries of a
finite-range MERA, "and all disentanglers are the identity, save for the first layer, which is
identified with the single layer of unitaries that prepare the fixed-point state". -/
structure BinaryMERA (n D k : ℕ) where
  /-- The unitary of the first layer, preparing each pair `R_i L_{i+1}` from `|0⟩|0⟩`. -/
  disentangler : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ
  disentangler_mem_unitaryGroup : disentangler ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ
  /-- The isometry `ℂ^{D²} → ℂⁿ ⊗ ℂⁿ` of the finest layer. -/
  fineIso : Matrix (Fin (blockPhysDim n 2)) (Fin (D * D)) ℂ
  isIsometry_fineIso : fineIso.IsIsometry
  /-- The isometries `ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` of the coarse layers, from fine to coarse. -/
  coarseIso : Fin k → Matrix (Fin (blockPhysDim (D * D) 2)) (Fin (D * D)) ℂ
  isIsometry_coarseIso : ∀ j, (coarseIso j).IsIsometry

namespace BinaryMERA

variable (𝓜 : BinaryMERA n D k)

/-- The isometry `ℂ^{D²} → (ℂⁿ)^{⊗2^{k+1}}` of the `k + 1` isometry layers under one top
site. -/
noncomputable def treeMatrix : Matrix (Fin (blockPhysDim n (2 ^ (k + 1)))) (Fin (D * D)) ℂ :=
  binaryTreeMatrix k 𝓜.fineIso 𝓜.coarseIso

/-- The tree map `𝓜.treeMatrix` of the isometry layers of the network is an isometry: a binary
tree of isometries is an isometry (`isIsometry_binaryTreeMatrix`). -/
theorem isIsometry_treeMatrix : 𝓜.treeMatrix.IsIsometry :=
  isIsometry_binaryTreeMatrix k 𝓜.isIsometry_fineIso 𝓜.isIsometry_coarseIso

/-- The pair `u |0⟩|0⟩` prepared by the disentangler on `R_i L_{i+1}`. -/
def topPair [NeZero D] : Fin D × Fin D → ℂ := fun p => 𝓜.disentangler p (0, 0)

/-- The amplitude of the MERA state on `M` top sites at a configuration of the `M` blocks of
`2^{k+1}` sites: the tree isometries applied to the top state `⊗ᵢ u_{R_i L_{i+1}} |0⟩|0⟩`. -/
noncomputable def amplitude [NeZero D] {M : ℕ}
    (s : Fin M → Fin (blockPhysDim n (2 ^ (k + 1)))) : ℂ :=
  ∑ τ : Fin M → Fin (D * D), (∏ j, 𝓜.treeMatrix (s j) (τ j)) *
    pairProductState 𝓜.topPair (fun j => finProdFinEquiv.symm (τ j))

/-- The **state of the MERA** on `N = M 2^{k+1}` sites with `M` top sites, read through the
regrouping of the sites into blocks. -/
noncomputable def state [NeZero D] (M : ℕ) : MPVSpace n (M * 2 ^ (k + 1)) :=
  (EuclideanSpace.equiv (ι := Cfg n (M * 2 ^ (k + 1))) (𝕜 := ℂ)).symm fun s =>
    𝓜.amplitude ((blockedConfigEquiv n M (2 ^ (k + 1))).symm s)

@[simp] lemma state_apply [NeZero D] (M : ℕ) (s : Cfg n (M * 2 ^ (k + 1))) :
    𝓜.state M s = 𝓜.amplitude ((blockedConfigEquiv n M (2 ^ (k + 1))).symm s) := by
  simp [state, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- The pair prepared by a unitary from `|0⟩|0⟩` is normalized. -/
theorem sum_star_topPair_mul [NeZero D] : ∑ p, star (𝓜.topPair p) * 𝓜.topPair p = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1
    𝓜.disentangler_mem_unitaryGroup) (0, 0)) (0, 0)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simpa [topPair, Matrix.star_apply] using h

/-- The state of a MERA is a unit vector: the isometries preserve the norm of the normalized
top state. -/
theorem norm_state [NeZero D] (M : ℕ) : ‖𝓜.state M‖ = 1 := by
  have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (𝓜.state M)).symm
  rw [PiLp.inner_apply, ← (blockedConfigEquiv n M (2 ^ (k + 1))).sum_comp] at h
  simp only [RCLike.inner_apply, state_apply, Equiv.symm_apply_apply, amplitude] at h
  set ψ : (Fin M → Fin (D * D)) → ℂ :=
    fun τ => pairProductState 𝓜.topPair (fun j => finProdFinEquiv.symm (τ j))
  have key := 𝓜.isIsometry_treeMatrix.sum_star_mul_tensorPower ψ ψ
  have hsum : ∑ τ, star (ψ τ) * ψ τ = 1 := by
    calc ∑ τ, star (ψ τ) * ψ τ
        = ∑ c : Fin M → Fin D × Fin D,
            star (pairProductState 𝓜.topPair c) * pairProductState 𝓜.topPair c :=
          Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _
            fun _ => rfl
      _ = 1 := by rw [pairProductState_norm_sq, 𝓜.sum_star_topPair_mul, one_pow]
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (Complex.ofReal_injective ?_)
  push_cast
  exact h.trans (((Finset.sum_congr rfl fun _ _ => mul_comm _ _).trans key).trans hsum)

end BinaryMERA

/-! ### The tree-RG circuit as a MERA -/

/-- The **tree-RG MERA** of a tensor `A` whose two-site blocked tensor is injective: its
isometries are the layers `V⁽¹⁾, …, V⁽ᵏ⁺¹⁾` of eq. (16) and its disentangler is a unitary `u`.
With `u |0⟩|0⟩ = |ω⟩` its top state is the fixed-point state `|Ω⟩`
(`approximatingMPVState_eq_state_treeMERA`).

arXiv:2307.01696, paragraph "Connection to MERA". -/
noncomputable def treeMERA (A : MPSTensor n D) (hA : Kraus.IsInjective (blockTensor A 2))
    (k : ℕ) (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ) : BinaryMERA n D k where
  disentangler := u
  disentangler_mem_unitaryGroup := hu
  fineIso := polarIsoMatrix (blockTensor A 2)
  isIsometry_fineIso := isIsometry_polarIsoMatrix_of_isInjective hA
  coarseIso := treeLayers k A
  isIsometry_coarseIso := isIsometry_treeLayers hA k

/-- A unitary on `ℂ^D ⊗ ℂ^D` preparing the pair `|ω⟩` from `|0⟩|0⟩` exists when `ω` is
normalized, that is, for `σ ≥ 0` with `Tr σ = 1`.

arXiv:2307.01696, paragraph "Connection to MERA": "the single layer of unitaries that prepare
the fixed-point state". -/
theorem exists_disentangler_fixedPointPair [NeZero D] {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∃ u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ, ∀ p, u p (0, 0) = fixedPointPair σ p := by
  let V : Matrix (Fin D × Fin D) Unit ℂ := Matrix.of fun p _ => fixedPointPair σ p
  have hV : V.IsIsometry := by
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, V,
      Matrix.of_apply]
    exact (fixedPointPair_norm_sq hσ).trans htr
  obtain ⟨u, hu, huV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV
    ⟨fun _ => ((0 : Fin D), (0 : Fin D)), fun a b _ => Subsingleton.elim a b⟩
  exact ⟨u, hu, fun p => huV p ()⟩

end MPSPreparation
