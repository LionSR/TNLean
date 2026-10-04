/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.TreeFactorization

/-!
# The tree-RG circuit as a finite-range MERA

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, paragraph "Connection to MERA") observe that
the tree-RG circuit of eq. (16) is a finite-range MERA with `O(log log N)` layers: the
isometries `V⁽ʲ⁾` of eq. (16) are the isometries of the MERA, and all disentanglers are the
identity except those of the first layer, which prepare the fixed-point state. Hence, within
the approximation error, normal translation-invariant MPS are finite-range MERA with
`O(log log N)` layers.

This file gives a minimal definition of a binary finite-range MERA on a ring and proves the
statement for block length `q = 2^{k+1}`.

## The MERA

A `MPSPreparation.BinaryMERA n D k` consists of

* one layer of disentanglers: a unitary `u` on `ℂ^D ⊗ ℂ^D`, applied to `|0⟩|0⟩` on every
  pair `R_i L_{i+1}` of neighbouring bond legs of the ring of top sites `ℂ^{D²} = L_i ⊗ R_i`;
* `k + 1` layers of isometries: `k` coarse isometries `ℂ^{D²} → ℂ^{D²} ⊗ ℂ^{D²}` and a finest
  isometry `ℂ^{D²} → ℂⁿ ⊗ ℂⁿ`, each copied on every site of its layer.

Every isometry maps one site to two neighbouring sites and every disentangler acts on two
neighbouring legs, so the network has range two and bond dimension `D²` in every layer. The
disentanglers of the lower layers are the identity, as in the source's identification; the
class is therefore a subclass of the finite-range MERA with `k + 2` layers.

## Main declarations

* `MPSTensor.binaryTreeMatrix` — the product `W^{⊗2^k} (V₀)^{⊗2^{k-1}} ⋯ V_{k-1}` of a
  binary tree of layers, regrouped along neighbouring pairs.
* `MPSPreparation.BinaryMERA` and `MPSPreparation.BinaryMERA.state` — the MERA and its state on
  `M 2^{k+1}` sites; `MPSPreparation.BinaryMERA.norm_state` — the state is a unit vector.
* `MPSPreparation.treeMERA` — the MERA whose isometries are the layers `V⁽ʲ⁾` of eq. (16) and
  whose disentanglers prepare the pairs `|ω⟩` of the fixed-point state.
* `MPSPreparation.approximatingMPVState_eq_state_treeMERA` — the approximating state
  `|φ'_N⟩ = V^{⊗M} |Ω⟩` of eq. (10) for `q = 2^{k+1}` is the state of `treeMERA` (exact).
* `MPSPreparation.exists_state_treeMERA_approximationError_le` — with the approximation-error
  bound `exists_approximationError_le_mul` at `γ = 1/2` (the rate `e^{-2γq/ξ}` of that theorem,
  which strengthens Lemma 1'(i) of the source, stated there for `0 < γ < 1/2` with rate
  `e^{-γq/ξ}`), the error of the MERA state against `|φ_N⟩` is at most `ε` once
  `2^{k+1} ≥ ξ log(C N/ε)`;
  `MPSPreparation.exists_state_treeMERA_approximationError_le_and_le_logb` shows that for every
  `M` such a `k` exists with `k ≤ log₂(max 1 (ξ log(C N/ε)))`, so
  `k + 1 = O(log log(N/ε))` layers suffice.
* `MPSPreparation.mul_mul_exp_neg_div_le_of_mul_log_le` and
  `MPSPreparation.exists_mul_log_le_mul_two_pow_and_le_logb` — the two real inequalities behind
  these bounds, also used with registers of `s` sites in
  `TNLean.MPS.Preparation.TreeMERARegisters`.

**Scope of the equal-block construction:** the theorems
`approximatingMPVState_eq_state_treeMERA`, `exists_state_treeMERA_approximationError_le` and
`exists_state_treeMERA_approximationError_le_and_le_logb` (and the definition `treeMERA`) assume
that the two-site blocked tensor is injective, so that every layer `V⁽ʲ⁾` is an isometry, as in
the source, whose eq. (16) starts from a blocked tensor and calls the layers isometries.
`TNLean.MPS.Preparation.TreeMERARegisters` applies `treeMERA` to the tensor blocked over `s`
sites, with registers of `s` sites, and covers every normal tensor. The chain length is
`N = M 2^{k+1}`: the layer count holds for the chain lengths `M 2^{k+1}` with `k` given by the
threshold, not for every fixed `N` and `ε` (for `N = 2p` with `p` odd only `k = 0` is available).
The sibling construction in `TNLean.MPS.Preparation.UnequalTreeMERA` covers every positive
length with nonzero periodic state, using uniformly bounded physical leaves chosen before
`N` and `ε`. The resolved scope is documented in `docs/paper-gaps/mswc24_tree_mera_scope.tex`.

## References

* arXiv:2307.01696, paragraphs "The tree-RG circuit" (eq. (16)) and "Connection to MERA".
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

/-- **The approximating state is a MERA state** (arXiv:2307.01696, paragraph "Connection to
MERA", with eqs. (10) and (16)). Let the two-site blocked tensor of `A` be injective, let
`σ ≥ 0` with `Tr σ = 1`, and let `u` be a unitary with `u |0⟩|0⟩ = |ω⟩`. For block length
`q = 2^{k+1}` and `M ≥ 1` blocks, the approximating state `|φ'_N⟩ = V^{⊗M} |Ω⟩` of eq. (10) is
exactly the state of the tree-RG MERA with `k + 1` isometry layers. -/
theorem approximatingMPVState_eq_state_treeMERA [NeZero D] (A : MPSTensor d D)
    (hA : Kraus.IsInjective (blockTensor A 2)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (k M : ℕ) [NeZero M]
    (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ) (hu0 : ∀ p, u p (0, 0) = fixedPointPair σ p) :
    approximatingMPVState A σ (2 ^ (k + 1)) M = (treeMERA A hA k u hu).state M := by
  have hq : Kraus.IsInjective (blockTensor A (2 ^ (k + 1))) := by
    have := blockTensor_isInjective_mul_of_blockTensor_isInjective A
      (pow_pos two_pos k) hA
    rwa [← pow_succ] at this
  rw [(inner_approximatingMPVState_mpvState A hq hσ htr M).1]
  have htop : (treeMERA A hA k u hu).topPair = fixedPointPair σ := funext hu0
  have htree : (treeMERA A hA k u hu).treeMatrix = polarIsoMatrix (blockTensor A (2 ^ (k + 1))) :=
    (binaryTreeMatrix_treeLayers k A).trans (polarIsoMatrix_blockTensor_eq_treeIsoMatrix k A).symm
  ext s
  rw [approximatingMPVStateRaw_apply, BinaryMERA.state_apply, BinaryMERA.amplitude, htop, htree,
    mpv_approximatingTensor]

/-! ### The threshold of the number of layers -/

/-- **From the threshold of the MERA to the error.** For `K, ξ, ε > 0` and `M, q ≥ 1`, if
`ξ log(K M q/ε) ≤ q` then `K (M e^{-q/ξ}) ≤ ε`. -/
theorem mul_mul_exp_neg_div_le_of_mul_log_le {K M q ξ ε : ℝ} (hK : 0 < K) (hM : 1 ≤ M)
    (hq : 1 ≤ q) (hξ : 0 < ξ) (hε : 0 < ε) (h : ξ * Real.log (K * (M * q) / ε) ≤ q) :
    K * (M * Real.exp (-(q / ξ))) ≤ ε := by
  have hM0 : 0 < M := by linarith
  refine mul_mul_exp_neg_le_of_log_le hK hM0 hε ?_
  rw [← Real.log_mul hK.ne' hM0.ne', ← Real.log_div (by positivity) hε.ne', le_div_iff₀ hξ]
  refine le_trans ?_ ((mul_comm _ _).trans_le h)
  refine mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) ?_) hξ.le
  gcongr
  exact le_mul_of_one_le_right hM0.le hq

/-- **The least number of layers with the threshold.** For `ξ, C, M, ε > 0` and `s ≥ 1` there is
`k` with `x ≤ s 2^{k+1}` and `k ≤ log₂(max 1 x)`, where `x = ξ log(C M s 2^{k+1}/ε)`. The left
side of the threshold grows linearly in `k` and the right side exponentially; for the least such
`k`, if `k ≥ 1` the threshold fails at `k - 1`, so `2^k ≤ s 2^k < x`. -/
theorem exists_mul_log_le_mul_two_pow_and_le_logb {ξ C M ε s : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    (hM : 0 < M) (hε : 0 < ε) (hs : 1 ≤ s) : ∃ k : ℕ,
      ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) ≤ s * 2 ^ (k + 1) ∧
      (k : ℝ) ≤ Real.logb 2 (max 1 (ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε))) := by
  classical
  set x : ℕ → ℝ := fun k => ξ * Real.log (C * (M * (s * 2 ^ (k + 1))) / ε) with hx
  have hxk : ∀ k : ℕ,
      x k = ξ * Real.log (C * M * s / ε) + ξ * Real.log 2 * ((k + 1 : ℕ) : ℝ) := by
    intro k
    simp only [hx]
    rw [show C * (M * (s * 2 ^ (k + 1))) / ε = C * M * s / ε * 2 ^ (k + 1) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hex : ∃ k, x k ≤ s * 2 ^ (k + 1) := by
    have hlim : Filter.Tendsto (fun m : ℕ => ξ * Real.log (C * M * s / ε) * ((m : ℝ) ^ 0 / 2 ^ m) +
        ξ * Real.log 2 * ((m : ℝ) ^ 1 / 2 ^ m)) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_pow_const_div_const_pow_of_one_lt 0 one_lt_two).const_mul
        (ξ * Real.log (C * M * s / ε))).add
          ((tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two).const_mul (ξ * Real.log 2))
    obtain ⟨m, hm1, hm⟩ := ((Filter.eventually_ge_atTop 1).and
      (hlim.eventually (gt_mem_nhds one_pos))).exists
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨k, ?_⟩
    rw [hxk]
    have h2m : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    simp only [pow_zero, pow_one] at hm
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_lt_one h2m, mul_one] at hm
    calc _ ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hm.le
      _ ≤ s * 2 ^ (k + 1) := le_mul_of_one_le_left h2m.le hs
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  obtain h0 | ⟨j, hj⟩ : Nat.find hex = 0 ∨ ∃ j, Nat.find hex = j + 1 :=
    (Nat.eq_zero_or_pos _).imp id fun hpos => ⟨Nat.find hex - 1, by omega⟩
  · rw [h0, Nat.cast_zero]
    exact Real.logb_nonneg one_lt_two (le_max_left _ _)
  · rw [hj]
    have hfail : ¬ x j ≤ s * 2 ^ (j + 1) := Nat.find_min hex (by omega)
    have hmono : x j ≤ x (j + 1) := by
      rw [hxk, hxk]
      have : 0 ≤ ξ * Real.log 2 := mul_nonneg hξ.le (Real.log_nonneg one_le_two)
      gcongr
      omega
    have hlt : (2 : ℝ) ^ (j + 1) < x (j + 1) :=
      (le_mul_of_one_le_left (by positivity) hs).trans_lt ((not_le.1 hfail).trans_le hmono)
    have hx1 : 1 < x (j + 1) := (one_le_pow₀ one_le_two).trans_lt hlt
    rw [max_eq_right hx1.le]
    refine (Real.lt_logb_iff_rpow_lt one_lt_two (zero_lt_one.trans hx1)).2 ?_ |>.le
    rwa [Real.rpow_natCast]

/-- **Normal MPS are finite-range MERA with `O(log log(N/ε))` layers, within `ε`**
(arXiv:2307.01696, paragraph "Connection to MERA"). Let `A` be normal, in the
gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` of eq. (5), let `0 < t < 1` bound the
moduli of the eigenvalues of `E_A` other than `1`, with `ξ = -1/log t`, and let the two-site
blocked tensor of `A` be injective. Then there is `C > 0` such that for every unitary `u` with
`u |0⟩|0⟩ = |ω⟩`, every `ε > 0`, and every `k` and `M ≥ 1` with
`ξ log(C N/ε) ≤ 2^{k+1}`, `N = M 2^{k+1}`, the state of the tree-RG MERA with `k + 1` isometry
layers has error `1 - |⟨ψ|φ_N⟩| ≤ ε` against the normalized state `|φ_N⟩` of `A`.

The error bound is `exists_approximationError_le_mul` at `γ = 1/2`, with rate `e^{-q/ξ}`; that
theorem strengthens Lemma 1'(i) of the source, which is stated for `0 < γ < 1/2` with rate
`e^{-γq/ξ}` and would give the threshold `(ξ/γ) log(C N/ε)` instead. The MERA state is the
approximating state (`approximatingMPVState_eq_state_treeMERA`). -/
theorem exists_state_treeMERA_approximationError_le [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) (h2 : Kraus.IsInjective (blockTensor A 2))
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (k M : ℕ) [NeZero M],
        correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε) ≤ 2 ^ (k + 1) →
          1 - ‖⟪(treeMERA A h2 k u hu).state M, normalizedMPVState A (M * 2 ^ (k + 1))⟫_ℂ‖ ≤
            ε := by
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (γ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K, hK, fun u hu hu0 ε hε k M _ hk => ?_⟩
  rw [← approximatingMPVState_eq_state_treeMERA A h2 hσ.posSemidef htr k M u hu hu0]
  refine (herr _ M).trans ?_
  set ξ := correlationLength (t : ℂ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hq1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
  have hexp : Real.exp (-(2 * (1 / 2 : ℝ)) * ((2 ^ (k + 1) : ℕ) : ℝ) / ξ) =
      Real.exp (-((2 : ℝ) ^ (k + 1) / ξ)) := by
    push_cast
    ring_nf
  rw [hexp]
  exact mul_mul_exp_neg_div_le_of_mul_log_le hK hM1 hq1 hξ hε hk

/-- **The number of layers is `O(log log(N/ε))`** (arXiv:2307.01696, paragraph "Connection to
MERA": "a finite-range MERA with $O(\log \log N)$ layers"). In the setting of
`exists_state_treeMERA_approximationError_le`, for every unitary `u` with `u |0⟩|0⟩ = |ω⟩`, every
`ε > 0` and every `M ≥ 1` there is `k` such that, with `N = M 2^{k+1}` and
`x = ξ log(C N/ε)`, the threshold `x ≤ 2^{k+1}` holds, the tree-RG MERA with `k + 1` isometry
layers has error at most `ε`, and `k ≤ log₂(max 1 x)`. The exponent `k` is the least one with the
threshold: the left side of the threshold grows linearly in `k` and the right side exponentially,
and if `k ≥ 1` the threshold fails at `k - 1`, so `2^k < x`. -/
theorem exists_state_treeMERA_approximationError_le_and_le_logb [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) (h2 : Kraus.IsInjective (blockTensor A 2))
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (hfix : Kraus.transferMap A σ = σ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ), (∀ p, u p (0, 0) = fixedPointPair σ p) →
      ∀ ε : ℝ, 0 < ε → ∀ (M : ℕ) [NeZero M], ∃ k : ℕ,
        correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε) ≤ 2 ^ (k + 1) ∧
        1 - ‖⟪(treeMERA A h2 k u hu).state M, normalizedMPVState A (M * 2 ^ (k + 1))⟫_ℂ‖ ≤ ε ∧
        (k : ℝ) ≤ Real.logb 2 (max 1
          (correlationLength (t : ℂ) * Real.log (C * (M * 2 ^ (k + 1)) / ε))) := by
  obtain ⟨C, hC, h⟩ := exists_state_treeMERA_approximationError_le A hN hA h2 hσ htr hfix ht0 ht1
    hlam
  refine ⟨C, hC, fun u hu hu0 ε hε M _ => ?_⟩
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨k, hk, hlog⟩ := exists_mul_log_le_mul_two_pow_and_le_logb
    (correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])) hC
    (M := (M : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)) hε (s := 1) le_rfl
  simp only [one_mul] at hk hlog
  exact ⟨k, hk, h u hu hu0 ε hε k M hk, hlog⟩

end MPSPreparation
