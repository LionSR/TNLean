/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Examples.ZMod2

/-!
# Cluster state as a Matrix Product State

This module defines the 1D cluster-state MPS tensor with physical dimension
`d = 2` and bond dimension `D = 2`, and proves its key properties.  The cluster
state is the canonical example of a non-injective MPS whose length-`2` blocking
is injective and which lies in a non-trivial symmetry-protected topological
(SPT) phase, protected by an on-site `Z₂ × Z₂` symmetry.

## Main definitions

* `clusterTensor` : the cluster-state MPS tensor with `A⁰ = |+⟩⟨0|`,
  `A¹ = |−⟩⟨1|`
* `clusterBlocked` : the length-`2` blocked tensor (physical dimension `4`)
* `clusterZ2Z2Action` : the `Z₂ × Z₂` on-site representation on the blocked
  physical space via `σx ⊗ I` and `I ⊗ σx`

## Main results

* `cluster_not_isInjective` : the cluster tensor is not `1`-block injective
* `cluster_isNBlkInjective_two` / `cluster_isNormal` : the cluster tensor is
  `2`-block injective, hence normal
* `clusterBlocked_isInjective` : the length-`2` blocked tensor is injective
* `cluster_isOnSiteSymmetric_Z2Z2` : the blocked tensor is on-site symmetric
  under `Z₂ × Z₂`, with anticommuting virtual gauges `σz` and `σx`

## References

* RMP review (arXiv:2011.12127) Appendix, "The cluster state"; SPT discussion
  around line 1157.  The review writes the tensor in the reflected convention
  `A⁰ = |0⟩⟨+|`, `A¹ = |1⟩⟨−|`; the convention used here is its transpose
  (equivalently, the MPS read in the opposite direction), which represents the
  same state and carries the same SPT order.
* Raussendorf, Briegel (arXiv:quant-ph/0010033) — original cluster state
-/

open scoped Matrix BigOperators
open Matrix Finset MPSTensor

noncomputable section

namespace MPSTensor

/-! ### Definition -/

/-- The cluster-state MPS tensor: a qubit chain (`d = 2`) with bond dimension
`D = 2`.

* `A⁰ = |+⟩⟨0| = (1/√2) · !![1, 0; 1, 0]`
* `A¹ = |−⟩⟨1| = (1/√2) · !![0, 1; 0, -1]` -/
def clusterTensor : MPSTensor 2 2 := fun i =>
  match i with
  | 0 => (↑(1 / Real.sqrt 2) : ℂ) • !![1, 0; 1, 0]
  | 1 => (↑(1 / Real.sqrt 2) : ℂ) • !![0, 1; 0, -1]

@[simp]
lemma clusterTensor_zero :
    clusterTensor 0 = (↑(1 / Real.sqrt 2) : ℂ) • !![1, 0; 1, 0] := rfl

@[simp]
lemma clusterTensor_one :
    clusterTensor 1 = (↑(1 / Real.sqrt 2) : ℂ) • !![0, 1; 0, -1] := rfl

/-! ### Scalar arithmetic -/

private lemma inv_sqrt2_sq :
    (↑(1 / Real.sqrt 2) : ℂ) * ↑(1 / Real.sqrt 2) = 1 / 2 := by
  rw [← Complex.ofReal_mul]
  rw [show (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 from by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
  norm_num

/-! ### Non-injectivity -/

/-- The cluster tensor is **not** injective: `span{A⁰, A¹}` is the `2`-dimensional
space of matrices whose two left-column entries agree, not the full `4`-dimensional
matrix algebra `M₂(ℂ)`. -/
theorem cluster_not_isInjective : ¬ IsInjective clusterTensor := by
  intro h
  have hmem : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈
      Submodule.span ℂ (Set.range clusterTensor) := h ▸ Submodule.mem_top
  -- Every element of the span has equal left-column entries `M 0 0 = M 1 0`.
  suffices hcol : ∀ M ∈ Submodule.span ℂ (Set.range clusterTensor), M 0 0 = M 1 0 by
    have hcontra := hcol _ hmem
    simp [Matrix.single] at hcontra
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp [clusterTensor, Matrix.smul_apply]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Matrix.add_apply]; rw [hx, hy]
  | smul c x _ hx =>
    simp only [Matrix.smul_apply, smul_eq_mul]; rw [hx]

/-! ### Length-2 products

The four products `A^{ij} = AⁱAʲ` are scalar multiples of integer matrices; the
common factor `(1/√2)² = 1/2` is collected once, leaving integer-matrix
arithmetic.  These products are reused for both the blocked tensor and the
`Z₂ × Z₂` symmetry below. -/

private lemma cluster_prod_00 :
    clusterTensor 0 * clusterTensor 0 = (1 / 2 : ℂ) • !![1, 0; 1, 0] := by
  rw [clusterTensor_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt2_sq]
  congr 1
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma cluster_prod_10 :
    clusterTensor 1 * clusterTensor 0 = (1 / 2 : ℂ) • !![1, 0; -1, 0] := by
  rw [clusterTensor_zero, clusterTensor_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt2_sq]
  congr 1
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma cluster_prod_01 :
    clusterTensor 0 * clusterTensor 1 = (1 / 2 : ℂ) • !![0, 1; 0, 1] := by
  rw [clusterTensor_zero, clusterTensor_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt2_sq]
  congr 1
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma cluster_prod_11 :
    clusterTensor 1 * clusterTensor 1 = (1 / 2 : ℂ) • !![0, -1; 0, 1] := by
  rw [clusterTensor_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt2_sq]
  congr 1
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Normality (length-2 blocked injectivity) -/

private abbrev clusterWordSpan :=
  Submodule.span ℂ (Set.range fun σ : Fin 2 → Fin 2 => evalWord clusterTensor (List.ofFn σ))

private lemma cluster_product_in_wordSpan (i j : Fin 2) :
    clusterTensor i * clusterTensor j ∈ clusterWordSpan := by
  rw [show clusterTensor i * clusterTensor j = evalWord clusterTensor [i, j] from by
    simp [evalWord]]
  have : [i, j] = List.ofFn (![i, j] : Fin 2 → Fin 2) := by
    simp [List.ofFn_succ, List.ofFn_zero]
  rw [this]
  exact Submodule.subset_span ⟨_, rfl⟩

private lemma cluster_single_00_in_wordSpan :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ clusterWordSpan := by
  have h : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) =
      clusterTensor 0 * clusterTensor 0 + clusterTensor 1 * clusterTensor 0 := by
    rw [cluster_prod_00, cluster_prod_10]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.add_apply, smul_eq_mul]; norm_num
  rw [h]
  exact Submodule.add_mem _ (cluster_product_in_wordSpan 0 0) (cluster_product_in_wordSpan 1 0)

private lemma cluster_single_10_in_wordSpan :
    Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ clusterWordSpan := by
  have h : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) =
      clusterTensor 0 * clusterTensor 0 - clusterTensor 1 * clusterTensor 0 := by
    rw [cluster_prod_00, cluster_prod_10]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.sub_apply, smul_eq_mul]; norm_num
  rw [h]
  exact Submodule.sub_mem _ (cluster_product_in_wordSpan 0 0) (cluster_product_in_wordSpan 1 0)

private lemma cluster_single_01_in_wordSpan :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ clusterWordSpan := by
  have h : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) =
      clusterTensor 0 * clusterTensor 1 - clusterTensor 1 * clusterTensor 1 := by
    rw [cluster_prod_01, cluster_prod_11]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.sub_apply, smul_eq_mul]; norm_num
  rw [h]
  exact Submodule.sub_mem _ (cluster_product_in_wordSpan 0 1) (cluster_product_in_wordSpan 1 1)

private lemma cluster_single_11_in_wordSpan :
    Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ clusterWordSpan := by
  have h : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) =
      clusterTensor 0 * clusterTensor 1 + clusterTensor 1 * clusterTensor 1 := by
    rw [cluster_prod_01, cluster_prod_11]
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.add_apply, smul_eq_mul]; norm_num
  rw [h]
  exact Submodule.add_mem _ (cluster_product_in_wordSpan 0 1) (cluster_product_in_wordSpan 1 1)

/-- The cluster tensor is `2`-block injective: products of length `2` span `M₂(ℂ)`. -/
theorem cluster_isNBlkInjective_two : IsNBlkInjective clusterTensor 2 := by
  rw [IsNBlkInjective, eq_top_iff]
  intro M _
  have hM : M = M 0 0 • Matrix.single 0 0 1 + M 0 1 • Matrix.single 0 1 1 +
      M 1 0 • Matrix.single 1 0 1 + M 1 1 • Matrix.single 1 1 1 := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  rw [hM]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ cluster_single_00_in_wordSpan)
    (Submodule.smul_mem _ _ cluster_single_01_in_wordSpan))
    (Submodule.smul_mem _ _ cluster_single_10_in_wordSpan))
    (Submodule.smul_mem _ _ cluster_single_11_in_wordSpan)

/-- The cluster tensor is normal (eventually block-injective). -/
theorem cluster_isNormal : IsNormal clusterTensor := ⟨2, cluster_isNBlkInjective_two⟩

/-! ### The length-2 blocked tensor

`clusterBlocked` is the length-`2` physical blocking of `clusterTensor`, presented
on the physical index `Fin 4 = Fin (2²)`.  Its four matrices are the products
`A^{w₀}A^{w₁}` indexed in the little-endian order used by `blockTensor`. -/

private lemma cluster_blockPhysDim : blockPhysDim 2 2 = 4 := by
  simp [blockPhysDim_eq_pow]

/-- The length-`2` blocked cluster tensor, presented on `Fin 4`. -/
def clusterBlocked : MPSTensor 4 2 :=
  fun i => blockTensor clusterTensor 2 (Fin.cast cluster_blockPhysDim.symm i)

private lemma clusterBlocked_apply (i : Fin 4) :
    clusterBlocked i =
      clusterTensor (decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm i) 0) *
        clusterTensor (decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm i) 1) := by
  simp only [clusterBlocked, blockTensor, wordOfBlock]
  simp [List.ofFn_succ, List.ofFn_zero, evalWord]

private lemma decodeBlock_cast_val (i : Fin 4) (j : Fin 2) :
    ((decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm i)) j : ℕ) =
      i.val / 2 ^ (j : ℕ) % 2 := by
  unfold decodeBlock
  simp only [Function.comp_apply, finFunctionFinEquiv_symm_apply_val]
  rfl

private lemma decode_0 : decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm 0) = ![0, 0] := by
  funext j; apply Fin.ext; rw [decodeBlock_cast_val]; fin_cases j <;> decide

private lemma decode_1 : decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm 1) = ![1, 0] := by
  funext j; apply Fin.ext; rw [decodeBlock_cast_val]; fin_cases j <;> decide

private lemma decode_2 : decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm 2) = ![0, 1] := by
  funext j; apply Fin.ext; rw [decodeBlock_cast_val]; fin_cases j <;> decide

private lemma decode_3 : decodeBlock 2 2 (Fin.cast cluster_blockPhysDim.symm 3) = ![1, 1] := by
  funext j; apply Fin.ext; rw [decodeBlock_cast_val]; fin_cases j <;> decide

@[simp] private lemma clusterBlocked_zero :
    clusterBlocked 0 = (1 / 2 : ℂ) • !![1, 0; 1, 0] := by
  rw [clusterBlocked_apply, decode_0]; simpa using cluster_prod_00

@[simp] private lemma clusterBlocked_one :
    clusterBlocked 1 = (1 / 2 : ℂ) • !![1, 0; -1, 0] := by
  rw [clusterBlocked_apply, decode_1]; simpa using cluster_prod_10

@[simp] private lemma clusterBlocked_two :
    clusterBlocked 2 = (1 / 2 : ℂ) • !![0, 1; 0, 1] := by
  rw [clusterBlocked_apply, decode_2]; simpa using cluster_prod_01

@[simp] private lemma clusterBlocked_three :
    clusterBlocked 3 = (1 / 2 : ℂ) • !![0, -1; 0, 1] := by
  rw [clusterBlocked_apply, decode_3]; simpa using cluster_prod_11

/-- The length-`2` blocked cluster tensor is injective: its four matrices span
`M₂(ℂ)`.  This is the blocked-tensor form of `cluster_isNBlkInjective_two`. -/
theorem clusterBlocked_isInjective : IsInjective clusterBlocked := by
  rw [IsInjective, eq_top_iff]
  intro M _
  have hspan : ∀ p q : Fin 2, Matrix.single p q (1 : ℂ) ∈
      Submodule.span ℂ (Set.range clusterBlocked) := by
    have mem : ∀ i : Fin 4, clusterBlocked i ∈ Submodule.span ℂ (Set.range clusterBlocked) :=
      fun i => Submodule.subset_span ⟨i, rfl⟩
    intro p q
    fin_cases p <;> fin_cases q
    · refine (show Matrix.single (0 : Fin 2) 0 (1 : ℂ) = clusterBlocked 0 + clusterBlocked 1 from
        by ext a b; fin_cases a <;> fin_cases b <;>
          simp [Matrix.single, Matrix.add_apply, smul_eq_mul]; norm_num) ▸
        Submodule.add_mem _ (mem 0) (mem 1)
    · refine (show Matrix.single (0 : Fin 2) 1 (1 : ℂ) = clusterBlocked 2 - clusterBlocked 3 from
        by ext a b; fin_cases a <;> fin_cases b <;>
          simp [Matrix.single, Matrix.sub_apply, smul_eq_mul]; norm_num) ▸
        Submodule.sub_mem _ (mem 2) (mem 3)
    · refine (show Matrix.single (1 : Fin 2) 0 (1 : ℂ) = clusterBlocked 0 - clusterBlocked 1 from
        by ext a b; fin_cases a <;> fin_cases b <;>
          simp [Matrix.single, Matrix.sub_apply, smul_eq_mul]; norm_num) ▸
        Submodule.sub_mem _ (mem 0) (mem 1)
    · refine (show Matrix.single (1 : Fin 2) 1 (1 : ℂ) = clusterBlocked 2 + clusterBlocked 3 from
        by ext a b; fin_cases a <;> fin_cases b <;>
          simp [Matrix.single, Matrix.add_apply, smul_eq_mul]; norm_num) ▸
        Submodule.add_mem _ (mem 2) (mem 3)
  have hM : M = M 0 0 • Matrix.single 0 0 1 + M 0 1 • Matrix.single 0 1 1 +
      M 1 0 • Matrix.single 1 0 1 + M 1 1 • Matrix.single 1 1 1 := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  rw [hM]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hspan 0 0)) (Submodule.smul_mem _ _ (hspan 0 1)))
    (Submodule.smul_mem _ _ (hspan 1 0))) (Submodule.smul_mem _ _ (hspan 1 1))

/-! ### The Z₂ × Z₂ on-site symmetry of the blocked tensor

The two generators act on the blocked physical space `(ℂ²)^{⊗2}` by `σx ⊗ I`
(flip the first site) and `I ⊗ σx` (flip the second site).  On the bond space
these are implemented by the anticommuting virtual gauges `σz` and `σx`; their
anticommutation (proved as `cluster_gauge_anticomm`) is the projective obstruction
distinguishing this SPT phase. -/

/-- Flip the first physical qubit (`σx ⊗ I`): the permutation `(0 1)(2 3)` of the
blocked physical index. -/
def clusterPhysX1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- Flip the second physical qubit (`I ⊗ σx`): the permutation `(0 2)(1 3)`. -/
def clusterPhysX2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

private lemma clusterPhysX1_sq : clusterPhysX1 * clusterPhysX1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clusterPhysX1, Matrix.mul_apply, Fin.sum_univ_four]

private lemma clusterPhysX2_sq : clusterPhysX2 * clusterPhysX2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clusterPhysX2, Matrix.mul_apply, Fin.sum_univ_four]

private lemma clusterPhysX1X2_comm :
    clusterPhysX1 * clusterPhysX2 = clusterPhysX2 * clusterPhysX1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clusterPhysX1, clusterPhysX2, Matrix.mul_apply, Fin.sum_univ_four]

/-- The `Z₂ × Z₂` on-site representation on the blocked physical space.  The two
generators act by `σx ⊗ I` and `I ⊗ σx`. -/
def clusterZ2Z2Action :
    Multiplicative (ZMod 2 × ZMod 2) →* Matrix (Fin 4) (Fin 4) ℂ :=
  ofCommutingInvolutions clusterPhysX1 clusterPhysX2
    clusterPhysX1_sq clusterPhysX2_sq clusterPhysX1X2_comm

@[simp] private lemma clusterZ2Z2Action_10 :
    clusterZ2Z2Action (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) = clusterPhysX1 := by
  simp only [clusterZ2Z2Action, ofCommutingInvolutions_ofAdd_10]

@[simp] private lemma clusterZ2Z2Action_01 :
    clusterZ2Z2Action (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) = clusterPhysX2 := by
  simp only [clusterZ2Z2Action, ofCommutingInvolutions_ofAdd_01]

@[simp] private lemma clusterZ2Z2Action_11 :
    clusterZ2Z2Action (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) =
      clusterPhysX1 * clusterPhysX2 := by
  simp only [clusterZ2Z2Action, ofCommutingInvolutions_ofAdd_11]

/-! #### Virtual gauges `σz`, `σx`, and `σz σx` -/

private def clusterGaugeZ : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by norm_num [Matrix.det_fin_two])

@[simp] private lemma clusterGaugeZ_val :
    (clusterGaugeZ : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma clusterGaugeZ_inv_val :
    ((clusterGaugeZ⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := by
  have hsq : clusterGaugeZ * clusterGaugeZ = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, clusterGaugeZ_val]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show clusterGaugeZ⁻¹ = clusterGaugeZ from inv_eq_of_mul_eq_one_right hsq,
    clusterGaugeZ_val]

private def clusterGaugeX : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero pauliX (by
    simp only [Matrix.det_fin_two, pauliX, Matrix.of_apply]; norm_num)

@[simp] private lemma clusterGaugeX_val :
    (clusterGaugeX : Matrix (Fin 2) (Fin 2) ℂ) = pauliX :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma clusterGaugeX_inv_val :
    ((clusterGaugeX⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = pauliX := by
  have hsq : clusterGaugeX * clusterGaugeX = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, clusterGaugeX_val, pauliX_sq]
  rw [show clusterGaugeX⁻¹ = clusterGaugeX from inv_eq_of_mul_eq_one_right hsq,
    clusterGaugeX_val]

private def clusterGaugeZX : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by norm_num [Matrix.det_fin_two])

@[simp] private lemma clusterGaugeZX_val :
    (clusterGaugeZX : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma clusterGaugeZX_inv_val :
    ((clusterGaugeZX⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0] := by
  have h : clusterGaugeZX * Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (by norm_num [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, clusterGaugeZX_val,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show clusterGaugeZX⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) (by norm_num [Matrix.det_fin_two]) from
    inv_eq_of_mul_eq_one_right h]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The two virtual gauges `σz` and `σx` anticommute.  This is the projective
phase that witnesses the non-trivial SPT order: the group elements commute on
the physical level but their virtual representatives do not. -/
lemma cluster_gauge_anticomm :
    (!![(1 : ℂ), 0; 0, -1]) * pauliX = -(pauliX * !![(1 : ℂ), 0; 0, -1]) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.of_apply]

/-! #### Gauge equivalences for the three nontrivial group elements -/

private lemma cluster_gaugeEquiv_X1 :
    GaugeEquiv clusterBlocked
      (twistedTensor clusterBlocked clusterZ2Z2Action (Multiplicative.ofAdd (1, 0))) := by
  refine ⟨clusterGaugeZ, fun i => ?_⟩
  simp only [twistedTensor, clusterZ2Z2Action_10]
  rw [clusterGaugeZ_val, clusterGaugeZ_inv_val]
  fin_cases i <;>
    (simp only [Fin.sum_univ_four, clusterPhysX1, clusterBlocked_zero, clusterBlocked_one,
        clusterBlocked_two, clusterBlocked_three, Matrix.of_apply]
     ext a b
     fin_cases a <;> fin_cases b <;>
       simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul])

private lemma cluster_gaugeEquiv_X2 :
    GaugeEquiv clusterBlocked
      (twistedTensor clusterBlocked clusterZ2Z2Action (Multiplicative.ofAdd (0, 1))) := by
  refine ⟨clusterGaugeX, fun i => ?_⟩
  simp only [twistedTensor, clusterZ2Z2Action_01]
  rw [clusterGaugeX_val, clusterGaugeX_inv_val]
  fin_cases i <;>
    (simp only [Fin.sum_univ_four, clusterPhysX2, clusterBlocked_zero, clusterBlocked_one,
        clusterBlocked_two, clusterBlocked_three, Matrix.of_apply]
     ext a b
     fin_cases a <;> fin_cases b <;>
       simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul,
         Matrix.of_apply])

private lemma cluster_gaugeEquiv_X1X2 :
    GaugeEquiv clusterBlocked
      (twistedTensor clusterBlocked clusterZ2Z2Action (Multiplicative.ofAdd (1, 1))) := by
  refine ⟨clusterGaugeZX, fun i => ?_⟩
  simp only [twistedTensor, clusterZ2Z2Action_11]
  rw [clusterGaugeZX_val, clusterGaugeZX_inv_val]
  fin_cases i <;>
    (simp only [Fin.sum_univ_four, clusterPhysX1, clusterPhysX2, clusterBlocked_zero,
        clusterBlocked_one, clusterBlocked_two, clusterBlocked_three, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        add_zero, zero_add, mul_zero, mul_one]
     ext a b
     fin_cases a <;> fin_cases b <;>
       simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul])

/-- The length-`2` blocked cluster tensor is on-site symmetric under `Z₂ × Z₂`,
with anticommuting virtual gauges `σz` and `σx`.  This exhibits the cluster
state as a non-trivial symmetry-protected topological phase. -/
theorem cluster_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric clusterBlocked clusterZ2Z2Action := by
  intro g
  rcases zmod2sq_cases g with rfl | rfl | rfl | rfl
  · rw [twistedTensor_one]; exact fun _ _ => rfl
  · exact cluster_gaugeEquiv_X1.sameMPV
  · exact cluster_gaugeEquiv_X2.sameMPV
  · exact cluster_gaugeEquiv_X1X2.sameMPV

end MPSTensor

end
