/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Examples.KramersWannier.KramersWannierSource
import TNLean.MPS.FundamentalTheorem.Reduction.MPOProduct
import TNLean.MPS.MPDO.BondOneOperator
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Kramers–Wannier duality as a matrix product operator bimodule

**Source.** Aasen, Mong, Fendley 2016 (arXiv:1601.07185), subsection "The duality defect",
`References/1601.07185/source/Ising-Defects.tex` lines 1033–1056: the duality defect `D_σ`
absorbs the spin-flip defect on both sides, `D_σ D_ψ = D_ψ D_σ = D_σ`, and fuses with its
return map to the primal lattice to `1 + D_ψ`. Lootens, Delcamp, Ortiz, Verstraete 2021
(arXiv:2112.09091), `References/2112.09091/source/_Hamiltonian.tex` lines 49–77 and 318–336,
read the Kramers–Wannier kernel as a matrix product operator intertwiner between two
realizations of the `ℤ₂` symmetry: it is fused with the symmetry operators of either side,
rather than being a member of one fusion algebra. On one lattice the square of the kernel is
`2^N (1 + η) T` with the translation `T` (`KWExample.kwTensor_mpo_mul_self`), so the kernel does
not belong to the fusion algebra `{1, η}`.

**Formalized here.** For the raw kernel `K = kwTensor.mpo N` on a ring of `N ≥ 1` sites, with
`η` the global spin flip:

* the operators `1` and `η` are the periodic operators of two bond-one tensors, and form a
  matrix product operator fusion algebra with the group fusion rule of `ℤ₂`;
* `K` is a bimodule over this algebra with trivial action: `K O_a = O_a K = K` for both labels;
* `K Kᵀ = Kᵀ K = 2^N (O_1 + O_η)`, where `Kᵀ = K†` is the periodic operator of the tensor
  `kwTransposeTensor` obtained by exchanging the two physical legs.

**Project results.** The tensor-level form of these relations, obtained from the asymmetric
compression theorem for products of matrix product operators
(`MPOTensor.exists_multiBlockCompression_mulTensor_of_mpo_eq_sum`, Theorem 7.12 of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`), with no computation of
gauges.

* Absorption of `η` is a gauge equivalence: the stacked tensors `K · η` and `η · K` of bond
  dimension two are conjugate, letter by letter, to the kernel tensor itself.
* The stacked tensor `K · Kᵀ` of bond dimension four compresses onto the two weighted bond-one
  blocks `2 · 1` and `2 · η`, and the dimension count `4 = 1 + 1 + 2` forces exactly two zero
  slots. The same holds for `Kᵀ · K`. The biorthogonal pairs of this compression are the fusion
  tensors of the channels `1` and `η` in the product of the intertwiner with its adjoint.

By contrast, the stacked tensor `K · K` compresses onto the bond-two blocks `2 T` and `2 η T`
with no zero slot (`KWExample.kwSquare_compression`).

## Main definitions

* `KWExample.flipTensor`: the bond-one tensor of `η`; the identity is `MPOTensor.idTensor 2`.
* `KWExample.z2Tensor`: the two blocks of the `ℤ₂` symmetry algebra, labelled by `ℤ/2`.
* `KWExample.kwTransposeTensor`: the kernel tensor with its physical legs exchanged.

## Main results

* `KWExample.mpo_flipTensor`: the flip tensor generates the global spin flip.
* `KWExample.isMPOFusionAlgebra_z2Tensor`: the `ℤ₂` fusion rule.
* `KWExample.kwTensor_mpo_mul_z2Tensor_mpo`, `KWExample.z2Tensor_mpo_mul_kwTensor_mpo`: the
  two-sided absorption of the symmetry.
* `KWExample.kwTensor_mpo_mul_kwTransposeTensor_mpo`,
  `KWExample.kwTransposeTensor_mpo_mul_kwTensor_mpo`: the fusion of the kernel with its adjoint.
* `KWExample.exists_gauge_mulTensor_kwTensor_flipTensor`,
  `KWExample.exists_gauge_mulTensor_flipTensor_kwTensor`: the tensor-level absorption.
* `KWExample.exists_compression_mulTensor_kwTensor_kwTransposeTensor`,
  `KWExample.exists_compression_mulTensor_kwTransposeTensor_kwTensor`: the compressions onto
  `2 · 1 ⊕ 2 · η` with two zero slots.

## References

- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong,
  P. Fendley, *Topological defects on the lattice I: The Ising model*
- [arXiv:2112.09091](https://arxiv.org/abs/2112.09091) -- L. Lootens, C. Delcamp, G. Ortiz,
  F. Verstraete, *Dualities in one-dimensional quantum lattice models: symmetric Hamiltonians and
  matrix product operator intertwiners*
-/

noncomputable section

open scoped Matrix BigOperators

namespace KWExample

open MPOTensor

variable {N : ℕ}

/-! ### The symmetry algebra -/

/-- The bond-one tensor of the global spin flip `η = ∏_j X_j`, `δ_{s', 1 - s}`. -/
def flipTensor : MPOTensor 2 1 := fun i j => Matrix.of fun _ _ => if i = j.rev then 1 else 0

/-- The flip tensor generates the global spin flip at every positive length. -/
theorem mpo_flipTensor [NeZero N] : flipTensor.mpo N = spinFlip N := by
  ext σ τ
  rw [mpo_apply_of_bondOne]
  simp only [flipTensor, Matrix.of_apply, spinFlip]
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  split_ifs with h₁ h₂ h₂ <;> simp_all [funext_iff, flipConfig]

/-- The two blocks `1` and `η` of the `ℤ₂` symmetry algebra, labelled by `ℤ/2`. -/
def z2Tensor : Fin 2 → MPOTensor 2 1
  | 0 => idTensor 2
  | 1 => flipTensor

/-- Source: arXiv:2203.12563, line 660: the fusion ring of the group `ℤ/2`,
`N_{ab}^c = δ_{c, a + b}`. -/
def z2Fusion (a b c : Fin 2) : ℕ := if c = a + b then 1 else 0

/-- Both blocks of the symmetry algebra are normal: each has a one-site matrix equal to the
scalar `1`. -/
theorem z2Tensor_isNormal (a : Fin 2) : Kraus.IsNormal (z2Tensor a).toMPSTensor := by
  fin_cases a
  · exact isNormal_of_bondOne (idTensor 2) 0 0 (by simp [idTensor])
  · exact isNormal_of_bondOne flipTensor 1 0 (by simp [flipTensor])

/-- The block labelled `0` generates the identity. -/
theorem mpo_z2Tensor_zero : (z2Tensor 0).mpo N = 1 := mpo_idTensor 2 N

/-- The block labelled `1` generates the global spin flip at every positive length. -/
theorem mpo_z2Tensor_one [NeZero N] : (z2Tensor 1).mpo N = spinFlip N := mpo_flipTensor

/-- **The `ℤ₂` symmetry algebra of the Ising chain.** The periodic operators `1` and `η` obey
the group fusion rule of `ℤ/2` at every positive length.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1052–1056
(`D_ψ² = 1`), in the form of arXiv:2203.12563, lines 361–362 and 660. -/
theorem isMPOFusionAlgebra_z2Tensor : IsMPOFusionAlgebra z2Tensor z2Fusion := by
  intro a b L hL
  have : NeZero L := NeZero.of_pos hL
  have hsum : ∑ c, (z2Fusion a b c : ℂ) • (z2Tensor c).mpo L = (z2Tensor (a + b)).mpo L := by
    simp [z2Fusion, ite_smul]
  rw [hsum]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_add, add_zero,
      show (1 : Fin 2) + 1 = 0 from rfl, mpo_z2Tensor_zero, mpo_z2Tensor_one, one_mul, mul_one,
      spinFlip_mul_self]

/-! ### The kernel as a bimodule over the symmetry algebra -/

/-- **The kernel absorbs the symmetry on its input**, `K O_a = K` for both labels.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1052–1056
(`D_σ D_ψ = D_σ`). -/
theorem kwTensor_mpo_mul_z2Tensor_mpo [NeZero N] (a : Fin 2) :
    kwTensor.mpo N * (z2Tensor a).mpo N = kwTensor.mpo N := by
  fin_cases a
  · exact (congrArg _ mpo_z2Tensor_zero).trans (Matrix.mul_one _)
  · exact (congrArg _ mpo_z2Tensor_one).trans kwTensor_mpo_mul_spinFlip

/-- **The kernel absorbs the symmetry on its output**, `O_a K = K` for both labels.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1052–1056
(`D_ψ D_σ = D_σ`). -/
theorem z2Tensor_mpo_mul_kwTensor_mpo [NeZero N] (a : Fin 2) :
    (z2Tensor a).mpo N * kwTensor.mpo N = kwTensor.mpo N := by
  fin_cases a
  · exact (congrArg (· * _) mpo_z2Tensor_zero).trans (Matrix.one_mul _)
  · exact (congrArg (· * _) mpo_z2Tensor_one).trans spinFlip_mul_kwTensor_mpo

/-- The kernel tensor with its two physical legs exchanged, `(Kᵀ)^{s's} = K^{ss'}`. It
generates the transpose of the kernel, which is its adjoint (`kwTensor_mpo_conjTranspose`). -/
def kwTransposeTensor : MPOTensor 2 2 := fun i j => kwTensor j i

private theorem evalWord_kwTransposeTensor :
    ∀ is js : List (Fin 2),
      MPOTensor.evalWord kwTransposeTensor is js = MPOTensor.evalWord kwTensor js is
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | i :: is, j :: js => by
      rw [MPOTensor.evalWord_cons, MPOTensor.evalWord_cons, evalWord_kwTransposeTensor is js]
      rfl

/-- The exchanged tensor generates the transpose of the kernel at every length. -/
theorem mpo_kwTransposeTensor : kwTransposeTensor.mpo N = (kwTensor.mpo N)ᵀ := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, Matrix.transpose_apply]
  rw [evalWord_kwTransposeTensor]

/-- **The kernel fused with its adjoint**, `K Kᵀ = 2^N (O_1 + O_η)`, as a sum over the
symmetry algebra.

Project result: the dual-lattice companion of the source's fusion
(`kwTensor_mpo_mul_transpose`). -/
theorem kwTensor_mpo_mul_kwTransposeTensor_mpo [NeZero N] :
    kwTensor.mpo N * kwTransposeTensor.mpo N = ∑ a, (2 : ℂ) ^ N • (z2Tensor a).mpo N := by
  rw [mpo_kwTransposeTensor, kwTensor_mpo_mul_transpose, Fin.sum_univ_two, mpo_z2Tensor_zero,
    mpo_z2Tensor_one, smul_add]

/-- **The adjoint fused with the kernel**, `Kᵀ K = 2^N (O_1 + O_η)`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1033–1039
(`D_σ² = 1 + D_ψ`, with `D_σ²` the defect followed by its return map). -/
theorem kwTransposeTensor_mpo_mul_kwTensor_mpo [NeZero N] :
    kwTransposeTensor.mpo N * kwTensor.mpo N = ∑ a, (2 : ℂ) ^ N • (z2Tensor a).mpo N := by
  rw [mpo_kwTransposeTensor, kwTensor_mpo_transpose_mul, Fin.sum_univ_two, mpo_z2Tensor_zero,
    mpo_z2Tensor_one, smul_add]

/-! ### Tensor-level absorption: a gauge equivalence -/

/-- The kernel tensor is normal: its four one-site matrices span `M_2(ℂ)`. -/
theorem kwTensor_isNormal : Kraus.IsNormal kwTensor.toMPSTensor := by
  refine Kraus.IsInjective.isNormal (Submodule.eq_top_of_forall_single_mem _ fun p q => ?_)
  have hmem (i j : Fin 2) :
      kwTensor i j ∈ Submodule.span ℂ (Set.range kwTensor.toMPSTensor) :=
    Submodule.subset_span ⟨finProdFinEquiv (i, j), toMPSTensor_finProdFinEquiv _ _ _⟩
  have hcomb (i j i' j' : Fin 2) (c c' : ℂ)
      (h : Matrix.single p q (1 : ℂ) = c • kwTensor i j + c' • kwTensor i' j') :
      Matrix.single p q (1 : ℂ) ∈ Submodule.span ℂ (Set.range kwTensor.toMPSTensor) := by
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem i j))
      (Submodule.smul_mem _ _ (hmem i' j'))
  fin_cases p <;> fin_cases q
  · refine hcomb 0 0 1 0 (1 / 2) (1 / 2) ?_
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [kwTensor_apply, Matrix.single_apply]
  · refine hcomb 0 0 1 0 (1 / 2) (-1 / 2) ?_
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [kwTensor_apply, Matrix.single_apply]
  · refine hcomb 0 1 1 1 (1 / 2) (-1 / 2) ?_
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [kwTensor_apply, Matrix.single_apply]
  · refine hcomb 0 1 1 1 (1 / 2) (1 / 2) ?_
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [kwTensor_apply, Matrix.single_apply]

/-- A stacked tensor of bond dimension two whose periodic operators are those of the kernel is
conjugate to the kernel tensor letter by letter. This is the single-block compression theorem
with no room for a zero slot. -/
private theorem exists_gauge_of_mpo_eq (M : MPOTensor 2 (2 * 1))
    (hM : ∀ L : ℕ, 0 < L → M.mpo L = kwTensor.mpo L) :
    ∃ (V : Matrix (Fin 2) (Fin (2 * 1)) ℂ) (W : Matrix (Fin (2 * 1)) (Fin 2) ℂ),
      V * W = 1 ∧ W * V = 1 ∧ ∀ i j, M i j = W * kwTensor i j * V := by
  obtain ⟨V, W, hred, hnil⟩ :=
    MPSTensor.exists_isReduction_and_nilpotent_of_isNormal kwTensor.toMPSTensor
      kwTensor_isNormal two_pos M.toMPSTensor fun L hL σ => by
        rw [MPOTensor.mpv_toMPSTensor, MPOTensor.mpv_toMPSTensor, hM L hL]
  refine ⟨V, W, hred.1, (Matrix.mul_eq_one_comm_of_equiv (finCongr (by norm_num))).mp hred.1,
    fun i j => ?_⟩
  have h := hnil [finProdFinEquiv (i, j)] (by simp)
  simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one,
    toMPSTensor_finProdFinEquiv] at h
  exact sub_eq_zero.mp h

/-- **The kernel absorbs `η` on its input at the tensor level.** The stacked tensor
`(K · η)^{s's} = ∑_m K^{s'm} ⊗ η^{ms}` is conjugate to the kernel tensor by an invertible
matrix, uniformly in the physical indices.

Project result: the tensor-level form of `D_σ D_ψ = D_σ` (arXiv:1601.07185,
`References/1601.07185/source/Ising-Defects.tex` lines 1052–1056), obtained from the
single-block compression theorem. -/
theorem exists_gauge_mulTensor_kwTensor_flipTensor :
    ∃ (V : Matrix (Fin 2) (Fin (2 * 1)) ℂ) (W : Matrix (Fin (2 * 1)) (Fin 2) ℂ),
      V * W = 1 ∧ W * V = 1 ∧
        ∀ i j, mulTensor kwTensor flipTensor i j = W * kwTensor i j * V :=
  exists_gauge_of_mpo_eq _ fun L hL => by
    have : NeZero L := NeZero.of_pos hL
    rw [mpo_mulTensor]
    exact kwTensor_mpo_mul_z2Tensor_mpo 1

/-- **The kernel absorbs `η` on its output at the tensor level.** The stacked tensor
`(η · K)^{s's} = ∑_m η^{s'm} ⊗ K^{ms}` is conjugate to the kernel tensor by an invertible
matrix, uniformly in the physical indices.

Project result: the tensor-level form of `D_ψ D_σ = D_σ` (arXiv:1601.07185,
`References/1601.07185/source/Ising-Defects.tex` lines 1052–1056), obtained from the
single-block compression theorem. -/
theorem exists_gauge_mulTensor_flipTensor_kwTensor :
    ∃ (V : Matrix (Fin 2) (Fin (1 * 2)) ℂ) (W : Matrix (Fin (1 * 2)) (Fin 2) ℂ),
      V * W = 1 ∧ W * V = 1 ∧
        ∀ i j, mulTensor flipTensor kwTensor i j = W * kwTensor i j * V :=
  exists_gauge_of_mpo_eq _ fun L hL => by
    have : NeZero L := NeZero.of_pos hL
    rw [mpo_mulTensor]
    exact z2Tensor_mpo_mul_kwTensor_mpo 1

/-! ### Fusion of the kernel with its adjoint: two weighted blocks and two zero slots -/

/-- **The stacked tensor `K · Kᵀ` compresses onto `2 · 1 ⊕ 2 · η` with two zero slots.** The
product of the intertwiner with its adjoint, of bond dimension four, admits a multi-block
compression onto the two weighted bond-one blocks of the symmetry algebra, and the dimension
count `4 = 1 + 1 + 2` leaves exactly two zero slots. The biorthogonal pairs `P.left a`,
`P.right a` are the fusion tensors of the channel `a` in `K Kᵀ = 2^N (O_1 + O_η)`.

Project result: Theorem 7.12 of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex` applied to
`kwTensor_mpo_mul_kwTransposeTensor_mpo`. -/
theorem exists_compression_mulTensor_kwTensor_kwTransposeTensor :
    ∃ P : MPSTensor.MultiBlockCompression (mulTensor kwTensor kwTransposeTensor).toMPSTensor
        Finset.univ (fun a => (2 : ℂ) • (z2Tensor a).toMPSTensor), P.z = 2 := by
  obtain ⟨P⟩ := exists_multiBlockCompression_mulTensor_of_mpo_eq_sum kwTensor kwTransposeTensor
    Finset.univ (fun _ => (2 : ℂ)) z2Tensor (fun _ _ => two_ne_zero)
    (fun a _ => z2Tensor_isNormal a) (fun _ _ => Nat.one_pos) fun L hL => by
      have : NeZero L := NeZero.of_pos hL
      rw [mpo_mulTensor, kwTensor_mpo_mul_kwTransposeTensor_mpo]
  refine ⟨P, ?_⟩
  have h := P.dim_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

/-- **The stacked tensor `Kᵀ · K` compresses onto `2 · 1 ⊕ 2 · η` with two zero slots.**

Project result: Theorem 7.12 of
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex` applied to the source's
fusion `D_σ² = 1 + D_ψ` (`kwTransposeTensor_mpo_mul_kwTensor_mpo`). -/
theorem exists_compression_mulTensor_kwTransposeTensor_kwTensor :
    ∃ P : MPSTensor.MultiBlockCompression (mulTensor kwTransposeTensor kwTensor).toMPSTensor
        Finset.univ (fun a => (2 : ℂ) • (z2Tensor a).toMPSTensor), P.z = 2 := by
  obtain ⟨P⟩ := exists_multiBlockCompression_mulTensor_of_mpo_eq_sum kwTransposeTensor kwTensor
    Finset.univ (fun _ => (2 : ℂ)) z2Tensor (fun _ _ => two_ne_zero)
    (fun a _ => z2Tensor_isNormal a) (fun _ _ => Nat.one_pos) fun L hL => by
      have : NeZero L := NeZero.of_pos hL
      rw [mpo_mulTensor, kwTransposeTensor_mpo_mul_kwTensor_mpo]
  refine ⟨P, ?_⟩
  have h := P.dim_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

end KWExample
