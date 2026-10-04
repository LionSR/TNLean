/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.BNT.Construction
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceContinuity
import TNLean.MPS.ParentHamiltonian.BlockWordSpanSeparation
import TNLean.MPS.ParentHamiltonian.FrameOperator
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.Preparation.OneDimensionalBlocks

/-!
# Three normal blocks with the ferromagnetic Heisenberg parent interaction

The three bond-one qubit tensors \((1,0)\), \((0,1)\), and
\((1/\sqrt2,1/\sqrt2)\) are normalized, normal, and pairwise inequivalent.
Their word tuples span the three-dimensional block algebra at length two,
while their two-site local ground space is the symmetric qubit subspace.
The canonical parent interaction is consequently the singlet projector
\((1-\mathrm{Swap})/2\).

This construction addresses the unrestricted assertion that all MPS parent
Hamiltonians are uniformly gapped in arXiv:2011.12127, Section IV.C,
lines 2183--2187. The distinction between a range shorter than the simultaneous
injectivity length plus one and the sufficient ranges is essential here.
The example and the resulting failure of the unrestricted assertion are
documented in `docs/paper-gaps/cpgsv21_short_range_parent_gap.tex`.
-/

open scoped BigOperators Matrix InnerProductSpace

namespace MPSTensor

/-- The normalized qubit product-state blocks \(|0\rangle\),
\(|1\rangle\), and \(|+\rangle\). -/
noncomputable def shortRangeHeisenbergBlock (j : Fin 3) : MPSTensor 2 1 :=
  fun i _ _ => (![![1, 0], ![0, 1], ![Complex.invSqrtTwo, Complex.invSqrtTwo]] j) i

/-- The direct sum of the three product-state blocks, each with coefficient one. -/
noncomputable def shortRangeHeisenbergTensor : MPSTensor 2 (∑ _j : Fin 3, 1) :=
  toTensorFromBlocks (μ := fun _ => (1 : ℂ)) shortRangeHeisenbergBlock

/-- The three word tuples \(00,11,01\) span the block algebra at length two.
They are \((1,0,1/2)\), \((0,1,1/2)\), and \((0,0,1/2)\). -/
theorem wordTupleSpanTop_shortRangeHeisenbergBlock_two :
    WordTupleSpanTop shortRangeHeisenbergBlock 2 := by
  change Submodule.span ℂ (Set.range (wordTuple shortRangeHeisenbergBlock 2)) = ⊤
  refine Submodule.eq_top_iff'.mpr ?_
  intro X
  let S := Submodule.span ℂ (Set.range (wordTuple shortRangeHeisenbergBlock 2))
  have hword (σ : Cfg 2 2) : wordTuple shortRangeHeisenbergBlock 2 σ ∈ S :=
    Submodule.subset_span ⟨σ, rfl⟩
  convert S.add_mem
    (S.add_mem (S.smul_mem (X 0 0 0) (hword ![0, 0]))
      (S.smul_mem (X 1 0 0) (hword ![1, 1])))
    (S.smul_mem (2 * X 2 0 0 - X 0 0 0 - X 1 0 0) (hword ![0, 1])) using 1
  ext j a b
  fin_cases j, a, b <;>
    norm_num [wordTuple, shortRangeHeisenbergBlock, List.ofFn_succ, Kraus.evalWord_cons,
      Kraus.evalWord_nil, Matrix.mul_apply, Complex.invSqrtTwo_mul_self]
  ring

/-- The simultaneous injectivity length is exactly two: at length one,
two word tuples cannot span the three-dimensional block algebra. -/
theorem not_wordTupleSpanTop_shortRangeHeisenbergBlock_one :
    ¬ WordTupleSpanTop shortRangeHeisenbergBlock 1 := by
  intro hSpan
  have h := finrank_le_of_span_eq_top hSpan
  norm_num [Module.finrank_pi_fintype, Module.finrank_matrix, Cfg] at h

/-- Each bond-one block has unit transfer normalization. -/
theorem shortRangeHeisenbergBlock_normalization (j : Fin 3) :
    ∑ i, star (shortRangeHeisenbergBlock j i 0 0) *
      shortRangeHeisenbergBlock j i 0 0 = 1 := by
  fin_cases j <;>
    norm_num [shortRangeHeisenbergBlock, Fin.sum_univ_two, Complex.invSqrtTwo_mul_self]

/-- The three product-state blocks satisfy the normalized normal-tensor
predicate of CPSV16, lines 233--235. -/
theorem shortRangeHeisenbergBlock_isNormalTensor (j : Fin 3) :
    IsNormalTensor (shortRangeHeisenbergBlock j) :=
  isNormalTensor_of_dim_one _ (shortRangeHeisenbergBlock_normalization j)

/-- Each of the three blocks is algebraically normal. -/
theorem shortRangeHeisenbergBlock_isNormal (j : Fin 3) :
    Kraus.IsNormal (shortRangeHeisenbergBlock j) :=
  ⟨2, by decide, isNBlkInjective_of_wordTupleSpanTop shortRangeHeisenbergBlock
    wordTupleSpanTop_shortRangeHeisenbergBlock_two j⟩

/-- The three normalized blocks are pairwise gauge-phase inequivalent,
as required for a basis of normal tensors. Source: arXiv:1606.00608,
lines 317--345. -/
theorem shortRangeHeisenbergBlock_blocksNotGaugePhaseEquiv :
    BlocksNotGaugePhaseEquiv shortRangeHeisenbergBlock := by
  intro j k hjk h
  exact not_gaugePhaseEquiv_of_wordTupleSpanTop shortRangeHeisenbergBlock
    wordTupleSpanTop_shortRangeHeisenbergBlock_two k j hjk.symm h

/-- The displayed three blocks form a basis of normal tensors for the
assembled tensor, in the source predicate of CPSV16, lines 271--274,
and CPSV21, Definition 4.2, lines 1846--1850. -/
theorem isCPSVBasisOfNormalTensors_shortRangeHeisenbergTensor :
    IsCPSVBasisOfNormalTensors shortRangeHeisenbergTensor
      (fun j => ⟨1, shortRangeHeisenbergBlock j⟩) where
  blocks_normal := shortRangeHeisenbergBlock_isNormalTensor
  spans_mpv := fun N _ => ⟨fun _ => 1, fun σ => by
    simpa [shortRangeHeisenbergTensor] using
      mpv_toTensorFromBlocks_eq_sum (fun _ => (1 : ℂ)) shortRangeHeisenbergBlock σ⟩
  eventually_li := exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal
    shortRangeHeisenbergBlock
    (fun j => tendsto_mpvOverlap_self_of_dim_one _ (shortRangeHeisenbergBlock_normalization j))
    (cross_overlap_tendsto_zero_of_separated_normal_bnt_data shortRangeHeisenbergBlock
      ⟨fun j => isIrreducibleTensor_of_bondDim_one (shortRangeHeisenbergBlock j)⟩
      ⟨fun j => isLeftCanonical_of_dim_one _ (shortRangeHeisenbergBlock_normalization j)⟩
      shortRangeHeisenbergBlock_blocksNotGaugePhaseEquiv)

/-- Evaluation of the joint two-site boundary map. Its range is the symmetric
subspace of the two-qubit Hilbert space. -/
theorem blockGroundSpaceMapES_shortRangeHeisenbergBlock_apply
    (c : EuclideanSpace ℂ ((_j : Fin 3) × (Fin 1 × Fin 1))) (σ : Cfg 2 2) :
    blockGroundSpaceMapES shortRangeHeisenbergBlock 2 c σ =
      (if σ 0 = 0 ∧ σ 1 = 0 then c ⟨0, 0, 0⟩ else 0) +
      (if σ 0 = 1 ∧ σ 1 = 1 then c ⟨1, 0, 0⟩ else 0) + c ⟨2, 0, 0⟩ / 2 := by
  simp only [blockGroundSpaceMapES_apply, groundSpaceMap_apply, List.ofFn_succ, Fin.isValue,
    Fin.succ_zero_eq_one, List.ofFn_zero, Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one]
  generalize h₀ : σ 0 = a, h₁ : σ 1 = b
  fin_cases a, b <;>
    norm_num [shortRangeHeisenbergBlock, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.invSqrtTwo_mul_self, div_eq_mul_inv, mul_comm]

/-- A two-site vector belongs to the local ground space exactly when its
\(|01\rangle\) and \(|10\rangle\) coefficients agree. -/
theorem mem_groundSpaceES_shortRangeHeisenbergTensor_two_iff
    (v : EuclideanSpace ℂ (Cfg 2 2)) :
    v ∈ groundSpaceES shortRangeHeisenbergTensor 2 ↔ v ![0, 1] = v ![1, 0] := by
  rw [shortRangeHeisenbergTensor,
    groundSpaceES_toTensorFromBlocks_eq_iSup (fun _ => (1 : ℂ))
      shortRangeHeisenbergBlock (fun _ => one_ne_zero),
    ← range_blockGroundSpaceMapES]
  constructor
  · rintro ⟨c, rfl⟩
    change blockGroundSpaceMapES shortRangeHeisenbergBlock 2 c ![0, 1] =
      blockGroundSpaceMapES shortRangeHeisenbergBlock 2 c ![1, 0]
    simp only [blockGroundSpaceMapES_shortRangeHeisenbergBlock_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, and_false, false_and,
      ite_false, zero_add, Fin.isValue, zero_ne_one, one_ne_zero]
  · intro hv
    refine ⟨WithLp.toLp 2 (fun ⟨j, _, _⟩ =>
      ![v ![0, 0] - v ![0, 1], v ![1, 1] - v ![0, 1], 2 * v ![0, 1]] j), ?_⟩
    apply PiLp.ext
    intro σ
    simp only [ContinuousLinearMap.coe_coe,
      blockGroundSpaceMapES_shortRangeHeisenbergBlock_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have hσ : σ = ![σ 0, σ 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hσ]
    generalize σ 0 = a, σ 1 = b
    fin_cases a, b <;> simp [hv]

private theorem cfg_two_comp_rev (a b : Fin 2) :
    (![a, b] : Cfg 2 2) ∘ Fin.rev = ![b, a] := by
  funext i
  fin_cases i <;> rfl

/-- The local ground-space projection is the symmetrizer
\((1+\mathrm{Swap})/2\). -/
theorem groundSpaceES_shortRangeHeisenbergTensor_two_starProjection
    (v : EuclideanSpace ℂ (Cfg 2 2)) :
    (groundSpaceES shortRangeHeisenbergTensor 2).starProjection v =
      WithLp.toLp 2 (fun σ => (v σ + v (σ ∘ Fin.rev)) / 2) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_groundSpaceES_shortRangeHeisenbergTensor_two_iff _).2
    simp only [cfg_two_comp_rev]
    exact congrArg (fun z : ℂ => z / 2) (add_comm _ _)
  · intro w hw
    have hwsym := (mem_groundSpaceES_shortRangeHeisenbergTensor_two_iff w).1 hw
    simp only [PiLp.inner_apply, sum_cfg_two, Fin.sum_univ_two, PiLp.sub_apply,
      RCLike.inner_apply, cfg_two_comp_rev]
    simp only [hwsym, map_sub, map_add, map_div₀, map_ofNat]
    ring

/-- The canonical two-site parent interaction is the singlet projector
\((1-\mathrm{Swap})/2\). The swap exchanges the two physical sites.
Source for the parent-interaction definition: arXiv:2011.12127,
lines 1996--1999. -/
theorem parentInteractionES_shortRangeHeisenbergTensor_two_apply
    (v : EuclideanSpace ℂ (Cfg 2 2)) (σ : Cfg 2 2) :
    parentInteractionES shortRangeHeisenbergTensor 2 v σ =
      (v σ - v (σ ∘ Fin.rev)) / 2 := by
  change ((groundSpaceES shortRangeHeisenbergTensor 2)ᗮ.starProjection v) σ = _
  rw [Submodule.starProjection_orthogonal_val,
    groundSpaceES_shortRangeHeisenbergTensor_two_starProjection]
  change v σ - (v σ + v (σ ∘ Fin.rev)) / 2 = _
  ring

end MPSTensor
