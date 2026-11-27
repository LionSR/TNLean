/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTPresentation.Refinement
import TNLean.MPS.CanonicalForm.Periodic.Overlap.NormalizedSelfOverlap
import TNLean.MPS.Tensor.DirectSum.SectorWeightComparison
import TNLean.MPS.Tensor.DirectSum.IrreducibleDecomposition
import TNLean.MPS.Tensor.Overlap
import TNLean.MPS.CanonicalForm.PhysicalReindex

/-!
# Presentations by a basis of normal tensors in left-canonical gauge

A two-layer presentation of a tensor by a basis of normal tensors
(arXiv:1606.00608, eq. `II_ABasicTensors` and `decBSV`, lines 281--301) is
`IsBNTSectorPresentation A P`.  This module records the presentation of the
assembled tensor `P.toTensor` in which every basis tensor is left-canonical,
`∑_i (A_j^i)† A_j^i = 1`.

Left-canonicality is a gauge choice: no source statement contains it, and every
presentation can be brought into this gauge without changing the presented
vectors (`IsBNTSectorPresentation.exists_leftCanonical_withBasis`, using the
trace-preserving Perron gauge of arXiv:1606.00608, Appendix A, lines
1093--1117).  It is used by the overlap estimates in the proof of the
Fundamental Theorem.  No normalization of the copy weights (arXiv:1606.00608,
line 246) is imposed.

## Main results

* `IsLeftCanonicalBNTPresentation`: a presentation of `P.toTensor` by `P` with
  left-canonical basis tensors.
* `IsLeftCanonicalBNTPresentation.of_irreducible_selfOverlap`: the constructor from
  irreducible, left-canonical basis tensors whose self-overlap tends to one.
* `IsLeftCanonicalBNTPresentation.basis_dim_pos`, `basis_irreducible`,
  `basis_normalized_self_overlap`, `basis_distinct`, `basis_isNormal`: the
  consequences of normality and eventual linear independence used downstream.
* `IsBNTSectorPresentation.exists_leftCanonical_withBasis`: every presentation
  has a left-canonical gauge with the same sectors and weights.

## References

* arXiv:1606.00608, lines 217--301, 1093--1117 and 1135--1148.
* arXiv:2011.12127, lines 1815--1884.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {α : Type*} [Fintype α]

/-- **Presentation by a basis of normal tensors in left-canonical gauge.**

`IsLeftCanonicalBNTPresentation P` says that `P` is a two-layer presentation of its own
assembled tensor `P.toTensor` by a basis of normal tensors
(arXiv:1606.00608, eq. `II_ABasicTensors` and `decBSV`, lines 281--301;
arXiv:2011.12127, Definition 4.2 and lines 1864--1884), and that every basis
tensor is left-canonical (arXiv:2011.12127, lines 1815--1837).

The coefficient of the `j`th basis tensor at length `N` is the raw power sum
`∑_q μ_{j,q}^N`; no modulus normalization, equal-modulus layer or ordering of
the weights is imposed. -/
structure IsLeftCanonicalBNTPresentation (P : SectorDecomposition α) : Prop
    extends IsBNTSectorPresentation P.toTensor P where
  /-- Every basis tensor is left-canonical (arXiv:2011.12127, lines 1815--1837). -/
  basis_left_canonical : ∀ j : Fin P.basisCount, IsLeftCanonical (P.basis j)

namespace IsLeftCanonicalBNTPresentation

variable {P : SectorDecomposition α}

/-- Irreducible left-canonical basis tensors whose normalized self-overlap tends
to one, with eventually linearly independent matrix product vectors, give a
presentation in left-canonical gauge.

The basis tensors are then normal (arXiv:2011.12127, lines 1815--1830), and the
presentation is the two-layer display of arXiv:1606.00608, lines 281--301.  Normality is read
off after relabelling the physical alphabet by `Fin (Fintype.card α)`. -/
theorem of_irreducible_selfOverlap (hCount : 0 < P.basisCount)
    (hDim : ∀ j : Fin P.basisCount, 0 < P.basisDim j)
    (hIrr : ∀ j : Fin P.basisCount, Kraus.IsIrreducibleFamily (P.basis j))
    (hLeft : ∀ j : Fin P.basisCount, IsLeftCanonical (P.basis j))
    (hSelf : ∀ j : Fin P.basisCount,
      Tendsto (fun N : ℕ => mpvOverlap (P.basis j) (P.basis j) N) atTop (𝓝 1))
    (hData : HasBNTSectorData P) : IsLeftCanonicalBNTPresentation P where
  basisCount_pos := hCount
  sameMPV₂Pos := fun _ _ _ => rfl
  basis_normal := fun j => by
    have : NeZero (P.basisDim j) := ⟨(hDim j).ne'⟩
    let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
    have hIrr' := (Kraus.isIrreducibleFamily_reindexPhysical_equiv f (P.basis j)).2 (hIrr j)
    have hLeft' := (Kraus.isTP_reindexPhysical_iff f (P.basis j)).2 (hLeft j)
    have hSelf' : Tendsto (fun N : ℕ => mpvOverlap (Kraus.reindexPhysical f (P.basis j))
        (Kraus.reindexPhysical f (P.basis j)) N) atTop (𝓝 1) :=
      (hSelf j).congr' (Eventually.of_forall fun N =>
        (mpvOverlap_reindexPhysical_equiv f (P.basis j) (P.basis j)).symm)
    have hB := isNormalTensor_of_isIrreducibleFamily_leftCanonical _ hIrr'
      (isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
        _ hIrr' hLeft' hSelf').1 hLeft'
    have hback : Kraus.reindexPhysical f.symm (Kraus.reindexPhysical f (P.basis j)) =
        P.basis j := by
      funext i
      simp [Kraus.reindexPhysical]
    simpa only [hback] using hB.reindexPhysical f.symm
  eventually_li := hData
  basis_left_canonical := hLeft

/-- Every basis bond dimension is positive, since a normal tensor has nonzero
bond dimension (arXiv:1606.00608, lines 233--235). -/
theorem basis_dim_pos (h : IsLeftCanonicalBNTPresentation P) (j : Fin P.basisCount) :
    0 < P.basisDim j :=
  Nat.pos_of_ne_zero (h.basis_normal j).bondDim_ne_zero

/-- Every basis tensor is irreducible (arXiv:1606.00608, lines 233--234). -/
theorem basis_irreducible (h : IsLeftCanonicalBNTPresentation P) (j : Fin P.basisCount) :
    Kraus.IsIrreducibleFamily (P.basis j) :=
  (h.basis_normal j).no_invariant_proj

/-- The normalized self-overlap of every basis tensor tends to one
(arXiv:1606.00608, lines 1080--1097). -/
theorem basis_normalized_self_overlap (h : IsLeftCanonicalBNTPresentation P)
    (j : Fin P.basisCount) :
    Tendsto (fun N : ℕ => mpvOverlap (P.basis j) (P.basis j) N) atTop (𝓝 1) :=
  (h.basis_normal j).selfOverlap_tendsto_one

/-- Distinct basis tensors of equal bond dimension are not gauge-phase
equivalent (arXiv:1606.00608, lines 264--279 and Proposition 2.7, lines
1135--1148). -/
theorem basis_distinct (h : IsLeftCanonicalBNTPresentation P) :
    ∀ j k : Fin P.basisCount, j ≠ k →
      ∀ hjk : P.basisDim j = P.basisDim k,
        ¬ GaugePhaseEquiv (cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hjk) (P.basis j))
          (P.basis k) :=
  h.toIsBNTSectorPresentation.blocks_not_gaugePhaseEquiv

/-- Every basis tensor is algebraically normal: some positive length has full
word span (arXiv:1606.00608, lines 318--344; arXiv:2011.12127, lines
1815--1830). -/
theorem basis_isNormal (h : IsLeftCanonicalBNTPresentation P) (j : Fin P.basisCount) :
    Kraus.IsNormal (P.basis j) :=
  (h.basis_normal j).isNormal

/-- Every basis tensor is block injective at the common length `D^4`, where `D`
is the total bond dimension.

For the `j`th basis tensor of bond dimension `D_j ≤ D`, quantum Wielandt gives
block injectivity at `D_j^4`, which propagates to `D^4`.

Source: arXiv:1606.00608, line 332. -/
theorem basis_isNBlkInjective_totalDim_pow_four (h : IsLeftCanonicalBNTPresentation P) :
    ∀ j : Fin P.basisCount, Kraus.IsNBlkInjective (P.basis j) (P.totalDim ^ 4) := fun j => by
  let f : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  exact (isNBlkInjective_reindexPhysical_equiv f (P.basis j) _).1
    (((h.basis_normal j).reindexPhysical f).isNBlkInjective_of_bondDim_le
      (P.basisDim_le_totalDim j))

/-- The finitely many basis tensors have one common positive block-injectivity
length.

Source: arXiv:1606.00608, lines 318--344; arXiv:2011.12127, lines 1815--1837. -/
theorem exists_common_basis_isNBlkInjective (h : IsLeftCanonicalBNTPresentation P) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin P.basisCount, Kraus.IsNBlkInjective (P.basis j) L :=
  ⟨P.totalDim ^ 4,
    Nat.pow_pos (lt_of_lt_of_le (h.basis_dim_pos ⟨0, h.basisCount_pos⟩)
      (P.basisDim_le_totalDim _)),
    h.basis_isNBlkInjective_totalDim_pow_four⟩

end IsLeftCanonicalBNTPresentation

/-! ## The left-canonical gauge of a presentation -/

namespace SectorDecomposition

/-- Replace the basis tensors of a sector decomposition by tensors of the same
bond dimensions, keeping the copies and the copy weights.

Used with gauge-equivalent tensors: the two-layer display of arXiv:1606.00608,
lines 281--301, depends on the basis tensors only through their matrix product
vectors. -/
@[reducible]
def withBasis (P : SectorDecomposition α)
    (B : (j : Fin P.basisCount) → MPTensor α (Fin (P.basisDim j))) : SectorDecomposition α where
  basisCount := P.basisCount
  basisDim := P.basisDim
  basis := B
  sectors := P.sectors

/-- Gauging every basis tensor does not change the assembled matrix product
vectors (arXiv:1606.00608, lines 281--301). -/
theorem sameMPV₂Pos_toTensor_withBasis (P : SectorDecomposition α)
    {B : (j : Fin P.basisCount) → MPTensor α (Fin (P.basisDim j))}
    (hB : ∀ j, GaugeEquiv (P.basis j) (B j)) :
    SameMPV₂Pos P.toTensor (P.withBasis B).toTensor := by
  intro N _ σ
  rw [P.mpv_toTensor_eq_sum_coeff σ, (P.withBasis B).mpv_toTensor_eq_sum_coeff σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GaugeEquiv.sameMPV (hB j) N σ]
  rfl

end SectorDecomposition

/-- **Left-canonical gauge of a presentation.**  Every presentation of `A` by a
basis of normal tensors has a presentation of `A` with the same sectors and copy
weights whose basis tensors are gauge equivalent to the original ones and
left-canonical.

Each basis tensor is put in its trace-preserving Perron gauge, a pure
similarity (arXiv:1606.00608, Appendix A, lines 1093--1117); the presented
vectors do not change. -/
theorem IsBNTSectorPresentation.exists_leftCanonical_withBasis {D' : ℕ}
    {A : MPTensor α (Fin D')} {P : SectorDecomposition α} (h : IsBNTSectorPresentation A P) :
    ∃ B : (j : Fin P.basisCount) → MPTensor α (Fin (P.basisDim j)),
      (∀ j, GaugeEquiv (P.basis j) (B j)) ∧
      IsLeftCanonicalBNTPresentation (P.withBasis B) ∧
        IsBNTSectorPresentation A (P.withBasis B) := by
  choose σ _hσ _hσfix hLeft hGauge hPrim hIrr using fun j => (h.basis_normal j).exists_tpGauge
  let B : (j : Fin P.basisCount) → MPTensor α (Fin (P.basisDim j)) := fun j =>
    Kraus.tpGauge (P.basis j) (σ j)
  have hNormal : ∀ j, IsNormalTensor (B j) := fun j => by
    have : NeZero (P.basisDim j) := ⟨(h.basis_normal j).bondDim_ne_zero⟩
    exact isNormalTensor_of_isIrreducibleFamily_leftCanonical _ (hIrr j) (hPrim j) (hLeft j)
  have hLI : HasBNTSectorData (P.withBasis B) := by
    obtain ⟨N₀, hN₀⟩ := h.eventually_li
    refine ⟨N₀, fun N hN => ?_⟩
    have hState : (fun j => (EuclideanSpace.equiv (ι := Fin N → α) (𝕜 := ℂ)).symm
        fun τ => mpv ((P.withBasis B).basis j) τ) =
        fun j => (EuclideanSpace.equiv (ι := Fin N → α) (𝕜 := ℂ)).symm
          fun τ => mpv (P.basis j) τ := by
      funext j
      congr 1
      funext τ
      exact (GaugeEquiv.sameMPV (hGauge j) N τ).symm
    rw [hState]
    exact hN₀ N hN
  have hSame := P.sameMPV₂Pos_toTensor_withBasis hGauge
  refine ⟨B, hGauge, ⟨⟨h.basisCount_pos, fun _ _ _ => rfl, hNormal, hLI⟩, hLeft⟩,
    ⟨h.basisCount_pos, h.sameMPV₂Pos.trans hSame, hNormal, hLI⟩⟩

/-- Multiplying every tensor letter and every copy weight by the same nonzero scalar
preserves a basis-of-normal-tensors presentation.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--244. -/
theorem IsBNTSectorPresentation.smul_left {d D : ℕ} {A : MPSTensor d D}
    {P : SectorDecomposition (Fin d)} (h : IsBNTSectorPresentation A P) (c : ℂ) (hc : c ≠ 0) :
    IsBNTSectorPresentation (c • A) (P.scaleWeights c hc) := by
  refine ⟨h.basisCount_pos, ?_, h.basis_normal, h.eventually_li⟩
  intro N hN σ
  calc
    mpv (c • A) σ = c ^ N * mpv A σ := mpv_smul c A σ
    _ = c ^ N * mpv P.toTensor σ :=
      congrArg (fun z : ℂ => c ^ N * z) (h.sameMPV₂Pos N hN σ)
    _ = mpv (P.scaleWeights c hc).toTensor σ := by
      change c ^ N * mpv P.toTensor σ =
        mpv (toTensorFromBlocks (fun k => c * P.flatWeight k) P.flatBasis) σ
      exact (mpv_toTensorFromBlocks_weight_mul_left c P.flatWeight P.flatBasis σ).symm

end MPSTensor
