/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Flattening nested block decompositions at the MPV level

If each block of a weighted direct sum has an unweighted MPV decomposition,
the whole tensor has the corresponding flattened weighted decomposition.
The statement concerns matrix product vectors, so it does not assert a
bond-space similarity between the two assembled tensors.

This is the sum-of-sectors step in the arbitrary blocking argument of
arXiv:1708.00029, Section 4.1.
-/

open scoped BigOperators

namespace MPSTensor

/-- Bond dimension of a sector in a nested block family, indexed by one
flattened natural-number coordinate. Source: arXiv:1708.00029, Section 4.1. -/
noncomputable def nestedBlockFlatDim {r : ℕ} (sectorCount : Fin r → ℕ)
    (sectorDim : (j : Fin r) → Fin (sectorCount j) → ℕ)
    (x : Fin (∑ j : Fin r, sectorCount j)) : ℕ :=
  let y := finSigmaFinEquiv.symm x
  sectorDim y.1 y.2

/-- Tensor of one sector in a nested family, indexed by the flattened
coordinate. Source: arXiv:1708.00029, Section 4.1. -/
noncomputable def nestedBlockFlatTensor {d r : ℕ}
    (sectorCount : Fin r → ℕ)
    (sectorDim : (j : Fin r) → Fin (sectorCount j) → ℕ)
    (C : (j : Fin r) → (s : Fin (sectorCount j)) → MPSTensor d (sectorDim j s))
    (x : Fin (∑ j : Fin r, sectorCount j)) :
    MPSTensor d (nestedBlockFlatDim sectorCount sectorDim x) :=
  let y := finSigmaFinEquiv.symm x
  C y.1 y.2

/-- A weighted direct sum of tensors, each of which is MPV-equivalent to
an unweighted direct sum of sectors, is MPV-equivalent to the single direct
sum over all sectors. Each sector retains the weight of its original block.
Source: arXiv:1708.00029, Section 4.1. -/
theorem sameMPV₂_weighted_nested_blocks_flatten
    {d r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (B : (j : Fin r) → MPSTensor d (dim j))
    (sectorCount : Fin r → ℕ)
    (sectorDim : (j : Fin r) → Fin (sectorCount j) → ℕ)
    (C : (j : Fin r) → (s : Fin (sectorCount j)) → MPSTensor d (sectorDim j s))
    (hSame : ∀ j, SameMPV₂ (B j)
      (toTensorFromBlocks (μ := fun _ : Fin (sectorCount j) => 1) (C j))) :
    SameMPV₂ (toTensorFromBlocks μ B)
      (toTensorFromBlocks
        (μ := fun x : Fin (∑ j : Fin r, sectorCount j) =>
          μ (finSigmaFinEquiv.symm x).1)
        (nestedBlockFlatTensor sectorCount sectorDim C)) := by
  intro N σ
  let f : ((j : Fin r) × Fin (sectorCount j)) → ℂ := fun y ↦
    (μ y.1) ^ N * mpv (C y.1 y.2) σ
  calc
    mpv (toTensorFromBlocks μ B) σ
        = ∑ j : Fin r, (μ j) ^ N • mpv (B j) σ :=
          mpv_toTensorFromBlocks_eq_sum μ B σ
    _ = ∑ j : Fin r, (μ j) ^ N •
          mpv (toTensorFromBlocks (μ := fun _ : Fin (sectorCount j) => 1) (C j)) σ := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hSame j N σ]
    _ = ∑ j : Fin r, ∑ s : Fin (sectorCount j),
          (μ j) ^ N • mpv (C j s) σ := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [mpv_toTensorFromBlocks_eq_sum]
          simp [smul_eq_mul, Finset.mul_sum]
    _ = ∑ y : ((j : Fin r) × Fin (sectorCount j)),
          (μ y.1) ^ N • mpv (C y.1 y.2) σ :=
          (Fintype.sum_sigma'
            (fun j s ↦ (μ j) ^ N • mpv (C j s) σ)).symm
    _ = ∑ x : Fin (∑ j : Fin r, sectorCount j),
          (μ (finSigmaFinEquiv.symm x).1) ^ N •
            mpv (nestedBlockFlatTensor sectorCount sectorDim C x) σ := by
          have h := (Equiv.sum_comp
            (finSigmaFinEquiv.symm :
              Fin (∑ j : Fin r, sectorCount j) ≃
                ((j : Fin r) × Fin (sectorCount j))) f).symm
          calc
            _ = ∑ x : Fin (∑ j : Fin r, sectorCount j),
                f (finSigmaFinEquiv.symm x) := by
                  simpa only [f, smul_eq_mul] using h
            _ = _ := by
                  congr 1
    _ = mpv (toTensorFromBlocks
          (μ := fun x : Fin (∑ j : Fin r, sectorCount j) =>
            μ (finSigmaFinEquiv.symm x).1)
          (nestedBlockFlatTensor sectorCount sectorDim C)) σ :=
          (mpv_toTensorFromBlocks_eq_sum _ _ σ).symm

end MPSTensor
