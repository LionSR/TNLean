/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.NormalReduction
import TNLean.MPS.SharedInfra.SectorDecomposition

open scoped Matrix BigOperators

/-!
# Granular sector decomposition from a weighted block family

This file provides the **one-sector-per-block** sector decomposition used by
the canonical-form existence reduction.  Each block in the input family
`(μ k, blocks k)` becomes its own sector basis tensor with multiplicity
`copies j = 1` and sector weight `μ j`.

The construction is deliberately a structural form: it does not assert the
basis-of-normal-tensors linear-independence condition `HasBNTSectorData`
from `TNLean.MPS.SharedInfra.SectorDecomposition`, and it is not the
paper's minimal BNT representative construction.

## Main definitions

* `MPSTensor.trivialSectorDecomp` — one-sector-per-block `SectorDecomposition`
  with `copies j = 1` and sector weight `μ j` on each sector.

## Main results

* `MPSTensor.sameMPV₂_trivialSectorDecomp` — the granular sector
  decomposition has `SameMPV₂` with the original weighted block-sum tensor.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Definition 2.6, Proposition 2.7]:
  BNT minimal representative condition.
- [Cirac--Perez-Garcia--Schuch--Verstraete 2021, Section IV.A]: Existence of canonical form.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **One-sector-per-block `SectorDecomposition`.**

Forms from a block family `(μ, blocks)` a `SectorDecomposition` with `copies j = 1`
for every `j`.  Each input block becomes its own sector basis tensor with sector
weight `μ j`.  This construction is deliberately only a structural form: by itself
it does **not** assert the basis-of-normal-tensors linear-independence condition
`HasBNTSectorData` from `TNLean.MPS.SharedInfra.SectorDecomposition`, and it is
not the paper's minimal BNT representative construction. -/
def trivialSectorDecomp {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) : SectorDecomposition d where
  basisCount := r
  basisDim   := dim
  basis      := blocks
  sectors    := {
    copies         := fun _ => 1
    copies_pos     := fun _ => Nat.one_pos
    weight         := fun j _ => μ j
    weight_ne_zero := fun j _ => hμne j
  }

/-- **MPV identity for `trivialSectorDecomp`.**

The tensor of `trivialSectorDecomp μ blocks hμne` has the same MPV family
as `toTensorFromBlocks μ blocks`.  The proof expands both sides using the
sector-decomposition formula and the block-sum formula, together with the identity
`coeff N j = (μ j)^N` because `copies j = 1`. -/
lemma sameMPV₂_trivialSectorDecomp {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) :
    SameMPV₂ (trivialSectorDecomp μ blocks hμne).toTensor
      (toTensorFromBlocks (d := d) (μ := μ) blocks) := by
  intro N σ
  set P := trivialSectorDecomp μ blocks hμne
  calc mpv P.toTensor σ
      = ∑ j : Fin r, P.coeff N j * mpv (P.basis j) σ :=
          P.mpv_toTensor_eq_sum_coeff σ
    _ = ∑ j : Fin r, (μ j) ^ N * mpv (blocks j) σ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hcoeff : P.coeff N j = (μ j) ^ N := by
            simp [P, trivialSectorDecomp, SectorDecomposition.coeff,
              SectorWeightData.coeff]
          rw [hcoeff]
          rfl
    _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
          symm
          simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ

end MPSTensor
