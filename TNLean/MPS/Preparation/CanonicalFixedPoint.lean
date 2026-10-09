/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.Ergodicity
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.Preparation.NonNormalCanonicalForm

/-!
# Faithful fixed points of the canonical basis blocks

For a basis of normal tensors in left-canonical form, the right transfer fixed point of
each block is the unique density matrix fixed by that transfer map. Irreducibility makes
it positive definite. Thus the pair vectors in arXiv:2307.01696, eqs. (8), (19), and (S7),
can be formed from the actual blocks, without supplied matrices or fixed-point hypotheses.

The embeddings here use one chosen multiplicity copy. Their orthonormality follows from
trace-one normalization and disjoint virtual coordinates. The physical coefficients require
the correction described in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`;
no claim about the printed coefficients of eq. (S7) is made here.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

private theorem exists_basisFixedPoint (h : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    ∃ σ : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ,
      σ ∈ densityMatrices (P.basisDim j) ∧ σ.PosDef ∧
      Kraus.transferMap (P.basis j) σ = σ ∧
      ∀ τ, τ ∈ densityMatrices (P.basisDim j) →
        Kraus.transferMap (P.basis j) τ = τ → τ = σ :=
  IsChannel.exists_unique_density_fixedPoint_of_irreducible
    (Kraus.transferMap (P.basis j))
    (Kraus.isChannel_mapLM (P.basis j) (h.basis_left_canonical j))
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily (P.basis j)
      (h.basis_irreducible j)) (h.basis_dim_pos j)

/-- The unique trace-one right fixed point of the normal block `A_j` in left-canonical
form, used in arXiv:2307.01696, eqs. (8) and (S7). Existence and faithfulness follow from
irreducibility and trace preservation, by Wolf Corollary 6.3. -/
noncomputable def basisFixedPoint (h : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ :=
  (h.exists_basisFixedPoint j).choose

/-- The actual block fixed point is faithful and normalized and is the only stationary
density matrix of its transfer map (arXiv:2307.01696, eqs. (8) and (S7)). -/
theorem basisFixedPoint_spec (h : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    (h.basisFixedPoint j).PosDef ∧ (h.basisFixedPoint j).trace = 1 ∧
      Kraus.transferMap (P.basis j) (h.basisFixedPoint j) = h.basisFixedPoint j ∧
      ∀ τ, τ ∈ densityMatrices (P.basisDim j) →
        Kraus.transferMap (P.basis j) τ = τ → τ = h.basisFixedPoint j := by
  obtain ⟨hmem, hpos, hfix, huniq⟩ := (h.exists_basisFixedPoint j).choose_spec
  exact ⟨hpos, hmem.2, hfix, huniq⟩

/-- The fixed-point pair of `A_j`, embedded on copy `κ j` of its actual canonical block
(arXiv:2307.01696, eqs. (S2) and (S7)). -/
noncomputable def basisFixedPointPair (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (j : Fin P.basisCount) :
    Fin P.totalDim × Fin P.totalDim → ℂ :=
  P.embeddedFixedPointPair h.basisFixedPoint κ j

/-- The actual canonical block pairs are orthonormal. No fixed-point or pair-normalization
hypothesis is supplied (arXiv:2307.01696, the sentence following eq. (S7)). -/
theorem inner_basisFixedPointPair (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (j j' : Fin P.basisCount) :
    ∑ p, star (h.basisFixedPointPair κ j p) * h.basisFixedPointPair κ j' p =
      if j = j' then 1 else 0 :=
  P.inner_embeddedFixedPointPair (fun j => (h.basisFixedPoint_spec j).1.posSemidef)
    (fun j => (h.basisFixedPoint_spec j).2.1) κ j j'

/-- The map from a block label to its actual normalized fixed-point pair is an isometry
(arXiv:2307.01696, the paragraph following eq. (19)). -/
theorem isIsometry_pairIsometry_basisFixedPointPair (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) :
    (pairIsometry (h.basisFixedPointPair κ)).IsIsometry :=
  isIsometry_pairIsometry (h.inner_basisFixedPointPair κ)

end MPSTensor.IsBNTCanonicalForm
