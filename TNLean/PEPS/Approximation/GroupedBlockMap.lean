/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordOwnerMap

/-!
# Aggregate operations within a group of parties

An operation on several parties becomes a local operation when all its input
and output registers belong to one group. Its complete linear map is retained,
with all spectator registers untouched. In particular, an exterior gate may be
used as its original contraction without opening its monomial expansion.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 351–417.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

variable {P Q : Type}

private theorem homogeneous_group (f : P → Q) (q : Q) {a : Layout P}
    (ha : ∀ r ∈ a, f r.owner = q) :
    ∀ r ∈ Layout.mapOwner f a, r.owner = q := by
  rintro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  exact ha s hs

/-- Retain a whole operation as one local map after grouping its participating
registers. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def groupedBlockMap (f : P → Q) (q : Q) (a b : Layout P)
    (ha : ∀ r ∈ a, f r.owner = q) (hb : ∀ r ∈ b, f r.owner = q)
    (A : Mem a →L[ℂ] Mem b) (ℓ : Layout P) :
    Word (Layout.mapOwner f (a ++ ℓ)) (Layout.mapOwner f (b ++ ℓ)) :=
  (Word.localMap q (homogeneous_group f q ha) (homogeneous_group f q hb)
    (isoL (Layout.mapOwnerIso f b) ∘L A ∘L isoL (Layout.mapOwnerIso f a).symm)
    (Layout.mapOwner f ℓ)).castLayouts
      (Layout.mapOwner_append f a ℓ).symm (Layout.mapOwner_append f b ℓ).symm

/-- An aggregate contraction remains allowed and introduces no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem groupedBlockMap_spec (f : P → Q) (q : Q) (a b : Layout P)
    (ha : ∀ r ∈ a, f r.owner = q) (hb : ∀ r ∈ b, f r.owner = q)
    (A : Mem a →L[ℂ] Mem b) (hA : ‖A‖ ≤ 1) (ℓ : Layout P) :
    (groupedBlockMap f q a b ha hb A ℓ).IsAllowed ∧
      (groupedBlockMap f q a b ha hb A ℓ).sources = [] := by
  constructor
  · rw [groupedBlockMap, isAllowed_castLayouts]
    exact norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
      (norm_comp_le_one hA (LinearIsometry.norm_toContinuousLinearMap_le _))
  · simp only [groupedBlockMap, sources_castLayouts, sources]

/-- The grouped local map is exactly the original operation tensored with the
identity on the spectator memory, in the canonical grouped coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem eval_groupedBlockMap (f : P → Q) (q : Q) (a b : Layout P)
    (ha : ∀ r ∈ a, f r.owner = q) (hb : ∀ r ∈ b, f r.owner = q)
    (A : Mem a →L[ℂ] Mem b) (ℓ : Layout P) :
    (groupedBlockMap f q a b ha hb A ℓ).eval ∘L
        isoL (Layout.mapOwnerIso f (a ++ ℓ)) =
      isoL (Layout.mapOwnerIso f (b ++ ℓ)) ∘L
        isoL (appendIso b ℓ).symm ∘L A.rTensor (Mem ℓ) ∘L isoL (appendIso a ℓ) := by
  have he : (groupedBlockMap f q a b ha hb A ℓ).eval ∘L
        isoL (Layout.mapOwnerIso f (a ++ ℓ)) ∘L isoL (appendIso a ℓ).symm =
      isoL (Layout.mapOwnerIso f (b ++ ℓ)) ∘L
        isoL (appendIso b ℓ).symm ∘L A.rTensor (Mem ℓ) := by
    apply clm_ext_tmul
    intro u z
    simp only [groupedBlockMap, eval_castLayouts,
      Layout.memCongr_symm (Layout.mapOwner_append f a ℓ),
      Layout.memCongr_symm (Layout.mapOwner_append f b ℓ), LinearIsometryEquiv.symm_symm,
      eval, comp_apply, isoL_apply]
    rw [Layout.mapOwnerIso_append_tmul]
    simp only [LinearIsometryEquiv.apply_symm_apply, rTensor_tmul, comp_apply,
      isoL_apply, LinearIsometryEquiv.symm_apply_apply]
    apply (Layout.memCongr (Layout.mapOwner_append f b ℓ)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, Layout.mapOwnerIso_append_tmul]
  ext x
  have h := DFunLike.congr_fun he ((appendIso a ℓ) x)
  simpa only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply] using h

/-- Grouping parties preserves every scalar coefficient in a gate expansion.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate` and
`04-compression.tex`, lines 351–417. -/
theorem eval_sum_mapOwner_comp {ι : Type} [Fintype ι] (f : P → Q)
    {a b : Layout P} (c : ι → ℂ) (w : ι → Word a b) :
    (∑ ξ, c ξ • ((w ξ).mapOwner f).eval) ∘L isoL (Layout.mapOwnerIso f a) =
      isoL (Layout.mapOwnerIso f b) ∘L (∑ ξ, c ξ • (w ξ).eval) := by
  simp only [finsetSum_comp, smul_comp, eval_mapOwner_comp, comp_finsetSum, comp_smul]

end TNLean.PEPS.PairEffect.Word
