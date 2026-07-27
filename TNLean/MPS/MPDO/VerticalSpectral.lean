/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.MPDO.CyclicProjector
import TNLean.MPS.MPDO.VerticalReduction

/-!
# Spectral normalization of the vertical reducing sectors

This file retains the physical sector isometries from the vertical reducing
decomposition while removing zero corners and normalizing every remaining
corner to spectral radius one.

The construction is the isometry-preserving form of the canonical-form steps
in arXiv:1606.00608, lines 214--225, applied after the invariant-projection and
periodic-sector arguments of Proposition 4.13, lines 1873--1893.  It assumes
normalized BNT-refined horizontal form, which is stronger than literal CPSV
canonical form.  It gives a literal reconstruction of every vertical letter
on the retained support.  It does not yet group gauge-equivalent normal tensors
into a basis of normal tensors or prove positivity of the grouped multiplicity
weights at lines 1895--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Spectrally normalized nonzero vertical corners, with their physical
isometries retained.

Let `M` generate matrix product density operators and be in normalized
BNT-refined horizontal form.  The nonzero irreducible reducing corners of its
vertically viewed tensor can be written as positive scalar multiples of normal
tensors.

**Scope restriction (BNT-refined horizontal form):** The horizontal hypothesis
`IsHorizontalCF` is stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Their physical isometries remain pairwise orthogonal, both intertwining
identities and the exact compression formula are preserved, and the retained
corners reconstruct every vertical letter literally.

The omitted irreducible corners have every letter equal to zero.  Consequently
the retained range projections need not sum to the physical identity, but
their orthogonal complement is a zero sector.  This is the zero-corner removal
allowed by arXiv:1606.00608, lines 216--225, and supplies the sector embeddings
used at lines 1895--1898 of Proposition 4.13. -/
theorem IsHorizontalCF.exists_normal_verticalBlockDecomp_with_isometry
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      ∀ v, verticalTensor M v =
        ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ := by
  classical
  obtain ⟨r₀, dim₀, blocks₀, V₀, hpos, hiso, hsum, horth, hint, hintStar,
    hcorner, hirr, _hMPV⟩ :=
    hHorizontal.exists_irreducible_verticalBlockDecomp_with_isometry M hM
  have hPF : ∀ k : Fin r₀, (∃ v, blocks₀ k v ≠ 0) →
      ∃ (ρ : Matrix (Fin (dim₀ k)) (Fin (dim₀ k)) ℂ) (t : ℝ),
        ρ.PosDef ∧ 0 < t ∧
        MPSTensor.transferMap (d := D * D) (D := dim₀ k) (blocks₀ k) ρ =
          (t : ℂ) • ρ := by
    intro k hk
    haveI : NeZero (dim₀ k) := ⟨(hpos k).ne'⟩
    exact MPSTensor.exists_posDef_transferMap_eigenvector_of_irreducible
      (blocks₀ k) (hirr k) hk
  choose ρf tf hρf htf hEigf using hPF
  let κ := {k : Fin r₀ // ∃ v, blocks₀ k v ≠ 0}
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let μf : κ → ℂ := fun x => ((Real.sqrt (tf x.1 x.2) : ℝ) : ℂ)
  let normalized : (x : κ) → MPSTensor (D * D) (dim₀ x.1) := fun x v =>
    (μf x)⁻¹ • blocks₀ x.1 v
  have hμpos : ∀ x : κ, (0 : ℂ) < μf x := by
    intro x
    change (0 : ℂ) < ((Real.sqrt (tf x.1 x.2) : ℝ) : ℂ)
    exact Complex.zero_lt_real.mpr (Real.sqrt_pos.mpr (htf x.1 x.2))
  have hμne : ∀ x : κ, μf x ≠ 0 := fun x => (hμpos x).ne'
  have hrecover : ∀ (x : κ) (v : Fin (D * D)),
      μf x • normalized x v = blocks₀ x.1 v := by
    intro x v
    simp only [normalized, smul_smul, mul_inv_cancel₀ (hμne x), one_smul]
  have hPer := hasNoPeriodicVectors_verticalTensor_of_horizontalCF M hM hHorizontal
  refine ⟨Fintype.card κ, fun j => dim₀ (e j).1, fun j => μf (e j),
    fun j => normalized (e j), fun j => V₀ (e j).1,
    fun j => hpos (e j).1, fun j => hμpos (e j), ?_,
    fun j => hiso (e j).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    haveI : NeZero (dim₀ (e j).1) := ⟨(hpos (e j).1).ne'⟩
    exact MPSTensor.isNormalTensor_invSqrt_smul_of_unique_peripheral
      (blocks₀ (e j).1) (hirr (e j).1)
      (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2)
      (hρf (e j).1 (e j).2) (htf (e j).1 (e j).2)
      (hEigf (e j).1 (e j).2)
      (fun z hz hnorm =>
        hPer (V₀ (e j).1) (blocks₀ (e j).1)
          (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2)
          (hiso (e j).1) (hint (e j).1) (hirr (e j).1)
          (hρf (e j).1 (e j).2) (htf (e j).1 (e j).2)
          (hEigf (e j).1 (e j).2) z hz hnorm)
  · intro j l hjl
    exact horth (e j).1 (e l).1 fun h => hjl (e.injective (Subtype.ext h))
  · intro j v
    rw [hrecover]
    exact hint (e j).1 v
  · intro j v
    rw [hrecover]
    exact hintStar (e j).1 v
  · intro j v
    rw [hrecover]
    exact hcorner (e j).1 v
  · intro v
    have hfull : verticalTensor M v =
        ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
      calc
        verticalTensor M v = verticalTensor M v * 1 :=
          (Matrix.mul_one _).symm
        _ = verticalTensor M v * ∑ k : Fin r₀, V₀ k * (V₀ k)ᴴ := by
          rw [hsum]
        _ = ∑ k : Fin r₀, verticalTensor M v * (V₀ k * (V₀ k)ᴴ) := by
          rw [Matrix.mul_sum]
        _ = ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Matrix.mul_assoc, hint k v, Matrix.mul_assoc]
    have hkeep :
        ∑ k ∈ Finset.univ.filter (fun k => ∃ w, blocks₀ k w ≠ 0),
            V₀ k * blocks₀ k v * (V₀ k)ᴴ =
          ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := by
      refine Finset.sum_filter_of_ne ?_
      intro k _ hne
      by_contra hk
      push Not at hk
      exact hne (by rw [hk v, Matrix.mul_zero, Matrix.zero_mul])
    have hsubtype :
        ∑ k ∈ Finset.univ.filter (fun k => ∃ w, blocks₀ k w ≠ 0),
            V₀ k * blocks₀ k v * (V₀ k)ᴴ =
          ∑ x : κ, V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ :=
      Finset.sum_subtype _ (by simp) _
    calc
      verticalTensor M v =
          ∑ k : Fin r₀, V₀ k * blocks₀ k v * (V₀ k)ᴴ := hfull
      _ = ∑ x : κ, V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ := by
        rw [← hkeep, hsubtype]
      _ = ∑ j : Fin (Fintype.card κ),
          V₀ (e j).1 * blocks₀ (e j).1 v * (V₀ (e j).1)ᴴ :=
        (Equiv.sum_comp e
          (fun x : κ => V₀ x.1 * blocks₀ x.1 v * (V₀ x.1)ᴴ)).symm
      _ = ∑ j : Fin (Fintype.card κ),
          V₀ (e j).1 * (μf (e j) • normalized (e j) v) * (V₀ (e j).1)ᴴ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hrecover]

end MPOTensor
