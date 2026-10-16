/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairInitialMarkFacts
import TNLean.PEPS.AreaLaw.Geometry.CellFanRunCount
import TNLean.PEPS.AreaLaw.Geometry.PolynomialBudget

/-!
# A uniform count of the actual initial belt regions

The initial belt regions are the connected fan runs of the selected belt
cells, with the same joint residue choices as the actual initial repair
stage. Their carrier is the belt summand of the existing initial region
index. The count concerns all such regions before restriction to a finite
cut; it does not include the primary regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:belt-count`, lines 220–233;
initial fan runs, lines 299–318; and the initial-belt contribution to
`geometry:total-repairs`, lines 685–692.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The carrier of the actual initial belt regions is finite, and its
cardinality is bounded by one constant times the edge boundary and the
squared layer-width factor. The constant precedes all geometric data.
The carrier is the literal belt summand of the existing initial region
index, with the jointly chosen residues used by the actual initial stage.

The intended argument restricts to the finite support of the selected belt
layers, counts at most eight connected fan runs per cell, and applies the
uniform selected-cell estimate with coefficient 64. If `B₀` bounds the
numerical dyadic sum at exponent zero, the intended choice is `B = 512 * B₀`.

Source: area-law Section 11, `geometry:belt-count`, lines 220–233;
initial fan runs, lines 299–318; and `geometry:total-repairs`, lines 685–692,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_uniform_initial_belt_card_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀),
        let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
          o Λ A C k₀ hC h₀
        let a := Classical.choose h
        let hb := Classical.choose_spec h
        let b := Classical.choose hb
        let F := fun k => beltCellIndices
          (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
          (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
        let I : Type :=
          Σ k : {k : ℕ // k₀ ≤ k},
            Σ z : {z : ℤ × ℤ // z ∈ F k.val},
              CellFanRun o (fineScaleIndex k.val) z.val
                (fineLayerSplitMask o k₀ k.val (boundaryEndpoints Λ A) C z.val)
                (beltCellFanColor o k₀ (boundaryEndpoints Λ A) C a b k.val z.val
                  hC h₀ k.property z.property)
        Finite I ∧
          (Nat.card I : ℝ) ≤
            B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨B₀, hB₀, hbudget⟩ := exists_uniform_polynomial_dyadic_sum_bound 0
  refine ⟨512 * B₀, mul_pos (by norm_num) hB₀, ?_⟩
  intro o Λ A C k₀ hC h₀ h a hb b F I
  obtain ⟨hFcard, hFfinite, _, _, _, _⟩ :=
    initialRepairStage_mark_spec o Λ A C k₀ hC h₀
  let K : Finset ℕ := hFfinite.toFinset.filter (k₀ ≤ ·)
  let R (k : {k : ℕ // k ∈ K}) (z : {z : ℤ × ℤ // z ∈ F k.val}) : Type :=
    CellFanRun o (fineScaleIndex k.val) z.val
      (fineLayerSplitMask o k₀ k.val (boundaryEndpoints Λ A) C z.val)
      (beltCellFanColor o k₀ (boundaryEndpoints Λ A) C a b k.val z.val
        hC h₀ (Finset.mem_filter.mp k.property).2 z.property)
  let J : Type := Σ k : {k : ℕ // k ∈ K}, Σ z : {z : ℤ × ℤ // z ∈ F k.val}, R k z
  let : Finite J := by
    dsimp only [J]
    infer_instance
  let f : I → J := fun p ↦
    ⟨⟨p.1.val, Finset.mem_filter.mpr
      ⟨hFfinite.mem_toFinset.mpr ⟨p.2.1.val, p.2.1.property⟩, p.1.property⟩⟩, p.2⟩
  let g : J → I := fun p ↦
    ⟨⟨p.1.val, (Finset.mem_filter.mp p.1.property).2⟩, p.2⟩
  have hf : Function.Injective f :=
    (show Function.LeftInverse g f from fun _ ↦ rfl).injective
  let : Finite I := Finite.of_injective f hf
  refine ⟨inferInstance, ?_⟩
  have hcard : Nat.card I ≤ Nat.card J := Nat.card_le_card_of_injective f hf
  have hRcard (k : {k : ℕ // k ∈ K}) (z : {z : ℤ × ℤ // z ∈ F k.val}) :
      Nat.card (R k z) ≤ 8 := card_cellFanRun_le_eight _ _ _ _ _
  have hcell (k : {k : ℕ // k ∈ K}) :
      Nat.card (Σ z : {z : ℤ × ℤ // z ∈ F k.val}, R k z) ≤ 8 * (F k.val).card := by
    rw [Nat.card_sigma]
    simpa only [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, Nat.cast_id, mul_comm] using
      Finset.sum_le_card_nsmul Finset.univ
        (fun z : {z : ℤ × ℤ // z ∈ F k.val} ↦ Nat.card (R k z)) 8
        (fun z _ ↦ hRcard k z)
  have hJ : Nat.card J ≤ ∑ k ∈ K, 8 * (F k).card := by
    dsimp only [J]
    rw [Nat.card_sigma]
    exact le_of_le_of_eq
      (Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hcell k))
      (Finset.sum_coe_sort K (fun k ↦ 8 * (F k).card))
  have hcount : (Nat.card I : ℝ) ≤ ∑ k ∈ K, 8 * ((F k).card : ℝ) := by
    exact_mod_cast hcard.trans hJ
  have hsparse (k : ℕ) : 8 * ((F k).card : ℝ) ≤
      512 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2) := by
    convert mul_le_mul_of_nonneg_left (hFcard k) (show (0 : ℝ) ≤ 8 by norm_num) using 1
    ring
  have hbudgetK :
      (∑ k ∈ K, (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2)) ≤ B₀ := by
    simpa only [Real.rpow_zero, one_mul] using hbudget K
  refine hcount.trans ((Finset.sum_le_sum (fun k _ ↦ hsparse k)).trans ?_)
  rw [← Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left hbudgetK
    (show 0 ≤ 512 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card by
      positivity) using 1
  ring

end TNLean.PEPS.AreaLaw.Geometry
