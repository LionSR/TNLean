/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CoarseInformation
import TNLean.PEPS.Approximation.CellTwoFamilyPartition
import TNLean.PEPS.Approximation.ConditionalTwoFamilies
import TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartitionComap

/-!
# Conditional information of a physical cell

A sublinear collar bound controls the mutual information of each tile in the
ordered two-family partition of a cell. The two-family entropy inequality then
bounds the cell's conditional mutual information by a fixed power of its
logarithmic side length, uniformly over the grid origin, exterior conditioning
cells and the original gapped ground state.

Source: polynomial-PEPS manuscript, Lemma 3.2 (`lem:cell-cmi`),
`02-information.tex`, lines 163–311; its use in Proposition 3.4,
lines 688–737, source revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
**Scope restriction (conditional collar bound):** The sublinear collar bound
is an explicit premise of this intermediate result. For positive local dimension,
nonnegative interaction bound and positive spectral gap, the physical collar theorem
supplies the range-one estimate with clearance 13 and template constant 24. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.AreaLaw
open TNLean.PEPS.AreaLaw.Geometry

open Classical in
/-- Conditional information of one physical cell, assuming the original-gap
sublinear collar bound. The conditioning region is the physical sample of an
arbitrary union of other cells. Separation is measured from the full closed
ambient cell. The constants precede the side length, origin, conditioning cells,
finite domain and Hamiltonian. No nonempty-region or local-dimension assumption
is imposed.

Source: polynomial-PEPS Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
lines 163–222 and 304–311; the coarse tile estimate is Proposition 3.1. -/
theorem exists_cell_conditionalMutualInformation_le_of_sublinearCollarBound
    {q : ℕ} {J Δ D₀ Ctpl : ℝ} (hΔ : 0 < Δ)
    (hcol : SublinearCollarBound q 1 J Δ D₀ Ctpl) {c : ℝ} (hc : 0 < c) :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
        m₀ ∉ A →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : AreaLaw.LocalHamiltonian Λ q 1 J)
          (E₀ : ℝ) (Ω : AreaLaw.StateSpace Λ q),
          AreaLaw.IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          let G : Finset (Site Λ) :=
            Finset.univ.filter (fun x ↦ x.val ∈ CellPartition.cellSample o s m₀)
          let B : Finset (Site Λ) := Finset.univ.filter
            (fun x ↦ CellPartition.cellIndex o s (integerPoint x.val) ∈ A)
          ∀ E : Finset (Site Λ), E ⊆ (G ∪ B)ᶜ →
            (∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner o s m₀) s),
              ∀ y ∈ E, c * s ≤ dist x (integerPoint y.val)) →
            FiniteProduct.conditionalMutualInformation (fun _ : Site Λ ↦ Fin q)
              Ω G E B ≤ C₁ * (1 + Real.log s) ^ K := by
  obtain ⟨β, hβ, C₂, u₀, hcoarse⟩ :=
    coarse_mutualInformation_le_of_sublinearCollarBound hΔ hcol (66 * 66) 1
  obtain ⟨u₁, hu₁, hsmall⟩ :=
    CellPartition.exists_const_mul_rpow_le_rpow (K := 2 / c) (γ := β) (δ := 1)
      (div_pos two_pos hc) hβ
  obtain ⟨ustar, hustar, hustar1, Cp, K, hCp, hpart⟩ :=
    CellPartition.exists_cell_twoFamily_partition hβ (max u₀ u₁)
  refine ⟨max 1 (max (2 * Real.log q) C₂) * Cp, max K 0,
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCp, le_max_right _ _, ?_⟩
  intro s hs o m₀ A hm₀ Λ h E₀ Ω hΩ G B E hE hclear
  obtain ⟨P, scale, hscale, hrect, hdiam, houtside, hearlier, hcount⟩ :=
    hpart s hs o m₀ (fun i ↦ if i ∈ A then 0 else 1)
  let Q : OrderedTwoFamilyPartition G := P.comap (fun x : Site Λ ↦ x.val)
  have hbox (i : Fin P.pieceCount) : IsBoxUnion (66 * 66) (P.piece i) := by
    rcases hrect i with ⟨n, hn, R, hR, hT⟩
    choose a₁ b₁ a₂ b₂ hR using hR
    exact ⟨n, hn, fun j ↦ (a₁ j, a₂ j), fun j ↦ (b₁ j, b₂ j),
      hT.trans (congrArg (fun F : Fin n → Finset (ℤ × ℤ) ↦ Finset.univ.biUnion F)
        (funext fun j ↦ (hR j).trans (Finset.Icc_product_Icc _ _ _ _)))⟩
  have hdist (x y : ℤ × ℤ) : (Scan.ambientSupDistance x y : ℝ) =
      dist (integerPoint x) (integerPoint y) := by
    simp only [Scan.ambientSupDistance, integerPoint, Prod.dist_eq, Real.dist_eq,
      Int.cast_max, Int.cast_abs, Int.cast_sub]
  have hGB : Disjoint G B := Finset.disjoint_left.mpr fun x hxG hxB ↦
    hm₀ (((CellPartition.mem_cellSample (lt_of_lt_of_le zero_lt_one hs)).mp
      (Finset.mem_filter.mp hxG).2) ▸ (Finset.mem_filter.mp hxB).2)
  have hdisj : Disjoint G E ∧ Disjoint B E :=
    ⟨Finset.disjoint_left.mpr fun x hxG hxE ↦
      Finset.mem_compl.mp (hE hxE) (Finset.mem_union_left _ hxG),
     Finset.disjoint_left.mpr fun x hxB hxE ↦
      Finset.mem_compl.mp (hE hxE) (Finset.mem_union_right _ hxB)⟩
  have htile (i : Fin P.pieceCount) (F : Finset (Site Λ))
      (hF : ∀ x ∈ P.piece i, ∀ y ∈ F,
        scale i ^ β < dist (integerPoint x) (integerPoint y.val)) :
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Q.piece i) F ≤ C₂ :=
    hcoarse (scale i) ((le_max_left _ _).trans (hustar.trans (hscale i).1))
      Λ h E₀ Ω hΩ (P.piece i) (hbox i)
      (fun x hx y hy ↦ by simpa only [hdist, one_mul] using hdiam i x hx y hy)
      (Q.piece i) (fun _ hx ↦ hx) F
      (fun x hx y hy ↦ by simpa only [hdist] using hF x hx y hy)
  have hclosure (i : Fin P.pieceCount) (x : ℤ × ℤ) (hx : x ∈ P.piece i) :
      integerPoint x ∈ closure (CellPartition.box (CellPartition.cellCorner o s m₀) s) :=
    subset_closure (CellPartition.mem_latticeBox.mp ((Finset.ext_iff.mp P.cover x).mpr
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))))
  have hfar (i : Fin P.pieceCount) : scale i ^ β < c * s := by
    have hh : 2 * scale i ^ β / c ≤ scale i := by
      simpa only [Real.rpow_one, div_mul_eq_mul_div] using
        hsmall (scale i) ((le_max_right _ _).trans (hustar.trans (hscale i).1))
    nlinarith only [(div_le_iff₀ hc).mp hh,
      mul_le_mul_of_nonneg_left (hscale i).2 hc.le,
      mul_pos hc (lt_of_lt_of_le zero_lt_one hs)]
  have h₀ (i : Fin P.pieceCount) (hi : P.family i = 0) :
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Q.piece i)
        (E ∪ B ∪ Q.earlierSameFamily i) ≤ C₂ := by
    apply htile i
    intro x hx y hy
    simp only [Finset.mem_union] at hy
    rcases hy with (hy | hy) | hy
    · exact (hfar i).trans_le (hclear _ (hclosure i x hx) y hy)
    · exact houtside i x hx y.val
        (fun heq ↦ hm₀ (heq ▸ (Finset.mem_filter.mp hy).2))
        ((ite_eq_left (Finset.mem_filter.mp hy).2).trans hi.symm)
    · exact hearlier i x hx y.val (by
        simpa only [Q, OrderedTwoFamilyPartition.earlierSameFamily_comap,
          Finset.mem_filter, Finset.mem_univ, true_and] using hy)
  have h₁ (i : Fin P.pieceCount) (hi : P.family i = 1) :
      FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (Q.piece i)
        ((G ∪ B)ᶜ ∪ Q.earlierSameFamily i) ≤ C₂ := by
    refine htile i _ (fun x hx y hy ↦ ?_)
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [Finset.mem_compl, Finset.mem_union, not_or] at hy
      exact houtside i x hx y.val
        (fun heq ↦ hy.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (CellPartition.mem_cellSample
            (lt_of_lt_of_le zero_lt_one hs)).mpr heq⟩))
        ((ite_eq_right (fun hA ↦ hy.2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩))).trans hi.symm)
    · exact hearlier i x hx y.val (by
        simpa only [Q, OrderedTwoFamilyPartition.earlierSameFamily_comap,
          Finset.mem_filter, Finset.mem_univ, true_and] using hy)
  have hinfo : FiniteProduct.conditionalMutualInformation (fun _ : Site Λ ↦ Fin q)
      Ω G E B ≤ 2 * (Q.residual.card : ℝ) * Real.log q + Q.pieceCount * C₂ := by
    simpa only [regionalEntropy_eq_finiteProduct,
      FiniteProduct.conditionalMutualInformation] using
      regionalEntropy_conditional_le_card_residual_add_pieceCount
        Λ q Ω hΩ.1 G B E Q hGB hdisj.1 hdisj.2 C₂ h₀ h₁
  have hres : (Q.residual.card : ℝ) ≤ P.residual.card :=
    Nat.cast_le.mpr (P.card_residual_comap_le (fun x : Site Λ ↦ x.val)
      Subtype.val_injective)
  let M := max 1 (max (2 * Real.log q) C₂)
  have hMlog : 2 * Real.log q ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMC : C₂ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hcost : 2 * (Q.residual.card : ℝ) * Real.log q + Q.pieceCount * C₂ ≤
      M * ((P.pieceCount : ℝ) + P.residual.card) := by
    change 2 * (Q.residual.card : ℝ) * Real.log q + P.pieceCount * C₂ ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hres
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.log_natCast_nonneg q)),
      mul_le_mul_of_nonneg_right hMlog (Nat.cast_nonneg P.residual.card),
      mul_le_mul_of_nonneg_left hMC (Nat.cast_nonneg P.pieceCount)]
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hpow : (1 + Real.log s) ^ K ≤ (1 + Real.log s) ^ max K 0 :=
    Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right (Real.log_nonneg hs)) (le_max_left _ _)
  exact hinfo.trans (hcost.trans ((mul_le_mul_of_nonneg_left hcount hM).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hM hCp.le))))

end TNLean.PEPS.Approximation
