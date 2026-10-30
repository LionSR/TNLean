/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveConstruction
import TNLean.MPS.AreaLaw.ViableSet.FinalMPS

/-!
# Uniform polynomial successive viable sets and final-span MPS approximation

For fixed local dimension and positive gap, the natural polynomial coefficient and
degree are chosen before the length and physical interaction. The successive families
are then chosen from that interaction before any ground pair. Every such ground pair
has a normalized approximation in the span of the final actual family.

**Local fix (trimming radius):** The independent trimmings use the quadratic radius
recorded at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The library constant-cut bound and corrected net exponent are documented in
`docs/paper-gaps/lvv13_constant_bond.tex`; the conservative Gaussian error-reduction
scope is documented in `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, final induction, lines 652--678,
using Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. The conclusion concerns
the mathematical construction and its cardinality and bond bounds; no computational
running-time statement is asserted.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- Natural polynomial budgets chosen before length bound every retained family and
the normalized MPS extracted from its final span. Families are selected before ground
data. LVV13, `algo53.tex`, final induction, lines 652--678, with the documented
quadratic trimming correction and Huang's Gaussian error reduction. -/
theorem exists_uniform_positive_chain_successive_approximation {q : ℕ} (hq : 2 ≤ q)
    {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ L : ℕ, 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (_hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j.val (j.val + 2))) (_h0 : ∀ j, 0 ≤ h j) (_h1 : ∀ j, h j ≤ 1),
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
        S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, i ≤ L → (S i).card ≤ P * (L + 1) ^ d ∧
          (∀ v ∈ S i, IsLeftOpenMPS (P * (L + 1) ^ d) v) ∧
          ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
            IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
            IsViable Γ (lvvSuccessiveError Delta / L) (S i : Set (LeftBlockVector L q i))) ∧
        ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
          IsGappedGroundState (∑ j, h j) E₀ Γ Delta →
          ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
            1 - lvvSuccessiveError Delta / L ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧
            IsOpenMPS L q (P * (L + 1) ^ d) (fun x ↦ ψ x) ∧
            fullLeftEquiv L q ψ ∈ Submodule.span ℂ (S L : Set (LeftBlockVector L q L)) := by
  classical
  obtain ⟨P, d, hP, hbudgets⟩ := exists_lvvSuccessive_uniform_polynomial (q := q) (by omega) hDelta
  refine ⟨P, d, hP, ?_⟩
  intro L hL h hs h0 h1
  obtain ⟨S, hS0, hS⟩ := exists_positive_chain_successive_viable_sets hq h hs h0 h1 hDelta hL
  obtain ⟨hcardBudget, hbondBudget, hspanBudget⟩ := hbudgets L hL
  refine ⟨S, hS0, ?_, ?_⟩
  · intro i hi
    obtain ⟨hcard, hMPS, hviable⟩ := hS i hi
    have hsize : (if i = 0 then 1 else lvvSuccessiveCardBound q Delta L) ≤
        P * (L + 1) ^ d := by
      split_ifs
      · exact (le_max_left 1 _).trans hcardBudget
      · exact (le_max_right 1 _).trans hcardBudget
    have hbond : (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L) ≤
        P * (L + 1) ^ d := by
      split_ifs
      · exact (le_max_left 1 _).trans hbondBudget
      · exact (le_max_right 1 _).trans hbondBudget
    refine ⟨hcard.trans hsize, ?_, hviable⟩
    intro v hv
    apply isOpenMPS_of_internal_cutMatrix_rank_le
      (WithLp.toLp 2 fun x ↦ v (leftConfigOfFin x))
    intro k hk0 hki
    have hvMPS : IsOpenMPS i q
        (max 1 (if i = 0 then 1 else lvvSuccessiveBondBound q Delta L))
        (fun x ↦ v (leftConfigOfFin x)) := hMPS v hv
    exact (hvMPS.rank_cutMatrix_le hk0 hki).trans (max_le_max le_rfl hbond)
  · intro E₀ Γ hgs
    obtain ⟨hcard, hMPS, hviable⟩ := hS L le_rfl
    have hLne : L ≠ 0 := by omega
    simp only [hLne, ite_false] at hcard hMPS
    obtain ⟨v, hvspan, hvnorm, hoverlap⟩ := (hviable E₀ Γ hgs).exists_fullLeftVector
    let ψ := (fullLeftEquiv L q).symm v
    have hψimage : fullLeftEquiv L q ψ = v := (fullLeftEquiv L q).apply_symm_apply v
    have hinner : ⟪ψ, Γ⟫_ℂ = ⟪v, fullLeftEquiv L q Γ⟫_ℂ := by
      rw [← (fullLeftEquiv L q).inner_map_map ψ Γ, hψimage]
    refine ⟨ψ, ?_, ?_, ?_, ?_⟩
    · simpa only [ψ, LinearIsometryEquiv.norm_map] using hvnorm
    · rwa [hinner]
    · have hspan := isOpenMPS_leftChain_of_mem_span (S L) hMPS hvspan
      apply isOpenMPS_of_internal_cutMatrix_rank_le ψ
      intro k hk0 hkL
      exact (hspan.rank_cutMatrix_le hk0 hkL).trans
        ((Nat.mul_le_mul_right _ hcard).trans hspanBudget)
    · rwa [hψimage]

end TNLean.MPS.AreaLaw
