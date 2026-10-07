/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError

/-!
# One decay rate for a canonical sector family

Finite families of normal left-canonical tensors admit a common strict transfer bound.
If all mixed eigenvalues between distinct sectors have modulus below one, the same bound
can include every mixed transfer map. These spectral choices are independent of circuit
compilation and measurement protocols.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equation (5) and
  Supplemental Material, proof of Lemma 1'(ii).
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d b : ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}

/-- **A common gap for normal blocks.** For finitely many normal left-canonical blocks there is
`0 < t < 1` bounding the moduli of the eigenvalues other than `1` of all their transfer maps
(arXiv:2307.01696, eq. (5) and the remark after it, for each block). -/
theorem exists_forall_eigenvalue_norm_le [NeZero b] (hN : ∀ j, Kraus.IsNormal (Aj j))
    (hA : ∀ j, IsLeftCanonical (Aj j)) (hD : ∀ j, NeZero (Dj j)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖(t : ℂ)‖ := by
  choose t ht0 ht1 hgap using fun j =>
    haveI := hD j
    exists_eigenvalue_norm_le_of_isNormal (Aj j) (hN j) (hA j)
  set t₀ := Finset.univ.sup' Finset.univ_nonempty t
  have ht₀ : 0 < t₀ := (ht0 0).trans_le (Finset.le_sup' t (Finset.mem_univ 0))
  refine ⟨t₀, ht₀, (Finset.sup'_lt_iff _).2 fun j _ => ht1 j, fun j μ' hμ hne => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
  exact (hgap j μ' hμ hne).trans (Finset.le_sup' t (Finset.mem_univ j))

/-- **A common rate for the blocks and their mixed transfer maps.** For finitely many normal
left-canonical blocks whose mixed transfer maps have all eigenvalues of modulus below one, there
is `0 < t < 1` bounding the moduli of the eigenvalues other than `1` of every transfer map and of
all eigenvalues of the mixed transfer maps of distinct blocks (arXiv:2307.01696, eq. (5), and
the spectral radius `τ < 1` of the mixed transfer matrices used in the Supplemental Material,
proof of Lemma 1'(ii)). -/
theorem exists_forall_eigenvalue_norm_le_of_mixed {b : ℕ} [NeZero b] {Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)} (hN : ∀ j, Kraus.IsNormal (Aj j))
    (hA : ∀ j, IsLeftCanonical (Aj j)) (hD : ∀ j, NeZero (Dj j))
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' → μ' ≠ 1 →
        ‖μ'‖ ≤ ‖(t : ℂ)‖) ∧
      ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
        ‖μ'‖ ≤ ‖(t : ℂ)‖ := by
  classical
  obtain ⟨t₁, ht₁0, ht₁1, hdiag⟩ := exists_forall_eigenvalue_norm_le hN hA hD
  have hpair : ∀ p : Fin b × Fin b, ∃ s : ℝ, s < 1 ∧ (p.1 ≠ p.2 → ∀ μ',
      Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj p.1) (Aj p.2)) μ' → ‖μ'‖ ≤ s) := by
    rintro ⟨j, j'⟩
    by_cases h : j = j'
    · exact ⟨0, zero_lt_one, fun h' => absurd h h'⟩
    · obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
        (Module.End.finite_hasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')))
        fun μ' hμ _ => hmix j j' h μ' hμ
      refine ⟨1 - δ, by linarith, fun _ μ' hμ => ?_⟩
      by_cases h1 : μ' = 1
      · have := hmix j j' h μ' hμ
        rw [h1, norm_one] at this
        exact absurd this (lt_irrefl _)
      · exact hgap μ' hμ h1
  choose s hs1 hs using hpair
  set t := max t₁ (Finset.univ.sup' Finset.univ_nonempty s)
  have ht0 : 0 < t := lt_max_of_lt_left ht₁0
  have ht1 : t < 1 := max_lt ht₁1 ((Finset.sup'_lt_iff _).2 fun p _ => hs1 p)
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hn₁ : ‖(t₁ : ℂ)‖ = t₁ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₁0]
  refine ⟨t, ht0, ht1, fun j μ' hμ h1 => ?_, fun j j' h μ' hμ => ?_⟩
  · rw [hnt]
    exact (hn₁ ▸ hdiag j μ' hμ h1).trans (le_max_left _ _)
  · rw [hnt]
    exact (hs (j, j') h μ' hμ).trans ((Finset.le_sup' s (Finset.mem_univ (j, j'))).trans
      (le_max_right _ _))


end MPSPreparation
