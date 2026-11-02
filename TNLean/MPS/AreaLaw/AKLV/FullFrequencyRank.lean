/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.CutTransport
import QICLean.Algebra.OneMarkerFullCounts

/-!
# The original full-frequency family at a target cut

The fixed-frequency rank estimate applies to the actual original window alphabet,
without assuming that a selected coefficient family has an optional-letter presentation.
The latter presentation follows by renaming words and inserting the distinguished count.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 626--662.
**Local fix (count):** The corrected commuting-gap count is documented in
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

open Classical in
/-- An arbitrary weighted slice of the original full-frequency coefficients obeys the
window estimate at any target cut. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--662. -/
theorem operatorSchmidtRank_aklv_full_frequency_slice_target_le {L q a s : ℕ}
    (hq : 1 ≤ q) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (u : Fin s) (m k target : ℕ) :
    let A := Fin s ⊕ Fin 2
    let F := (@Finset.piAntidiag A ℕ (Classical.decEq A) _ _ _ Finset.univ (m + k)).filter
      (fun β ↦ β (Sum.inl u) = k)
    ∀ weight : (A → ℕ) → ℂ, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L target)
        (∑ β ∈ F, weight β •
          WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) (m + k) β)) ≤
      (m + s).choose s * (m + 2 * k + 1).choose (2 * k + 1) *
        q ^ (2 * k + 2 * Nat.dist (a + u.val + 1) target) := by
  intro A F weight
  have heq := WordMultiplicity.sum_smul_wordCoefficient_marker_eq
    (aklvWindowFamily H HL HR) (Sum.inl u) m k weight
  change (∑ β ∈ F, weight β •
      WordMultiplicity.wordCoefficient (aklvWindowFamily H HL HR) (m + k) β) = _ at heq
  rw [heq]
  exact operatorSchmidtRank_aklv_window_one_marker_target_le hq hspace H hH HL HR hL hR
    u m k target (fun α ↦ weight (WordMultiplicity.insertMarkerFrequency (Sum.inl u) k α.val))

end TNLean.MPS.AreaLaw
