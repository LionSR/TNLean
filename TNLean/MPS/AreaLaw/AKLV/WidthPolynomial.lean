/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.ShortWindow
import QICLean.Algebra.AKLVFrequencyBounds
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# A uniform polynomial rank estimate for a bounded AKLV window

The actual power decomposition is bounded uniformly over all degrees up to a prescribed
cutoff. Expansion into powers then gives the same estimate for arbitrary complex
polynomials, with one additional factor for the number of degrees.

**Local fix (count):** The commuting-gap coefficient uses the correction at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 598--663.
The restriction on the window width is explicit here; the unrestricted central-cut
statement follows by regrouping the actual interactions into a shorter window.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- A polynomial of degree at most `ell` obeys a uniform explicit rank bound when the
physical middle window has width at most `ell + 1`. This is the bounded-window step
in AKLV, arXiv:1301.1162v1, Lemma 4.2, before shorter-window regrouping. -/
theorem operatorSchmidtRank_aklv_polynomial_of_width_le {L q a s ell : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hwidth : s ≤ ell + 1) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ ell) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2))
      (Polynomial.aeval (HL + (∑ j, H j) + HR) P)) ≤
      (q * (ell + 1)) ^ (3 * s + 6 * (ell / s) + 5) := by
  let G := HL + (∑ j, H j) + HR
  let B := q * (ell + 1)
  let e := 3 * s + 6 * (ell / s) + 4
  have hbase : ell + 1 ≤ B := by dsimp [B]; nlinarith
  have hpower (r : ℕ) (hr : r ≤ ell) :
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L (a + s / 2)) (G ^ r)) ≤ B ^ e :=
    (operatorSchmidtRank_aklv_power_le_sum hq hs hspace H hH HL HR hL hR r).trans
      (Nat.aklv_frequency_sum_le hq hwidth hr)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L (a + s / 2)))
  change operatorSchmidtRank (φ (Polynomial.aeval G P)) ≤ _
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP) G]
  simp only [map_sum, map_smul]
  calc
    _ ≤ ∑ r ∈ Finset.range (ell + 1),
        operatorSchmidtRank (P.coeff r • φ (G ^ r)) :=
      operatorSchmidtRank_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range (ell + 1), B ^ e :=
      Finset.sum_le_sum fun r hr ↦ (operatorSchmidtRank_smul_le _ _).trans
        (hpower r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)))
    _ = (ell + 1) * B ^ e := by simp
    _ ≤ B * B ^ e := Nat.mul_le_mul_right _ hbase
    _ = _ := by rw [← pow_succ']

end TNLean.MPS.AreaLaw
