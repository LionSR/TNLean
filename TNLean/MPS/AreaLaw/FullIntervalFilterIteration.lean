/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FullIntervalFilterTrimming

/-!
# Actual finite filter-and-trim iterates of the same root

The sequence starts at the given interval subspace and applies the literal
filter-image and collective-trimming operation at every successor. The
candidate dimension never increases. Every positive iterate retains its
actual trimmed spanning vectors and their weighted Schmidt-rank bounds.

This is the finite repeated operation of ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1634–1640. No independent approximation space
replaces an iterate. Error convergence, physical parameter selection and
final spectral extraction are separate consequences.
-/

namespace TNLean.MPS.AreaLaw

/-- The literal repeated filter and collective trim, starting from the
given root. ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
noncomputable def fullIntervalFilterTrimIterate (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    ℕ → Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))
  | 0 => S
  | n + 1 => fullIntervalFilterTrimStep L q K xi
      (fullIntervalFilterTrimIterate L q K xi S n)

/-- The initial iterate is exactly the initial root. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
@[simp]
theorem fullIntervalFilterTrimIterate_zero (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) :
    fullIntervalFilterTrimIterate L q K xi S 0 = S := rfl

/-- Every successor is the actual next filter image and collective trim.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1634–1640. -/
@[simp]
theorem fullIntervalFilterTrimIterate_succ (L q : ℕ)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) (n : ℕ) :
    fullIntervalFilterTrimIterate L q K xi S (n + 1) =
      fullIntervalFilterTrimStep L q K xi (fullIntervalFilterTrimIterate L q K xi S n) := rfl

/-- The dimension of every actual iterate is bounded by the initial root
 dimension. Supporting ALVV, arXiv:1602.08828v2, repeated trimming,
Figure `fig:algo1`, lines 1634–1640. -/
theorem finrank_fullIntervalFilterTrimIterate_le {L q : ℕ}
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (xi : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q))) (n : ℕ) :
    Module.finrank ℂ (fullIntervalFilterTrimIterate L q K xi S n) ≤ Module.finrank ℂ S := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (finrank_fullIntervalFilterTrimStep_le K xi _).trans ih

/-- Every positive iterate has actual recorded trimmed generators within
one uniform count and weighted-rank bound. This does not give the same
rank bound to their entire span. Supporting ALVV, arXiv:1602.08828v2,
collective trimming, lines 660–697, and its repetition, lines 1634–1640. -/
theorem isIntervalSpanWithRankBound_fullIntervalFilterTrimIterate_succ
    {L q count : ℕ} {xi : ℝ} (hxi : 0 < xi)
    (K : EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L 0 L → Fin q)))
    (hS : Module.finrank ℂ S ≤ count) (n : ℕ) :
    IsIntervalSpanWithRankBound L q 0 L count xi
      (fullIntervalFilterTrimIterate L q K xi S (n + 1)) := by
  exact isIntervalSpanWithRankBound_fullIntervalFilterTrimStep hxi K _
    ((finrank_fullIntervalFilterTrimIterate_le K xi S n).trans hS)

end TNLean.MPS.AreaLaw
