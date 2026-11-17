/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalFamilyTrimming

/-!
# Literal interleaved tensor-family applications and collective trims

Every round applies the retained-factor family to the current space and
then takes the actual collective trim. The same family, reference, target
and threshold are used throughout. A scalar error envelope controls
viability at every round. Dimension and weighted recorded ranks refer to
these actual iterates, rather than to a separately chosen viable space.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the reference argument, lines 1801–1805.
Physical parameter selection and probability remain separate.

**Local fix (recursive assignment):** The current space is used at each
successor; see `docs/paper-gaps/alvv16_approximation_parameters.tex`.
The integer round count is explicit and is not identified with the
possibly nonintegral choice printed in `eq:algo-sk-dg`.
-/

open scoped TensorProduct InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The literal interleaving of family applications and collective trims.
ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670,
with the recursive assignment correction recorded in the module. -/
noncomputable def intervalFamilyTrimIterate (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) :
    ℕ → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))
  | 0 => S
  | n + 1 => intervalFamilyTrimStep L q p r F xi
      (intervalFamilyTrimIterate L q p r F xi S n)

/-- The initial space is the actual zeroth iterate. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670. -/
@[simp]
theorem intervalFamilyTrimIterate_zero (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) :
    intervalFamilyTrimIterate L q p r F xi S 0 = S := rfl

/-- Every successor uses the previous actual space. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670. -/
@[simp]
theorem intervalFamilyTrimIterate_succ (L q p r : ℕ) {N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (n : ℕ) :
    intervalFamilyTrimIterate L q p r F xi S (n + 1) =
      intervalFamilyTrimStep L q p r F xi (intervalFamilyTrimIterate L q p r F xi S n) := rfl

/-- After `n` literal rounds the actual dimension is at most `N^n` times
the sampled dimension, including an empty family and zero rounds.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
and Figure `fig:merge-prime`, lines 1668–1670. -/
theorem finrank_intervalFamilyTrimIterate_le {L q p r N : ℕ}
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (n : ℕ) :
    Module.finrank ℂ (intervalFamilyTrimIterate L q p r F xi S n) ≤
      N ^ n * Module.finrank ℂ S := by
  induction n with
  | zero =>
    change Module.finrank ℂ S ≤ 1 * Module.finrank ℂ S
    rw [Nat.one_mul]
  | succ n ih =>
    calc
      _ ≤ N * Module.finrank ℂ (intervalFamilyTrimIterate L q p r F xi S n) :=
        finrank_intervalFamilyTrimStep_le F xi _
      _ ≤ N * (N ^ n * Module.finrank ℂ S) := Nat.mul_le_mul_left N ih
      _ = _ := by rw [pow_succ]; ring

/-- Every positive actual iterate has recorded generators with weighted
internal-cut ranks bounded by its same dimension-growth count. This is
not an all-span rank assertion. Supporting ALVV, arXiv:1602.08828v2,
collective trimming, lines 660–697, and Figure `fig:merge-prime`,
lines 1668–1670. -/
theorem isIntervalSpanWithRankBound_intervalFamilyTrimIterate_succ
    {L q p r N : ℕ} {xi : ℝ} (hxi : 0 < xi)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) (n : ℕ) :
    IsIntervalSpanWithRankBound L q p r (N ^ (n + 1) * Module.finrank ℂ S) xi
      (intervalFamilyTrimIterate L q p r F xi S (n + 1)) := by
  have h := isIntervalSpanWithRankBound_intervalFamilyTrimStep hxi F _
    (finrank_intervalFamilyTrimIterate_le F xi S n)
  simpa only [intervalFamilyTrimIterate_succ, pow_succ,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- A scalar envelope controls viability of every actual interleaved
iterate. The envelope inequality is numerical; the actual post-trim
viability is derived from the tensor decomposition and the weighted
reference theorem. No image-to-trim closeness is assumed. This auxiliary
supports ALVV, arXiv:1602.08828v2, Figure `fig:merge-prime`,
lines 1668–1670, and the reference argument, lines 1801–1805. -/
theorem isViable_intervalFamilyTrimIterate_of_tensor_decomposition
    {L q p r N D : ℕ} (hD : 1 ≤ D)
    {T U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon Delta xi theta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hDelta : 0 ≤ Delta) (hxi : 0 < xi) (htheta : 0 < theta)
    (hTU : Submodule.IsCloseTo epsilon T U) (hUT : Submodule.IsCloseTo epsilon U T)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (Rop : Fin N → EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q) →L[ℂ]
      EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) :
    let Tcoord := T.map
      (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap
    ∀ (K : (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q)) →L[ℂ]
      (EuclideanSpace ℂ (interval L p r → Fin q) ⊗[ℂ]
        EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q))),
    K = ∑ i, TensorProduct.mapL (F i) (Rop i) →
    (∀ t ∈ Tcoord, K t ∈ Tcoord) →
    (∀ z ∈ Tcoordᗮ, K z ∈ Tcoordᗮ) →
    (∀ t ∈ Tcoord, ‖t‖ ≤ ‖K t‖) →
    (∀ z ∈ Tcoordᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) →
    ∀ delta : ℕ → ℝ, (∀ j, 0 ≤ delta j) → (∀ j, delta j < 1) →
    (∀ j,
      (1 + theta) * ((1 + theta) * (Delta * delta j / (1 - delta j + Delta * delta j)) +
        (1 + 1 / theta) * epsilon +
        2 * (xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)))) +
        (1 + 1 / theta) * epsilon ≤ delta (j + 1)) →
    ∀ S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)),
    Submodule.IsViable (delta 0) S Tcoord →
    ∀ j, Submodule.IsViable (delta j) (intervalFamilyTrimIterate L q p r F xi S j) Tcoord := by
  intro Tcoord K hdec hKT hKTo hlow hhigh delta hdelta0 hdelta herror S hS j
  induction j with
  | zero => simpa only [intervalFamilyTrimIterate_zero] using hS
  | succ j ih =>
    obtain ⟨_hdim, _hranks, hnext⟩ :=
      isViable_intervalFamilyTrimStep_of_tensor_decomposition hD hepsilon
        (hdelta0 j) (hdelta j) hDelta hxi htheta hTU hUT hU F Rop
        K hdec hKT hKTo hlow hhigh _ ih
    exact hnext.of_le (herror j)

end TNLean.MPS.AreaLaw
