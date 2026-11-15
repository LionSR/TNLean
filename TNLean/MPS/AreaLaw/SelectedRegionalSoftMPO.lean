/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalSoftTruncationMPO
import Mathlib.Data.Fintype.EquivFin

/-!
# An actual MPO for selected regional soft replacements

Only the selected regional sums are replaced. Reindexing the selected finite set preserves
the same actual matrix and makes the represented bond depend on the number of replacements.
This operator-construction auxiliary supports ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1392. It uses the corrected cluster construction and retains
independent scale at least three times order; no efficient-GEN or running-time bound follows.
See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A selected family of the original regional sums has an actual Hermitian MPO
approximation. The same finite partial-replacement sum is represented; no regional MPO or
rank estimate is supplied. Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1392. -/
theorem exists_selected_regional_softTruncations_hermitian_mpo_of_accuracy
    {N q m v : ℕ} (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (I : Fin v → Finset (Fin N)) (p : Fin v → ℝ) (S : Finset (Fin v))
    (t xi z : ℝ) (hlo : ∀ j ∈ S, (p j : ℂ) • 1 ≤ ∑ i ∈ I j, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let R := fun j ↦ ∑ i ∈ I j, h i
    let G := (∑ i, h i) + (z : ℂ) • 1 + ∑ j ∈ S, ((p j : ℂ) • 1 +
      cfc (Real.softTruncation t m) (R j - (p j : ℂ) • 1) - R j)
    let delta := xi / (max 1 S.card : ℕ)
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + delta / W))) / (-Real.log b)⌉₊
    let D0 := 1 + N * q ^ 2
    let D := D0 + ((D0 + (r ^ 2 * q ^ r) * (m + 1)) * 2) * S.card
    ∃ T : Fin (N + 1) → MPOTensor q D,
      G.IsHermitian ∧ (MPOTensor.traceChainOperator T 1).IsHermitian ∧
      ‖G - MPOTensor.traceChainOperator T 1‖ ≤ xi := by
  classical
  intro R G delta W b r D0 D
  let sel := S.equivFin.symm
  let I' := fun j : Fin S.card ↦ I (sel j).val
  let p' := fun j : Fin S.card ↦ p (sel j).val
  obtain ⟨T, hG, hT, herr⟩ := exists_regional_softTruncations_hermitian_mpo_of_accuracy
    hq hm h hs hh hnorm I' p' t xi z (fun j ↦ hlo (sel j).val (sel j).property)
      hscale hxi
  let F := fun j : Fin v ↦ (p j : ℂ) • 1 +
    cfc (Real.softTruncation t m) (R j - (p j : ℂ) • 1) - R j
  have hsum : (∑ j : Fin S.card, F (sel j).val) = ∑ j ∈ S, F j := by
    rw [← S.sum_attach]
    simpa only [Finset.attach_eq_univ] using
      (S.equivFin.symm.sum_comp (fun j : S ↦ F j.val))
  have hmatrix : (∑ i, h i) + (z : ℂ) • 1 + ∑ j : Fin S.card,
      ((p' j : ℂ) • 1 + cfc (Real.softTruncation t m)
        ((∑ i ∈ I' j, h i) - (p' j : ℂ) • 1) - ∑ i ∈ I' j, h i) = G := by
    change (∑ i, h i) + (z : ℂ) • 1 + (∑ j : Fin S.card, F (sel j).val) = G
    rw [hsum]
  refine ⟨T, ?_, hT, ?_⟩
  · rw [← hmatrix]
    exact hG
  · rw [← hmatrix]
    exact herr

end TNLean.MPS.AreaLaw
