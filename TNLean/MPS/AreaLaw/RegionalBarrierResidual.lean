/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalTruncationResidual
import QICLean.Analysis.SoftTruncationRestrictedResidual
import QICLean.Analysis.ShiftedSoftHardTruncation

/-!
# A regional hard tail with an arbitrary commuting interior

The interior matrix may include nonlocal functions of other regional Hamiltonians.
Only the selected raw nearest-neighbour bonds and the actual raw crossing terms enter
the local conjugation estimate. The high-projection floor is kept distinct from its
energy threshold. This conditional auxiliary supports ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1392.
The physical construction must derive the interior commutation and the projection floor;
no physical reverse comparison is concluded from independently supplied data here.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A high-projection floor can differ from its energy threshold in the existing weighted
restriction argument. The boundary forcing is still derived from the original bonds.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem norm_hard_residual_low_of_barrier
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (c b0 energy s cut : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (hcut : c ≤ cut)
    (hBA : Commute B (∑ i ∈ I, h i))
    (hproj : b0 • spectralProjectionGE (∑ i ∈ I, h i) c ≤ B)
    (basis : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (B + ∑ i ∈ J, h i) (basis v) = (a v : ℂ) • basis v)
    (hgap : 2 * (J.card : ℝ) < b0 - energy) :
    let A := ∑ i ∈ I, h i
    let S := Submodule.spectralSpanLE basis a energy
    ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (A - energyTruncation A cut)).domRestrict S‖ ≤
      (Real.exp (-s * (cut - c) - 1) / s) *
        ((2 * (J.card : ℝ)) / (b0 - energy - 2 * (J.card : ℝ))) := by
  intro A S
  have hproj' : b0 • spectralProjectionGE A ((c - b0) + b0) ≤ B := by
    simpa only [sub_add_cancel] using hproj
  obtain ⟨Z, hZ, hZn⟩ := exists_nearestNeighbour_weighted_low_restriction
    I J h hs h0 h1 B (c - b0) b0 energy s hs0 hs1 hBA hproj' basis a hEigen hgap
  have hA : A.IsHermitian :=
    (isSelfAdjoint_sum I fun i hi ↦
      IsSelfAdjoint.of_nonneg (h0 i (Finset.mem_union_left J hi))).isHermitian
  have hcut' : (c - b0) + b0 ≤ cut := by simpa only [sub_add_cancel] using hcut
  have htail := hA.norm_excess_domRestrict_le_actual_weighted_map
    s cut ((c - b0) + b0) hs0 hcut' Z hZ
  have hfinal := htail.trans (mul_le_mul_of_nonneg_left hZn (by positivity))
  simpa only [sub_add_cancel, energyTruncation] using hfinal


/-- An actual soft residual above a lower energy is controlled on a low spectral space
of an arbitrary commuting interior plus the original local boundary. Both the weighted
map and the hard-to-soft comparison are derived. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem norm_soft_residual_low_of_barrier
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i ∈ I ∪ J, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ h i) (h1 : ∀ i ∈ I ∪ J, h i ≤ 1)
    (B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (p c b0 energy s t T : ℝ) (m : ℕ)
    (hp : (p : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ ∑ i ∈ I, h i)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T)
    (hcut : c ≤ p + T) (hBA : Commute B (∑ i ∈ I, h i))
    (hproj : b0 • spectralProjectionGE (∑ i ∈ I, h i) c ≤ B)
    (basis : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ v, toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (B + ∑ i ∈ J, h i) (basis v) = (a v : ℂ) • basis v)
    (hgap : 2 * (J.card : ℝ) < b0 - energy) :
    let A := ∑ i ∈ I, h i
    let S := Submodule.spectralSpanLE basis a energy
    ‖(toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (A - (p : ℂ) • 1 - cfc (Real.softTruncation t m) (A - (p : ℂ) • 1))).domRestrict S‖ ≤
      (Real.exp (-s * ((p + T) - c) - 1) / s) *
        ((2 * (J.card : ℝ)) / (b0 - energy - 2 * (J.card : ℝ))) +
          (t / (m : ℝ)) * (T / t) ^ m := by
  intro A S
  have htail := norm_hard_residual_low_of_barrier I J h hs h0 h1 B
    c b0 energy s (p + T) hs0 hs1 hcut hBA hproj basis a hEigen hgap
  have hA : A.IsHermitian :=
    (isSelfAdjoint_sum I fun i hi ↦
      IsSelfAdjoint.of_nonneg (h0 i (Finset.mem_union_left J hi))).isHermitian
  have hX : (A - (p : ℂ) • 1).PosSemidef := le_iff.mp hp
  have hcmp := hX.norm_softTruncation_residual_domRestrict_le t m T ht hm hT S
  have hclip : A - (p : ℂ) • 1 - energyTruncation (A - (p : ℂ) • 1) T =
      A - energyTruncation A (p + T) := by
    rw [hA.energyTruncation_sub_smul_one p T]
    abel
  rw [hclip] at hcmp
  exact hcmp.trans (_root_.add_le_add htail (le_refl ((t / (m : ℝ)) * (T / t) ^ m)))

end TNLean.MPS.AreaLaw
