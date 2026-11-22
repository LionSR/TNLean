/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.BoundaryGap
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Spectral.Gap.PositiveGapUniqueness
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.FrustrationFree

/-!
# Local dimension and gap of a frustration-free chain

A positive nearest-neighbour chain with frustration-free unit ground vector and an
excitation at energy `g > 0` has local dimension at least two and `g ≤ 1`. The
source theorems take the gap to be an actual spectral value, so both bounds are
derived rather than assumed.

Source: AKLV, arXiv:1301.1162v1, Section 5, before equation (4), and Theorem `t:ent`,
lines 820–846, at ground energy zero.
-/

open ManyBody (interval)

open Matrix Real
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Two spectral values `0` and `g > 0` of a positive nearest-neighbour chain with
frustration-free unit ground vector force local dimension at least two and `g ≤ 1`.
This is the normalization of AKLV, arXiv:1301.1162v1, Section 5, before equation (4),
at ground energy zero. -/
theorem aklv_frustrationFree_dimension_and_gap_bounds {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1)
    (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (hzero : Ω ∈ Φ.zeroSpace)
    (hgap : (Φ.hamiltonian - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : g ∈ spectrum ℝ Φ.hamiltonian) :
    2 ≤ q ∧ g ≤ 1 := by
  classical
  replace hzero : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = 0 :=
    (ManyBody.Interaction.mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero
      fun j ↦ Matrix.nonneg_iff_posSemidef.mp (h0 j)).mp hzero
  have hH : Φ.hamiltonian.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun j _ ↦ h0 j)).isHermitian
  have hground : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = ((0 : ℝ) : ℂ) • WithLp.ofLp Ω := by
    rw [hzero, Complex.ofReal_zero, zero_smul]
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hexcited (ne_of_lt hg)
  have hL : 0 < L := by
    by_contra hnot
    have hL0 : L = 0 := by omega
    have hcfg : Subsingleton (Fin L → Fin q) := by subst L; infer_instance
    let := hcfg
    obtain ⟨i, hi⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
    obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hexcited
    have heq : (0 : ℝ) = g := hi.symm.trans
      ((congrArg hH.eigenvalues (Subsingleton.elim i j)).trans hj)
    linarith
  obtain ⟨-, -, hgap, hspan⟩ := (ManyBody.isGapped_and_groundSpace_eq_span_iff hg Ω).mp
    ⟨hΩ, by rw [← (WithLp.ofLp_injective 2).eq_iff, Matrix.ofLp_toEuclideanCLM,
      WithLp.ofLp_smul]; exact hground, by simpa only [Complex.ofReal_zero, zero_smul, sub_zero]
        using hgap⟩
  exact ⟨hq, gap_le_one_of_positive_nearest_neighbor_terms hL hq Φ h0 h1 hΩ hgap hspan⟩

end TNLean.MPS.AreaLaw
