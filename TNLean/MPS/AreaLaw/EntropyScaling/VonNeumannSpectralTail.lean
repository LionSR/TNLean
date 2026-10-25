/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.VonNeumannEntropySpectralTail
import QICLean.Entropy.RegionEntropy

/-!
# Regional entropy from a supplied spectral tail

For a unit vector on a chain of local dimension `q`, a region `R` has
configuration-space dimension `q ^ R.card`. A bound `ε` on the spectral mass
outside the first `D` eigenvalues therefore gives
`S(R) ≤ log D + ε * R.card * log q + log 2`.

This is an auxiliary spectral-mass implication, not the approximation theorem
of Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 278–305.
Substituting `ε = δ / 2` gives the required half-error coefficient once that
spectral-mass estimate has been established separately. The rank budget `D`
is not identified here with the bond dimension; an interior block has two
boundaries and generally requires its square.
-/

open scoped ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- A supplied spectral-tail mass bounds the entropy of any region of a homogeneous
chain. This is an auxiliary concentration estimate for the entropy obstruction in
SWVC08, arXiv:0705.0292v2, lines 278–305. It does not infer the tail mass from a
matrix approximation error. -/
theorem regionEntropy_le_log_rank_add_spectral_tail {L q D : ℕ}
    (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (hψ : ‖ψ‖ = 1) (R : Finset (Fin L)) {ε : ℝ}
    (htail : ∑ i ∈ Finset.Ico D (Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q) R)),
      (Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) R ψ).isHermitian.descEigenvalue i
        ≤ ε) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) R ψ ≤
      Real.log D + ε * (R.card : ℝ) * Real.log q + Real.log 2 := by
  have hρ := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) R ψ
  have hb := hρ.vonNeumannEntropy_le_log_rank_add_tail
    (by simp [Entropy.trace_regionState, hψ]) htail
  simpa [Entropy.regionEntropy, Entropy.RegionConfig, Fintype.card_pi, Real.log_pow,
    mul_assoc] using hb

end TNLean.MPS.AreaLaw
