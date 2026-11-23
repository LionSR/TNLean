/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Gap.PrimitiveBlockOpenGapAllLengths

/-!
# Uniform open-chain gaps from eventual ground-space identities

Consider a positive finite-range interaction whose open-chain kernels agree,
for all sufficiently large volumes, with the boundary-condition spaces of a
finite family of inequivalent primitive MPS blocks. A sufficiently long
window then has the exact MPS kernel and dominates a positive multiple of
its orthogonal excitation projection. The finite-window comparison transfers
a canonical long-range gap to the original interaction. Taking a minimum
with the gaps at the remaining finitely many volumes gives one positive
constant for every volume.

The original interaction has arbitrary positive range. Its local kernel need
not be the MPS space at that range. This proves the finite-chain conclusion
of Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947, for the
primitive-sector representation, directly from the eventual kernel hypothesis.

**Scope restriction (primitive sector families):** The source also permits
more general periodic GVBS presentations. These gap results concern the given
primitive tensor family; the eventual kernel hypothesis on the interaction
has its source scope within that family. See
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open scoped Topology ComplexOrder MatrixOrder
open ManyBody.Interaction (chainTranslates)

namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ j, NeZero (D j)]
/-- The eventual open-chain kernel identity suffices for a uniform gap at
all finite lengths: every eigenvalue of the Hamiltonian of the open-chain translates is `0` or at
least the gap. No condition is imposed on the local kernel or on the range. Source:
Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947; this is its finite-chain
conclusion. -/
theorem exists_hamiltonian_chainTranslates_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : (j : Fin b) → MPSTensor d (D j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, Kraus.HasComplementaryFixedPointGap (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, ∀ ν : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) ν → ν = 0 ∨ (γ : ℂ) ≤ ν := by
  have hpos (N : ℕ) := ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates hh N
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hker
  obtain ⟨L₀, hL₀, hCanonicalKernel⟩ :=
    exists_ker_hamiltonian_parentChainInteraction_toTensorFromBlocks_eq_groundSpaceES
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨p, hpBound, hp, δ, hδ, hCanonicalGap⟩ :=
    exists_ge_hamiltonian_parentChainInteraction_toTensorFromBlocks_gap_all_of_fixedPointGap
      μ A hμ ρ hP hρ hDistinct (max R (max N₀ L₀))
  obtain ⟨κ, hκ, hLocal⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (Matrix.isPositive_toEuclideanLin_iff.mpr (hpos (2 * p)))
  rw [hN₀ (2 * p) (by omega)] at hLocal
  have hLocal' : (κ : ℂ) • LinearMap.toMatrix'
      (parentInteraction (toTensorFromBlocks (d := d) (μ := μ) A) (2 * p)) ≤
      (chainTranslates R (2 * p) h).hamiltonian := by
    rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_smul,
      toEuclideanLin_toMatrix'_parentInteraction]
    exact hLocal
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ ↦ ∀ ν : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) ν → ν = 0 ∨ (γ : ℂ) ≤ ν)
    (fun N γ δ hle hgap ν hν ↦
      (hgap ν hν).imp_right (Complex.real_le_real.mpr hle).trans)
    (fun N ↦ ManyBody.exists_pos_forall_hasEigenvalue (hpos N))
    (M := 2 * p) (δ := κ * δ / (2 * p - R + 1 : ℕ))
    (div_pos (mul_pos hκ hδ) (Nat.cast_pos.mpr (by omega))) ?_
  intro N hN
  exact toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length
    (toTensorFromBlocks (d := d) (μ := μ) A) h hh (by omega) hκ
    hLocal' (hN₀ N (by omega)) (hCanonicalKernel (2 * p) N (by omega) hN)
    (hCanonicalGap N)

end MPSTensor
