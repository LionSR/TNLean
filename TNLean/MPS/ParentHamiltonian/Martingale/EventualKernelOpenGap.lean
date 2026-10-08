/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteractionRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PrimitiveBlockOpenGapAllLengths

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

open scoped Topology ComplexOrder
namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ j, NeZero (D j)]
/-- The eventual open-chain kernel identity suffices for a uniform gap at
all finite lengths. No condition is imposed on the local kernel or on the
range beyond positivity. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.2, lines 933--947; this is its finite-chain conclusion. -/
theorem exists_openInteractionHamiltonianES_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : (j : Fin b) → MPSTensor d (D j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : h.IsPositive)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES h N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ,
      ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖ := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hker
  obtain ⟨L₀, hL₀, hCanonicalKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  obtain ⟨p, hpBound, hp, δ, hδ, hCanonicalGap⟩ :=
    exists_ge_openParentHamiltonianES_toTensorFromBlocks_gap_all_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct (max R (max N₀ L₀))
  obtain ⟨κ, hκ, hLocal⟩ :=
    LinearMap.IsPositive.exists_pos_smul_orthogonal_ker_projection_le
      (openInteractionHamiltonianES_isPositive hh (2 * p))
  rw [hN₀ (2 * p) (by omega)] at hLocal
  refine Nat.exists_pos_forall_of_eventually
    (P := fun N γ ↦ ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES h N))ᗮ,
      γ * ‖v‖ ≤ ‖openInteractionHamiltonianES h N v‖)
    (fun N γ δ hle hgap v hv ↦
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv))
    (fun N ↦ LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
      (openInteractionHamiltonianES h N))
    (M := 2 * p) (δ := κ * δ / (2 * p - R + 1 : ℕ))
    (div_pos (mul_pos hκ hδ) (Nat.cast_pos.mpr (by omega))) ?_
  intro N hN
  rw [hN₀ N (by omega)]
  refine openInteractionHamiltonianES_gap_of_long_gap_at_length
    (toTensorFromBlocks (d := d) (μ := μ) A) h hh hR (by omega) hN hκ hδ
    hLocal (hN₀ N (by omega)) (hCanonicalKernel (2 * p) N (by omega) hN) ?_
  simpa only [hCanonicalKernel (2 * p) N (by omega) hN] using hCanonicalGap N
/-- Matrix form of the finite-chain gap under the eventual kernel hypothesis
of Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.2, lines 933--947. -/
theorem exists_openInteractionMatrix_gap_of_eventual_kernel
    (μ : Fin b → ℂ) (A : (j : Fin b) → MPSTensor d (D j))
    (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) {R : ℕ} (hR : 0 < R)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ,
      ∀ v ∈ (LinearMap.ker
        (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N))ᗮ,
        γ * ‖v‖ ≤ ‖openInteractionHamiltonianES (Matrix.toEuclideanLin h) N v‖ := by
  exact exists_openInteractionHamiltonianES_gap_of_eventual_kernel
    μ A hμ ρ hP hρ hDistinct hR (Matrix.toEuclideanLin h)
    (Matrix.isPositive_toEuclideanLin_iff.mpr hh) hker
end MPSTensor
