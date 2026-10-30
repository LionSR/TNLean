/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyTensorCoordinates

/-!
# The final unary map of the periodic retained hierarchy

The binary contraction gives the root frame. The actual closing spectral
window has an isometric range inclusion, whose coordinates in that root frame
are the final unary map. Every retained vector is recovered from its actual
closing-frame coordinates.

Source: Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–743.
No bound on intermediate retained dimensions or efficient construction from the
Hamiltonian is asserted.

**Local fix (closing window):** these coordinates include the additional periodic
closing window recorded in `docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The local root columns evaluated on full physical configurations. When the
root block covers all sites this is a reindexing, without exterior multiplicity.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 669–685. -/
noncomputable def hierarchyRootFrame (blk : ι → ℕ) (r : ℕ → ℕ → ℕ)
    (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
      (Fin (r m k)) ℂ) (h : ℕ) : Matrix (ι → Fin d) (Fin (r h 0)) ℂ :=
  fun σ j ↦ U h 0 (fun v ↦ σ v) j

/-- The root columns remain isometric after identifying its region with all sites.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 669–685. -/
theorem isIsometry_hierarchyRootFrame (blk : ι → ℕ) (r : ℕ → ℕ → ℕ)
    (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
      (Fin (r m k)) ℂ) (h : ℕ) (hroot : ∀ i, blk i < 2 ^ h)
    (hU : (U h 0).IsIsometry) : (hierarchyRootFrame blk r U h).IsIsometry := by
  done

/-- Choose the local frames once, then construct the actual final unary map for
any Hermitian closing operator and every retained vector. The vector coordinates
are obtained by applying the adjoint of the actual closing-range inclusion.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–743, with the closing
window correction in `docs/paper-gaps/hastings05_hierarchical_energy.tex`. -/
theorem exists_hierarchyClosing_tensor_coordinates (blk : ι → ℕ)
    (M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hsupp : ∀ m k, M m k ∈ supportedOperators d (levelBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (σ₀ : ι → Fin d) :
    ∃ (r : ℕ → ℕ → ℕ)
      (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
        (Fin (r m k)) ℂ),
      (∀ m k, (U m k).IsIsometry ∧
        hierarchyProjection M c x m k =
          Entropy.localLift (hierarchyBlock blk m k) (U m k * (U m k)ᴴ) ∧
        r m k = (U m k * (U m k)ᴴ).rank) ∧
      (∀ m k, (hierarchyCoefficient blk r U m k).IsIsometry) ∧
      (∀ m k σ j, hierarchyAmplitude blk r U m k σ j = U m k (fun v ↦ σ v) j) ∧
      ∀ h, (∀ i, blk i < 2 ^ h) →
        ∀ (W : Matrix (ι → Fin d) (ι → Fin d) ℂ), W.IsHermitian → ∀ cW : ℝ,
          ∃ (s : ℕ) (Z : Matrix (ι → Fin d) (Fin s) ℂ),
            Z.IsIsometry ∧ Z * Zᴴ = hierarchyClosingProjection M c x h W cW ∧
            let A := hierarchyRootFrame blk r U h
            let F := Aᴴ * Z
            F.IsIsometry ∧ Z = A * F ∧
            ∀ (φ : EuclideanSpace ℂ (ι → Fin d)),
              toEuclideanLin (hierarchyClosingProjection M c x h W cW) φ = φ →
              ∀ σ, φ σ = ∑ a : Fin (r h 0), ∑ b : Fin s,
                hierarchyAmplitude blk r U h 0 σ a * F a b *
                  (Zᴴ *ᵥ WithLp.ofLp φ) b := by
  done

end TNLean.MPS.AreaLaw.LocalSolution
