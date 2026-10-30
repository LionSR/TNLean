/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyBlockCoordinates
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyConstruction
import TNLean.Circuit.EntropySupport
import QICLean.Entropy.SupportedProjectionCoordinates
import QICLean.Entropy.LocalProjectionTensorCoordinates

/-!
# Tensor coordinates of the constructed retained hierarchy

The local range frames are chosen once for the actual recursively defined
spectral projections. The parent coefficients are their adjoint tensor-product
coordinates. The amplitude contraction is evaluated directly on physical
configurations, including those of empty padded blocks.

This is the retained-basis construction of Hastings,
arXiv:cond-mat/0508554v3, Section III, lines 630–685. No bound on intermediate
retained dimensions or computational running time is asserted. The corrected
windows are recorded in `docs/paper-gaps/hastings05_hierarchical_projection.tex`
and `docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The parent coefficients in two fixed local child frames. Hastings,
arXiv:cond-mat/0508554v3, Section III, lines 669–685. -/
noncomputable def hierarchyCoefficient (blk : ι → ℕ) (r : ℕ → ℕ → ℕ)
    (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
      (Fin (r m k)) ℂ) (m k : ℕ) :
    Matrix (Fin (r m (2 * k)) × Fin (r m (2 * k + 1))) (Fin (r (m + 1) k)) ℂ :=
  (reindex (Entropy.regionUnionEquiv (disjoint_hierarchyBlock_children blk m k)).symm
    (Equiv.refl _) (U m (2 * k) ⊗ₖ U m (2 * k + 1)))ᴴ *
    (show Matrix (Entropy.RegionConfig (fun _ : ι ↦ d)
      (hierarchyBlock blk m (2 * k) ∪ hierarchyBlock blk m (2 * k + 1)))
      (Fin (r (m + 1) k)) ℂ from U (m + 1) k)

/-- Recursive amplitudes of the fixed local frames and their actual coefficient
matrices. Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
noncomputable def hierarchyAmplitude (blk : ι → ℕ) (r : ℕ → ℕ → ℕ)
    (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
      (Fin (r m k)) ℂ) : (m k : ℕ) → (ι → Fin d) → Fin (r m k) → ℂ
  | 0, k, σ, j => U 0 k (fun v ↦ σ v) j
  | m + 1, k, σ, j => ∑ a : Fin (r m (2 * k)) × Fin (r m (2 * k + 1)),
      hierarchyAmplitude blk r U m (2 * k) σ a.1 *
        hierarchyAmplitude blk r U m (2 * k + 1) σ a.2 *
          hierarchyCoefficient blk r U m k a j

/-- Fixed local frames satisfying the actual nesting identity contract to their
physical column amplitudes. This is the finite algebraic induction used in
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 669–685. -/
private theorem hierarchyAmplitude_eq_of_nesting (blk : ι → ℕ) (r : ℕ → ℕ → ℕ)
    (U : ∀ m k, Matrix (Entropy.RegionConfig (fun _ : ι ↦ d) (hierarchyBlock blk m k))
      (Fin (r m k)) ℂ) (σ₀ : ι → Fin d)
    (hU : ∀ m k, (U m k).IsIsometry)
    (hcontain : ∀ m k,
      Entropy.localLift (hierarchyBlock blk m (2 * k)) (U m (2 * k) * (U m (2 * k))ᴴ) *
        Entropy.localLift (hierarchyBlock blk m (2 * k + 1))
          (U m (2 * k + 1) * (U m (2 * k + 1))ᴴ) *
        Entropy.localLift (hierarchyBlock blk (m + 1) k)
          (U (m + 1) k * (U (m + 1) k)ᴴ) =
        Entropy.localLift (hierarchyBlock blk (m + 1) k)
          (U (m + 1) k * (U (m + 1) k)ᴴ)) (m : ℕ) :
    ∀ k σ j, hierarchyAmplitude blk r U m k σ j = U m k (fun v ↦ σ v) j := by
  induction m with
  | zero => simp only [hierarchyAmplitude]
  | succ m ih =>
      intro k σ j
      have hentry := (Entropy.localLift_tensor_range_coordinates
        (disjoint_hierarchyBlock_children blk m k) (hU (m + 1) k)
        (U m (2 * k)) (U m (2 * k + 1)) σ₀ (hcontain m k)).2.2.2 σ j
      simpa only [hierarchyAmplitude, ih, hierarchyCoefficient, hierarchyBlock] using hentry.symm

/-- The constructed hierarchy has one simultaneous family of local range frames
whose actual coefficient tensors contract to the local amplitudes. The ranks
refer to local projections, before their exterior identity is restored.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem exists_hierarchy_tensor_coordinates (blk : ι → ℕ)
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
      ∀ m k σ j, hierarchyAmplitude blk r U m k σ j = U m k (fun v ↦ σ v) j := by
  have hproj := isStarProjection_supersiteHierarchy blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp hM
  have hsupport := mem_supportedOperators_hierarchy blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp
  have hlocalSupport (m k : ℕ) : Entropy.IsSupportedOn (n := fun _ : ι ↦ d)
      (hierarchyProjection M c x m k) (hierarchyBlock blk m k) :=
    isSupportedOn_of_mem_supportedOperators
      ((coe_hierarchyBlock blk m k).symm ▸ hsupport m k)
  have hframes (m k : ℕ) :=
    (hlocalSupport m k).exists_local_range_isometry (hproj m k) σ₀
  choose r U hU hP hRank _hDim using hframes
  have hcomm := commute_supersiteHierarchy blk (hierarchyProjection M c x) M c x
    (hierarchyProjection_zero M c x) (hierarchyProjection_succ M c x) hsupp
  have hpair (m k : ℕ) := (hproj m (2 * k)).mul (hproj m (2 * k + 1)) (hcomm m k)
  have hcontain (m k : ℕ) :
      Entropy.localLift (hierarchyBlock blk m (2 * k)) (U m (2 * k) * (U m (2 * k))ᴴ) *
        Entropy.localLift (hierarchyBlock blk m (2 * k + 1))
          (U m (2 * k + 1) * (U m (2 * k + 1))ᴴ) *
        Entropy.localLift (hierarchyBlock blk (m + 1) k)
          (U (m + 1) k * (U (m + 1) k)ᴴ) =
        Entropy.localLift (hierarchyBlock blk (m + 1) k)
          (U (m + 1) k * (U (m + 1) k)ᴴ) := by
    rw [← hP m (2 * k), ← hP m (2 * k + 1), ← hP (m + 1) k]
    rw [hierarchyProjection_succ, compressedWindowProjection, ← Matrix.mul_assoc,
      (hpair m k).isIdempotentElem.eq]
  refine ⟨r, U, (fun m k ↦ ⟨hU m k, hP m k, hRank m k⟩), ?_,
    hierarchyAmplitude_eq_of_nesting blk r U σ₀ hU hcontain⟩
  intro m k
  simpa only [hierarchyCoefficient] using
    (Entropy.localLift_tensor_range_coordinates (disjoint_hierarchyBlock_children blk m k)
      (hU (m + 1) k) (U m (2 * k)) (U m (2 * k + 1)) σ₀ (hcontain m k)).1

end TNLean.MPS.AreaLaw.LocalSolution
