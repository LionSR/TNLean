/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalIsometryPath
import TNLean.MPS.Symmetry.PhysicalIsometricEmbedding
import TNLean.MPS.Symmetry.InjectiveParentGappedPath

/-!
# Gapped paths between orthogonal physical embeddings

Two symmetry-intertwining isometric embeddings of one injective tensor,
with orthogonal physical ranges, are connected by a plane rotation of the
embedding. Injectivity and symmetry persist, so the canonical parent
Hamiltonians form a uniformly gapped path. This is a step in the common
physical-space construction of arXiv:1010.3732, Sections II.B.2 and II.C.2.
-/

namespace MPSTensor

open scoped Matrix

/-- Orthogonal symmetry-intertwining embeddings of an injective tensor
have symmetric gapped canonical-parent paths between them. Source:
arXiv:1010.3732, Sections II.B.2 and II.C.2. -/
noncomputable def orthogonalEmbeddingGappedPath
    {G : Type*} [Group G] {d e D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G → Matrix (Fin d) (Fin d) ℂ)
    (R : G →* Matrix.unitaryGroup (Fin e) ℂ)
    (V W : Matrix (Fin e) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (hVW : Vᴴ * W = 0)
    (hInterV : ∀ g, (R g : Matrix (Fin e) (Fin e) ℂ) * V = V * U g)
    (hInterW : ∀ g, (R g : Matrix (Fin e) (Fin e) ℂ) * W = W * U g)
    (hCov : ∀ g, GaugeEquiv A (rotatePhysical (U g) A)) :
    SymmetricGappedInteractionPath R
      (canonicalParentMatrix (fun τ : Fin e ↦ ∑ σ : Fin d, V τ σ • A σ))
      (canonicalParentMatrix (fun τ : Fin e ↦ ∑ σ : Fin d, W τ σ • A σ)) := by
  let B : Set.Icc (0 : ℝ) 1 → MPSTensor e D := fun t τ ↦
    ∑ σ : Fin d, Matrix.orthogonalIsometryPath V W t τ σ • A σ
  have hCont : Continuous B := by
    apply continuous_pi
    intro τ
    apply continuous_finsetSum
    intro σ _
    exact ((Matrix.continuous_orthogonalIsometryPath V W).comp
      continuous_subtype_val).matrix_elem τ σ |>.smul continuous_const
  have hInj (t : Set.Icc (0 : ℝ) 1) : Kraus.IsInjective (B t) :=
    isInjective_kraus_isometry A _
      (Matrix.orthogonalIsometryPath_isometry V W hV hW hVW t) hA
  have hSym (t : Set.Icc (0 : ℝ) 1) (g : G) :
      GaugeEquiv (B t) (rotatePhysical (R g : Matrix (Fin e) (Fin e) ℂ) (B t)) :=
    gaugeEquiv_physicalEmbedding_of_intertwining A
      (Matrix.orthogonalIsometryPath V W t) (U g) (R g)
      (Matrix.orthogonalIsometryPath_intertwining V W
        (R g : Matrix (Fin e) (Fin e) ℂ) (U g)
        (hInterV g) (hInterW g) t) (hCov g)
  convert injectiveParentGappedPath R B hCont hInj hSym using 1 <;>
    simp [B]

end MPSTensor
