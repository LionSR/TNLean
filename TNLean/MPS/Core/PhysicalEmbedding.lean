/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EuclideanExtendByZero
import TNLean.MPS.Overlap.Basic

/-!
# Physical extension of a periodic matrix product tensor

Extending a tensor by zero along an embedding of its one-site alphabet extends
its actual periodic state by zero along the induced configuration embedding.
The bond space and the system size are unchanged. The identity includes the
empty chain and empty physical alphabets.

This is the tensor-level physical embedding used in the finite-prefix
investigation of SPWC10, arXiv:0909.5347, Theorem 5, lines 850–880. It asserts
only the actual state identity, not a ground-space or all-volume conclusion.
-/

namespace MPSTensor

/-- Extension of the physical tensor by zero produces exactly the isometric
extension of its periodic state, at every chain length. The bond dimension is
unchanged. Source context: physical-sector embeddings in the finite-prefix
investigation of SPWC10, arXiv:0909.5347, Theorem 5. -/
theorem mpvState_extend_physical {a d D : ℕ} (e : Fin a ↪ Fin d)
    (A : MPSTensor a D) (N : ℕ) :
    mpvState (Function.extend e A 0) N =
      (Function.Embedding.piCongrRight (fun _ : Fin N ↦ e)).euclideanExtendByZero
        (mpvState A N) := by
  classical
  let E := Function.Embedding.piCongrRight (fun _ : Fin N ↦ e)
  have hA : Kraus.reindexPhysical e (Function.extend e A 0) = A := by
    funext i
    exact e.injective.extend_apply A 0 i
  ext σ
  change mpvState (Function.extend e A 0) N σ = E.euclideanExtendByZero (mpvState A N) σ
  by_cases hσ : σ ∈ Set.range E
  · obtain ⟨τ, rfl⟩ := hσ
    rw [Function.Embedding.euclideanExtendByZero_apply_image, mpvState_apply,
      mpvState_apply]
    have h := mpv_reindexPhysical e (Function.extend e A 0) τ
    rw [hA] at h
    exact h.symm
  · rw [Function.Embedding.euclideanExtendByZero_apply_not_mem_range _ _ _ hσ,
      mpvState_apply]
    have hout : ∃ i, σ i ∉ Set.range e := by
      by_contra! h
      apply hσ
      refine ⟨fun i ↦ Classical.choose (h i), ?_⟩
      funext i
      exact Classical.choose_spec (h i)
    obtain ⟨i, hi⟩ := hout
    have hmem : σ i ∈ List.ofFn σ := List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨u, v, hw⟩ := List.mem_iff_append.mp hmem
    change Matrix.trace (Kraus.evalWord (Function.extend e A 0) (List.ofFn σ)) = 0
    rw [hw, Kraus.evalWord_append, Kraus.evalWord_cons,
      Function.extend_apply' A (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) (σ i) hi]
    simp

end MPSTensor
