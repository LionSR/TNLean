/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalAlphabetEmbedding
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorMaps

/-!
# Actual local parent terms under physical embeddings

The complementary pair projector is extended by the identity on the physical
coordinates outside that pair. Physical extension by zero intertwines these
actual extended local terms, including independent embeddings of the outside
configuration space. This is the local-to-global operator identity needed to
transport the varying-physical-space open parent Hamiltonian in PGVWC07,
arXiv:quant-ph/0608197, Theorem 9, source lines 1201–1220.
-/

namespace Function.Embedding

variable {I J S T : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

private theorem rightFiber_extendByZero_image (e : I ↪ J) (g : S ↪ T)
    (v : EuclideanSpace ℂ (I × S)) (s : S) :
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) (g s) =
      e.euclideanExtendByZero (ContinuousLinearMap.rightFiber v s) := by
  classical
  ext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    change (e.prodMap g).euclideanExtendByZero v ((e.prodMap g) (i, s)) = _
    rw [euclideanExtendByZero_apply_image, euclideanExtendByZero_apply_image]
  · have hp : (j, g s) ∉ Set.range (e.prodMap g) := by
      rintro ⟨⟨i, t⟩, h⟩
      exact hj ⟨i, congrArg Prod.fst h⟩
    change (e.prodMap g).euclideanExtendByZero v (j, g s) =
      e.euclideanExtendByZero (ContinuousLinearMap.rightFiber v s) j
    rw [euclideanExtendByZero_apply_not_mem_range _ _ _ hp,
      euclideanExtendByZero_apply_not_mem_range _ _ _ hj]

private theorem rightFiber_extendByZero_not_mem_range (e : I ↪ J) (g : S ↪ T)
    (v : EuclideanSpace ℂ (I × S)) (t : T) (ht : t ∉ Set.range g) :
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) t = 0 := by
  ext j
  have hp : (j, t) ∉ Set.range (e.prodMap g) := by
    rintro ⟨⟨i, s⟩, h⟩
    exact ht ⟨s, congrArg Prod.snd h⟩
  exact euclideanExtendByZero_apply_not_mem_range _ _ _ hp

private theorem rightFiberwiseMap_extendByZero (e : I ↪ J) (g : S ↪ T)
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (H : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)
    (h : ∀ v, H (e.euclideanExtendByZero v) = e.euclideanExtendByZero (G v))
    (v : EuclideanSpace ℂ (I × S)) :
    ContinuousLinearMap.rightFiberwiseMap H ((e.prodMap g).euclideanExtendByZero v) =
      (e.prodMap g).euclideanExtendByZero (ContinuousLinearMap.rightFiberwiseMap G v) := by
  classical
  apply PiLp.ext
  rintro ⟨j, t⟩
  change H (ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) t) j =
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero
      (ContinuousLinearMap.rightFiberwiseMap G v)) t j
  by_cases ht : ∃ s, g s = t
  · obtain ⟨s, rfl⟩ := ht
    rw [rightFiber_extendByZero_image, rightFiber_extendByZero_image,
      ContinuousLinearMap.rightFiber_rightFiberwiseMap, h]
  · rw [rightFiber_extendByZero_not_mem_range _ _ _ _ ht,
      rightFiber_extendByZero_not_mem_range _ _ _ _ ht, map_zero]

end Function.Embedding

namespace Matrix

variable {I J K L S T a b c : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype S] [Fintype T]
  [Fintype a] [Fintype b] [Fintype c]

/-- Extending an actual pair parent projector by the identity outside that pair
commutes with independent physical embeddings of both sites and the entire
outside configuration space. The local intertwining is derived from the actual
boundary ranges, not supplied as an assumption.
Source: PGVWC07, Theorem 9 proof, lines 1213–1220. -/
theorem pair_parent_localTerm_extend_physical
    (e : I ↪ J) (f : K ↪ L) (g : S ↪ T)
    (A : I → Matrix a b ℂ) (B : K → Matrix b c ℂ)
    (v : EuclideanSpace ℂ ((I × K) × S)) :
    ContinuousLinearMap.rightFiberwiseMap
        (LinearMap.range (rectangularPairBoundary
          (Function.extend e A 0) (Function.extend f B 0)))ᗮ.starProjection
        (((e.prodMap f).prodMap g).euclideanExtendByZero v) =
      ((e.prodMap f).prodMap g).euclideanExtendByZero
        (ContinuousLinearMap.rightFiberwiseMap
          (LinearMap.range (rectangularPairBoundary A B))ᗮ.starProjection v) :=
  Function.Embedding.rightFiberwiseMap_extendByZero (e.prodMap f) g _ _
    (pair_parent_projection_extend_physical e f A B) v

end Matrix
