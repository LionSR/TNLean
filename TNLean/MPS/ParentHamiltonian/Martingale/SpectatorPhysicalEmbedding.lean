/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EuclideanExtendByZero
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorMaps

/-!
# Spectator extensions and Euclidean physical embeddings

Extending an active operator by the identity on a finite spectator space
commutes with coordinate embeddings, whenever the active operators intertwine.
The result uses the existing fiberwise extension and actual extension by zero,
including empty active or spectator alphabets.
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

end Function.Embedding

namespace ContinuousLinearMap

variable {I J S T : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

/-- Fiberwise identity extension intertwines with Euclidean extension by zero
whenever the active operators intertwine. Outside the spectator image both
fibers vanish; no nonempty-coordinate hypothesis is needed. -/
theorem rightFiberwiseMap_extendByZero (e : I ↪ J) (g : S ↪ T)
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
    rw [Function.Embedding.rightFiber_extendByZero_image,
      Function.Embedding.rightFiber_extendByZero_image,
      ContinuousLinearMap.rightFiber_rightFiberwiseMap, h]
  · rw [Function.Embedding.rightFiber_extendByZero_not_mem_range _ _ _ _ ht,
      Function.Embedding.rightFiber_extendByZero_not_mem_range _ _ _ _ ht, map_zero]

end ContinuousLinearMap