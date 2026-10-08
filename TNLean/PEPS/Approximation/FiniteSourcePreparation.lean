/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonSourcePreparation
import TNLean.PEPS.Approximation.FinitePairSources

/-!
# Finite coordinates for a family of source preparations

Finite coordinate spaces for the two halves of each source can be included into
their original private spaces by local isometries. Applying these inclusions in
the fixed source order recovers the original preparation exactly and creates no
additional sources. No dimension bound on the private ambient spaces is required.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, common private slot spaces and finite source representations,
lines 253–267 and 279–305.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P ι : Type}

/-- Include both halves of one source by local isometries while retaining the tail.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
private theorem pair_cons_mapIsometry_expands (r : PairSource P) (U V U' V' : HSpace)
    (f : U →ₗᵢ[ℂ] U') (g : V →ₗᵢ[ℂ] V') (η : U ⊗[ℂ] V) (T : SourceInventory P) :
    Expands (⟨r.left, r.right, r.distinct, U, V, η⟩ :: T)
      (⟨r.left, r.right, r.distinct, U', V', TensorProduct.mapIsometry f g η⟩ :: T) := by
  intro ℓ
  obtain ⟨hw, hs⟩ := Word.mapPair_spec r.left r.right f.toContinuousLinearMap
    g.toContinuousLinearMap (LinearIsometry.norm_toContinuousLinearMap_le _)
    (LinearIsometry.norm_toContinuousLinearMap_le _) (T.layout ++ ℓ)
  refine ⟨Word.mapPair r.left r.right f.toContinuousLinearMap g.toContinuousLinearMap
    (T.layout ++ ℓ), hw, hs, ?_⟩
  have h := Word.eval_mapPair_source r.distinct f.toContinuousLinearMap
    g.toContinuousLinearMap η (T.layout ++ ℓ)
  simp only [← TensorProduct.toContinuousLinearMap_mapIsometry] at h
  exact (comp_assoc _ _ _).symm.trans (congrArg (· ∘L (T.prepare ℓ).eval) h)

/-- Applying the isometric inclusions in each pair slot recovers the preparation
of the included vectors, using only local isometries.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267. -/
theorem ofSlots_mapIsometry_expands (R : SourceInventory P)
    (U V U' V' : Fin R.length → HSpace)
    (f : ∀ i, U i →ₗᵢ[ℂ] U' i) (g : ∀ i, V i →ₗᵢ[ℂ] V' i)
    (η : ∀ i, U i ⊗[ℂ] V i) :
    (ofSlots R U V η).Expands
      (ofSlots R U' V' (fun i ↦ TensorProduct.mapIsometry (f i) (g i) (η i))) := by
  induction R with
  | nil => exact Expands.refl []
  | cons r R ih =>
      rw [ofSlots_cons, ofSlots_cons]
      exact (pair_cons_mapIsometry_expands r (U 0) (V 0) (U' 0) (V' 0)
        (f 0) (g 0) (η 0) _).trans
        (Expands.cons _ (ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ U' i.succ) (fun i ↦ V' i.succ) (fun i ↦ f i.succ)
          (fun i ↦ g i.succ) (fun i ↦ η i.succ)))

/-- A finite family of source preparations has common finite coordinate spaces
at every endpoint. The coordinate vectors retain their exact norms, and local
isometric inclusions recover every original preparation for all spectator registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 279–305. -/
theorem exists_finite_coordinate_expansions [Finite ι] (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η : ι → ∀ i, U i ⊗[ℂ] V i) :
    ∃ a b : Fin R.length → ℕ,
      ∃ f : ∀ i, EuclideanSpace ℂ (Fin (a i)) →ₗᵢ[ℂ] U i,
      ∃ g : ∀ i, EuclideanSpace ℂ (Fin (b i)) →ₗᵢ[ℂ] V i,
      ∃ η₀ : ι → ∀ i,
        EuclideanSpace ℂ (Fin (a i)) ⊗[ℂ] EuclideanSpace ℂ (Fin (b i)),
        (∀ ξ i, TensorProduct.mapIsometry (f i) (g i) (η₀ ξ i) = η ξ i) ∧
        (∀ ξ i, ‖η₀ ξ i‖ = ‖η ξ i‖) ∧
        ∀ ξ, (ofSlots R (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i)))
          (η₀ ξ)).Expands (ofSlots R U V (η ξ)) := by
  classical
  choose a b f g η₀ hmap hnorm using fun i ↦
    PairSource.exists_finite_coordinates (U i) (V i) (fun ξ ↦ η ξ i)
  refine ⟨a, b, f, g, fun ξ i ↦ η₀ i ξ,
    fun ξ i ↦ hmap i ξ, fun ξ i ↦ hnorm i ξ, ?_⟩
  intro ξ
  have h := ofSlots_mapIsometry_expands R
    (fun i ↦ euc (Fin (a i))) (fun i ↦ euc (Fin (b i))) U V f g
    (fun i ↦ η₀ i ξ)
  simpa only [hmap] using h

end TNLean.PEPS.PairEffect.SourceInventory
