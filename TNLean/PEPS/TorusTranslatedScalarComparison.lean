/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGaugedWeightCovariance
import TNLean.PEPS.TorusFundamentalTheorem
import TNLean.PEPS.RegionBlock.ReindexInjectivity

/-!
# Translating a one-site scalar comparison

A proportionality comparison on R and on R with one additional vertex determines
one common scalar at every torus vertex when the tensors are translation invariant
and the edge gauge family is translation covariant. The proof transports the same
comparison, including its scalars, rather than choosing new scalars after translation.

This is the final one-site comparison in arXiv:1804.04964, proof of Theorem 3,
lines 1544–1571, stated for an arbitrary reference region.
-/

namespace TNLean.PEPS
open scoped Matrix
variable {width height d : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]

/-- A translated comparison on a region and its one-site extension gives the same scalar
ratio at every vertex; arXiv:1804.04964, proof of Theorem 3, lines 1544–1571. -/
theorem component_eq_gaugeVertex_of_translatedProportional
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    {X : (e : Edge (torusGraph width height)) → GL (Fin (B.bondDim e)) ℂ}
    (hXcov : IsTranslationCovariantGaugeFamily B X)
    (hbond : A.bondDim = B.bondDim)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (R : Finset (TorusVertex width height)) (v₀ : TorusVertex width height)
    (hvR : v₀ ∉ R) {cR cS : ℂ} (hcR0 : cR ≠ 0)
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R)
    (hcRprop : TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A R)
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond) R) cR)
    (hcSprop : TwoBlockScalarProportional.{0, 0, 0, 0}
      (regionTwoBlock (G := torusGraph width height) A (insert v₀ R))
      (regionTwoBlock (G := torusGraph width height)
        (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond)
        (insert v₀ R)) cS)
    (v : TorusVertex width height)
    (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
    (σ : Fin d) :
    A.component v η σ =
      (cS / cR) * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ := by
  let a := v.1 - v₀.1
  let b := v.2 - v₀.2
  have hvmap : translate a b v₀ = v := by
    apply Prod.ext <;> simp [a, b, translate]
  have hvR' : v ∉ Region.map (translate a b) R := by
    rw [← hvmap, mem_Region_map_apply]
    exact hvR
  have htr : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Region.map (translate a b) R) :=
    regionBlockedTensorInjective_translate hB a b R hRB
  have hRC : RegionBlockedTensorInjective (G := torusGraph width height)
      (reindexTensor (G := torusGraph width height) (applyGauge B X) hbond)
      (Region.map (translate a b) R) :=
    regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ htr)
  have hRp := twoBlockScalarProportional_translate hA hB hXcov hbond a b R hcRprop
  have hSp := twoBlockScalarProportional_translate hA hB hXcov hbond a b
    (insert v₀ R) hcSprop
  have hmapinsert : Region.map (translate a b) (insert v₀ R) =
      insert (translate a b v₀) (Region.map (translate a b) R) := Finset.map_insert _ _ _
  rw [hmapinsert, hvmap] at hSp
  exact component_eq_gaugeVertex_of_twoBlockProportional A B
    (Region.map (translate a b) R) hvR' hbond X cR cS hcR0 hposA hRC hRp hSp η σ

end TNLean.PEPS
