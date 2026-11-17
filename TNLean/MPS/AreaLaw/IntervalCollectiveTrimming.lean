/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.EntropyScaling.CutReducedState
import QICLean.Entropy.RegionalViability
import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ViableSubspaceTrimming
import QICLean.Analysis.ViableSubspaceCoordinates

/-!
# Collective trimming on an arbitrary interval

The retained interval is split from its whole outside environment. Its
internal regional prefixes have two global boundaries; the reference rank
bound is therefore the square of the whole-chain MPS bond bound.

These are supporting coordinate and trimming estimates for ALVV,
arXiv:1602.08828v2, `def:trimming`, `lem:trimming`, lines 646–697,
and the reference-space argument following `t:alg1`, lines 1801–1805.
No sampled tree or recursive merge construction is asserted here.
-/

open Matrix
open scoped BigOperators InnerProductSpace TensorProduct ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The internal increasing cuts of a physical interval. Supporting ALVV,
arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
def intervalTrimCut (L p r j : ℕ) : Finset (interval L p r) :=
  Entropy.subregionCut (interval L p r) (interval L p (p + j + 1))

theorem intervalTrimCut_mono (L p r : ℕ) : Monotone (intervalTrimCut L p r) := by
  intro j k hjk v hv
  apply Entropy.mem_subregionCut.mpr
  exact interval_mono le_rfl (by omega) (Entropy.mem_subregionCut.mp hv)

/-- An internal regional prefix, with the whole exterior retained, crosses
at most two global MPS bonds. Supporting ALVV, arXiv:1602.08828v2,
`lem:trimming`, lines 660–697; the squared rank is retained explicitly. -/
theorem schmidtRank_cutEnvVector_interval_le {L q D : ℕ}
    {psi : EuclideanSpace ℂ (Fin L → Fin q)}
    (hpsi : IsOpenMPS L q D (fun x ↦ psi x)) (p r j : ℕ) (hj : p + j + 1 ≤ r) :
    Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
        (intervalTrimCut L p r j)
        (Entropy.regionConfigurationSplit q (interval L p r) psi))) ≤ (max 1 D) ^ 2 := by
  rw [intervalTrimCut, Entropy.schmidtRank_cutEnvVector_regionConfigurationSplit
    (interval_mono le_rfl hj)]
  have heq : interval L p (p + j + 1) = leftBlock L (p + j + 1) \ leftBlock L p := by
    ext v
    simp only [mem_interval, Finset.mem_sdiff, mem_leftBlock]
    omega
  rw [heq]
  exact hpsi.rank_regionState_sdiff_leftBlock_le_max_sq (by omega)

/-- The actual collectively trimmed interval vectors. Supporting ALVV,
arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
noncomputable def intervalTrimVector (L q p r : ℕ) {s : ℕ} (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (interval L p r → Fin q)) (k : Fin s) :
    EuclideanSpace ℂ (interval L p r → Fin q) :=
  Matrix.toEuclideanLin (Entropy.trimProj (intervalTrimCut L p r) xi u (r - p - 1)) (u k)

/-- The span of the actual collectively trimmed interval vectors.
Supporting ALVV, arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
noncomputable def intervalTrimSubspace (L q p r : ℕ) {s : ℕ} (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (interval L p r → Fin q)) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  Entropy.trimSubspace (intervalTrimCut L p r) xi u (r - p - 1)

/-- The actual trimmed interval space is spanned by its recorded vectors.
Supporting ALVV, arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
theorem intervalTrimSubspace_eq_span (L q p r : ℕ) {s : ℕ} (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (interval L p r → Fin q)) :
    intervalTrimSubspace L q p r xi u =
      Submodule.span ℂ (Set.range (intervalTrimVector L q p r xi u)) := rfl

/-- Collective trimming does not increase the dimension of its recorded
spanning family. Supporting ALVV, arXiv:1602.08828v2, `lem:trimming`,
lines 662–663. -/
theorem finrank_intervalTrimSubspace_le (L q p r : ℕ) {s : ℕ} (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (interval L p r → Fin q)) :
    Module.finrank ℂ (intervalTrimSubspace L q p r xi u) ≤ s := by
  classical
  rw [intervalTrimSubspace_eq_span]
  convert _root_.finrank_range_le_card (R := ℂ)
    (intervalTrimVector L q p r xi u) using 1
  · rfl
  · exact (Fintype.card_fin s).symm

/-- Each recorded trimmed vector has bounded rank across every internal
interval cut. Supporting ALVV, arXiv:1602.08828v2, `lem:trimming`,
lines 662–663 and 690–692. -/
theorem schmidtRank_cutVector_intervalTrimVector_le {L q p r s : ℕ}
    {xi : ℝ} (hxi : 0 < xi)
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin s) ℂ S) {j : ℕ} (hj : j < r - p - 1) (k : Fin s) :
    xi ^ 2 * Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
        (intervalTrimCut L p r j)
        (intervalTrimVector L q p r xi (fun t ↦ (u t : _)) k))) ≤ s :=
  Entropy.schmidtRank_cutVector_trimmed_le (intervalTrimCut_mono L p r) hxi u hj k

/-- A common whole-chain MPS reference controls collective trimming on any
interval, using the squared reference bond for its whole outside environment.
Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805. -/
theorem isCloseTo_prodExt_intervalTrimSubspace_of_reference
    {L q p r s D : ℕ} (hD : 1 ≤ D)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta xi : ℝ} (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hxi : 0 < xi)
    (hGU : Submodule.IsCloseTo epsilon G U) (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin s) ℂ S)
    (hS : Submodule.IsCloseTo delta
      (Submodule.prodExt S (↥((interval L p r)ᶜ) → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsCloseTo
      (4 * delta + 6 * epsilon + 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * D ^ 2))
      (Submodule.prodExt
        (intervalTrimSubspace L q p r xi
          (fun k ↦ (u k : EuclideanSpace ℂ (interval L p r → Fin q))))
        (↥((interval L p r)ᶜ) → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap) := by
  let F := Entropy.regionConfigurationSplit q (interval L p r)
  have hGUmap := (Submodule.isCloseTo_map_iff F).mpr hGU
  have hUGmap := (Submodule.isCloseTo_map_iff F).mpr hUG
  have hSU := hS.trans hGUmap hdelta
  have hrank : ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < r - p - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
          (intervalTrimCut L p r j) t)) ≤ D ^ 2 := by
    rintro _ ⟨v, hv, rfl⟩ j hj
    change Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
        (intervalTrimCut L p r j)
        (Entropy.regionConfigurationSplit q (interval L p r) v))) ≤ D ^ 2
    simpa only [max_eq_right hD] using
      schmidtRank_cutEnvVector_interval_le (hU v hv) p r j (by omega)
  have htrim := Entropy.isCloseTo_prodExt_trimSubspace
    (intervalTrimCut_mono L p r) hxi u hSU hrank
  have hback := htrim.trans hUGmap (by positivity)
  have herror :
      2 * (2 * (delta + epsilon) +
        2 * (xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ))) + epsilon) ≤
      4 * delta + 6 * epsilon +
        4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) := by
    push_cast
    exact le_of_eq (by ring)
  exact hback.of_le herror

/-- The reference-space interval trimming bound in the actual tensor
coordinates. Supporting ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1801–1805. -/
theorem isViable_intervalTrimSubspace_of_reference
    {L q p r s D : ℕ} (hD : 1 ≤ D)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta xi : ℝ} (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hxi : 0 < xi)
    (hGU : Submodule.IsCloseTo epsilon G U) (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin s) ℂ S)
    (hS : Submodule.IsViable (F := EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q))
      delta S
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsViable (F := EuclideanSpace ℂ (↥((interval L p r)ᶜ) → Fin q))
      (4 * delta + 6 * epsilon + 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * D ^ 2))
      (intervalTrimSubspace L q p r xi
        (fun k ↦ (u k : EuclideanSpace ℂ (interval L p r → Fin q))))
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
  apply (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) _ G).mp
  exact isCloseTo_prodExt_intervalTrimSubspace_of_reference hD hepsilon hdelta hxi
    hGU hUG hU u ((Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) S G).mpr hS)

end TNLean.MPS.AreaLaw
