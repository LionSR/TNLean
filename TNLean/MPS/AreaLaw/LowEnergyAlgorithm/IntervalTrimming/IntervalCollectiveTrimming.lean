/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.Tensor.OpenMPS.CutReducedState
import QICLean.ManyBody.Entropy.Cut.RegionalViability
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.ManyBody.Subspace.Trimming
import QICLean.Analysis.Subspace.ViableSubspaceCoordinates
import QICLean.ManyBody.Subspace.Sampling.CanonicalHalfSamplingParent
import QICLean.ManyBody.Subspace.Sampling.StoppedHalfSamplingSeed

/-!
# Collective trimming on an arbitrary interval

The retained interval is split from its whole outside environment. Its
internal regional prefixes have two global boundaries; the reference rank
bound is therefore the square of the whole-chain MPS bond bound.

These are supporting coordinate and trimming estimates for ALVV,
arXiv:1602.08828v2, `def:trimming`, `lem:trimming`, lines 646–697,
and the reference-space argument following `t:alg1`, lines 1801–1805.
No sampled tree or recursive merge construction is asserted here.

## The complete stopped half-sampling parent on an actual interval

The actual candidate projection is expressed in fixed finite coordinates.
A prescribed finite sequence supplies fresh samples for the stopped native
iteration. Its terminal full-family image and collective trim use the same
interval cuts and the same operator family. Supporting ALVV,
arXiv:1602.08828v2, the resampling description at lines 749–755 and
reference trimming at lines 1801–1813.

**Local fix (repeated sampling and terminal amplification):** This is the
corrected repeated-sampling parent, including its terminal full-family
image and trim, rather than the sample-once Figure `fig:merge-prime`.
The correction is recorded at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
No running-time estimate is asserted.

## The last untrimmed image of an interval run

The candidate projection, finite sequence and stopped iteration are exactly
those of the complete interval parent. This names its last full-family
image before the terminal collective trim. It has no spectral target or
energy-center parameter. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813.

**Local fix (repeated sampling and terminal amplification):** The image
belongs to the corrected repeated-sampling operation, including a terminal
full-family image even when the initial rank is below the threshold. See
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.

## Weighted reference bounds for interval trimming

A common whole-chain MPS reference bounds the actual collective trim on
an arbitrary interval, retaining its entire exterior. The reference rank
is the square of its whole-chain bond bound. The robustness weight is
free, so the coefficient of the incoming viability error can be chosen
arbitrarily close to one.

This supports the reference argument in ALVV, arXiv:1602.08828v2,
proof of `t:alg1`, lines 1801–1813.

**Local fix (collective trimming constant):** The increment is the proved
`2 ξ √(m b)`; see
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
-/

section

open ManyBody (interval interval_mono mem_interval)

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
  have heq : interval L p (p + j + 1) = interval L 0 (p + j + 1) \ interval L 0 p := by
    ext v
    simp only [mem_interval, Finset.mem_sdiff, Nat.zero_le, true_and]
    omega
  rw [heq]
  exact hpsi.rank_regionState_sdiff_interval_le_max_sq (by omega)

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
      (ManyBody.cutVector (X := fun _ ↦ Fin q)
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
      (Submodule.prodExt S ({v // v ∉ interval L p r} → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsCloseTo
      (4 * delta + 6 * epsilon + 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * D ^ 2))
      (Submodule.prodExt
        (intervalTrimSubspace L q p r xi
          (fun k ↦ (u k : EuclideanSpace ℂ (interval L p r → Fin q))))
        ({v // v ∉ interval L p r} → Fin q))
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
    (hS : Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ interval L p r} → Fin q))
      delta S
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsViable (F := EuclideanSpace ℂ ({v // v ∉ interval L p r} → Fin q))
      (4 * delta + 6 * epsilon + 4 * xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * D ^ 2))
      (intervalTrimSubspace L q p r xi
        (fun k ↦ (u k : EuclideanSpace ℂ (interval L p r → Fin q))))
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) := by
  apply (Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) _ G).mp
  exact isCloseTo_prodExt_intervalTrimSubspace_of_reference hD hepsilon hdelta hxi
    hGU hUG hU u ((Entropy.isCloseTo_prodExt_region_iff_isViable (interval L p r) S G).mpr hS)

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The literal native complete parent, using the candidate's actual
projection, the interval's internal cuts and the fixed finite sequence
extended by identity coordinates. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1801–1813. -/
noncomputable def canonicalHalfSampledIntervalParent (L q p r D threshold rounds : ℕ)
    {N : ℕ} (F : Fin N →
      EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  Entropy.canonicalHalfSamplingParent (n := fun _ : interval L p r ↦ q)
    e (intervalTrimCut L p r) xi (r - p - 1) D threshold rounds F P
    (Entropy.halfSamplingSeedSequence U)

/-- The literal finite-seed parent has measurable actual projection for
any candidate family with measurable projection. No successful-sampling
or measurable-basis hypothesis is supplied. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
theorem measurable_projectionMatrix_canonicalHalfSampledIntervalParent
    {X : Type*} [MeasurableSpace X] {L q p r N : ℕ}
    (D threshold rounds : ℕ)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : X → Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (hW : Measurable (fun x ↦ (Matrix.toEuclideanCLM
      (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection)) :
    Measurable (fun x : X × (Fin rounds → Matrix.rankUnitaryProduct
        (Fintype.card (interval L p r → Fin q))) ↦
      (Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
        (canonicalHalfSampledIntervalParent L q p r D threshold rounds F xi
          (W x.1) x.2).starProjection) := by
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := fun x ↦ ((Matrix.toEuclideanCLM
    (n := interval L p r → Fin q) (𝕜 := ℂ)).symm (W x).starProjection).reindex e.symm e.symm
  let input := fun x : X × (Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) ↦
    (P x.1, Entropy.halfSamplingSeedSequence x.2)
  have hP : Measurable P :=
    ((continuous_id : Continuous (fun M : Matrix (interval L p r → Fin q)
      (interval L p r → Fin q) ℂ ↦ M)).matrix_reindex e.symm e.symm).measurable.comp hW
  have hInput : Measurable input := (hP.comp measurable_fst).prodMk
    ((Entropy.measurable_halfSamplingSeedSequence _ rounds).comp measurable_snd)
  exact (Entropy.measurable_projectionMatrix_canonicalHalfSamplingParent
    (n := fun _ : interval L p r ↦ q) e (intervalTrimCut L p r) xi
    (r - p - 1) D threshold rounds F).comp (f := input) hInput

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The actual last full-family image of the prescribed stopped interval
run, before its final collective trim. All family, cut and sequence data
are the same as in the complete parent. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813. -/
noncomputable def canonicalHalfSampledIntervalImage (L q p r D threshold rounds : ℕ)
    {N : ℕ} (F : Fin N →
      EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q)) (xi : ℝ)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) :=
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let Q := Entropy.canonicalHalfSampleTrimIterate (n := fun _ : interval L p r ↦ q)
    e (intervalTrimCut L p r) xi (r - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) P
    (Entropy.halfSamplingSeedSequence U) rounds
  (Matrix.toEuclideanLin (Matrix.familySupportProj
    (fun i ↦ Entropy.nativeFamilyMatrix e F i * Q))).range

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Transport one actual reference vector into interval/exterior
coordinates without discarding the exterior. Its internal-cut rank is
bounded by the squared whole-chain bond. Supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 660–697, and the reference
argument, lines 1801–1805. -/
theorem schmidtRank_cutEnvVector_interval_reference_le
    {L q D : ℕ} (hD : 1 ≤ D)
    {U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x)) (p r : ℕ)
    {t : EuclideanSpace ℂ
      ((interval L p r → Fin q) × ({v // v ∉ interval L p r} → Fin q))}
    (ht : t ∈ U.map
      (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)
    (j : ℕ) (hj : j < r - p - 1) :
    Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
        (intervalTrimCut L p r j) t)) ≤ D ^ 2 := by
  obtain ⟨v, hv, rfl⟩ := ht
  change Matrix.schmidtRank (WithLp.ofLp
    (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
      (intervalTrimCut L p r j)
      (Entropy.regionConfigurationSplit q (interval L p r) v))) ≤ D ^ 2
  simpa only [max_eq_right hD] using
    schmidtRank_cutEnvVector_interval_le (hU v hv) p r j (by omega)

/-- The actual collective interval trim has a target-relative bound with
a free positive robustness weight. The one reference controls the whole
exterior at every internal cut. Supporting ALVV, arXiv:1602.08828v2,
proof of `t:alg1`, lines 1801–1813. -/
theorem isCloseTo_prodExt_intervalTrimSubspace_of_reference_weighted
    {L q p r s D : ℕ} (hD : 1 ≤ D)
    {G U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    {epsilon delta xi theta : ℝ} (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 ≤ delta) (hxi : 0 < xi) (htheta : 0 < theta)
    (hGU : Submodule.IsCloseTo epsilon G U) (hUG : Submodule.IsCloseTo epsilon U G)
    (hU : ∀ v ∈ U, IsOpenMPS L q D (fun x ↦ v x))
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin s) ℂ S)
    (hS : Submodule.IsCloseTo delta
      (Submodule.prodExt S ({v // v ∉ interval L p r} → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap)) :
    Submodule.IsCloseTo
      ((1 + theta) * ((1 + theta) * delta + (1 + 1 / theta) * epsilon +
        2 * (xi * Real.sqrt (((r - p - 1 : ℕ) : ℝ) * (D ^ 2 : ℕ)))) +
        (1 + 1 / theta) * epsilon)
      (Submodule.prodExt (intervalTrimSubspace L q p r xi (fun k ↦ (u k : _)))
        ({v // v ∉ interval L p r} → Fin q))
      (G.map (Entropy.regionConfigurationSplit q (interval L p r)).toLinearEquiv.toLinearMap) := by
  let F := Entropy.regionConfigurationSplit q (interval L p r)
  have hGUmap := (Submodule.isCloseTo_map_iff F).mpr hGU
  have hUGmap := (Submodule.isCloseTo_map_iff F).mpr hUG
  have hrank : ∀ t ∈ U.map F.toLinearEquiv.toLinearMap, ∀ j < r - p - 1,
      Matrix.schmidtRank (WithLp.ofLp
        (Entropy.cutEnvVector (n := fun _ : interval L p r ↦ q)
          (intervalTrimCut L p r j) t)) ≤ D ^ 2 := by
    intro t ht j hj
    exact schmidtRank_cutEnvVector_interval_reference_le hD hU p r ht j hj
  exact Entropy.isCloseTo_prodExt_trimSubspace_of_reference_weighted
    (intervalTrimCut_mono L p r) hxi hdelta hepsilon htheta u hS hGUmap hUGmap hrank

end TNLean.MPS.AreaLaw

end
