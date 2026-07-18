/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

/-!
# Finite-dimensional mean-ergodic projection

Let $f$ be a linear endomorphism of a finite-dimensional real or complex normed space.
If every forward orbit of $f$ is bounded, then
$$
  \ker(f-1) \oplus \operatorname{range}(f-1)
$$
is the whole space. Projection onto the first summand is the pointwise limit of the
Cesàro averages of the iterates of $f$.

The proof first uses the telescoping identity for Cesàro averages to show that the two
summands have zero intersection. Rank-nullity makes them complementary. The algebraic
projection associated with this decomposition then gives the limiting map.

## Main definitions

* `LinearMap.HasBoundedOrbits`: every forward orbit has bounded range.
* `LinearMap.meanErgodicProjection`: projection onto the fixed-point space along
  the range of $f-1$.

## Main statements

* `LinearMap.HasBoundedOrbits.tendsto_birkhoffAverage_meanErgodicProjection`:
  pointwise convergence of the Cesàro averages.
* `LinearMap.HasBoundedOrbits.range_meanErgodicProjection`: the range is the
  fixed-point space.
* `LinearMap.HasBoundedOrbits.comp_meanErgodicProjection` and
  `LinearMap.HasBoundedOrbits.meanErgodicProjection_comp`: the limiting projection
  absorbs $f$ on both sides.

This theorem supplies the finite-dimensional mean-ergodic argument used in the
construction of fixed-point projections for positive maps. The positivity and unitality
of those projections are separate matrix-algebra statements. In particular, the present
result does not by itself establish the fixed-point structure in Wolf's Theorem 6.14.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equation 6.14][Wolf2012QChannels]

## Tags

mean ergodic theorem, Cesàro average, fixed point, bounded orbit
-/

open Filter Function
open scoped Topology

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A linear endomorphism has bounded orbits if the range of
$n \mapsto f^n x$ is bounded for every vector $x$. -/
def HasBoundedOrbits (f : E →ₗ[𝕜] E) : Prop :=
  ∀ x : E, Bornology.IsBounded (Set.range fun n : ℕ ↦ f^[n] x)

/-- The Cesàro averages of a vector in the range of $f-1$ tend to zero when the
forward orbit of every vector is bounded. -/
theorem HasBoundedOrbits.tendsto_birkhoffAverage_of_mem_range_sub_one
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) {x : E}
    (hx : x ∈ LinearMap.range (f - 1)) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (nhds 0) := by
  obtain ⟨y, rfl⟩ := hx
  have hsub : ∀ n : ℕ, f^[n] (f y - y) = f^[n] (f y) - f^[n] y :=
    fun n ↦ iterate_map_sub (f : E →+ E) n (f y) y
  have hseq :
      (fun n ↦ birkhoffAverage 𝕜 f _root_.id n ((f - 1) y)) =
        fun n ↦ birkhoffAverage 𝕜 f _root_.id n (f y) -
          birkhoffAverage 𝕜 f _root_.id n y := by
    funext n
    change birkhoffAverage 𝕜 f _root_.id n (f y - y) = _
    simp only [birkhoffAverage, birkhoffSum, id_eq, hsub, Finset.sum_sub_distrib,
      smul_sub]
  rw [hseq]
  exact tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 (hf y)

/-- If every orbit of $f$ is bounded, then the fixed-point space and the range
of $f-1$ have zero intersection. -/
theorem HasBoundedOrbits.disjoint_ker_sub_one_range_sub_one
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    Disjoint (LinearMap.ker (f - 1)) (LinearMap.range (f - 1)) := by
  rw [Submodule.disjoint_def]
  intro x hxker hxrange
  have hxfix : IsFixedPt f x := by
    rw [LinearMap.mem_ker] at hxker
    change f x = x
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using sub_eq_zero.mp hxker
  exact tendsto_nhds_unique (hxfix.tendsto_birkhoffAverage 𝕜 _root_.id)
    (hf.tendsto_birkhoffAverage_of_mem_range_sub_one hxrange)

variable [FiniteDimensional 𝕜 E]

/-- In finite dimension, bounded orbits imply that the fixed-point space and the
range of $f-1$ are complementary. -/
theorem HasBoundedOrbits.isCompl_ker_sub_one_range_sub_one
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    IsCompl (LinearMap.ker (f - 1)) (LinearMap.range (f - 1)) := by
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · exact hf.disjoint_ker_sub_one_range_sub_one
  · rw [← (f - 1).finrank_range_add_finrank_ker]
    omega

/-- The mean-ergodic projection of a finite-dimensional linear endomorphism with
bounded orbits is the projection onto $\ker(f-1)$ along $\operatorname{range}(f-1)$. -/
noncomputable def meanErgodicProjection (f : E →ₗ[𝕜] E) (hf : f.HasBoundedOrbits) :
    E →ₗ[𝕜] E :=
  (LinearMap.ker (f - 1)).projection (LinearMap.range (f - 1))
    hf.isCompl_ker_sub_one_range_sub_one

/-- **Finite-dimensional mean-ergodic theorem for bounded orbits.** The Cesàro averages
of the iterates of $f$ converge pointwise to the projection onto $\ker(f-1)$ along
$\operatorname{range}(f-1)$.

This is the abstract convergence argument underlying Equation 6.14 of Wolf's
*Quantum Channels & Operations*. The matrix specialization must separately prove
that the limiting projection is positive and unital. -/
theorem HasBoundedOrbits.tendsto_birkhoffAverage_meanErgodicProjection
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop
      (nhds (meanErgodicProjection f hf x)) := by
  let P := meanErgodicProjection f hf
  change Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (nhds (P x))
  have hcompl := hf.isCompl_ker_sub_one_range_sub_one
  have hPker : P x ∈ LinearMap.ker (f - 1) := by
    exact Submodule.projection_apply_mem hcompl x
  have hPfix : IsFixedPt f (P x) := by
    rw [LinearMap.mem_ker] at hPker
    change f (P x) = P x
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using sub_eq_zero.mp hPker
  have hrem : x - P x ∈ LinearMap.range (f - 1) := by
    exact Submodule.sub_projection_mem hcompl x
  have hrem_lim := hf.tendsto_birkhoffAverage_of_mem_range_sub_one hrem
  have hsum := (hPfix.tendsto_birkhoffAverage 𝕜 _root_.id).add hrem_lim
  have hadd : ∀ n : ℕ, f^[n] (P x + (x - P x)) =
      f^[n] (P x) + f^[n] (x - P x) :=
    fun n ↦ iterate_map_add (f : E →+ E) n (P x) (x - P x)
  have hseq :
      (fun n ↦ birkhoffAverage 𝕜 f _root_.id n x) =
        fun n ↦ birkhoffAverage 𝕜 f _root_.id n (P x) +
          birkhoffAverage 𝕜 f _root_.id n (x - P x) := by
    funext n
    have hdecomp : x = P x + (x - P x) := by abel
    conv_lhs => rw [hdecomp]
    simp only [birkhoffAverage, birkhoffSum, id_eq, hadd, Finset.sum_add_distrib,
      smul_add]
  rw [hseq]
  simpa only [id_eq, add_zero] using hsum

/-- The range of the mean-ergodic projection is exactly the fixed-point space
$\ker(f-1)$. -/
@[simp]
theorem HasBoundedOrbits.range_meanErgodicProjection
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    LinearMap.range (meanErgodicProjection f hf) = LinearMap.ker (f - 1) := by
  exact Submodule.range_projection hf.isCompl_ker_sub_one_range_sub_one

/-- The mean-ergodic projection fixes exactly the fixed points of $f$. -/
@[simp]
theorem HasBoundedOrbits.meanErgodicProjection_apply_eq_self_iff
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) (x : E) :
    meanErgodicProjection f hf x = x ↔ f x = x := by
  change
    (LinearMap.ker (f - 1)).projection (LinearMap.range (f - 1))
        hf.isCompl_ker_sub_one_range_sub_one x = x ↔ _
  rw [Submodule.projection_eq_self_iff, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

/-- The mean-ergodic projection is idempotent. -/
theorem HasBoundedOrbits.isIdempotentElem_meanErgodicProjection
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    IsIdempotentElem (meanErgodicProjection f hf) := by
  exact Submodule.isIdempotentElem_projection hf.isCompl_ker_sub_one_range_sub_one

/-- Applying the mean-ergodic projection twice is the same as applying it once. -/
@[simp]
theorem HasBoundedOrbits.meanErgodicProjection_apply_meanErgodicProjection
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) (x : E) :
    meanErgodicProjection f hf (meanErgodicProjection f hf x) =
      meanErgodicProjection f hf x := by
  have h := congrArg (fun g : E →ₗ[𝕜] E ↦ g x)
    hf.isIdempotentElem_meanErgodicProjection.eq
  simpa only [Module.End.mul_apply] using h

/-- The endomorphism fixes the range of its mean-ergodic projection. -/
theorem HasBoundedOrbits.comp_meanErgodicProjection
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    f.comp (meanErgodicProjection f hf) = meanErgodicProjection f hf := by
  apply LinearMap.ext
  intro x
  have hmem : meanErgodicProjection f hf x ∈ LinearMap.ker (f - 1) := by
    exact Submodule.projection_apply_mem hf.isCompl_ker_sub_one_range_sub_one x
  rw [LinearMap.mem_ker] at hmem
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]
    using sub_eq_zero.mp hmem

/-- The mean-ergodic projection is unchanged after precomposition with the
endomorphism. -/
theorem HasBoundedOrbits.meanErgodicProjection_comp
    {f : E →ₗ[𝕜] E} (hf : f.HasBoundedOrbits) :
    (meanErgodicProjection f hf).comp f = meanErgodicProjection f hf := by
  apply LinearMap.ext
  intro x
  have hdiff : f x - x ∈ LinearMap.range (f - 1) := by
    refine ⟨x, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply]
  have hzero := Submodule.projection_apply_of_mem_right
    hf.isCompl_ker_sub_one_range_sub_one hdiff
  change meanErgodicProjection f hf (f x - x) = 0 at hzero
  simpa only [LinearMap.comp_apply, map_sub, sub_eq_zero] using hzero

end LinearMap
