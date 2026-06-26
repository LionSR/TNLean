/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtNumber
import TNLean.Algebra.MatrixRankClosed
import TNLean.Analysis.ConvexHullCompact

/-!
# Compactness of the Schmidt-number state set

Wolf's Chapter 3, Section 3.2 (the paragraph *Detecting entanglement*) builds an
entanglement witness for any state outside the set `S_n` of trace-one bipartite
states of Schmidt number at most `n` by separating it from `S_n` with a
hyperplane.  The separation requires `S_n` to be a compact convex set; convexity
is `Matrix.convex_setOf_hasSchmidtNumberLE`, and this file supplies the second
geometric input, the **compactness of `S_n`** (Wolf §3.2, Proposition 3.3).

## The compactness argument

A trace-one state of Schmidt number at most `n` is a convex combination of pure
states `|ψ⟩⟨ψ|` whose vector ψ has unit norm and Schmidt rank at most `n`.  The
file realizes `S_n` as the convex hull of the compact set `P_n` of those pure
states and invokes the finite-dimensional fact that the convex hull of a compact
set is compact.

The pure-state set `P_n` is compact because it is the continuous image of the
set `Q` of unit vectors of Schmidt rank at most `n`.  In the L2 (Euclidean) norm
the unit vectors form the unit sphere, which is compact in finite dimension, and
the Schmidt-rank bound is a closed condition because the Schmidt coefficient
matrix depends continuously on the vector and bounded-rank matrices form a closed
set (`Matrix.isClosed_setOf_rank_le`).  Mapping a unit vector ψ to its projector
`|ψ⟩⟨ψ|` is continuous, so `P_n` is compact, and its convex hull `S_n` is compact.

The Euclidean norm enters through the trace identity
`(|ψ⟩⟨ψ|).trace = ψ ⬝ᵥ star ψ = ‖ψ‖²` (the squared L2 norm): the trace-one
constraint on the mixed state is exactly the unit-norm constraint on its pure
components, and the weights of the convex decomposition are the squared norms of
the unnormalized vectors, which sum to the trace.

## Main results

* `Matrix.isCompact_setOf_hasSchmidtRankLE`: the set of unit vectors of Schmidt
  rank at most `n` is compact (the L2 unit sphere intersected with the closed
  bounded-rank set).
* `Matrix.isCompact_pureStates_hasSchmidtNumberLE`: the set `P_n` of pure-state
  projectors of unit-norm Schmidt-rank-≤`n` vectors is compact.
* `Matrix.isCompact_setOf_hasSchmidtNumberLE_trace_one`: **the Schmidt-number set
  `S_n` is compact** — the second hypothesis of the separating-hyperplane
  construction of Wolf Proposition 3.3.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, the *Detecting entanglement* paragraph, Proposition 3.3][Wolf2012QChannels]
-/

open scoped BigOperators Matrix
open Matrix

-- The Frobenius norm equips the matrix space with a finite-dimensional real normed
-- structure whose topology agrees with the entrywise-convergence topology used for the
-- compactness inputs; it supplies the `NormedSpace ℝ`/`FiniteDimensional ℝ` instances
-- that the convex-hull compactness lemma requires.
open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {d d' : ℕ}

/-! ## Continuity and closedness inputs -/

/-- The Schmidt coefficient matrix depends continuously on the bipartite vector:
it is the entrywise reindexing `ψ ↦ (fun i j ↦ ψ (i, j))`. -/
theorem continuous_schmidtCoeffMatrix :
    Continuous fun ψ : Fin d × Fin d' → ℂ => schmidtCoeffMatrix ψ := by
  refine continuous_matrix fun i j => ?_
  exact continuous_apply (i, j)

/-- **The bounded-Schmidt-rank condition is closed.**  The set of bipartite
vectors of Schmidt rank at most `n` is the preimage of the closed set of
bounded-rank matrices under the continuous Schmidt-coefficient map. -/
theorem isClosed_setOf_hasSchmidtRankLE (n : ℕ) :
    IsClosed {ψ : Fin d × Fin d' → ℂ | HasSchmidtRankLE n ψ} := by
  have hpre :
      {ψ : Fin d × Fin d' → ℂ | HasSchmidtRankLE n ψ}
        = (fun ψ => schmidtCoeffMatrix ψ) ⁻¹'
            {A : Matrix (Fin d) (Fin d') ℂ | A.rank ≤ n} := by
    ext ψ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, HasSchmidtRankLE, schmidtRank]
  rw [hpre]
  exact (isClosed_setOf_rank_le n).preimage continuous_schmidtCoeffMatrix

/-! ## The compact set of unit Schmidt-rank-bounded vectors

The Euclidean structure on `Fin d × Fin d' → ℂ` makes the unit vectors a compact
sphere.  We carry it through `EuclideanSpace ℂ (Fin d × Fin d')`, whose norm is
the L2 norm, and transport the closed Schmidt-rank condition across the
homeomorphism `EuclideanSpace.equiv`. -/

/-- The pure-state projector map sending a Euclidean unit vector φ to
`|φ⟩⟨φ| = vecMulVec (ofLp φ) (star (ofLp φ))`.  Carrying it on
`EuclideanSpace ℂ (Fin d × Fin d')` makes the norm the L2 norm, so the trace of
the projector is the squared Euclidean norm. -/
noncomputable def euclideanProj (φ : EuclideanSpace ℂ (Fin d × Fin d')) :
    Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ :=
  vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))

/-- The pure-state projector map is continuous: it is a bilinear expression in the
continuous coordinate maps of `φ`. -/
theorem continuous_euclideanProj :
    Continuous (euclideanProj (d := d) (d' := d')) := by
  unfold euclideanProj
  refine continuous_matrix fun i j => ?_
  have hi : Continuous fun φ : EuclideanSpace ℂ (Fin d × Fin d') => WithLp.ofLp φ i :=
    PiLp.continuous_apply 2 _ i
  have hj : Continuous fun φ : EuclideanSpace ℂ (Fin d × Fin d') => WithLp.ofLp φ j :=
    PiLp.continuous_apply 2 _ j
  have : Continuous fun φ : EuclideanSpace ℂ (Fin d × Fin d') =>
      WithLp.ofLp φ i * (starRingEnd ℂ) (WithLp.ofLp φ j) :=
    hi.mul hj.star
  simpa [vecMulVec_apply, Pi.star_apply] using this

/-- The trace of the pure-state projector of a Euclidean vector is its squared
Euclidean (L2) norm.  This is the trace–norm identity
`(|φ⟩⟨φ|).trace = φ ⬝ᵥ star φ = ‖φ‖²` underlying the trace-one ↔ unit-norm
correspondence. -/
theorem trace_euclideanProj (φ : EuclideanSpace ℂ (Fin d × Fin d')) :
    (euclideanProj φ).trace = ((‖φ‖ : ℂ)) ^ 2 := by
  rw [euclideanProj, trace_vecMulVec]
  have hinner : (inner ℂ φ φ : ℂ) = WithLp.ofLp φ ⬝ᵥ star (WithLp.ofLp φ) :=
    EuclideanSpace.inner_eq_star_dotProduct φ φ
  rw [← hinner]
  exact inner_self_eq_norm_sq_to_K φ

/-- **The set of unit vectors of Schmidt rank at most `n` is compact.**  In the
Euclidean (L2) norm the unit vectors are the unit sphere, compact in finite
dimension, and the Schmidt-rank bound is a closed condition transported across the
homeomorphism `EuclideanSpace.equiv`; the intersection of a compact set with a
closed set is compact. -/
theorem isCompact_setOf_hasSchmidtRankLE (n : ℕ) :
    IsCompact {φ : EuclideanSpace ℂ (Fin d × Fin d') |
      ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)} := by
  -- The sphere of radius `1` is compact in the finite-dimensional Euclidean space.
  have hsphere : IsCompact (Metric.sphere (0 : EuclideanSpace ℂ (Fin d × Fin d')) 1) :=
    isCompact_sphere 0 1
  -- The Schmidt-rank condition is closed: pull back the closed set of vectors of
  -- bounded Schmidt rank along the continuous coordinate equivalence.
  have hclosed :
      IsClosed {φ : EuclideanSpace ℂ (Fin d × Fin d') |
        HasSchmidtRankLE n (WithLp.ofLp φ)} := by
    have hpre :
        {φ : EuclideanSpace ℂ (Fin d × Fin d') | HasSchmidtRankLE n (WithLp.ofLp φ)}
          = (fun φ : EuclideanSpace ℂ (Fin d × Fin d') => WithLp.ofLp φ) ⁻¹'
              {ψ : Fin d × Fin d' → ℂ | HasSchmidtRankLE n ψ} := rfl
    rw [hpre]
    exact (isClosed_setOf_hasSchmidtRankLE n).preimage
      (PiLp.continuous_ofLp 2 (fun _ : Fin d × Fin d' => ℂ))
  -- The target set is the sphere intersected with that closed set.
  have hset :
      {φ : EuclideanSpace ℂ (Fin d × Fin d') |
          ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)}
        = Metric.sphere (0 : EuclideanSpace ℂ (Fin d × Fin d')) 1 ∩
            {φ : EuclideanSpace ℂ (Fin d × Fin d') | HasSchmidtRankLE n (WithLp.ofLp φ)} := by
    ext φ
    simp [and_comm]
  rw [hset]
  exact hsphere.inter_right hclosed

/-! ## The compact pure-state set `P_n` -/

/-- The pure-state set `P_n`: the projectors `|ψ⟩⟨ψ|` of unit vectors ψ of Schmidt
rank at most `n`, written as the image of the compact unit-vector set under the
continuous projector map. -/
theorem isCompact_pureStates_hasSchmidtNumberLE (n : ℕ) :
    IsCompact (euclideanProj (d := d) (d' := d') ''
      {φ : EuclideanSpace ℂ (Fin d × Fin d') |
        ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)}) :=
  (isCompact_setOf_hasSchmidtRankLE n).image continuous_euclideanProj

/-- Every pure state in `P_n` has Schmidt number at most `n` and trace one.  The
projector `|ψ⟩⟨ψ|` of a Schmidt-rank-≤`n` vector ψ has Schmidt number at most `n`,
and the trace of `|ψ⟩⟨ψ|` is the squared norm of ψ, equal to one for a unit
vector. -/
theorem pureStates_subset_setOf_hasSchmidtNumberLE_trace_one (n : ℕ) :
    euclideanProj (d := d) (d' := d') ''
        {φ : EuclideanSpace ℂ (Fin d × Fin d') |
          ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)}
      ⊆ {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          HasSchmidtNumberLE n ρ ∧ ρ.trace = 1} := by
  rintro _ ⟨φ, ⟨hnorm, hrank⟩, rfl⟩
  refine ⟨hasSchmidtNumberLE_vecMulVec hrank, ?_⟩
  rw [trace_euclideanProj, hnorm]
  norm_num

/-! ## `S_n` is the convex hull of `P_n` -/

/-- The trace-one Schmidt-number set is convex: it is the intersection of the
convex Schmidt-number set with the affine trace-one hyperplane. -/
theorem convex_setOf_hasSchmidtNumberLE_trace_one (n : ℕ) :
    Convex ℝ {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
      HasSchmidtNumberLE n ρ ∧ ρ.trace = 1} := by
  -- The trace-one condition is an affine hyperplane: trace is ℝ-linear, so a convex
  -- combination of trace-one matrices has trace `a + b = 1`.
  have hconvex_hyper :
      Convex ℝ {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ | ρ.trace = 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx, hy,
      Complex.real_smul, Complex.real_smul, mul_one, mul_one, ← Complex.ofReal_add, hab,
      Complex.ofReal_one]
  have hset :
      {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          HasSchmidtNumberLE n ρ ∧ ρ.trace = 1}
        = {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ | HasSchmidtNumberLE n ρ}
            ∩ {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ | ρ.trace = 1} := by
    ext ρ; simp [Set.mem_inter_iff]
  rw [hset]
  exact convex_setOf_hasSchmidtNumberLE.inter hconvex_hyper

/-- The convex hull of `P_n` is contained in the trace-one Schmidt-number set: the
set is convex and contains each pure state of `P_n`. -/
theorem convexHull_pureStates_subset (n : ℕ) :
    convexHull ℝ (euclideanProj (d := d) (d' := d') ''
        {φ : EuclideanSpace ℂ (Fin d × Fin d') |
          ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)})
      ⊆ {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          HasSchmidtNumberLE n ρ ∧ ρ.trace = 1} :=
  convexHull_min (pureStates_subset_setOf_hasSchmidtNumberLE_trace_one n)
    (convex_setOf_hasSchmidtNumberLE_trace_one n)

/-- The squared Euclidean norm of a bipartite vector equals the trace of its
projector, read off the dot product `ψ ⬝ᵥ star ψ`. -/
theorem ofReal_normSq_eq_dotProduct_star (ψ : Fin d × Fin d' → ℂ) :
    (((‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin d × Fin d'))‖ : ℝ) ^ 2 : ℝ) : ℂ)
      = ψ ⬝ᵥ star ψ := by
  have h := trace_euclideanProj (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin d × Fin d'))
  rw [euclideanProj, trace_vecMulVec] at h
  rw [Complex.ofReal_pow, ← h]

/-- **Normalizing a nonzero pure component.**  A nonzero bipartite vector ψ of
Schmidt rank at most `n` has a unit Euclidean vector φ of Schmidt rank at most `n`
whose pure-state projector, scaled by the squared norm `‖ψ‖²`, recovers `|ψ⟩⟨ψ|`.
This is the per-component normalization underlying the convex decomposition of a
trace-one state of Schmidt number at most `n`. -/
theorem exists_unit_smul_euclideanProj_eq {n : ℕ} {ψ : Fin d × Fin d' → ℂ}
    (hψne : ψ ≠ 0) (hψrank : HasSchmidtRankLE n ψ) :
    ∃ φ : EuclideanSpace ℂ (Fin d × Fin d'),
      ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ) ∧
        ((‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin d × Fin d'))‖ : ℝ) ^ 2) •
            euclideanProj φ = vecMulVec ψ (star ψ) := by
  classical
  set ψE : EuclideanSpace ℂ (Fin d × Fin d') := WithLp.toLp 2 ψ with hψE
  have hψEne : ψE ≠ 0 := by rw [hψE]; simpa [WithLp.toLp_eq_zero] using hψne
  set s : ℝ := ‖ψE‖ with hs
  have hs_pos : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hψEne
  refine ⟨(Real.sqrt (s ^ 2))⁻¹ • ψE, ?_, ?_, ?_⟩
  · -- The rescaled vector has unit norm.
    rw [Real.sqrt_sq hs_pos.le, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs_pos,
      inv_mul_cancel₀ (ne_of_gt hs_pos)]
  · -- Scaling by a nonzero scalar preserves the Schmidt rank.
    have hofLp : WithLp.ofLp ((Real.sqrt (s ^ 2))⁻¹ • ψE)
        = (Real.sqrt (s ^ 2) : ℂ)⁻¹ • ψ := by
      rw [hψE]; ext p; simp [PiLp.smul_apply, Complex.real_smul]
    have hc : (Real.sqrt (s ^ 2) : ℂ)⁻¹ ≠ 0 := by
      rw [Real.sqrt_sq hs_pos.le]
      simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
      exact ne_of_gt hs_pos
    rw [HasSchmidtRankLE, schmidtRank, hofLp]
    have hcoeff : schmidtCoeffMatrix ((Real.sqrt (s ^ 2) : ℂ)⁻¹ • ψ)
        = (Real.sqrt (s ^ 2) : ℂ)⁻¹ • schmidtCoeffMatrix ψ := by
      ext p q; simp [schmidtCoeffMatrix]
    rw [hcoeff, rank_smul_of_ne_zero hc]
    exact hψrank
  · -- The squared norm scales the normalized projector back to `|ψ⟩⟨ψ|`.
    have hofLp : WithLp.ofLp ((Real.sqrt (s ^ 2))⁻¹ • ψE)
        = (Real.sqrt (s ^ 2) : ℂ)⁻¹ • ψ := by
      rw [hψE]; ext p; simp [PiLp.smul_apply, Complex.real_smul]
    have hproj : euclideanProj ((Real.sqrt (s ^ 2))⁻¹ • ψE)
        = ((s ^ 2 : ℝ) : ℂ)⁻¹ • vecMulVec ψ (star ψ) := by
      rw [euclideanProj, hofLp]
      have hstar : star ((Real.sqrt (s ^ 2) : ℂ)⁻¹ • ψ)
          = (Real.sqrt (s ^ 2) : ℂ)⁻¹ • star ψ := by
        rw [star_smul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [hstar, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
        ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (sq_nonneg s), Complex.ofReal_inv]
    have hs2_ne : ((s ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact pow_ne_zero 2 (ne_of_gt hs_pos)
    rw [hproj, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact smul_inv_smul₀ hs2_ne (vecMulVec ψ (star ψ))

/-- **The trace-one Schmidt-number set is contained in the convex hull of `P_n`.**
A trace-one state of Schmidt number at most `n` is a sum of projectors of
Schmidt-rank-≤`n` vectors; normalizing each nonzero vector to unit norm exhibits
the state as a convex combination of pure states of `P_n`, with weights the
squared norms summing to the trace, namely one.  Zero summands carry weight zero
and reuse a fixed pure state of `P_n`, which exists because a trace-one state has at
least one nonzero component. -/
theorem subset_convexHull_pureStates (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : HasSchmidtNumberLE n ρ) (htr : ρ.trace = 1) :
    ρ ∈ convexHull ℝ (euclideanProj (d := d) (d' := d') ''
      {φ : EuclideanSpace ℂ (Fin d × Fin d') |
        ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)}) := by
  classical
  obtain ⟨ι, hιfin, ψ, hψ, rfl⟩ := hρ
  -- The squared L2 norm of each component, the would-be convex weight.
  set wt : ι → ℝ := fun i =>
    (‖(WithLp.toLp 2 (ψ i) : EuclideanSpace ℂ (Fin d × Fin d'))‖ : ℝ) ^ 2 with hwt
  have hwt_nonneg : ∀ i, 0 ≤ wt i := fun i => by rw [hwt]; positivity
  -- The trace identity reading each weight as the trace of its component projector.
  have hwt_dot : ∀ i, ((wt i : ℝ) : ℂ) = (ψ i) ⬝ᵥ star (ψ i) :=
    fun i => ofReal_normSq_eq_dotProduct_star (ψ i)
  -- A trace-one state has a nonzero component, supplying a default pure state.
  have hnonzero : ∃ i, ψ i ≠ 0 := by
    by_contra h
    push Not at h
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    rw [← htr, Matrix.trace_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; simp
  obtain ⟨i₀, hi₀⟩ := hnonzero
  obtain ⟨φ₀, hφ₀norm, hφ₀rank, _⟩ :=
    exists_unit_smul_euclideanProj_eq hi₀ (hψ i₀)
  -- The chosen pure state for each index: the normalized component, or `φ₀` if zero.
  have hchoice : ∀ i, ∃ φ : EuclideanSpace ℂ (Fin d × Fin d'),
      (‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)) ∧
        wt i • euclideanProj φ = vecMulVec (ψ i) (star (ψ i)) := by
    intro i
    by_cases hi : ψ i = 0
    · refine ⟨φ₀, ⟨hφ₀norm, hφ₀rank⟩, ?_⟩
      have hwti : wt i = 0 := by simp [hwt, hi]
      rw [hwti, zero_smul, hi, star_zero, Matrix.vecMulVec_zero]
    · obtain ⟨φ, hn, hr, he⟩ := exists_unit_smul_euclideanProj_eq hi (hψ i)
      exact ⟨φ, ⟨hn, hr⟩, by rw [hwt]; exact he⟩
  choose z hzmem hzeq using hchoice
  -- The points lie in `P_n`.
  have hPmem : ∀ i, euclideanProj (z i) ∈ euclideanProj (d := d) (d' := d') ''
      {φ : EuclideanSpace ℂ (Fin d × Fin d') |
        ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)} :=
    fun i => ⟨z i, hzmem i, rfl⟩
  -- The weights sum to the trace, which is one.
  have hsum_weights : ∑ i, wt i = 1 := by
    have hcast : ((∑ i, wt i : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.ofReal_sum, ← htr, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hwt_dot i, trace_vecMulVec]
    exact_mod_cast hcast
  -- The weighted sum of pure states recovers `ρ`.
  have hbary : ∑ i, wt i • euclideanProj (z i) = ∑ i, vecMulVec (ψ i) (star (ψ i)) :=
    Finset.sum_congr rfl fun i _ => hzeq i
  -- Assemble: a convex combination of pure states of `P_n`.  The weight body is no
  -- longer needed; keep it opaque so the convex-hull unification does not unfold the
  -- Euclidean-norm machinery.
  clear_value wt
  exact mem_convexHull_of_exists_fintype
    (R := ℝ) (E := Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) (ι := ι)
    wt (fun i => euclideanProj (z i)) hwt_nonneg hsum_weights hPmem hbary

/-- **Compactness of the Schmidt-number state set `S_n`** (Wolf §3.2,
Proposition 3.3).  For each `n`, the set `S_n` of trace-one bipartite states of
Schmidt number at most `n` is compact.

The set is the convex hull of the compact pure-state set `P_n` of unit vectors of
Schmidt rank at most `n`, and the convex hull of a compact set is compact in a
finite-dimensional real normed space.  With the convexity of `S_n`
(`Matrix.convex_setOf_hasSchmidtNumberLE`), this is the second geometric input to
Wolf's separating-hyperplane construction of an entanglement witness for any state
outside `S_n`. -/
theorem isCompact_setOf_hasSchmidtNumberLE_trace_one (n : ℕ) :
    IsCompact {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
      HasSchmidtNumberLE n ρ ∧ ρ.trace = 1} := by
  have heq :
      {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          HasSchmidtNumberLE n ρ ∧ ρ.trace = 1}
        = convexHull ℝ (euclideanProj (d := d) (d' := d') ''
            {φ : EuclideanSpace ℂ (Fin d × Fin d') |
              ‖φ‖ = 1 ∧ HasSchmidtRankLE n (WithLp.ofLp φ)}) := by
    apply Set.Subset.antisymm
    · rintro ρ ⟨hρ, htr⟩
      exact subset_convexHull_pureStates n hρ htr
    · exact convexHull_pureStates_subset n
  rw [heq]
  exact TNLean.IsCompact.convexHull (isCompact_pureStates_hasSchmidtNumberLE n)

end Matrix
