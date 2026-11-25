/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatches.AdaptivePatchSupply
import TNLean.PEPS.ParentHamiltonian.Placement.DependentRegionCoordinates
import QICLean.ManyBody.Sites.Lattice.Rectangle
import TNLean.PEPS.Injectivity.Normal.NormalBlocking
import TNLean.PEPS.AreaLaw.Polygons.Squares.ClosedSquare

/-!
# Square patches from nested cylinder spaces

Orthogonalization of nested cylinders gives square-patch data with the same
radii, no larger total inside dimension, and no larger approximation error.
The matrix in the residual is the literal sum of its cylinder projectors.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 563–603, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.

## Square samples in integer coordinates

The maximum metric on the plane identifies the square samples of an encoded
patch with the coordinate inequalities used for finite integer domains.
The integer embedding of the open square starts at zero; translation by
\((1,1)\) gives the positions used in the polynomial-PEPS manuscript.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25,
and `03-patches.tex`, lines 14–22 and 53–54, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.

## Exact square patches at bounded radius

A square of radius at most four contains at most 81 integer sites. Taking
its full inside space in the nested-cylinder construction gives zero
approximation error with at most \(q^{81}\) cylinder terms.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 53–54, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

section

open scoped BigOperators Matrix

namespace TNLean.PEPS.EncodedFrame

variable {V : Type*} [Fintype V] [LinearOrder V] {q m : ℕ}

/-- A vector in the sum of cylinders over nested square samples gives square-patch
cylinder data at the same radii. Orthogonalization does not increase the sum of
inside dimensions, and orthogonal projection does not increase the approximation
error. The residual uses the literal cylinder sum, including for empty samples.

Source: the polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 563–603, especially the projected-image spaces and
`eq:patch-cylinder-projection`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The underlying projection argument applies
to arbitrary vectors, repeated radii, zero inside spaces, and an empty family. -/
theorem exists_squarePatch_of_mem_iSup_dependentRegionCylinder
    (pos : V → ℝ × ℝ) (z : ℝ × ℝ) {u : ℝ} (hu : 0 < u)
    (r : Fin m → ℝ) (hr : Monotone r)
    (hur : ∀ j, u ≤ r j) (hru : ∀ j, r j ≤ 2 * u)
    (S : (j : Fin m) →
      Submodule ℂ ((squareSample pos z (r j) → Fin q) → ℂ))
    (Ω v : EuclideanSpace ℂ ((v : V) → Fin q))
    (hv : (v : (((v : V) → Fin q) → ℂ)) ∈
      (⨆ j, dependentRegionCylinder (Out := fun _ : V ↦ Fin q)
        (squareSample pos z (r j)) (S j))) :
    ∃ (P : SquarePatch pos q) (hn : P.n = m),
      P.center = z ∧ P.scale = u ∧
      (∀ j, P.radius (Fin.cast hn.symm j) = r j) ∧
      (∑ j, P.dim j) ≤ ∑ j, Module.finrank ℂ (S j) ∧
      ‖Matrix.toEuclideanLin (1 - P.cylSum)
        (Ω)‖ ≤ ‖Ω - v‖ := by
  classical
  let R : Fin m → Finset V := fun j ↦ squareSample pos z (r j)
  have hR : Monotone R := fun i j hij ↦ squareSample_mono pos z (hr hij)
  let T := nestedCylinderInnovation (Out := fun _ : V ↦ Fin q) R hR S
  let d : Fin m → ℕ := fun j ↦ Module.finrank ℂ (coordinateSubspaceES (T j))
  let b (j : Fin m) (ℓ : Fin (d j)) : EuclideanSpace ℂ (R j → Fin q) :=
    (holeEncoderBasis (Out := fun _ : V ↦ Fin q) R hR S j ℓ).val
  have hb (j : Fin m) (ℓ : Fin (d j)) : ‖b j ℓ‖ = 1 :=
    (holeEncoderBasis (Out := fun _ : V ↦ Fin q) R hR S j).norm_eq_one ℓ
  let C (j : Fin m) := dependentRegionCylinder (Out := fun _ : V ↦ Fin q) (R j) (T j)
  have hzero (i j : Fin m) (hij : i ≠ j) :
      coordinateRangeProjector (C i) * coordinateRangeProjector (C j) = 0 := by
    let : DecidableEq ((v : V) → Fin q) := Classical.decEq _
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2]
    simp only [coordinateRangeProjector, LinearEquiv.apply_symm_apply, map_zero]
    exact congrArg ContinuousLinearMap.toLinearMap
        (nestedCylinderInnovation_pairwise_orthogonal (Out := fun _ : V ↦ Fin q)
          R hR S hij).starProjection_comp_starProjection
  have hbmem (j : Fin m) (ℓ : Fin (d j)) : (b j ℓ).ofLp ∈ T j := by
    simpa [coordinateSubspaceES, b] using
      (holeEncoderBasis (Out := fun _ : V ↦ Fin q) R hR S j ℓ).property
  have hfix (j : Fin m) (ℓ : Fin (d j)) :
      coordinateRangeProjector (T j) * rankOne (b j ℓ) = rankOne (b j ℓ) := by
    rw [rankOne, Matrix.mul_vecMulVec,
      (coordinateRangeProjector_mulVec_eq_self_iff (T j) _).mpr (hbmem j ℓ)]
  let B (j : Fin m) (ℓ : Fin (d j)) :=
    ManyBody.place (X := fun _ : V ↦ Fin q) (R j) (rankOne (b j ℓ))
  have hBfix (j : Fin m) (ℓ : Fin (d j)) :
      coordinateRangeProjector (C j) * B j ℓ = B j ℓ := by
    dsimp only [C, B]
    rw [coordinateRangeProjector_dependentRegionCylinder (Out := fun _ : V ↦ Fin q),
      ← ManyBody.place_mul (X := fun _ : V ↦ Fin q), hfix]
  have hBstar (j : Fin m) (ℓ : Fin (d j)) : star (B j ℓ) = B j ℓ := by
    simp only [B, Matrix.star_eq_conjTranspose,
      ← ManyBody.place_conjTranspose (X := fun _ : V ↦ Fin q),
      rankOne_conjTranspose]
  have hBfixr (j : Fin m) (ℓ : Fin (d j)) :
      B j ℓ * coordinateRangeProjector (C j) = B j ℓ := by
    simpa only [star_mul, hBstar,
      (coordinateRangeProjector_isStarProjection (C j)).isSelfAdjoint.star_eq] using
      congrArg star (hBfix j ℓ)
  have hcross (i j : Fin m) (hi : Fin (d i)) (hj : Fin (d j)) (hij : i ≠ j) :
      B i hi * B j hj = 0 := by
    calc
      B i hi * B j hj = (B i hi * coordinateRangeProjector (C i)) *
          (coordinateRangeProjector (C j) * B j hj) := by rw [hBfixr, hBfix]
      _ = B i hi * (coordinateRangeProjector (C i) * coordinateRangeProjector (C j)) *
          B j hj := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero i j hij, Matrix.mul_zero, Matrix.zero_mul]
  have hinner (j : Fin m) (i ℓ : Fin (d j)) (hiℓ : i ≠ ℓ) :
      star (b j i).ofLp ⬝ᵥ (b j ℓ).ofLp = 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact (holeEncoderBasis (Out := fun _ : V ↦ Fin q) R hR S j).inner_eq_zero hiℓ
  have hsame (j : Fin m) (i ℓ : Fin (d j)) (hiℓ : i ≠ ℓ) :
      B j i * B j ℓ = 0 := by
    dsimp only [B]
    rw [← ManyBody.place_mul (X := fun _ : V ↦ Fin q),
      rankOne, rankOne, Matrix.vecMulVec_mul_vecMulVec, hinner j i ℓ hiℓ,
      zero_smul, Matrix.vecMulVec_zero]
    simp [ManyBody.place]
  have hBorth (s s' : (j : Fin m) × Fin (d j)) (hss' : s ≠ s') :
      B s.1 s.2 * B s'.1 s'.2 = 0 := by
    rcases s with ⟨i, hi⟩
    rcases s' with ⟨j, hj⟩
    by_cases hij : i = j
    · subst j
      exact hsame i hi hj (fun h ↦ hss' (congrArg (Sigma.mk i) h))
    · exact hcross i j hi hj hij
  have hFB (j : Fin m) (ℓ : Fin (d j)) :
      B j ℓ = ManyBody.place (X := fun _ ↦ Fin _) (R j) (rankOne (b j ℓ)) :=
    rfl
  have horth (s s' : (j : Fin m) × Fin (d j)) (hss' : s ≠ s') :
      ManyBody.place (X := fun _ ↦ Fin _) (R s.1) (rankOne (b s.1 s.2)) *
        ManyBody.place (X := fun _ ↦ Fin _) (R s'.1) (rankOne (b s'.1 s'.2)) = 0 := by
    exact hBorth s s' hss'
  let P : SquarePatch pos q :=
    { center := z
      scale := u
      scale_pos := hu
      n := m
      radius := r
      radius_mono := hr
      scale_le_radius := hur
      radius_le := hru
      dim := d
      vec := b
      norm_vec := hb
      orthogonal := horth }
  refine ⟨P, rfl, rfl, rfl, fun _ ↦ rfl, ?_, ?_⟩
  · simpa only [P, d, finrank_coordinateSubspaceES] using
      sum_finrank_nestedCylinderInnovation_le (Out := fun _ : V ↦ Fin q) R hR S
  · have hsumj (j : Fin m) : (∑ ℓ, B j ℓ) =
        ManyBody.place (X := fun _ : V ↦ Fin q) (R j)
          (coordinateRangeProjector (T j)) := by
      rw [coordinateRangeProjector_eq_sum_basis _
        (holeEncoderBasis (Out := fun _ : V ↦ Fin q) R hR S j)]
      ext α β
      simp [B, b, rankOne, ManyBody.place, Matrix.reindex_apply,
        Matrix.sum_apply, Finset.sum_mul]
      rfl
    let W := ⨆ j, dependentRegionCylinder (Out := fun _ : V ↦ Fin q) (R j) (S j)
    have hsum : (∑ s : (j : Fin m) × Fin (d j), B s.1 s.2) =
        coordinateRangeProjector W := by
      rw [Fintype.sum_sigma]
      simp_rw [hsumj]
      exact (nestedCylinderInnovation_projector_sum (Out := fun _ : V ↦ Fin q) R hR S).symm
    have hPsum : P.cylSum = coordinateRangeProjector W := by
      rw [← hsum]
      simp only [hFB, SquarePatch.cylSum, SquarePatch.sample, P, R]
    let U := coordinateSubspaceES W
    have hvU : v ∈ U := by
      exact ⟨v.ofLp, hv, rfl⟩
    have hres : ‖Ω - U.starProjection Ω‖ ≤ ‖Ω - v‖ := by
      calc
        ‖Ω - U.starProjection Ω‖ = ‖Uᗮ.starProjection (Ω - v)‖ := by
          rw [map_sub, U.starProjection_orthogonal_apply_eq_zero hvU, sub_zero,
            U.starProjection_orthogonal_val]
        _ ≤ ‖Ω - v‖ := Uᗮ.norm_starProjection_apply_le _
    have hproj : WithLp.toLp 2 (coordinateRangeProjector W *ᵥ Ω.ofLp) =
        U.starProjection Ω := by
      let : DecidableEq ((v : V) → Fin q) := Classical.decEq _
      change Matrix.toEuclideanLin (coordinateRangeProjector W) Ω = _
      rw [coordinateRangeProjector, LinearEquiv.apply_symm_apply]
      rfl
    have hact : Matrix.toEuclideanLin (coordinateRangeProjector W) Ω = U.starProjection Ω := by
      rw [← hproj]
      rfl
    rw [hPsum, map_sub, LinearMap.sub_apply, Matrix.toEuclideanLin_one_apply, hact]
    exact hres

end TNLean.PEPS.EncodedFrame

end

section

open ManyBody (SquareLatticeVertex)

namespace TNLean.PEPS.Approximation

/-- The metric square sample equals the closed coordinate sample on any finite
integer domain. No restriction on the center or radius is required.

Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 14–22. -/
theorem squareSample_integerCoordinates (Λ : Finset (ℤ × ℤ))
    (center : ℝ × ℝ) (r : ℝ) :
    EncodedFrame.squareSample
      (fun x : ↥Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) center r =
      AreaLaw.Geometry.closedSquareSample Λ center r := by
  ext x
  simp [EncodedFrame.squareSample, AreaLaw.Geometry.mem_closedSquareSample,
    Prod.dist_eq, Real.dist_eq]

/-- Translating the integer embedding by one in each coordinate gives the
physical lattice positions of the polynomial-PEPS manuscript.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25. -/
theorem integerCoordinates_add_one_eq_latticePos (L : ℕ) :
    (fun v : SquareLatticeVertex L L ↦
      (((ManyBody.rectangleSiteEquiv L L v).1.1 : ℝ),
        ((ManyBody.rectangleSiteEquiv L L v).1.2 : ℝ)) + (1, 1)) =
      latticePos L := by
  funext v
  simp [latticePos, ManyBody.rectangleEmbedding]

end TNLean.PEPS.Approximation

end

section

open scoped BigOperators Matrix

namespace TNLean.PEPS.Approximation

/-- Every square of radius at most four admits an exact square-patch expansion
with at most `q ^ 81` terms. The input vector is arbitrary, and the domain and
sample may be empty. The residual uses the literal sum of cylinder projectors.

Source: polynomial-PEPS manuscript, Proposition 4.1, `03-patches.tex`,
lines 53–54, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The same counting argument includes the endpoint `u = 4`. -/
theorem exists_squarePatch_integerCoordinates_of_radius_le_four
    (Λ : Finset (ℤ × ℤ)) {q : ℕ} (hq : 1 ≤ q)
    (z : ℝ × ℝ) {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 4)
    (Ω : EuclideanSpace ℂ
      ((v : ↥Λ) → Fin q)) :
    letI : LinearOrder ↥Λ :=
      (Fintype.equivFin ↥Λ).linearOrder
    ∃ P : EncodedFrame.SquarePatch
        (fun x : ↥Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) q,
      P.center = z ∧ P.scale = u ∧
      (∑ j, P.dim j) ≤ q ^ 81 ∧
      ‖Matrix.toEuclideanLin (1 - P.cylSum) Ω‖ = 0 := by
  classical
  let : LinearOrder ↥Λ :=
    (Fintype.equivFin ↥Λ).linearOrder
  obtain ⟨P, _, hz, hs, _, hd, he⟩ :=
    EncodedFrame.exists_squarePatch_of_mem_iSup_dependentRegionCylinder
      (fun x : ↥Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) z hu
      (fun _ : Fin 1 ↦ u) monotone_const (fun _ ↦ le_rfl) (fun _ ↦ by linarith)
      (fun _ ↦ ⊤) Ω Ω (Submodule.mem_iSup_of_mem (0 : Fin 1)
        ((mem_dependentRegionCylinder _ _ _).mpr (fun _ ↦ Submodule.mem_top)))
  refine ⟨P, hz, hs, ?_, ?_⟩
  · refine hd.trans ?_
    simp only [Fin.sum_univ_one, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    simpa only [squareSample_integerCoordinates] using
      pow_le_pow_right' hq
        (AreaLaw.Geometry.card_closedSquareSample_le_eightyOne Λ z hu.le hu4)
  · exact le_antisymm (by simpa only [sub_self, norm_zero] using he) (norm_nonneg _)

end TNLean.PEPS.Approximation

end
