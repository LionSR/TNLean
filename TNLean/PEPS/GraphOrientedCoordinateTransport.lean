/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenBondCoordinateTransport
import TNLean.PEPS.GraphOrientedAveragingBondState

/-!
# Fourier transport for arbitrary graph edge orientations

Reversing an edge exchanges its two physical registers. Thus its coordinate
operation is conjugated by the pair swap, or equivalently uses the entrywise
conjugate virtual coordinate matrix. The same oriented coordinate operation
acts on each retained virtual boundary label.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2938–3019.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {G X Y : Type*} [Group G] [Fintype G]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Reversing the physical bond registers conjugates the coordinate matrix
entrywise. Source: SCP10, Section 7. -/
theorem bondCoordinateMatrix_map_star (Q : Matrix Y X ℂ) :
    bondCoordinateMatrix (Q.map star) =
      (bondCoordinateMatrix Q).submatrix Prod.swap Prod.swap := by
  ext i j
  simp [bondCoordinateMatrix, mul_comm]

omit [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- The reversed physical pair transports the transposed bond entries. -/
theorem bondCoordinateMatrix_map_star_mulVec (Q : Matrix Y X ℂ) (M : Matrix X X ℂ) :
    bondCoordinateMatrix (Q.map star) *ᵥ (fun c => M c.2 c.1) =
      fun r => (Q * M * Q.conjTranspose) r.2 r.1 := by
  ext r
  rcases r with ⟨a, b⟩
  simp only [bondCoordinateMatrix, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.map_apply, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The effective virtual coordinate matrix in the original ordered edge
registers. True reverses the edge. -/
def graphOrientedEdgeCoordinateMatrix (Q : Matrix Y X ℂ) (o : Edge Γ → Bool)
    (e : Edge Γ) : Matrix Y X ℂ :=
  if o e then Q.map star else Q

/-- The actual physical coordinate matrix for one arbitrarily oriented edge. -/
def graphOrientedBondCoordinateMatrix (Q : Matrix Y X ℂ) (o : Edge Γ → Bool)
    (e : Edge Γ) : Matrix (Y × Y) (X × X) ℂ :=
  bondCoordinateMatrix (graphOrientedEdgeCoordinateMatrix Q o e)

/-- The coordinate matrix on the retained endpoint of a crossing edge. -/
def graphOrientedBoundaryCoordinateMatrix (Q : Matrix Y X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) (e : RB (Γ := Γ) R) : Matrix Y X ℂ :=
  if e.1.1.1 ∈ R then (graphOrientedEdgeCoordinateMatrix Q o e.1).map star
  else graphOrientedEdgeCoordinateMatrix Q o e.1

/-- The Fourier matrix on all actual regional physical coordinates. -/
def graphOrientedRegionCoordinateMatrix (Q : Matrix Y X ℂ)
    (o : Edge Γ → Bool) (R : Finset V) :=
  mixedPhysicalProductMatrix (graphOrientedBoundaryCoordinateMatrix Q o R)
    (fun e : RI (Γ := Γ) R => graphOrientedBondCoordinateMatrix Q o e.1)

omit [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- Entrywise conjugation preserves an inverse pair of coordinate matrices. -/
theorem map_star_mul_eq_one {Z : Type*} [DecidableEq Z]
    (A : Matrix Z X ℂ) (B : Matrix X Z ℂ) (h : A * B = 1) :
    A.map star * B.map star = 1 := by
  ext i j
  have hh := congrArg star (congr_fun (congr_fun h i) j)
  simpa only [Matrix.mul_apply, Matrix.map_apply, star_sum, star_mul,
    Matrix.one_apply, apply_ite, star_one, star_zero, mul_comm] using hh

omit [DecidableEq X] [Fintype Y] in
/-- Regional oriented coordinates cancel against their inverse on every vector. -/
theorem graphOrientedRegionCoordinateMatrix_mul_conjTranspose
    (Q : Matrix Y X ℂ) (hQ : Q * Q.conjTranspose = 1)
    (o : Edge Γ → Bool) (R : Finset V) :
    graphOrientedRegionCoordinateMatrix Q o R *
      graphOrientedRegionCoordinateMatrix Q.conjTranspose o R = 1 := by
  have he (e : Edge Γ) : graphOrientedEdgeCoordinateMatrix Q o e *
      graphOrientedEdgeCoordinateMatrix Q.conjTranspose o e = 1 := by
    unfold graphOrientedEdgeCoordinateMatrix
    split_ifs
    · exact map_star_mul_eq_one Q Q.conjTranspose hQ
    · exact hQ
  have hb (e : RB (Γ := Γ) R) : graphOrientedBoundaryCoordinateMatrix Q o R e *
      graphOrientedBoundaryCoordinateMatrix Q.conjTranspose o R e = 1 := by
    unfold graphOrientedBoundaryCoordinateMatrix
    split_ifs
    · exact map_star_mul_eq_one _ _ (he e.1)
    · exact he e.1
  rw [graphOrientedRegionCoordinateMatrix, graphOrientedRegionCoordinateMatrix,
    mixedPhysicalProductMatrix_mul]
  simp only [hb, graphOrientedBondCoordinateMatrix, bondCoordinateMatrix_mul, he]
  rw [bondCoordinateMatrix_one]
  exact mixedPhysicalProductMatrix_one

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Each crossing coordinate operation transforms its arbitrary virtual
boundary label with the same native edge orientation. -/
theorem graphOrientedOpenBoundaryFactor_coordinates
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) (q : RV R → G)
    (e : RB (Γ := Γ) R) (θ : X) :
    graphOrientedBoundaryCoordinateMatrix Q o R e *ᵥ
        graphOrientedOpenBoundaryFactor U 1 o R q e θ =
      fun y => ∑ a : Y, graphOrientedBoundaryCoordinateMatrix Q o R e a θ *
        graphOrientedOpenBoundaryFactor L 1 o R q e a y := by
  have hleft (g : G) : Q.conjTranspose * L g = U g * Q.conjTranspose := by
    rw [hL, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hright (g : G) : L g * Q = Q * U g := by
    rw [hL, Matrix.mul_assoc, Matrix.mul_assoc, hQ, Matrix.mul_one]
  funext y
  unfold graphOrientedBoundaryCoordinateMatrix graphOrientedEdgeCoordinateMatrix
    graphOrientedOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R <;> cases ho : o e.1
  · simp only [ht, Bool.false_eq_true, ↓reduceIte, dite_true, Matrix.one_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using
      congr_fun (congr_fun (hleft ((q ⟨e.1.1.1, ht⟩)⁻¹)).symm θ) y
  · simp only [ht, ↓reduceIte, dite_true, Matrix.mul_one, Matrix.mulVec,
      dotProduct, Matrix.map_apply, star_star]
    simpa only [Matrix.mul_apply, mul_comm] using
      congr_fun (congr_fun (hright (q ⟨e.1.1.1, ht⟩)).symm y) θ
  · simp only [ht, Bool.false_eq_true, ↓reduceIte, dite_false, Matrix.mul_one,
      Matrix.mulVec, dotProduct]
    simpa only [Matrix.mul_apply, mul_comm] using
      congr_fun (congr_fun (hright (q ⟨e.1.1.2,
        (e.2.resolve_left (fun h' => ht h'.1)).2⟩)).symm y) θ
  · simp only [ht, ↓reduceIte, dite_false, Matrix.one_mul, Matrix.mulVec,
      dotProduct, Matrix.map_apply]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using
      congr_fun (congr_fun (hleft ((q ⟨e.1.1.2,
        (e.2.resolve_left (fun h' => ht h'.1)).2⟩)⁻¹)).symm θ) y

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Every internal pair transforms in its native orientation, while the
underlying ordered physical registers are unchanged. -/
theorem graphOrientedOpenInternalFactor_coordinates
    (Q : Matrix Y X ℂ) (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) (q : RV R → G)
    (e : RI (Γ := Γ) R) :
    graphOrientedBondCoordinateMatrix Q o e.1 *ᵥ
        graphOrientedOpenInternalFactor U 1 o R q e =
      graphOrientedOpenInternalFactor L 1 o R q e := by
  unfold graphOrientedBondCoordinateMatrix graphOrientedEdgeCoordinateMatrix
    graphOrientedOpenInternalFactor
  cases ho : o e.1
  · simp only [Bool.false_eq_true, ↓reduceIte, one_pow, Matrix.one_mul]
    rw [bondCoordinateMatrix_mulVec, ← hL]
  · simp only [↓reduceIte, one_pow, Matrix.one_mul]
    rw [bondCoordinateMatrix_map_star_mulVec, ← hL]

/-- All open generators transform with their complete virtual boundary
coefficients for any assignment of edge orientations. -/
theorem graphOrientedRegionCoordinateMatrix_open
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    graphOrientedRegionCoordinateMatrix Q o R *ᵥ graphOrientedOpenBondCoordinates U 1 o R θ =
      ∑ a : RB (Γ := Γ) R → Y,
        (∏ e, graphOrientedBoundaryCoordinateMatrix Q o R e (a e) (θ e)) •
          graphOrientedOpenBondCoordinates L 1 o R a := by
  rw [graphOrientedOpenBondCoordinates_eq_sum_prod]
  change mixedPhysicalProductMap (graphOrientedBoundaryCoordinateMatrix Q o R)
    (fun e : RI (Γ := Γ) R => graphOrientedBondCoordinateMatrix Q o e.1) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOrientedOpenBoundaryFactor_coordinates Q hQ U L hL,
    graphOrientedOpenInternalFactor_coordinates Q U L hL]
  simp_rw [graphOrientedOpenBondCoordinates_eq_sum_prod]
  exact sum_prod_sum_mul_eq_sum_prod_smul _ _ _ _

/-- Arbitrary entangled boundary coefficient vectors transform explicitly,
without a fixed-label or product-boundary restriction. -/
theorem graphOrientedRegionCoordinateMatrix_open_superposition
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) (c : (RB (Γ := Γ) R → X) → ℂ) :
    graphOrientedRegionCoordinateMatrix Q o R *ᵥ
        (∑ θ, c θ • graphOrientedOpenBondCoordinates U 1 o R θ) =
      ∑ a : RB (Γ := Γ) R → Y,
        (∑ θ, (∏ e, graphOrientedBoundaryCoordinateMatrix Q o R e (a e) (θ e)) * c θ) •
          graphOrientedOpenBondCoordinates L 1 o R a := by
  change Matrix.mulVecLin (graphOrientedRegionCoordinateMatrix Q o R)
    (∑ θ, c θ • graphOrientedOpenBondCoordinates U 1 o R θ) = _
  rw [map_sum]
  simp only [map_smul, Matrix.mulVecLin_apply,
    graphOrientedRegionCoordinateMatrix_open Q hQ U L hL,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro θ _
  rw [mul_comm]

/-- Inclusion of the actual regional contraction ranges follows from the
unrestricted open coefficient identity. -/
theorem graphOrientedRegionCoordinateMatrix_maps_openBondSpace
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) :
    (graphOrientedOpenBondSpace U 1 o R).map
      (Matrix.mulVecLin (graphOrientedRegionCoordinateMatrix Q o R)) ≤
      graphOrientedOpenBondSpace L 1 o R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change graphOrientedRegionCoordinateMatrix Q o R *ᵥ
    graphOrientedOpenBondCoordinates U 1 o R θ ∈ graphOrientedOpenBondSpace L 1 o R
  rw [graphOrientedRegionCoordinateMatrix_open Q hQ U L hL]
  apply Submodule.sum_smul_mem
  intro a _
  exact Submodule.subset_span ⟨a, rfl⟩

/-- Oriented Fourier coordinates identify the entire actual open-region
range in both directions. -/
theorem graphOrientedRegionCoordinateMatrix_map_openBondSpace
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (o : Edge Γ → Bool) (R : Finset V) :
    (graphOrientedOpenBondSpace U 1 o R).map
      (Matrix.mulVecLin (graphOrientedRegionCoordinateMatrix Q o R)) =
      graphOrientedOpenBondSpace L 1 o R := by
  apply le_antisymm (graphOrientedRegionCoordinateMatrix_maps_openBondSpace Q hQ U L hL o R)
  intro ψ hψ
  have hQQ := mul_conjTranspose_eq_one_of_representation_coordinates Q U L hL
  have hinv : ∀ g, U g = Q.conjTranspose * L g * Q.conjTranspose.conjTranspose := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      representation_coordinates_conjTranspose Q hQ U L hL
  refine ⟨graphOrientedRegionCoordinateMatrix Q.conjTranspose o R *ᵥ ψ, ?_, ?_⟩
  · apply graphOrientedRegionCoordinateMatrix_maps_openBondSpace Q.conjTranspose
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hQQ) L U hinv o R
    exact ⟨ψ, hψ, rfl⟩
  · change graphOrientedRegionCoordinateMatrix Q o R *ᵥ
      (graphOrientedRegionCoordinateMatrix Q.conjTranspose o R *ᵥ ψ) = ψ
    rw [Matrix.mulVec_mulVec, graphOrientedRegionCoordinateMatrix_mul_conjTranspose Q hQQ,
      Matrix.one_mulVec]

end TNLean.PEPS
