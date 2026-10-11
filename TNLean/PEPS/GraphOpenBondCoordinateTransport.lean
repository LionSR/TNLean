/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.SemiRegularCanonicalLocalTransport
import TNLean.PEPS.BondCoordinateTransport

/-!
# Fourier transport with arbitrary open virtual boundary data

The physical Fourier transformation acts by Q on incoming endpoints and by
its conjugate on outgoing endpoints. The identical oriented transformation
acts on virtual boundary coefficients. No boundary coefficient is restricted.

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

omit [Fintype G] in
/-- A unital coordinate identity already forces surjectivity of the virtual
coordinate map. Source: SCP10, Section 7, regular Fourier coordinates. -/
theorem mul_conjTranspose_eq_one_of_representation_coordinates
    (Q : Matrix Y X ℂ) (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) : Q * Q.conjTranspose = 1 := by
  simpa only [map_one, Matrix.mul_one] using (hL 1).symm

/-- The physical crossing factor remembers which endpoint lies in the region. -/
def graphBoundaryCoordinateMatrix (Q : Matrix Y X ℂ) (R : Finset V)
    (e : RB (Γ := Γ) R) : Matrix Y X ℂ :=
  if e.1.1.1 ∈ R then Q.map star else Q

/-- The Fourier matrix on actual regional physical bond coordinates. -/
def graphRegionCoordinateMatrix (Q : Matrix Y X ℂ) (R : Finset V) :=
  mixedPhysicalProductMatrix (graphBoundaryCoordinateMatrix (Γ := Γ) Q R)
    (fun _ : RI (Γ := Γ) R => bondCoordinateMatrix Q)

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Fourier transport of each retained virtual boundary factor. -/
theorem graphOpenBoundaryFactor_coordinates
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (R : Finset V) (q : RV R → G) (e : RB (Γ := Γ) R) (θ : X) :
    graphBoundaryCoordinateMatrix Q R e *ᵥ graphOpenBoundaryFactor U 1 R q e θ =
      fun y => ∑ a : Y, graphBoundaryCoordinateMatrix Q R e a θ *
        graphOpenBoundaryFactor L 1 R q e a y := by
  have hleft (g : G) : Q.conjTranspose * L g = U g * Q.conjTranspose := by
    rw [hL, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hright (g : G) : L g * Q = Q * U g := by
    rw [hL, Matrix.mul_assoc, Matrix.mul_assoc, hQ, Matrix.mul_one]
  funext y
  unfold graphBoundaryCoordinateMatrix graphOpenBoundaryFactor
  by_cases ht : e.1.1.1 ∈ R
  · simp only [ht, ↓reduceIte, dite_eq_left, Matrix.one_mul, Matrix.mulVec,
      dotProduct, Matrix.map_apply]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using
      congr_fun (congr_fun (hleft ((q ⟨e.1.1.1, ht⟩)⁻¹)).symm θ) y
  · simp only [dite_eq_right ht, ite_eq_right ht, Matrix.mul_one, Matrix.mulVec, dotProduct]
    simpa only [Matrix.mul_apply, mul_comm] using
      congr_fun (congr_fun (hright (q ⟨e.1.1.2,
        (e.2.resolve_left (fun h' => ht h'.1)).2⟩)).symm y) θ

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
/-- Internal paired physical coordinates transform by Q tensor conjugate Q. -/
theorem graphOpenInternalFactor_coordinates
    (Q : Matrix Y X ℂ) (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (R : Finset V) (q : RV R → G) (e : RI (Γ := Γ) R) :
    bondCoordinateMatrix Q *ᵥ graphOpenInternalFactor (Γ := Γ) U 1 R q e =
      graphOpenInternalFactor L 1 R q e := by
  unfold graphOpenInternalFactor
  simp only [one_pow, Matrix.one_mul]
  rw [bondCoordinateMatrix_mulVec, ← hL]

/-- Every actual open generator transforms with its full virtual boundary
coefficient, including arbitrary crossing labels. -/
theorem graphRegionCoordinateMatrix_open
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (R : Finset V) (θ : RB (Γ := Γ) R → X) :
    graphRegionCoordinateMatrix Q R *ᵥ graphOpenBondCoordinates U 1 R θ =
      ∑ a : RB (Γ := Γ) R → Y,
        (∏ e, graphBoundaryCoordinateMatrix Q R e (a e) (θ e)) •
          graphOpenBondCoordinates L 1 R a := by
  rw [graphOpenBondCoordinates_eq_sum_prod]
  change mixedPhysicalProductMap (graphBoundaryCoordinateMatrix Q R)
    (fun _ : RI (Γ := Γ) R => bondCoordinateMatrix Q) _ = _
  rw [mixedPhysicalProductMap_sum_prod]
  simp only [graphOpenBoundaryFactor_coordinates Q hQ U L hL,
    graphOpenInternalFactor_coordinates Q U L hL]
  simp_rw [graphOpenBondCoordinates_eq_sum_prod]
  exact sum_prod_sum_mul_eq_sum_prod_smul _ _ _ _

/-- Arbitrary virtual boundary coefficient vectors transform explicitly;
no product-state or fixed-label condition is imposed on the boundary. -/
theorem graphRegionCoordinateMatrix_open_superposition
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose)
    (R : Finset V) (c : (RB (Γ := Γ) R → X) → ℂ) :
    graphRegionCoordinateMatrix Q R *ᵥ
        (∑ θ, c θ • graphOpenBondCoordinates U 1 R θ) =
      ∑ a : RB (Γ := Γ) R → Y,
        (∑ θ, (∏ e, graphBoundaryCoordinateMatrix Q R e (a e) (θ e)) * c θ) •
          graphOpenBondCoordinates L 1 R a := by
  change Matrix.mulVecLin (graphRegionCoordinateMatrix Q R)
    (∑ θ, c θ • graphOpenBondCoordinates U 1 R θ) = _
  rw [map_sum]
  simp only [map_smul, Matrix.mulVecLin_apply, graphRegionCoordinateMatrix_open Q hQ U L hL,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro θ _
  rw [mul_comm]

/-- Actual regional range inclusion, derived from the open coefficient identity. -/
theorem graphRegionCoordinateMatrix_maps_openBondSpace
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (R : Finset V) :
    (graphOpenBondSpace (Γ := Γ) U 1 R).map (Matrix.mulVecLin (graphRegionCoordinateMatrix Q R)) ≤
      graphOpenBondSpace L 1 R := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨θ, rfl⟩
  change graphRegionCoordinateMatrix Q R *ᵥ graphOpenBondCoordinates U 1 R θ ∈
    graphOpenBondSpace L 1 R
  rw [graphRegionCoordinateMatrix_open Q hQ U L hL]
  apply Submodule.sum_smul_mem
  intro a _
  exact Submodule.subset_span ⟨a, rfl⟩

omit [Fintype G] in
/-- The inverse Fourier coordinate identity follows from virtual isometry. -/
theorem representation_coordinates_conjTranspose
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (g : G) :
    U g = Q.conjTranspose * L g * Q := by
  rw [hL, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
    Matrix.mul_assoc, hQ, Matrix.mul_one]

/-- Multiplication of mixed product matrices is componentwise. -/
theorem mixedPhysicalProductMatrix_mul {B E X Y Z P Q T : Type*}
    [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E] [Fintype Y] [Fintype Q]
    (F : B → Matrix Z Y ℂ) (K : E → Matrix T Q ℂ)
    (F' : B → Matrix Y X ℂ) (K' : E → Matrix Q P ℂ) :
    mixedPhysicalProductMatrix F K * mixedPhysicalProductMatrix F' K' =
      mixedPhysicalProductMatrix (fun b => F b * F' b) (fun e => K e * K' e) := by
  classical
  ext τ σ
  simp only [Matrix.mul_apply, mixedPhysicalProductMatrix]
  simp_rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [Fintype.prod_sum, Fintype.prod_sum]

/-- The mixed product of identity matrices is the identity. -/
theorem mixedPhysicalProductMatrix_one {B E X P : Type*}
    [Fintype B] [Fintype E]
    [DecidableEq X] [DecidableEq P] :
    mixedPhysicalProductMatrix (fun _ : B => (1 : Matrix X X ℂ))
      (fun _ : E => (1 : Matrix P P ℂ)) = 1 := by
  classical
  ext τ σ
  simp only [mixedPhysicalProductMatrix, Matrix.one_apply, Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_true_left, funext_iff, Prod.ext_iff]
  split_ifs <;> simp_all

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
/-- Composition of physical bond coordinate maps is composition of virtual maps. -/
theorem bondCoordinateMatrix_mul {Z : Type*} (A : Matrix Z Y ℂ) (B : Matrix Y X ℂ) :
    bondCoordinateMatrix A * bondCoordinateMatrix B = bondCoordinateMatrix (A * B) := by
  rw [bondCoordinateMatrix, bondCoordinateMatrix, bondCoordinateMatrix,
    ← Matrix.mul_kronecker_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
/-- The identity virtual coordinate change fixes both physical endpoints. -/
theorem bondCoordinateMatrix_one : bondCoordinateMatrix (1 : Matrix Y Y ℂ) = 1 := by
  ext i j
  change (1 : Matrix Y Y ℂ) i.1 j.1 * star ((1 : Matrix Y Y ℂ) i.2 j.2) =
    (1 : Matrix (Y × Y) (Y × Y) ℂ) i j
  simp only [Matrix.one_apply, apply_ite, star_one, star_zero, Prod.ext_iff]
  split_ifs <;> simp_all

omit [DecidableEq X] [Fintype Y] in
/-- The regional Fourier transformation and its inverse cancel on every vector. -/
theorem graphRegionCoordinateMatrix_mul_conjTranspose
    (Q : Matrix Y X ℂ) (hQ : Q * Q.conjTranspose = 1) (R : Finset V) :
    graphRegionCoordinateMatrix (Γ := Γ) Q R *
      graphRegionCoordinateMatrix (Γ := Γ) Q.conjTranspose R = 1 := by
  rw [graphRegionCoordinateMatrix, graphRegionCoordinateMatrix,
    mixedPhysicalProductMatrix_mul]
  have hb (e : RB (Γ := Γ) R) : graphBoundaryCoordinateMatrix Q R e *
      graphBoundaryCoordinateMatrix Q.conjTranspose R e = 1 := by
    unfold graphBoundaryCoordinateMatrix
    split_ifs
    · ext i j
      have h := congr_fun (congr_fun hQ i) j
      simpa only [Matrix.mul_apply, Matrix.map_apply, ← star_mul, ← star_sum,
        Matrix.one_apply, apply_ite, star_one, star_zero, mul_comm] using congrArg star h
    · exact hQ
  simp only [hb, bondCoordinateMatrix_mul, hQ]
  rw [bondCoordinateMatrix_one]
  exact mixedPhysicalProductMatrix_one

/-- Every target open-region vector has a source preimage. Both inclusions
are derived from arbitrary-boundary coefficient identities. -/
theorem graphRegionCoordinateMatrix_map_openBondSpace
    (Q : Matrix Y X ℂ) (hQ : Q.conjTranspose * Q = 1)
    (U : G →* Matrix X X ℂ) (L : G →* Matrix Y Y ℂ)
    (hL : ∀ g, L g = Q * U g * Q.conjTranspose) (R : Finset V) :
    (graphOpenBondSpace (Γ := Γ) U 1 R).map
      (Matrix.mulVecLin (graphRegionCoordinateMatrix Q R)) = graphOpenBondSpace L 1 R := by
  apply le_antisymm (graphRegionCoordinateMatrix_maps_openBondSpace Q hQ U L hL R)
  intro ψ hψ
  have hQQ := mul_conjTranspose_eq_one_of_representation_coordinates Q U L hL
  have hinv : ∀ g, U g = Q.conjTranspose * L g * Q.conjTranspose.conjTranspose := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      representation_coordinates_conjTranspose Q hQ U L hL
  refine ⟨graphRegionCoordinateMatrix (Γ := Γ) Q.conjTranspose R *ᵥ ψ, ?_, ?_⟩
  · apply graphRegionCoordinateMatrix_maps_openBondSpace Q.conjTranspose
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hQQ) L U hinv R
    exact ⟨ψ, hψ, rfl⟩
  · change graphRegionCoordinateMatrix Q R *ᵥ
      (graphRegionCoordinateMatrix (Γ := Γ) Q.conjTranspose R *ᵥ ψ) = ψ
    rw [Matrix.mulVec_mulVec, graphRegionCoordinateMatrix_mul_conjTranspose Q hQQ,
      Matrix.one_mulVec]

end TNLean.PEPS
