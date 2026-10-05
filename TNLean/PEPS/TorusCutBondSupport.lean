/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutBoundaryBasis
import TNLean.PEPS.TorusCutCoefficientExtraction
import TNLean.PEPS.TorusPhysicalBondRegrouping
import TNLean.PEPS.PhysicalProductRangeSupport
import TNLean.PEPS.TorusMatchedProjectorExpansion

/-!
# Bond support forced by complementary canonical cuts

On each uncut bond the canonical cut contraction has a relative group
representation matrix as its physical factor. Each single-bond slice therefore
lies in the representation-matrix span. The four cuts cover every physical
bond by their uncut bonds, forcing a vector in their intersection into the
full product of these spans. This derives the bond-product expansion before
using coefficient extraction on coherent sums.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

section CoordinateSlices
variable {Site Out : Type*} [Fintype Site] [DecidableEq Site]

/-- Fixing all but one coordinate in a product vector leaves a scalar multiple
of its factor at that coordinate. -/
theorem product_coordinateSlice_eq_smul
    (f : Site → Out → ℂ) (e : Site) (τ : Site → Out) :
    (fun s ↦ ∏ w, f w (Function.update τ e s w)) =
      (∏ w ∈ Finset.univ.erase e, f w (τ w)) • f e := by
  classical
  funext s
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

end CoordinateSlices

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- The canonical averaging tensor at each site of an independently matched
bond family. -/
noncomputable abbrev torusMatchedAveragingSites (Uh Uv : X → G →* Matrix V V ℂ) :
    X → V → V → V → V → (V × V × V × V) → ℂ :=
  fun v ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)

/-- The matrix whose columns are the individual representation matrices in
head-tail physical coordinates. -/
def representationBondMatrix (U : G →* Matrix V V ℂ) : Matrix (V × V) G ℂ :=
  fun t g ↦ U g t.1 t.2

/-- Each representation matrix is an actual column of the bond map. -/
theorem representation_matrix_mem_bond_range (U : G →* Matrix V V ℂ) (g : G) :
    (fun t : V × V ↦ U g t.1 t.2) ∈ (Matrix.mulVecLin (representationBondMatrix U)).range := by
  classical
  refine ⟨Pi.single g 1, ?_⟩
  ext t
  simp [representationBondMatrix, Matrix.mulVec_single, Matrix.col]

/-- One actual physical bond slice of a site-ordered tensor. -/
def torusPhysicalBondSlice (e : X × Bool) (τ : (X × Bool) → V × V) :
    ((X → V × V × V × V) → ℂ) →ₗ[ℂ] ((V × V) → ℂ) :=
  LinearMap.pi fun s ↦ LinearMap.proj
    (torusSiteBondEndpointEquiv.symm (Function.update τ e s))

/-- Read the independently assigned representation of one actual bond. -/
def torusBondRepresentation (Uh Uv : X → G →* Matrix V V ℂ)
    (e : X × Bool) : G →* Matrix V V ℂ :=
  if e.2 then Uv e.1 else Uh e.1

/-- The bond matrix after the local vertex group actions have been exposed. -/
def torusGaugeBondMatrix (Uh Uv : X → G →* Matrix V V ℂ)
    (Oh Ov : X → Matrix V V ℂ) (q : X → G) (e : X × Bool) : Matrix V V ℂ :=
  if e.2 then Uv e.1 (q e.1) * Ov e.1 * Uv e.1 (q (e.1.1, e.1.2 + 1))⁻¹
  else Uh e.1 (q (e.1.1 + 1, e.1.2)) * Oh e.1 * Uh e.1 (q e.1)⁻¹

/-- The canonical operator network is a coherent sum of actual bond factors,
with arbitrary inserted matrices retained on every bond. -/
theorem torusBondRegrouping_insertedAveragingSite_coherent
    (Uh Uv : X → G →* Matrix V V ℂ) (Oh Ov : X → Matrix V V ℂ) :
    torusBondRegrouping (fun σ ↦ torusBondNetwork
      (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) =
      fun β ↦ (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X *
        ∑ q : X → G, ∏ e : X × Bool, torusGaugeBondMatrix Uh Uv Oh Ov q e (β e).1 (β e).2 := by
  funext β
  rw [torusBondRegrouping_apply, torusBondNetwork_representationAveragingSite]
  simp only [torusSiteBondEndpointEquiv_symm_apply, add_sub_cancel_right]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [← torusBond_product]
  simp only [torusGaugeBondMatrix, Bool.false_eq_true, ↓reduceIte]

/-- When a bond is contracted with the identity, each of its physical slices
lies in the span of the representation matrices, even with arbitrary
operators and coherent contractions on all the other bonds. -/
theorem torusPhysicalBondSlice_averagingSite_mem_range
    (Uh Uv : X → G →* Matrix V V ℂ) (Oh Ov : X → Matrix V V ℂ)
    (e : X × Bool) (he : (if e.2 then Ov e.1 else Oh e.1) = 1)
    (τ : (X × Bool) → V × V) :
    torusPhysicalBondSlice e τ (fun σ ↦ torusBondNetwork
      (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) ∈
      (Matrix.mulVecLin (representationBondMatrix (torusBondRepresentation Uh Uv e))).range := by
  classical
  have hrepr : ∀ q : X → G,
      (fun s : V × V ↦ torusGaugeBondMatrix Uh Uv Oh Ov q e s.1 s.2) ∈
        (Matrix.mulVecLin (representationBondMatrix (torusBondRepresentation Uh Uv e))).range := by
    intro q
    rcases e with ⟨v, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      simpa only [torusGaugeBondMatrix, torusBondRepresentation, Bool.false_eq_true, ↓reduceIte, he,
        Matrix.mul_one, ← map_inv, ← map_mul] using
        representation_matrix_mem_bond_range (Uh v) (q (v.1 + 1, v.2) * (q v)⁻¹)
    · simp only [↓reduceIte] at he
      simpa only [torusGaugeBondMatrix, torusBondRepresentation, ↓reduceIte, he,
        Matrix.mul_one, ← map_inv, ← map_mul] using
        representation_matrix_mem_bond_range (Uv v) (q v * (q (v.1, v.2 + 1))⁻¹)
  have hexpand := torusBondRegrouping_insertedAveragingSite_coherent Uh Uv Oh Ov
  have heq : torusPhysicalBondSlice e τ (fun σ ↦ torusBondNetwork
      (fun v t ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) Oh Ov) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card X •
        ∑ q : X → G, (fun s ↦ ∏ w : X × Bool,
          torusGaugeBondMatrix Uh Uv Oh Ov q w
            (Function.update τ e s w).1 (Function.update τ e s w).2) := by
    funext s
    simpa only [torusPhysicalBondSlice, LinearMap.pi_apply, LinearMap.proj_apply,
      torusBondRegrouping_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using
      congrFun hexpand (Function.update τ e s)
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro q _
  rw [product_coordinateSlice_eq_smul
    (fun w (s : V × V) ↦ torusGaugeBondMatrix Uh Uv Oh Ov q w s.1 s.2) e τ]
  exact Submodule.smul_mem _ _ (hrepr q)

end TNLean.PEPS
