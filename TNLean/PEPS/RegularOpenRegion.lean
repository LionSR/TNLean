/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.OpenRegionContraction
import TNLean.PEPS.RegularBoundaryState

/-!
# Regular-group boundary symmetry of an actual region contraction

A tensor whose regular-basis coefficients are invariant under simultaneous left
translation of its virtual labels induces an open-region tensor with the same
boundary symmetry. The assertion follows by translating every internal bond label
in the finite contraction. In the dual regular basis the contragredient action has
the same permutation of labels, so incoming and outgoing legs obey this rule.

This is the boundary symmetry step in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, proof of Theorem 6.9 (local source lines 1935–1980 and 2043–2072).
It does not assert that a region containing loops is isometric on its invariant
boundary space, and does not establish the physical entropy formula.
-/

open scoped BigOperators Matrix
open Module Representation

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- A PEPS with group labels on every virtual bond, expressed in the finite-index
coordinates of `Tensor`. Source: SCP10, regular representation basis in §6. -/
noncomputable abbrev groupBondTensor
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) : Tensor Γ d where
  bondDim _ := Fintype.card G
  component v η s := a v (fun e => (Fintype.equivFin G).symm (η e)) s

/-- Simultaneous left translation of any finite family of regular-bond labels. -/
noncomputable def regularLabelTranslation {ι : Type*} (g : G) :
    (ι → Fin (Fintype.card G)) ≃ (ι → Fin (Fintype.card G)) :=
  Equiv.piCongrRight fun _ =>
    (Fintype.equivFin G).symm.trans ((Equiv.mulLeft g).trans (Fintype.equivFin G))

@[simp]
theorem regularLabelTranslation_apply {ι : Type*} (g : G)
    (η : ι → Fin (Fintype.card G)) (i : ι) :
    regularLabelTranslation g η i =
      Fintype.equivFin G (g * (Fintype.equivFin G).symm (η i)) := rfl

omit [Fintype V] in
/-- Translating incident labels translates their restriction to the crossing bonds. -/
theorem regionIncidentBoundaryLabel_translation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (g : G) (η : RegionIncidentConfig (groupBondTensor a) R) :
    regionIncidentBoundaryLabel (groupBondTensor a) R (regularLabelTranslation g η) =
      regularLabelTranslation g (regionIncidentBoundaryLabel (groupBondTensor a) R η) := rfl

omit [Fintype V] in
/-- Local regular-basis symmetry is preserved by the product of tensors in a region. -/
theorem regionIncidentWeight_translation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (g : G) (η : RegionIncidentConfig (groupBondTensor a) R)
    (σ : RegionPhysicalConfig (d := d) R) :
    regionIncidentWeight (groupBondTensor a) R (regularLabelTranslation g η) σ =
      regionIncidentWeight (groupBondTensor a) R η σ := by
  unfold regionIncidentWeight
  apply Finset.prod_congr rfl
  intro w _
  simp only [regularLabelTranslation_apply, Equiv.symm_apply_apply]
  exact ha g w.1 _ (σ w)

/-- Source: SCP10, region contraction in the proof of Theorem 6.9, lines 1935–1980.
The genuine open-region tensor is invariant under simultaneous left translation of
its crossing labels; all internal labels are translated in the summation. -/
theorem openRegionWeight_translation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun e => g * η e) s = a v η s)
    (R : Finset V) (g : G) (μ : RegionBoundaryConfig (groupBondTensor a) R)
    (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight (groupBondTensor a) R (regularLabelTranslation g μ) σ =
      openRegionWeight (groupBondTensor a) R μ σ := by
  classical
  unfold openRegionWeight
  rw [← Equiv.sum_comp (regularLabelTranslation g)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [regionIncidentBoundaryLabel_translation,
    (regularLabelTranslation g).injective.eq_iff,
    regionIncidentWeight_translation a ha]

/-- An enumeration of the crossing bonds identifies their regular labels with
ordered group configurations. -/
noncomputable def regularRegionBoundaryConfigEquiv
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (Fin b → G) ≃ RegionBoundaryConfig (groupBondTensor a) R :=
  e.symm.arrowCongr (Fintype.equivFin G)

/-- The actual open-region matrix in ordered regular group coordinates. -/
noncomputable def regularOpenRegionMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    Matrix (RegionPhysicalConfig (d := d) R) (Fin b → G) ℂ :=
  fun σ x => openRegionWeight (groupBondTensor a) R
    (regularRegionBoundaryConfigEquiv a R e x) σ

/-- Local regular symmetry passes to the columns of the ordered open-region matrix. -/
theorem regularOpenRegionMatrix_translation
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b)
    (g : G) (σ : RegionPhysicalConfig (d := d) R) (x : Fin b → G) :
    regularOpenRegionMatrix a R e σ (g • x) = regularOpenRegionMatrix a R e σ x := by
  have h : regularRegionBoundaryConfigEquiv a R e (g • x) =
      regularLabelTranslation g (regularRegionBoundaryConfigEquiv a R e x) := by
    funext f
    simp [regularRegionBoundaryConfigEquiv, Equiv.arrowCongr, Pi.smul_apply,
      regularLabelTranslation_apply]
  unfold regularOpenRegionMatrix
  rw [h, openRegionWeight_translation a ha]

variable [DecidableEq G]

/-- A matrix invariant under simultaneous regular translation is unchanged by
inserting the invariant-boundary projector on its virtual side. -/
theorem matrix_mul_regularBoundaryProjector_of_translation
    {α : Type*} (n : ℕ) (M : Matrix α (Fin (n + 1) → G) ℂ)
    (hM : ∀ (g : G) σ x, M σ (g • x) = M σ x) :
    M * regularBoundaryProjector (n + 1) = M := by
  ext σ x
  have hi : (fun y => M σ y) ∈
      (regularBoundaryRepresentation (G := G) (n + 1)).invariants := by
    intro g
    funext y
    simpa only [regularBoundaryRepresentation_apply] using hM g⁻¹ σ y
  have hid := (regularBoundaryRepresentation (G := G) (n + 1)).averageMap_id _ hi
  have hvec : regularBoundaryProjector (n + 1) *ᵥ (fun y => M σ y) = fun y => M σ y := by
    simpa only [regularBoundaryProjector, ← Matrix.toLin'_apply,
      Matrix.toLin'_toMatrix'] using hid
  rw [Matrix.mul_apply]
  calc
    _ = ∑ y, regularBoundaryProjector (n + 1) x y * M σ y := by
      apply Finset.sum_congr rfl
      intro y _
      have hsym : regularBoundaryProjector (G := G) (n + 1) y x =
          regularBoundaryProjector (n + 1) x y :=
        congrArg (fun Q : Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ => Q x y)
          (regularBoundaryProjector_transpose n)
      rw [hsym, mul_comm]
    _ = M σ x := congrFun hvec x

/-- Source: SCP10, proof of Theorem 6.9, lines 2043–2072. The actual region
contraction factors through the invariant regular-boundary projector. -/
theorem regularOpenRegionMatrix_mul_projector
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    regularOpenRegionMatrix a R e * regularBoundaryProjector (n + 1) =
      regularOpenRegionMatrix a R e := by
  apply matrix_mul_regularBoundaryProjector_of_translation
  exact regularOpenRegionMatrix_translation a ha R e

/-- The complementary open-region matrix, with crossing bonds ordered by the
same enumeration as the first region. -/
noncomputable def regularOpenComplementMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R)) (Fin b → G) ℂ :=
  fun τ x => openRegionWeight (groupBondTensor a) (Finset.univ \ R)
    (regionComplementBoundaryConfig (groupBondTensor a) R
      (regularRegionBoundaryConfigEquiv a R e x)) τ

/-- The coefficient matrix of the actual physical PEPS across a finite region cut. -/
noncomputable def regularPhysicalCutMatrix
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V) :
    Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
  fun σ τ => stateCoeff (groupBondTensor a) (assembleRegionσ R σ τ)

omit [DecidableEq G] in
/-- The exact physical cut is the contraction of the two actual open-region maps.
This uses unnormalized regular bonds. Source: SCP10, lines 1935–1980. -/
theorem regularPhysicalCutMatrix_eq_mul_transpose
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularPhysicalCutMatrix a R =
      regularOpenRegionMatrix a R e * (regularOpenComplementMatrix a R e).transpose := by
  ext σ τ
  rw [regularPhysicalCutMatrix,
    stateCoeff_eq_openRegionComplement_of_regularBonds (H := G)
      (groupBondTensor a) R (fun _ => rfl)]
  rw [← Equiv.sum_comp (regularRegionBoundaryConfigEquiv a R e)]
  rfl

/-- Source: SCP10, proof of Theorem 6.9, lines 2043–2072. Simultaneous boundary
symmetry inserts the regular averaging projector in the exact physical cut.
No assumption about the isometry of either region map is made. -/
theorem regularPhysicalCutMatrix_eq_mul_projector_mul_transpose
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    regularPhysicalCutMatrix a R = regularOpenRegionMatrix a R e *
      regularBoundaryProjector (n + 1) * (regularOpenComplementMatrix a R e).transpose := by
  rw [regularOpenRegionMatrix_mul_projector a ha R n e]
  exact regularPhysicalCutMatrix_eq_mul_transpose a R e

/-- Source: SCP10, virtual boundary-state transport in the proof of Theorem 6.9,
lines 2043–2072. Applying the actual open-region maps to the normalized virtual
matrix `C = P / sqrt(|G|^n)` gives the exact physical cut multiplied by that
reciprocal square root. The resulting physical vector need not be normalized
until the Gram operators of the region maps have been computed. -/
theorem regularOpenRegionMatrix_mul_schmidtMatrix_mul_transpose
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (n : ℕ)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    regularOpenRegionMatrix a R e * regularBoundarySchmidtMatrix n *
        (regularOpenComplementMatrix a R e).transpose =
      (Real.sqrt (Fintype.card G ^ n : ℝ) : ℂ)⁻¹ • regularPhysicalCutMatrix a R := by
  rw [regularBoundarySchmidtMatrix, Matrix.mul_smul, Matrix.smul_mul,
    ← regularPhysicalCutMatrix_eq_mul_projector_mul_transpose a ha R n e]

end TNLean.PEPS

