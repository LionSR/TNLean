/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondSupport
import TNLean.PEPS.TorusPhysicalMap
import TNLean.PEPS.RegionPhysicalMap

/-!
# Overlaps preserved by the physical product of supported bond maps

A bond transformation whose initial Gram operator is EE† preserves overlaps
against vectors in the range of the isometric inclusion E. This remains true
for its product over any finite set of bonds. The original endpoint-pair
multiplicity-restoring map therefore preserves every overlap on the actual
product matching-sector support. No isometry on unmatched sectors is asserted.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7,
local source lines 2992–3019.
-/

open scoped Matrix BigOperators
namespace TNLean.PEPS

/-- Products of physical maps compose bond by bond.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem physicalProductMatrix_mul {Site In Mid Out : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Mid]
    (F : Matrix Out Mid ℂ) (L : Matrix Mid In ℂ) :
    physicalProductMatrix Site F * physicalProductMatrix Site L =
      physicalProductMatrix Site (F * L) := by
  ext τ σ
  simp only [physicalProductMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (v : Site) (j : Mid) => F (τ v) j * L j (σ v))).symm

/-- A product of coordinate inclusions includes precisely the coordinatewise
embedded configurations. -/
theorem physicalProductMatrix_endpointEmbeddingMatrix {Site In Out : Type*}
    [Fintype Site] [DecidableEq Out] (e : In ↪ Out) :
    physicalProductMatrix Site (endpointEmbeddingMatrix e) =
      endpointEmbeddingMatrix (Function.Embedding.piCongrRight fun _ : Site => e) := by
  classical
  ext τ σ
  simp only [physicalProductMatrix, endpointEmbeddingMatrix, Fintype.prod_boole,
    ← funext_iff]
  rfl

private theorem productMatrix_conjTranspose {Site In Out : Type*} [Fintype Site]
    (F : Matrix Out In ℂ) :
    (physicalProductMatrix Site F).conjTranspose = physicalProductMatrix Site F.conjTranspose := by
  ext σ τ
  simp only [physicalProductMatrix, Matrix.conjTranspose_apply, star_prod]

private def siteUnivConfigurationEquiv {Site α : Type*} [Fintype Site] :
    ({v : Site // v ∈ (Finset.univ : Finset Site)} → α) ≃ (Site → α) :=
  Equiv.piCongrLeft' (fun _ => α) (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _))

/-- A product of physical isometries on any finite set is an isometry.
This is the region-univ specialization of the existing region product isometry.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem physicalProductMatrix_isIsometry {Site In Out : Type*}
    [Fintype Site] [DecidableEq Site] [Fintype Out] [DecidableEq In]
    (E : Matrix Out In ℂ) (hE : E.IsIsometry) :
    (physicalProductMatrix Site E).IsIsometry := by
  classical
  -- The region theorem uses an order only to choose finite configurations.
  -- Retain the existing equality decision when introducing that auxiliary order.
  let decSite : DecidableEq Site := inferInstance
  let ordSite := LinearOrder.lift' (Fintype.equivFin Site)
    (Fintype.equivFin Site).injective
  let : LinearOrder Site := { ordSite with
    toDecidableEq := decSite
    compare := fun a b => @compareOfLessAndEq Site a b ordSite.toLT
      (ordSite.toDecidableLT a b) decSite
    compare_eq_compareOfLessAndEq := fun _ _ => rfl }
  have hregion := regionPhysicalProductMatrix_isIsometry
    (In := fun _ : Site => In) (Out := fun _ : Site => Out) Finset.univ
    (fun _ => E) (fun _ => hE)
  have hmatrix : Matrix.reindex (siteUnivConfigurationEquiv (α := Out))
      (siteUnivConfigurationEquiv (α := In))
      (regionPhysicalProductMatrix Finset.univ (fun _ : Site => E)) =
        physicalProductMatrix Site E := by
    ext τ σ
    change (∏ v : {v : Site // v ∈ (Finset.univ : Finset Site)}, E (τ v.1) (σ v.1)) =
      ∏ v : Site, E (τ v) (σ v)
    exact Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _))
      _ _ (fun _ => rfl)
  simpa only [hmatrix] using Matrix.IsIsometry.reindex _ hregion
    (siteUnivConfigurationEquiv (α := Out)) (siteUnivConfigurationEquiv (α := In))

/-- Products of physical isometries preserve every physical overlap.
Source: SCP10, the product bond isometry in Section 7, lines 3008–3019. -/
theorem physicalProductMap_dotProduct_of_isIsometry
    {Site In Out : Type*} [Fintype Site] [DecidableEq Site]
    [Fintype In] [Fintype Out] [DecidableEq In]
    (F : Matrix Out In ℂ) (hF : F.IsIsometry) (ψ φ : (Site → In) → ℂ) :
    star (physicalProductMap Site F ψ) ⬝ᵥ physicalProductMap Site F φ = star ψ ⬝ᵥ φ := by
  have hproductF := physicalProductMatrix_isIsometry (Site := Site) F hF
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hproductF, Matrix.vecMul_one]

/-- Products of physical maps with initial Gram operator EE† preserve every
physical overlap against a vector in the product inclusion's range.
Source: the product of supported bond isometries in SCP10, Section 7,
lines 3008–3019. -/
theorem physicalProductMap_dotProduct_of_initialProjection
    {Site In Out K : Type*} [Fintype Site] [DecidableEq Site]
    [Fintype In] [Fintype Out] [Fintype K] [DecidableEq K]
    (F : Matrix Out In ℂ) (E : Matrix In K ℂ) (hE : E.IsIsometry)
    (hGram : F.conjTranspose * F = E * E.conjTranspose)
    (ψ φ : (Site → In) → ℂ) (hφ : φ ∈ LinearMap.range (physicalProductMap Site E)) :
    star (physicalProductMap Site F ψ) ⬝ᵥ physicalProductMap Site F φ = star ψ ⬝ᵥ φ := by
  classical
  obtain ⟨χ, rfl⟩ := hφ
  have hproductE := physicalProductMatrix_isIsometry (Site := Site) E hE
  have hproductGram : (physicalProductMatrix Site F).conjTranspose *
      physicalProductMatrix Site F =
      physicalProductMatrix Site E * (physicalProductMatrix Site E).conjTranspose := by
    rw [productMatrix_conjTranspose, physicalProductMatrix_mul, hGram,
      ← physicalProductMatrix_mul (Site := Site) E E.conjTranspose,
      ← productMatrix_conjTranspose (Site := Site) E]
  have hfixed : (physicalProductMatrix Site E *
      (physicalProductMatrix Site E).conjTranspose) *ᵥ
        (physicalProductMatrix Site E *ᵥ χ) = physicalProductMatrix Site E *ᵥ χ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hproductE, Matrix.mul_one]
  simp only [physicalProductMap, Matrix.mulVecLin_apply]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hproductGram, ← Matrix.dotProduct_mulVec, hfixed]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)] [∀ i, Nonempty (μ i)]

/-- The product of the actual full-endpoint multiplicity-restoring maps preserves
all overlaps on matching-sector physical states. The supported vector may be
an arbitrary coherent superposition. Source: SCP10, Section 7, lines 2992–3019. -/
theorem physicalProductMap_fullMultiplicityBondMap_dotProduct
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (ψ φ : (Edge → ((Σ i, ν i) × (Σ i, ν i))) → ℂ)
    (hφ : φ ∈ LinearMap.range (physicalProductMap Edge (blockBondInclusion ν))) :
    star (physicalProductMap Edge (fullMultiplicityBondMap ν μ) ψ) ⬝ᵥ
      physicalProductMap Edge (fullMultiplicityBondMap ν μ) φ = star ψ ⬝ᵥ φ :=
  physicalProductMap_dotProduct_of_initialProjection
    (fullMultiplicityBondMap ν μ) (blockBondInclusion ν)
    (blockBondInclusion_isIsometry ν) (fullMultiplicityBondMap_initialProjection ν μ) ψ φ hφ

end TNLean.PEPS
