/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionEntropy

/-!
# Reduced densities for central complementary bond insertions

Central bond labels commute with every simultaneous local regular translation.
They therefore preserve the actual local Gram kernels, and hence the Gram
matrix of every contracted open region. If the insertions are identity on
all bonds incident to an observation region, its original open-region map is
unchanged. Its actual physical reduced matrix is then exactly the vacuum
reduced matrix, without a connectivity, spanning-tree, or factorization premise.

Source: SCP10, arXiv:1001.3807v3, the regular isometry in Definition 6.1 and
the local flux-string claim in Lemma 6.14, source lines 1692–1700 and 2199–2214.

**Scope restriction (central complementary insertions):** Centrality and
identity on every incident bond are explicit structural hypotheses on the
insertions. The result covers arbitrary observation regions under those
hypotheses; it does not infer them from endpoint exclusion. Noncentral flux
labels and the annular Wilson-loop obstruction remain separate.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] in
private theorem twisted_translation_iff
    (u : Edge Γ → G) (hu : ∀ f g, Commute (u f) g) (v : V)
    (η θ : IncidentEdge Γ v → G) (g : G) :
    regularTwistedLabels u v η = g • regularTwistedLabels u v θ ↔ η = g • θ := by
  have hf (f : IncidentEdge Γ v) :
      regularTwistedLabels u v η f = g * regularTwistedLabels u v θ f ↔
        η f = g * θ f := by
    by_cases hv : v = f.1.1.2
    · simp only [regularTwistedLabels, hv, ite_true]
      rw [← mul_assoc, ← (hu f.1 g).eq, mul_assoc, mul_left_cancel_iff]
    · simp only [regularTwistedLabels, hv, ite_false]
  simp only [funext_iff, Pi.smul_apply, smul_eq_mul, hf]

private theorem site_gram_eq
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) (hu : ∀ f g, Commute (u f) g)
    (v : V) (η θ : IncidentEdge Γ v → G) :
    (∑ s : Fin d, star (regularTwistedSite a u v η s) * regularTwistedSite a u v θ s) =
      ∑ s : Fin d, star (a v η s) * a v θ s := by
  classical
  obtain ⟨c, _, h⟩ := (ha v).exists_regularSiteGram
  simp only [regularTwistedSite, h, twisted_translation_iff u hu]

/-- Central native edge insertions preserve the Gram matrix of the actual
open-region contraction. All local Gram identities are derived from regular
G-isometry. Source: SCP10, Definition 6.1 and Lemma 6.14. -/
theorem regularTwistedOpenRegionMatrix_gram_eq_of_central
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) (hu : ∀ f g, Commute (u f) g)
    (R : Finset V) {b : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularTwistedOpenRegionMatrix a u R e).conjTranspose *
        regularTwistedOpenRegionMatrix a u R e =
      (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e := by
  classical
  ext x y
  rw [regularOpenRegionMatrix_crossGram_apply_group,
    regularOpenRegionMatrix_crossGram_apply_group]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro θ _
  split_ifs
  · apply Finset.prod_congr rfl
    intro v _
    exact site_gram_eq a ha u hu v.1 _ _
  · rfl

/-- Central insertions supported away from every incident physical bond leave
the actual regional reduced matrix equal to the vacuum one. No topology or
nonzero-cut hypothesis is required for this unnormalized identity.
Source: SCP10, the regular-isometric subcase of Lemma 6.14. -/
theorem regularPhysicalCutMatrix_reduced_eq_of_central
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) (hu : ∀ f g, Commute (u f) g)
    (R : Finset V) (hR : ∀ f : Edge Γ, IsRegionIncidentEdge R f → u f = 1) :
    let M := regularPhysicalCutMatrix (regularTwistedSite a u) R
    let M₀ := regularPhysicalCutMatrix a R
    M * M.conjTranspose = M₀ * M₀.conjTranspose := by
  classical
  let e := Fintype.equivFin {f : Edge Γ // IsRegionBoundaryEdge R f}
  let ec := (regionBoundaryEdgeComplEquiv (G := Γ) R).symm.trans e
  have hM := regularTwistedOpenRegionMatrix_eq_of_trivial_on_incident a u R hR e
  change regularOpenRegionMatrix (regularTwistedSite a u) R e =
    regularOpenRegionMatrix a R e at hM
  have hN := regularTwistedOpenRegionMatrix_gram_eq_of_central a ha u hu
    (Finset.univ \ R) ec
  have hNt :
      (regularOpenComplementMatrix (regularTwistedSite a u) R e).transpose *
          (regularOpenComplementMatrix (regularTwistedSite a u) R e).transpose.conjTranspose =
        (regularOpenComplementMatrix a R e).transpose *
          (regularOpenComplementMatrix a R e).transpose.conjTranspose := by
    simpa only [regularOpenComplementMatrix_eq_regularOpenRegionMatrix,
      Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      ec] using congrArg Matrix.transpose hN
  dsimp only
  rw [regularPhysicalCutMatrix_eq_mul_transpose _ R e,
    regularPhysicalCutMatrix_eq_mul_transpose a R e, hM]
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = regularOpenRegionMatrix a R e *
        ((regularOpenComplementMatrix (regularTwistedSite a u) R e).transpose *
          (regularOpenComplementMatrix (regularTwistedSite a u) R e).transpose.conjTranspose) *
        (regularOpenRegionMatrix a R e).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hNt]; simp only [Matrix.mul_assoc]

/-- Normalizing the actual reduced matrices preserves the vacuum equality
for central complementary insertions. Source: SCP10, Lemma 6.14. -/
theorem regularPhysicalCutMatrix_normalized_reduced_eq_of_central
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) (hu : ∀ f g, Commute (u f) g)
    (R : Finset V) (hR : ∀ f : Edge Γ, IsRegionIncidentEdge R f → u f = 1) :
    let M := regularPhysicalCutMatrix (regularTwistedSite a u) R
    let M₀ := regularPhysicalCutMatrix a R
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  dsimp only
  rw [regularPhysicalCutMatrix_reduced_eq_of_central a ha u hu R hR]

end TNLean.PEPS
