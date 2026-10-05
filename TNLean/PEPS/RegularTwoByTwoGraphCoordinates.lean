/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGraphBondContraction
import TNLean.PEPS.RegularGraphPhysicalBlocking
import TNLean.PEPS.GIsometricCoordinateTransport
import TNLean.PEPS.GIsometricCanonicalSupport

/-!
# Paired block boundaries in regular bundled graph coordinates

The two regular labels on each coarse edge are identified with one
distinguished label and a one-coordinate surplus register. The identification
retains every fine boundary leg and the actual blocked physical tensor.
Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1818–1915.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {X : Type*}

/-- Two labels as one distinguished label and one surplus register.
This changes only the label type, not either label's value.
Source: SCP10, two-bond step, lines 1840–1874. -/
def pairUnitBundleEquiv : (X × X) ≃ (X × (Unit → X)) where
  toFun x := (x.1, fun _ => x.2)
  invFun x := (x.1, x.2 ())
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext rfl
    funext i
    cases i
    rfl

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height
variable {P : Type*}

/-- The actual four-site contraction with its paired boundary in the uniform
bundle alphabet. Source: SCP10, lines 1888–1906. -/
def twoByTwoBundledGraphSite [Fintype X] (a : FV → (Fin 4 → X) → P → ℂ)
    (v : TV) (η : IncidentEdge TG v → X × (Unit → X)) (σ : Fin 4 → P) : ℂ :=
  twoByTwoGraphSite a v (fun f => pairUnitBundleEquiv.symm (η f)) σ

/-- All virtual bonds are reindexed bijectively; the actual contracted state
is unchanged. Source: SCP10, paired bonds of the two-by-two diagram. -/
theorem graphBondNetwork_twoByTwoBundledGraphSite [Fintype X]
    (a : FV → (Fin 4 → X) → P → ℂ) (σ : TV → Fin 4 → P) :
    graphBondNetwork (twoByTwoBundledGraphSite a) σ =
      graphBondNetwork (twoByTwoGraphSite a) σ := by
  let E := (Equiv.refl (Edge TG)).arrowCongr (pairUnitBundleEquiv (X := X))
  unfold graphBondNetwork
  rw [← E.sum_comp]
  simp only [twoByTwoBundledGraphSite, E, Equiv.arrowCongr_apply,
    Equiv.symm_apply_apply, Function.comp_apply]
  rfl

/-- The original fine-torus coefficient equals the actual bundled coarse
network coefficient. No block-local or global Gram hypothesis is present.
Source: SCP10, geometric part of Observation 6.6, lines 1888–1906. -/
theorem torusBondNetwork_eq_twoByTwoBundledGraphSite [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 =
      graphBondNetwork (twoByTwoBundledGraphSite a) (twoByTwoPhysicalEquiv σ) := by
  rw [graphBondNetwork_twoByTwoBundledGraphSite, torusBondNetwork_eq_twoByTwoGraphSite]

/-- Each actual incident bundled label gives the eight separate block labels.
Source: SCP10, paired boundary in lines 1888–1906. -/
def twoByTwoIncidentBoundaryEquiv (v : TV) :
    (IncidentEdge TG v → X × (Unit → X)) ≃ (Fin 4 × Fin 2 → X) :=
  (((torusIncidentLegEquiv v).symm.arrowCongr (Equiv.refl (X × (Unit → X)))).trans
    ((Equiv.refl (Fin 4)).arrowCongr pairUnitBundleEquiv.symm)).trans twoByTwoBoundaryEquiv

/-- The physical site map is unchanged by the actual eight-boundary-label
identification. Source: SCP10, lines 1888–1906. -/
theorem regularSiteMap_twoByTwoBundledGraphSite [Fintype X]
    (a : FV → (Fin 4 → X) → P → ℂ) (v : TV)
    (x : (IncidentEdge TG v → X × (Unit → X)) → ℂ) :
    regularSiteMap (twoByTwoBundledGraphSite a v) x =
      regularSiteMap (fun β σ => twoByTwoTensor
        (fun i => a (kitaevPeriodicTilingEquiv (v, i))) (twoByTwoBoundaryEquiv.symm β) σ)
          (x ∘ (twoByTwoIncidentBoundaryEquiv v).symm) := by
  classical
  ext σ
  let E := twoByTwoIncidentBoundaryEquiv (X := X) v
  change (∑ η, twoByTwoBundledGraphSite a v η σ * x η) =
    ∑ β, twoByTwoTensor (fun i => a (kitaevPeriodicTilingEquiv (v, i)))
      (twoByTwoBoundaryEquiv.symm β) σ * x (E.symm β)
  rw [← E.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rfl

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- The actual eight-leg boundary identification respects simultaneous regular
translation, for arbitrary finite groups, including nonabelian groups.
Source: SCP10, lines 1830–1848 and 1888–1906. -/
theorem twoByTwoIncidentBoundaryEquiv_smul (v : TV) (g : G)
    (η : IncidentEdge TG v → G × (Unit → G)) :
    twoByTwoIncidentBoundaryEquiv v (g • η) = g • twoByTwoIncidentBoundaryEquiv v η := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases j <;> rfl

/-- The incident graph symmetry is the eight-leg regular boundary symmetry in
these coordinates. Source: SCP10, blocked symmetry in lines 1888–1896. -/
theorem twoByTwoIncidentBoundaryEquiv_rep (v : TV) (g : G)
    (x : (IncidentEdge TG v → G × (Unit → G)) → ℂ) :
    (graphIncidentRepresentation (regularBundleMatrix Unit) v g x) ∘
        (twoByTwoIncidentBoundaryEquiv v).symm =
      regularLegRepresentation (Fin 4 × Fin 2) g
        (x ∘ (twoByTwoIncidentBoundaryEquiv v).symm) := by
  funext θ
  simp only [Function.comp_apply, graphIncidentRepresentation_regularBundle_apply,
    regularLegRepresentation_apply]
  congr 1

/-- On an ordinary regular leg the graph orientation still gives simultaneous
left translation. Source: SCP10, regular symmetry in lines 1830–1848. -/
theorem graphIncidentRepresentation_leftRegularMatrix
    {V : Type*} [Fintype V] [LinearOrder V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (v : V) :
    graphIncidentRepresentation (leftRegularMatrix G) v =
      regularLegRepresentation (IncidentEdge Γ v) := by
  ext g x σ
  have h (η : IncidentEdge Γ v → G) :
      graphIncidentMatrix (leftRegularMatrix G) v g σ η =
        if σ = g • η then 1 else 0 := by
    have hf (f : IncidentEdge Γ v) :
        (if f.1.1.1 = v then leftRegularMatrix G g⁻¹ (η f) (σ f)
          else leftRegularMatrix G g (σ f) (η f)) =
          if σ f = g * η f then 1 else 0 := by
      rw [leftRegularMatrix_apply, leftRegularMatrix_apply]
      simp only [eq_inv_mul_iff_mul_eq, eq_comm (a := g * η f), ite_self]
    simp only [graphIncidentMatrix, hf, Fintype.prod_boole, ← funext_iff]
    rfl
  have he (η : IncidentEdge Γ v → G) : σ = g • η ↔ η = g⁻¹ • σ := by
    rw [eq_inv_smul_iff, eq_comm]
  simp [graphIncidentRepresentation_apply, regularLegRepresentation_apply,
    Matrix.mulVec, dotProduct, h, he]

/-- An original four-leg regular tensor remains G-isometric in the actual
coarse graph's four incident coordinates. Source: SCP10, lines 1896–1906. -/
theorem IsGIsometric.isGIsometric_torusIncidentFamily [Fintype P]
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) (v : TV) :
    IsGIsometric (graphIncidentRepresentation (leftRegularMatrix G) v)
      (regularSiteMap (torusIncidentFamily (fun _ : TV => a) v)) := by
  let E := (torusIncidentLegEquiv v).symm.arrowCongr (Equiv.refl G)
  refine ha.of_coordinateEquiv E (Equiv.refl P) ?_ ?_
  · intro g x
    rw [graphIncidentRepresentation_leftRegularMatrix]
    funext η
    simp only [Function.comp_apply, regularLegRepresentation_apply]
    rfl
  · intro x
    ext s
    change (∑ η, torusIncidentFamily (fun _ : TV => a) v η s * x η) =
      ∑ β, a β s * x (E.symm β)
    rw [← E.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rfl

/-- The coarse canonical tensor is the same original regular tensor up to
its derived positive scalar and an isometric equivalence of physical supports.
Unused original physical directions remain outside the support, without an
ambient-surjectivity premise. Source: SCP10, Observation 6.6, lines 1896–1906. -/
theorem IsGIsometric.exists_torusCanonicalSupportEquiv [Fintype P] [DecidableEq P]
    {a : (Fin 4 → G) → P → ℂ}
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) (v : TV) :
    ∃ c : ℝ, 0 < c ∧
      ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
          (regularSiteMap (torusIncidentFamily (fun _ : TV => a) v)))).range ≃ₗᵢ[ℂ]
        (Matrix.toEuclideanLin (LinearMap.toMatrix'
          (regularSiteMap (graphAveragingSite (Γ := TG) (leftRegularMatrix G) v)))).range,
        (∀ x, (I x).val.ofLp = ((Real.sqrt c : ℂ)⁻¹ •
          coordinateAdjoint (regularSiteMap (torusIncidentFamily (fun _ : TV => a) v)))
            x.val.ofLp) ∧
        ((Real.sqrt c : ℂ)⁻¹ •
          coordinateAdjoint (regularSiteMap (torusIncidentFamily (fun _ : TV => a) v))) ∘ₗ
            regularSiteMap (torusIncidentFamily (fun _ : TV => a) v) =
          (Real.sqrt c : ℂ) •
            regularSiteMap (graphAveragingSite (Γ := TG) (leftRegularMatrix G) v) := by
  rw [regularSiteMap_graphAveragingSite]
  exact (ha.isGIsometric_torusIncidentFamily v).exists_canonicalSupportEquiv (by
    rw [graphIncidentRepresentation_leftRegularMatrix]
    exact regularLegRepresentation_unitary _)

end TNLean.PEPS
