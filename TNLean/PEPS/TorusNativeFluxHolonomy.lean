/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusInsertedRegularBundles
import TNLean.PEPS.TorusBondFlatConnection
import TNLean.PEPS.TorusPlaquetteFluxMeasurement

/-!
# Native flux labels and plaquette detection

Horizontal native arrows point right and vertical native arrows point down.
The existing ordered-edge representation therefore transports a horizontal
label rightwards and the inverse of a vertical label upwards. This fixes the
clockwise plaquette product and identifies the actual native matrix contraction
with the regular twisted graph state measured by the four-site detector.

For powers of one group element, the clockwise plaquette exponent is the signed
sum of the four native bond counts. The detector's counterclockwise convention
measures the inverse class. In particular, an eastward dual segment carrying
`g` on its crossed downward bond has clockwise source flux `g`, whereas its
counterclockwise detector label is `g⁻¹`. A southward dual segment instead
carries `g⁻¹` on its crossed rightward native bond, as in the source figure.

Source: SCP10, arXiv:1001.3807, Definition 6.13 and its fluxon-string figure,
lines 2181–2197, and Theorem 6.15, lines 2217–2267. The graph and detector
statements require both periods to be at least three. They make no claim that
arbitrary paths with common endpoints have equal states on a torus.

**Scope restriction (regular native simple-graph detector):** See
`docs/paper-gaps/scp10_dual_flux_string_deformation.tex` for the distinction
from unrestricted source wording and arbitrary open-boundary geometries.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

variable {width height : ℕ} {G : Type*} [Group G]
local notation "X" => TorusVertex width height

/-- Clockwise native plaquette holonomy, with horizontal arrows pointing right
and vertical arrows pointing down. Source: SCP10, Definition 6.13 and the
fluxon-string figure, lines 2181–2197. -/
def torusBondPlaquetteHolonomy (p : TorusBondLabels width height G) (q : X) : G :=
  (p.1 q)⁻¹ * p.2 (q.1 + 1, q.2) * p.1 (q.1, q.2 + 1) * (p.2 q)⁻¹

/-- A common group element raised to arbitrary signed native bond counts has
clockwise flux given by their signed plaquette sum. Source: SCP10,
Definition 6.13 and its oriented string insertions, lines 2181–2197. -/
theorem torusBondPlaquetteHolonomy_zpow (g : G) (h v : X → ℤ) (q : X) :
    torusBondPlaquetteHolonomy (fun x => g ^ h x, fun x => g ^ v x) q =
      g ^ (h (q.1, q.2 + 1) + v (q.1 + 1, q.2) - h q - v q) := by
  simp only [torusBondPlaquetteHolonomy, ← zpow_neg, ← zpow_add]
  congr 1
  omega

variable [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "Γₜ" => torusGraph width height

/-- Ordered graph labels retain the native horizontal transport even at the
periodic seam. Source: SCP10, Definition 6.13, lines 2181–2197. -/
@[simp]
theorem torusNativeRightTransport_torusGraphRegularLabels (uh uv : X → G) (q : X) :
    torusNativeRightTransport (torusGraphRegularLabels uh uv) q = uh q := by
  unfold torusNativeRightTransport regularDirectedTransport
  change (if q < (q.1 + 1, q.2) then
    torusGraphRegularLabels uh uv (torusRightEdge q) else
    (torusGraphRegularLabels uh uv (torusRightEdge q))⁻¹) = _
  unfold torusGraphRegularLabels
  rw [show torusEdgeEquiv.symm (torusRightEdge q) = Sum.inl q from
    torusEdgeEquiv.symm_apply_apply (Sum.inl q)]
  by_cases hq : q < (q.1 + 1, q.2)
  · simp [hq, torusRightEdge, Edge.ofAdj_of_lt _ hq]
  · have hr : (q.1 + 1, q.2) < q :=
      lt_of_le_of_ne (le_of_not_gt hq) (torusGraph_adj_right q.1 q.2).ne.symm
    simp [hq, torusRightEdge, Edge.ofAdj_of_gt _ hr, ne_of_lt hr]

/-- Upward transport is the inverse downward native label, including at the
periodic seam. Source: SCP10, Definition 6.13, lines 2181–2197. -/
@[simp]
theorem torusNativeUpTransport_torusGraphRegularLabels (uh uv : X → G) (q : X) :
    torusNativeUpTransport (torusGraphRegularLabels uh uv) q = (uv q)⁻¹ := by
  unfold torusNativeUpTransport regularDirectedTransport
  change (if q < (q.1, q.2 + 1) then
    torusGraphRegularLabels uh uv (torusUpEdge q) else
    (torusGraphRegularLabels uh uv (torusUpEdge q))⁻¹) = _
  unfold torusGraphRegularLabels
  rw [show torusEdgeEquiv.symm (torusUpEdge q) = Sum.inr q from
    torusEdgeEquiv.symm_apply_apply (Sum.inr q)]
  by_cases hq : q < (q.1, q.2 + 1)
  · simp [hq, torusUpEdge, Edge.ofAdj_of_lt _ hq]
  · have hr : (q.1, q.2 + 1) < q :=
      lt_of_le_of_ne (le_of_not_gt hq) (torusGraph_adj_up q.1 q.2).ne.symm
    simp [hq, torusUpEdge, Edge.ofAdj_of_gt _ hr, ne_of_lt hr]

/-- The reverse graph plaquette walk is exactly the clockwise native product.
Source: SCP10, Definition 6.13, lines 2181–2197. -/
theorem regularWalkHolonomy_torusGraphRegularLabels_reverse
    (p : TorusBondLabels width height G) (q : X) :
    regularWalkHolonomy (torusGraphRegularLabels p.1 p.2) (torusPlaquetteWalk q).reverse =
      torusBondPlaquetteHolonomy p q := by
  rw [regularWalkHolonomy_torusPlaquetteWalk_reverse]
  change (torusNativeRightTransport _ q)⁻¹ *
    (torusNativeUpTransport _ (q.1 + 1, q.2))⁻¹ *
    torusNativeRightTransport _ (q.1, q.2 + 1) * torusNativeUpTransport _ q = _
  simp [torusBondPlaquetteHolonomy]

/-- The existing counterclockwise detector sees the inverse native clockwise
holonomy. Source: SCP10, Definition 6.13 and Theorem 6.15. -/
theorem regularWalkHolonomy_torusGraphRegularLabels
    (p : TorusBondLabels width height G) (q : X) :
    regularWalkHolonomy (torusGraphRegularLabels p.1 p.2) (torusPlaquetteWalk q) =
      (torusBondPlaquetteHolonomy p q)⁻¹ := by
  rw [← regularWalkHolonomy_torusGraphRegularLabels_reverse p q,
    regularWalkHolonomy_reverse, inv_inv]

/-- Clockwise graph holonomy for arbitrary signed native powers. Source:
SCP10, Definition 6.13, lines 2181–2197. -/
theorem regularWalkHolonomy_torusGraphRegularLabels_zpow_reverse
    (g : G) (h v : X → ℤ) (q : X) :
    regularWalkHolonomy (torusGraphRegularLabels (fun x => g ^ h x) (fun x => g ^ v x))
        (torusPlaquetteWalk q).reverse =
      g ^ (h (q.1, q.2 + 1) + v (q.1 + 1, q.2) - h q - v q) := by
  rw [regularWalkHolonomy_torusGraphRegularLabels_reverse
    (fun x => g ^ h x, fun x => g ^ v x), torusBondPlaquetteHolonomy_zpow]

/-- Counterclockwise graph holonomy for arbitrary signed native powers. Source:
SCP10, Definition 6.13 and Theorem 6.15. -/
theorem regularWalkHolonomy_torusGraphRegularLabels_zpow
    (g : G) (h v : X → ℤ) (q : X) :
    regularWalkHolonomy (torusGraphRegularLabels (fun x => g ^ h x) (fun x => g ^ v x))
        (torusPlaquetteWalk q) =
      g ^ (-(h (q.1, q.2 + 1) + v (q.1 + 1, q.2) - h q - v q)) := by
  rw [regularWalkHolonomy_torusGraphRegularLabels
    (fun x => g ^ h x, fun x => g ^ v x), torusBondPlaquetteHolonomy_zpow, zpow_neg]

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- The actual native regular-matrix contraction equals the existing twisted
regular graph state for every bond assignment and physical configuration.
Source: SCP10, Definition 6.13 and `eq:2d:peps-with-ug-uh`. -/
theorem torusBondNetwork_leftRegular_eq_stateCoeff
    (a : G → G → G → G → Fin d → ℂ)
    (p : TorusBondLabels width height G) (σ : X → Fin d) :
    torusBondNetwork (fun x c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ x))
        (fun x => leftRegularMatrix G (p.1 x)) (fun x => leftRegularMatrix G (p.2 x)) =
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a)
        (torusGraphRegularLabels p.1 p.2))) σ := by
  rw [torusBondNetwork_eq_graphInsertedBondNetwork, torusGraphBondMatrix_leftRegular,
    graphInsertedBondNetwork_leftRegular_eq_stateCoeff]
  rfl

/-- The physical cut matrix formed directly from the native inserted-matrix
contraction. Source: SCP10, Theorem 6.15, lines 2217–2267. -/
def torusBondRegularPhysicalCutMatrix
    (a : G → G → G → G → Fin d → ℂ) (p : TorusBondLabels width height G) (R : Finset X) :
    Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
  fun σ τ => torusBondNetwork
    (fun x c => a c.1 c.2.1 c.2.2.1 c.2.2.2 (assembleRegionσ R σ τ x))
    (fun x => leftRegularMatrix G (p.1 x)) (fun x => leftRegularMatrix G (p.2 x))

/-- Native and ordered-edge cut matrices agree entry by entry; this equality
is derived from their actual contractions. Source: SCP10, Theorem 6.15. -/
theorem torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix
    (a : G → G → G → G → Fin d → ℂ) (p : TorusBondLabels width height G) (R : Finset X) :
    torusBondRegularPhysicalCutMatrix a p R =
      regularPhysicalCutMatrix
        (regularTwistedSite (torusIncidentSite a) (torusGraphRegularLabels p.1 p.2)) R := by
  ext σ τ
  exact torusBondNetwork_leftRegular_eq_stateCoeff a p (assembleRegionσ R σ τ)

/-- A single complete projective measurement on four original physical spins
detects the counterclockwise flux class of every actual native regular-matrix
insertion. Source: SCP10, Theorem 6.15, lines 2217–2267. -/
theorem IsGIsometric.exists_torusNative_plaquette_cutMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (q : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (p : TorusBondLabels width height G) (C : Option (ConjClasses G)),
        Q C * torusBondRegularPhysicalCutMatrix a p (torusPlaquetteRegion q) =
          if C = some (ConjClasses.mk (torusBondPlaquetteHolonomy p q)⁻¹)
          then torusBondRegularPhysicalCutMatrix a p (torusPlaquetteRegion q) else 0 := by
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusPlaquette_holonomy_cutMeasurement q
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro p C
  simpa only [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix,
    regularWalkHolonomy_torusGraphRegularLabels] using hQact (torusGraphRegularLabels p.1 p.2) C

/-- For arbitrary signed native counts, one fixed four-spin measurement reads
the inverse signed plaquette exponent on the actual native contraction.
Source: SCP10, Definition 6.13 and Theorem 6.15, lines 2181–2267. -/
theorem IsGIsometric.exists_torusNativePower_plaquette_cutMeasurement
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (q : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (g : G) (h v : X → ℤ) (C : Option (ConjClasses G)),
        Q C * torusBondRegularPhysicalCutMatrix a
            (fun x => g ^ h x, fun x => g ^ v x) (torusPlaquetteRegion q) =
          if C = some (ConjClasses.mk
            (g ^ (-(h (q.1, q.2 + 1) + v (q.1 + 1, q.2) - h q - v q))))
          then torusBondRegularPhysicalCutMatrix a
            (fun x => g ^ h x, fun x => g ^ v x) (torusPlaquetteRegion q) else 0 := by
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := ha.exists_torusNative_plaquette_cutMeasurement q
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro g h v C
  simpa only [torusBondPlaquetteHolonomy_zpow, zpow_neg] using
    hQact (fun x => g ^ h x, fun x => g ^ v x) C

end TNLean.PEPS
