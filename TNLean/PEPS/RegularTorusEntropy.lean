/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusCut
import TNLean.PEPS.RegularTwistedRegionEntropy
import TNLean.PEPS.TorusRectangleConnectivity

/-!
# Entropy of regular torus closures across an interior rectangle

The native four-leg regular action and the incident-edge action are the same
permutation action in different coordinates. For an interior coordinate rectangle,
the two closure seams lie entirely in its complement, which remains connected
after the seams are removed. The finite twisted-cut calculation therefore applies
to arbitrary nonzero superpositions of the native closure vectors.

**Scope restriction (interior rectangles on a simple torus graph):** both torus
dimensions are at least three, the rectangle has positive side lengths and lies
strictly between the two coordinate seams. This is a restricted form of Schuch,
Cirac, and Pérez-García, arXiv:1001.3807, Theorem 6.9, proof, lines 2043–2076.
The source's arbitrary topologically trivial disk remains separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. Noncommuting closure pairs are
allowed only for this interior cut. No parent-Hamiltonian or ground-space assertion is made here.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix LinearMap

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

private theorem torusIncidentEdge_eq_leg (v : TorusVertex width height)
    (f : IncidentEdge (torusGraph width height) v) :
    f = torusTopLeg v ∨ f = torusRightLeg v ∨ f = torusDownLeg v ∨ f = torusLeftLeg v := by
  obtain ⟨z, hz⟩ := torusEdgeEquiv.surjective f.1
  rcases z with p | p
  · change torusRightEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2)
    have hp : p = v ∨ (p.1 + 1, p.2) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inr (Or.inl (Subtype.ext hz.symm))
    · have hp' : p = (v.1 - 1, v.2) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) hy
      exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [← hz, hp']; rfl))))
  · change torusUpEdge p = f.1 at hz
    have hi := f.2
    rw [← hz] at hi
    have hep := Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2)
    have hp : p = v ∨ (p.1, p.2 + 1) = v := by
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hi with hi | hi
      · exact Or.inl (h1.symm.trans hi)
      · exact Or.inr (h2.symm.trans hi)
      · exact Or.inr (h1.symm.trans hi)
      · exact Or.inl (h2.symm.trans hi)
    rcases hp with rfl | hp
    · exact Or.inl (Subtype.ext hz.symm)
    · have hp' : p = (v.1, v.2 - 1) := by
        have hx := congrArg Prod.fst hp
        have hy := congrArg Prod.snd hp
        exact Prod.ext hx ((eq_sub_iff_add_eq).mpr hy)
      exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [← hz, hp']; rfl))))

/-- The four native virtual labels of a site, in top, right, down, left order. -/
def torusIncidentCoordinates (v : TorusVertex width height)
    (η : IncidentEdge (torusGraph width height) v → G) : G × G × G × G :=
  (η (torusTopLeg v), η (torusRightLeg v), η (torusDownLeg v), η (torusLeftLeg v))

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The four native coordinates determine every incident-edge label. -/
theorem torusIncidentCoordinates_injective (v : TorusVertex width height) :
    Function.Injective (torusIncidentCoordinates (G := G) v) := by
  intro η θ h
  have ht := congrArg (fun p : G × G × G × G => p.1) h
  have hr := congrArg (fun p : G × G × G × G => p.2.1) h
  have hb := congrArg (fun p : G × G × G × G => p.2.2.1) h
  have hl := congrArg (fun p : G × G × G × G => p.2.2.2) h
  funext f
  rcases torusIncidentEdge_eq_leg v f with rfl | rfl | rfl | rfl
  · exact ht
  · exact hr
  · exact hb
  · exact hl

/-- Local regular isometry in the native torus coordinates gives the identical group-average
Gram formula on the incident graph edges. Source: SCP10, Definition 6.1, lines 1692–1700. -/
theorem IsGIsometric.exists_torusIncidentSiteGram
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : TorusVertex width height)
      (η θ : IncidentEdge (torusGraph width height) v → G),
      (∑ s : Fin d, star (torusIncidentSite a v η s) * torusIncidentSite a v θ s) =
        ((c : ℂ) / (Fintype.card G : ℂ)) *
          ∑ g : G, if η = g • θ then (1 : ℂ) else 0 := by
  obtain ⟨c, hc, h⟩ := ha.exists_torusRegularSiteGram
  refine ⟨c, hc, fun v η θ => ?_⟩
  have heq (g : G) : torusIncidentCoordinates v η = g • torusIncidentCoordinates v θ ↔
      η = g • θ := by
    change torusIncidentCoordinates v η = torusIncidentCoordinates v (g • θ) ↔ _
    exact (torusIncidentCoordinates_injective v).eq_iff
  have hηθ := h (torusIncidentCoordinates v η) (torusIncidentCoordinates v θ)
  simp only [heq] at hηθ
  exact hηθ

/-- Native regular isometry is preserved when the virtual legs are expressed as incident
edges of the simple torus graph. Source: SCP10, Definition 6.1, lines 1692–1700. -/
theorem IsGIsometric.isGIsometric_torusIncidentSite
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : TorusVertex width height) :
    IsGIsometric (regularLegRepresentation (IncidentEdge (torusGraph width height) v))
      (regularSiteMap (torusIncidentSite a v)) := by
  classical
  have hinv : ∀ g, regularSiteMap (torusIncidentSite a v) ∘ₗ
      regularLegRepresentation (IncidentEdge (torusGraph width height) v) g =
        regularSiteMap (torusIncidentSite a v) := by
    intro g
    apply LinearMap.ext
    intro x
    funext s
    change ((fun s η => torusIncidentSite a v η s) *ᵥ
      (regularLegRepresentation (IncidentEdge (torusGraph width height) v) g x)) s =
        ((fun s η => torusIncidentSite a v η s) *ᵥ x) s
    simp only [Matrix.mulVec, dotProduct, regularLegRepresentation_apply]
    change (∑ η, torusIncidentSite a v η s * x (g⁻¹ • η)) =
      ∑ η, torusIncidentSite a v η s * x η
    rw [← Equiv.sum_comp (MulAction.toPermHom G
      (IncidentEdge (torusGraph width height) v → G) g)]
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, inv_smul_smul,
      torusIncidentSite, Pi.smul_apply, smul_eq_mul, ha.torusRegularSite_translation]
  obtain ⟨c, hc, hgram⟩ := ha.exists_torusIncidentSiteGram (width := width) (height := height)
  apply isGIsometric_of_coordinateAdjoint_comp hinv hc
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, LinearMap.toMatrix'_toLin',
    toMatrix_regularSiteMap, map_smul]
  ext η θ
  change (∑ s : Fin d, star (torusIncidentSite a v η s) * torusIncidentSite a v θ s) =
    (c : ℂ) * regularLegProjector (IncidentEdge (torusGraph width height) v) η θ
  rw [hgram, regularLegProjector_apply]
  simp only [div_eq_mul_inv, mul_assoc]

omit [Fintype G] [DecidableEq G] in
/-- The closure assignment is trivial on every nonseam graph edge. -/
theorem torusClosureEdgeAssignment_eq_one_of_nonseam (g h : G)
    (f : Edge (torusGraph width height))
    (hf : (torusNonseamGraph width height).Adj f.1.1 f.1.2) :
    torusClosureEdgeAssignment g h f = 1 := by
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective f
  rcases z with v | v
  · change torusClosureEdgeAssignment g h (torusRightEdge v) = 1
    rw [torusClosureEdgeAssignment_right]
    change (torusNonseamGraph width height).Adj
      (Edge.ofAdj (torusGraph_adj_right v.1 v.2)).1.1
      (Edge.ofAdj (torusGraph_adj_right v.1 v.2)).1.2 at hf
    by_cases hw : v.1 + 1 = 0
    · have hv : (torusNonseamGraph width height).Adj v (v.1 + 1, v.2) := by
        rcases Edge.ofAdj_endpoints (torusGraph_adj_right v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simpa only [h1, h2] using hf
        · simpa only [h1, h2] using hf.symm
      exact False.elim (torusNonseamGraph_not_horizontal_wrap Fact.out v hw hv)
    · simp only [torusHorizontalClosureElement, hw, ite_false, inv_one]
  · change torusClosureEdgeAssignment g h (torusUpEdge v) = 1
    rw [torusClosureEdgeAssignment_up]
    change (torusNonseamGraph width height).Adj
      (Edge.ofAdj (torusGraph_adj_up v.1 v.2)).1.1
      (Edge.ofAdj (torusGraph_adj_up v.1 v.2)).1.2 at hf
    by_cases hw : v.2 + 1 = 0
    · have hv : (torusNonseamGraph width height).Adj v (v.1, v.2 + 1) := by
        rcases Edge.ofAdj_endpoints (torusGraph_adj_up v.1 v.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simpa only [h1, h2] using hf
        · simpa only [h1, h2] using hf.symm
      exact False.elim (torusNonseamGraph_not_vertical_wrap Fact.out v hw hv)
    · simp only [torusVerticalClosureElement, hw, ite_false]

omit [Fintype G] [DecidableEq G] in
/-- The native closure seams have no incident edge in a strictly interior rectangle. -/
theorem torusClosureEdgeAssignment_eq_one_on_rectangle_incident (g h : G)
    (xStart yStart xLen yLen : ℕ) (hxStart : 0 < xStart) (hyStart : 0 < yStart)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height)
    (f : Edge (torusGraph width height))
    (hf : IsRegionIncidentEdge (torusContiguousRectangle xStart yStart xLen yLen) f) :
    torusClosureEdgeAssignment g h f = 1 := by
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective f
  rcases z with v | v
  · change torusClosureEdgeAssignment g h (torusRightEdge v) = 1
    rw [torusClosureEdgeAssignment_right]
    by_cases hw : v.1 + 1 = 0
    · exact False.elim (torusRightEdge_not_incident_rectangle_of_wrap
        xStart yStart xLen yLen hxStart hxEnd v hw hf)
    · simp only [torusHorizontalClosureElement, hw, ite_false, inv_one]
  · change torusClosureEdgeAssignment g h (torusUpEdge v) = 1
    rw [torusClosureEdgeAssignment_up]
    by_cases hw : v.2 + 1 = 0
    · exact False.elim (torusUpEdge_not_incident_rectangle_of_wrap
        xStart yStart xLen yLen hyStart hyEnd v hw hf)
    · simp only [torusVerticalClosureElement, hw, ite_false]

variable {S : Type*} [Fintype S]

/-- A superposition of native closure vectors, expressed in the two physical coordinate
sets of the chosen cut. -/
noncomputable def torusClosureSuperpositionCut
    (a : G → G → G → G → Fin d → ℂ) (p : S → G × G) (w : S → ℂ)
    (R : Finset (TorusVertex width height)) :
    RegionPhysicalConfig (d := d) R × RegionPhysicalConfig (d := d) (Finset.univ \ R) → ℂ :=
  fun q => (∑ s, w s • torusGClosure (leftRegularMatrix G) a (p s).1 (p s).2)
    (assembleRegionσ R q.1 q.2)

/-- The native closure superposition across a cut is the actual twisted graph contraction. -/
theorem torusClosureSuperpositionCut_eq_twistedCutSuperposition
    (a : G → G → G → G → Fin d → ℂ) (p : S → G × G) (w : S → ℂ)
    (R : Finset (TorusVertex width height)) :
    torusClosureSuperpositionCut a p w R =
      regularTwistedPhysicalCutSuperposition (torusIncidentSite a)
        (fun s => torusClosureEdgeAssignment (p s).1 (p s).2) w R := by
  funext q
  simp only [torusClosureSuperpositionCut, regularTwistedPhysicalCutSuperposition,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact torusGClosure_assembleRegion_eq_regularPhysicalCutMatrix a (p s).1 (p s).2 R q.1 q.2

/-- Across a strictly interior rectangle, every nonzero superposition of native regular
torus closures has the same normalized reduced density, of rank \(|G|^{b-1}\), flat nonzero
spectrum, and entropy \((b-1)\log|G|\). Here \(b\) is the actual number of crossing graph
bonds. The rectangle geometry, its nonempty boundary, and all Gram identities follow
from the stated coordinate bounds and local regular isometry. Closure pairs need not
commute for this restricted interior-cut statement. Source: SCP10, the interior rectangular
case of the calculation in Theorem 6.9, proof, lines 2043–2076. -/
theorem exists_normalization_torusClosureSuperpositionCut_rectangle
    (a : G → G → G → G → Fin d → ℂ)
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (p : S → G × G) (xStart yStart xLen yLen : ℕ)
    (hxStart : 0 < xStart) (hyStart : 0 < yStart) (hxPos : 0 < xLen) (hyPos : 0 < yLen)
    (hxEnd : xStart + xLen < width) (hyEnd : yStart + yLen < height) :
    let R := torusContiguousRectangle xStart yStart xLen yLen
    ∃ n : ℕ, Fintype.card {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} =
        n + 1 ∧
      ∃ e : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f} ≃ Fin (n + 1),
        ∃ cA : ℝ, 0 < cA ∧
          (regularOpenRegionMatrix (torusIncidentSite a) R e).conjTranspose *
              regularOpenRegionMatrix (torusIncidentSite a) R e =
            (cA : ℂ) • regularBoundaryProjector (n + 1) ∧
          ∀ w : S → ℂ,
            (∑ s, w s • torusGClosure (width := width) (height := height)
              (leftRegularMatrix G) a (p s).1 (p s).2) ≠ 0 →
            ∃ z : ℝ, 0 < z ∧
              let ψ := (z : ℂ) • torusClosureSuperpositionCut a p w R
              let ρ := partialTraceRight (vecMulVec ψ (star ψ))
              ρ = physicalRegularBoundaryDensity n (normalizedRegularBoundaryMap cA
                  (regularOpenRegionMatrix (torusIncidentSite a) R e)) ∧
                star ψ ⬝ᵥ ψ = 1 ∧ ρ.rank = Fintype.card G ^ n ∧
                ρ * ρ = ((Fintype.card G : ℂ) ^ n)⁻¹ • ρ ∧
                vonNeumannEntropy ρ
                  (posSemidef_vecMulVec_self_star ψ).partialTraceRight.isHermitian =
                    (n : ℝ) * Real.log (Fintype.card G : ℝ) := by
  classical
  let R := torusContiguousRectangle (width := width) (height := height)
    xStart yStart xLen yLen
  let B := {f : Edge (torusGraph width height) // IsRegionBoundaryEdge R f}
  have hB : Nonempty B := nonempty_boundaryEdge_torusRectangle
    xStart yStart xLen yLen hxStart hxPos hyPos hxEnd.le hyEnd.le
  let _ : Nonempty B := hB
  have hb : 0 < Fintype.card B := Fintype.card_pos
  let n := Fintype.card B - 1
  have hn : Fintype.card B = n + 1 := by dsimp [n]; omega
  let e : B ≃ Fin (n + 1) := (Fintype.equivFin B).trans (finCongr hn)
  have hR := torusGraph_rectangle_connected xStart yStart xLen yLen
    hxPos hyPos hxEnd.le hyEnd.le
  have hRc := torusNonseamGraph_compl_rectangle_connected xStart yStart xLen yLen
    (by omega : xLen < width) (by omega : yLen < height)
  obtain ⟨cA, hcA, hM, hall⟩ := exists_normalization_regularTwistedPhysicalCutSuperposition
    n (torusIncidentSite a) (fun v => ha.isGIsometric_torusIncidentSite v) R hR
    (fun s => torusClosureEdgeAssignment (p s).1 (p s).2)
    (fun s f hf => torusClosureEdgeAssignment_eq_one_on_rectangle_incident
      (p s).1 (p s).2 xStart yStart xLen yLen hxStart hyStart hxEnd hyEnd f hf)
    torusNonseamGraph_le_torusGraph hRc
    (fun s f hf _ _ => torusClosureEdgeAssignment_eq_one_of_nonseam (p s).1 (p s).2 f hf) e
  refine ⟨n, hn, e, cA, hcA, hM, ?_⟩
  intro w hne
  have hcut := torusClosureSuperpositionCut_eq_twistedCutSuperposition a p w R
  have hcutne : torusClosureSuperpositionCut a p w R ≠ 0 := by
    intro hzero
    apply hne
    funext σ
    have h := congrFun hzero ((fun v => σ v.1), (fun v => σ v.1))
    have hglue : assembleRegionσ R (fun v => σ v.1) (fun v => σ v.1) = σ := by
      funext v
      simp only [assembleRegionσ]
      split_ifs <;> rfl
    simpa only [torusClosureSuperpositionCut, hglue, Pi.zero_apply] using h
  obtain ⟨z, hz, hresult⟩ := hall w (by rwa [← hcut])
  exact ⟨z, hz, by simpa only [← hcut] using hresult⟩

end TNLean.PEPS
