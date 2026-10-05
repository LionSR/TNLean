import TNLean.PEPS.TorusMatchedCutClosureMembership

/-! Regression checks for independently matched native torus bond representations. -/

open TNLean.PEPS
open scoped BigOperators Kronecker

section IndependentBonds

variable {G V Phys : Type*} [Group G] [Fintype V] [DecidableEq V]

-- Period two keeps the opposite parallel bond's representation on each incident leg.
example (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ) (g : G) :
    torusMatchedLegMatrix Uh Uv (0, 0) g =
      Uv (0, 0) g ⊗ₖ ((Uh (0, 0) g⁻¹).transpose ⊗ₖ
        ((Uv (0, 1) g⁻¹).transpose ⊗ₖ Uh (1, 0) g)) := by
  simp [torusMatchedLegMatrix]

-- Every bond family and every physical tensor remains an independent parameter.
-- Neither group finiteness nor bond semi-regularity is needed for this inclusion.
example (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v)) :
    matchedCommutingClosureSpan Uh Uv a ≤ fourTorusCutSpace a :=
  matchedCommutingClosureSpan_le_fourTorusCutSpace Uh Uv a ha

-- The boundary witness uses the crossed bonds' own representations.
example (Uh Uv : TorusVertex 2 2 → G →* Matrix V V ℂ)
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v g, siteMap (a v) ∘ₗ torusMatchedLegRep Uh Uv v g = siteMap (a v))
    (g h : G) (hgh : Commute g h) (c r : ZMod 2) :
    torusCutMap a c r (torusCutBondBoundary c r (fun v ↦ Uh v h) (fun v ↦ Uv v g)) =
      matchedTorusGClosure Uh Uv a g h :=
  torusCutMap_matchedClosureBoundary Uh Uv a ha g h hgh c r

variable [Fintype G]

-- The actual contraction expansion also includes the one-by-one torus's self bonds.
example (Uh Uv : TorusVertex 1 1 → G →* Matrix V V ℂ)
    (σ : TorusVertex 1 1 → V × V × V × V)
    (Oh Ov : TorusVertex 1 1 → Matrix V V ℂ) :
    torusBondNetwork
        (fun v c ↦ representationAveragingSite (torusMatchedLegRep Uh Uv v)
          c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v)) Oh Ov =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card (TorusVertex 1 1) *
        ∑ q : TorusVertex 1 1 → G, ∏ v,
          (Uh v (q (v.1 + 1, v.2)) * Oh v * Uh v ((q v)⁻¹))
            (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
          (Uv v (q v) * Ov v * Uv v ((q (v.1, v.2 + 1))⁻¹))
            (σ v).1 (σ (v.1, v.2 + 1)).2.2.1 :=
  torusBondNetwork_representationAveragingSite Uh Uv σ Oh Ov

end IndependentBonds

set_option linter.hashCommand false

#print axioms TNLean.PEPS.torusBondNetwork_legGauge
#print axioms TNLean.PEPS.torusBondNetwork_matchedVertexGauge
#print axioms TNLean.PEPS.torusBondNetwork_representationAveragingSite
#print axioms TNLean.PEPS.torusBondNetwork_matchedClosureAt_eq_matchedTorusGClosure
#print axioms TNLean.PEPS.torusCutMap_matchedClosureBoundary
#print axioms TNLean.PEPS.matchedCommutingClosureSpan_le_fourTorusCutSpace
