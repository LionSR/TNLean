/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTranslatedFluxMove
import TNLean.PEPS.RegularGaugedCyclePhysicalPermutation

/-!
# Horizontal flux movement with a common tree background

A fixed original-spin operation moves the two native horizontal plaquette fluxes
while both internal assignments are reconstructed from the same vertex gauge.
Its adjoint reverses the movement. All exterior and crossing operators remain
literally unchanged, so the same boundary transport applies on both sides.

Source: SCP10, arXiv:1001.3807, accessible coordinates, lines 1765–1920, and
Theorem 6.16, lines 2271–2305.

**Scope restriction (finite torus and regular action):** The actual three-by-two
block requires width at least four and height at least three. Both periodic
seams are included. This common-background operation does not compare distinct
crossing presentations or establish the prescribed four-endpoint braid. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance gaugedHorizontalWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance gaugedHorizontalWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance gaugedHorizontalHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev R (v : X) := translatedTwoPlaquetteRegion v
private abbrev T (v : X) := translatedTwoPlaquetteTree v
private abbrev RV (v : X) := {x : X // x ∈ R v}
variable {G : Type*} [Group G]

/-- Reconstruct the literal horizontal movement insertion from a common vertex gauge.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
def torusGaugedHorizontalFluxAssignment (v : X) (k : RV v → G)
    (extend : Bool) (g : G) (e : Edge Γₜ) : G :=
  if h : e.1.1 ∈ R v ∧ e.1.2 ∈ R v then
    k ⟨e.1.2, h.2⟩ * torusTranslatedFluxAssignment v extend g e * (k ⟨e.1.1, h.1⟩)⁻¹
  else 1

/-- Identity reconstruction recovers the literal insertion, including its seam
inversion. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem torusGaugedHorizontalFluxAssignment_one (v : X) (extend : Bool) (g : G) :
    torusGaugedHorizontalFluxAssignment v (fun _ => 1) extend g =
      torusTranslatedFluxAssignment v extend g := by
  classical
  funext e
  simp only [torusGaugedHorizontalFluxAssignment, one_mul, inv_one, mul_one]
  split_ifs with h
  · rfl
  · have hc := congrFun (torusTranslatedFluxAssignment_eq_treeCycleAssignment v extend g) e
    rw [hc]
    simp only [regularTreeCycleAssignment]
    by_cases ht : e.1.1 ∈ R v
    · have hh : e.1.2 ∉ R v := fun hh => h ⟨ht, hh⟩
      simp only [dite_eq_left ht, dite_eq_right hh]
    · simp only [dite_eq_right ht]

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- One original six-spin unitary moves right; its adjoint moves left,
before every common gauge, flux, boundary, and literal exterior assignment.
Source: SCP10, accessible operations and horizontal movement in Theorem 6.16,
lines 1765–1920 and 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusGaugedHorizontalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix (RV v → Fin d) (RV v → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV v → Fin d) ℂ ∧
      regionLocalTerm (R v) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (k : RV v → G) (reverse : Bool) (g : G) (u : Edge Γₜ → G)
        (θ : {e : Edge Γₜ // IsRegionBoundaryEdge (R v) e} → G),
        (if reverse then W.conjTranspose else W) *ᵥ
          openRegionWeight (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R v)
              (torusGaugedHorizontalFluxAssignment v k reverse g) u))) (R v)
            (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v)
            (torusGaugedHorizontalFluxAssignment v k (!reverse) g) u))) (R v)
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (k : RV v → G) (reverse : Bool) (g : G) (u : Edge Γₜ → G),
        (if reverse then (regionLocalTerm (R v) W).conjTranspose
          else regionLocalTerm (R v) W) *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
            (torusIncidentSite (width := width) (height := height) a)
            (regularRegionBondExtension (R v)
              (torusGaugedHorizontalFluxAssignment v k reverse g) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension (R v)
            (torusGaugedHorizontalFluxAssignment v k (!reverse) g) u))) := by
  classical
  let e₀ := translatedTwoPlaquetteCycleBond v 0
  let e₁ := translatedTwoPlaquetteCycleBond v 1
  have hne : e₀ ≠ e₁ := (translatedTwoPlaquetteCycleBond_injective v).ne (by decide)
  let ω := fun b : Bool => fun g : G => fun e =>
    if e = e₀ ∨ (b = true ∧ e = e₁)
    then (if v.2.val < (v.2+1).val then g else g⁻¹) else 1
  have hm (g : G) : regularTwoCycleMove e₀ e₁ hne (ω false g) = ω true g := by
    simpa [ω] using regularTwoCycleMove_single e₀ e₁ hne
      (if v.2.val < (v.2+1).val then g else g⁻¹)
  have hc (b : Bool) (g : G) : regularTreeCycleAssignment (R v) (T v) (ω b g) =
      torusTranslatedFluxAssignment v b g :=
    (torusTranslatedFluxAssignment_eq_treeCycleAssignment v b g).symm
  have hg (k : RV v → G) (b : Bool) (g : G) :
      regularGaugedTreeCycleAssignment (R v) (T v) k (ω b g) =
        torusGaugedHorizontalFluxAssignment v k b g := by
    funext e
    simp only [regularGaugedTreeCycleAssignment, torusGaugedHorizontalFluxAssignment, hc]
  obtain ⟨W, hW, hglobal, hlocal, hact⟩ :=
    exists_unitary_regularGaugedCyclePhysicalPermutation (R v) (T v)
      (torusIncidentSite (width := width) (height := height) a)
      (fun x => ha.isGIsometric_torusIncidentSite x)
      (translatedTwoPlaquetteTree_le v) (translatedTwoPlaquetteTree_isTree v)
      (translatedTwoPlaquetteIso v 0) (regularTwoCycleMove e₀ e₁ hne)
      (regularTwoCycleMove_conjugation e₀ e₁ hne)
  have hWgram : W.conjTranspose * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  have hUgram : (regionLocalTerm (R v) W).conjTranspose *
      regionLocalTerm (R v) W = 1 := Matrix.mem_unitaryGroup_iff'.mp hglobal
  refine ⟨W, hW, hglobal, ?_, ?_⟩
  · intro k reverse g u θ
    have h := hlocal k (ω false g) u θ
    rw [hm, hg, hg] at h
    cases reverse
    · exact h
    · change W.conjTranspose *ᵥ _ = _
      rw [← h, Matrix.mulVec_mulVec, hWgram, Matrix.one_mulVec]
      rfl
  · intro k reverse g u
    have h := hact k (ω false g) u
    rw [hm, hg, hg] at h
    cases reverse
    · exact h
    · change (regionLocalTerm (R v) W).conjTranspose *ᵥ _ = _
      rw [← h, Matrix.mulVec_mulVec, hUgram, Matrix.one_mulVec]
      rfl

end TNLean.PEPS
