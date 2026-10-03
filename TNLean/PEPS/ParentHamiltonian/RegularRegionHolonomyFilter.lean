/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionFlatness

/-!
# Linear holonomy filters for regular G-injective regions

A diagonal identity-holonomy detector in accessible regular coordinates can be
transported through local G-injective inverses. The resulting physical linear
operator fixes every original regional ground vector. On a regional ground
vector with inserted bonds, it is the identity or zero according as the chosen
closed-walk holonomy is the identity or not. No G-isometry is required, and no
Hermitian or positivity assertion is made for this linear operator.

**Scope restriction (regular local filters):** The virtual coordinates are
regular group labels. These auxiliary closed-walk filters do not classify the
full parent kernel; the missing identification is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, arXiv:1001.3807, the closure constraints in Theorem 5.5,
lines 1440–1514, and accessible-coordinate calculation, lines 1765–1920.
This is an auxiliary regular closed-walk statement, rather than a complete
classification of the torus parent kernel.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private noncomputable def identityDetector (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  Matrix.diagonal fun α =>
    if f (regularRegionCoordinatesEquiv R T hT htree o α).2.2.2 = 1 then 1 else 0

private theorem identityDetector_twistedRegion (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G)
    (hf : ∀ z x, f (fun e => x * z e * x⁻¹) = x * f z * x⁻¹) (u : Edge Γ → G) :
    identityDetector R T hT htree o f * regularProjectorTwistedRegionMatrix R u =
      (if f (regularRegionTreeCycleResidual R T hT htree o u) = 1
        then (1 : ℂ) else 0) • regularProjectorTwistedRegionMatrix R u := by
  classical
  ext α θ
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let c := E α
  have hα : E.symm c = α := E.symm_apply_apply α
  simp only [identityDetector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← hα, regularProjectorTwistedRegionMatrix_coordinates]
  rw [show regularRegionCoordinatesEquiv R T hT htree o (E.symm c) = c from
    E.apply_symm_apply c]
  rw [mul_left_comm _ ((Fintype.card G : ℂ)⁻¹ ^ R.card),
    mul_left_comm _ ((Fintype.card G : ℂ)⁻¹ ^ R.card)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.1 = x • regularRegionBoundaryTransport R
      (regularRegionTreeGauge R T hT htree o u).1 u θ ∧
      c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
  · have hk : f c.2.2.2 = 1 ↔
        f (regularRegionTreeCycleResidual R T hT htree o u) = 1 := by
      rw [h.2, hf, conj_eq_one_iff]
    simp only [hk]
  · simp only [h, ↓reduceIte, mul_zero]

variable {d : ℕ}

/-- A physical linear filter separates identity from nonidentity holonomy on
all actual inserted regional ground spaces, while fixing the original one.
Source: SCP10, Theorem 5.5 and accessible coordinates, lines 1440–1514 and
1765–1920; auxiliary regular closed-walk form, without G-isometry. -/
theorem exists_regularClosedWalkIdentityFilter
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (o : {v : V // v ∈ R}) (p : (Γ.induce (R : Set V)).Walk o o) :
    ∃ Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      (∀ ψ ∈ regionGroundSpace (groupBondTensor a) R, Q *ᵥ ψ = ψ) ∧
      ∀ (u : Edge Γ → G) (ψ : RegionPhysicalConfig (d := d) R → ℂ),
        ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R →
        Q *ᵥ ψ = if regularWalkHolonomy (regularRegionInternalOperators R u) p = 1
          then ψ else 0 := by
  classical
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  choose F hF using fun v => (ha v).exists_regularProjectorCoefficients
  let f : (RegionCycleEdge (Γ := Γ) R T → G) → G :=
    fun z => FreeGroup.lift z (regularRegionCycleWord R T p)
  let D := identityDetector R T hT htree o f
  let A := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let B := regionPhysicalProductMatrix R F
  let Q := A * D * B
  have heigen (u : Edge Γ → G) (ψ : RegionPhysicalConfig (d := d) R → ℂ)
      (hψ : ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a u)) R) :
      Q *ᵥ ψ = if regularWalkHolonomy (regularRegionInternalOperators R u) p = 1
        then ψ else 0 := by
    let z : ℂ := if regularWalkHolonomy (regularRegionInternalOperators R u) p = 1
      then 1 else 0
    have hD : D * regularProjectorTwistedRegionMatrix R u =
        z • regularProjectorTwistedRegionMatrix R u := by
      simpa only [D, f, z, regularRegionCycleWord_eval_rootLoop R T hT htree o] using
        identityDetector_twistedRegion R T hT htree o f
          (fun z x => regularRegionCycleWord_eval_conj R T z x p) u
    obtain ⟨χ, hχ⟩ := regionPhysicalMap_mem_regularProjectorTwistedRange a F hF R u hψ
    have hmul : D *ᵥ (B *ᵥ ψ) = z • (B *ᵥ ψ) := by
      change D *ᵥ regionPhysicalMap R F ψ = z • regionPhysicalMap R F ψ
      rw [← hχ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hD,
        Matrix.smul_mulVec]
    have hrec : A *ᵥ (B *ᵥ ψ) = ψ :=
      regionPhysicalMap_leftInverse_on_regularGroundSpace a ha F hF R u hψ
    change (A * D * B) *ᵥ ψ = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmul,
      Matrix.mulVec_smul, hrec]
    simp only [z]
    split_ifs <;> simp only [one_smul, zero_smul]
  refine ⟨Q, ?_, heigen⟩
  intro ψ hψ
  have hspaces := regionGroundSpace_regularTwisted_eq_of_internalGaugeFlat a
    (fun g v η s => (ha v).regularSiteMap_translation g η s)
    R (fun _ => 1) (fun _ => 1) (by intro e; simp [regularRegionGaugeResidual])
  have hψ' : ψ ∈ regionGroundSpace (groupBondTensor (regularTwistedSite a (fun _ => 1))) R := by
    rwa [hspaces]
  have hone : regularWalkHolonomy (regularRegionInternalOperators R (fun _ => (1 : G))) p = 1 := by
    have h : ∀ {v w} (q : (Γ.induce (R : Set V)).Walk v w),
        regularWalkHolonomy (regularRegionInternalOperators R (fun _ => (1 : G))) q = 1 := by
      intro v w q
      induction q with
      | nil => rfl
      | cons hxy q ih =>
        simp only [regularWalkHolonomy_cons, ih, regularDirectedTransport,
          regularRegionInternalOperators, inv_one, ite_self, one_mul]
    exact h p
  simpa only [hone, ↓reduceIte] using heigen (fun _ => 1) ψ hψ'


/-- The regional identity-holonomy filter fixes every global vector satisfying
the original parent constraint and selects precisely the inserted closed
states with identity holonomy. Source: SCP10, the local closure constraints
in Theorem 5.5, lines 1440–1514; auxiliary linear filter form. -/
theorem exists_regularClosedWalkGlobalIdentityFilter
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (o : {v : V // v ∈ R}) (p : (Γ.induce (R : Set V)).Walk o o) :
    ∃ Q : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      (∀ (P : Matrix (RegionPhysicalConfig (d := d) R)
          (RegionPhysicalConfig (d := d) R) ℂ)
        (Ψ : (V → Fin d) → ℂ),
        IsRegionParentInteraction (groupBondTensor a) R P →
        regionLocalTerm R P *ᵥ Ψ = 0 → regionLocalTerm R Q *ᵥ Ψ = Ψ) ∧
      ∀ u : Edge Γ → G,
        regionLocalTerm R Q *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a u)) =
          if regularWalkHolonomy (regularRegionInternalOperators R u) p = 1
          then stateCoeff (groupBondTensor (regularTwistedSite a u)) else 0 := by
  classical
  obtain ⟨Q, hfix, heigen⟩ := exists_regularClosedWalkIdentityFilter a ha R hR o p
  refine ⟨Q, ?_, ?_⟩
  · intro P Ψ hP hΨ
    have hslices := (regionLocalTerm_mulVec_eq_zero_iff (groupBondTensor a) R hP Ψ).mp hΨ
    funext η
    obtain ⟨⟨σ, τ⟩, rfl⟩ := (regionConfigEquiv (d := d) R).symm.surjective η
    change (regionLocalTerm R Q *ᵥ Ψ) (assembleRegionσ R σ τ) = _
    rw [regionLocalTerm_mulVec_assemble]
    exact congrFun (hfix _ (hslices τ)) σ
  · intro u
    funext η
    obtain ⟨⟨σ, τ⟩, rfl⟩ := (regionConfigEquiv (d := d) R).symm.surjective η
    change (regionLocalTerm R Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite a u))) (assembleRegionσ R σ τ) = _
    rw [regionLocalTerm_mulVec_assemble]
    simpa only [ite_apply, Pi.zero_apply, regionConfigEquiv, Equiv.coe_fn_symm_mk] using congrFun
      (heigen u _ (stateCoeff_slice_mem_regionGroundSpace _ R τ)) σ

end TNLean.PEPS
