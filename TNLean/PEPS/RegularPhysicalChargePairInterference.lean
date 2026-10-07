/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularPhysicalChargePairCreation
import TNLean.PEPS.RegularWeightedOpenContraction
import TNLean.Algebra.ScaledProjectionTransport

/-!
# Return measurement on the original physical charge-pair block

The original local isometries induce a complete binary projection measurement.
Its accepted column is the initial correlated charge column multiplied by the
dimension-normalized character. All boundary labels remain in the literal
weighted open contraction; no global state decomposition is assumed.

Source: SCP10, arXiv:1001.3807, the interference calculation, lines 2582–2615.
This auxiliary statement uses a finite block with a specified tree and two
distinct internal bonds. It does not assert a completed geometric braid.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- A complete return measurement is chosen before the flux and every actual
boundary label. Both accepted and rejected actions follow from the original
physical maps. Source: SCP10, interference measurement, lines 2582–2615. -/
theorem exists_regularPhysicalChargePairReturnMeasurement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (σ : Representation ℂ G H) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V) (T : SimpleGraph (RV R))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e₀ e₁ : RI (Γ := Γ) R) (hne : e₀ ≠ e₁) (p : G) :
    ∃ Q : Bool → Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
      (∀ b r, Q b * Q r = if b = r then Q b else 0) ∧ (∑ b, Q b) = 1 ∧
      ∀ (k : G) (θ : RB (Γ := Γ) R → G),
        let ψ := regularWeightedOpenRegionWeight a R (fun _ => 1)
          (fun η => σ.character (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * k⁻¹ *
            η ⟨e₀.1,Or.inl e₀.2.1⟩)) θ
        let φ := (σ.character k⁻¹ / Module.finrank ℂ H) •
          (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ σ.character p s θ)
        Q true *ᵥ ψ = φ ∧ Q false *ᵥ ψ = ψ - φ := by
  classical
  let : DecidableRel T.Adj := Classical.decRel _
  let A := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let P := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))
  let D := regularRegionChargeReferenceMatrix R T hT htree o e₀ e₁ hne
    (regularChargePairReturnProjection σ.character p)
  obtain ⟨c,hc,hGram⟩ := exists_positive_regionPhysicalProductMatrix_gram a ha R
  have hAP : A * P = A := regionPhysicalProductMatrix_mul_regularLocalProjector
    a (fun v => (ha v).toIsGInjective) R
  have hDh : D.IsHermitian := regularRegionChargeReferenceMatrix_isHermitian
    R T hT htree o e₀ e₁ hne _ (regularChargePairReturnProjection_conjTranspose _ _)
  have hDI : D * D = D := regularRegionChargeReferenceMatrix_mul_self
    R T hT htree o e₀ e₁ hne _ (regularChargePairReturnProjection_mul_self σ hσ p)
  have hcomm : D * P = P * D :=
    (regularRegionChargeReferenceMatrix_commute_localProjector R T hT htree o
      e₀ e₁ hne _ (regularChargePairReturnProjection_commute σ.character p)).eq
  obtain ⟨Q,hh,hi,hs,_,hQA,_⟩ :=
    Matrix.exists_binaryProjectionFamily_transport A P D c hc hGram hAP hcomm hDh hDI
  refine ⟨Q,hh,hi,hs,?_⟩
  intro k θ
  have htrue : Q true *ᵥ regularWeightedOpenRegionWeight a R (fun _ => 1)
      (fun η => σ.character (p * (η ⟨e₁.1,Or.inl e₁.2.1⟩)⁻¹ * k⁻¹ *
        η ⟨e₀.1,Or.inl e₀.2.1⟩)) θ =
    (σ.character k⁻¹ / Module.finrank ℂ H) •
      (fun s => regularChargePairOpenRegionMatrix a R e₀ e₁ σ.character p s θ) := by
    rw [← regionPhysicalMap_regularProjectorWeightedTwistedRegionMatrix a
      (fun v => (ha v).toIsGInjective)]
    change Q true *ᵥ (A *ᵥ _) = _
    rw [Matrix.mulVec_mulVec, hQA, ← Matrix.mulVec_mulVec,
      regularRegionChargeReferenceMatrix_mulVec_braided R T σ hσ hT htree o
        e₀ e₁ hne p k θ, Matrix.mulVec_smul]
    rw [regularChargePairOpenRegionMatrix_eq_image a
      (fun v => (ha v).toIsGInjective)]
  have hfalse : Q false = 1 - Q true := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [Fintype.sum_bool, add_comm] using hs
  refine ⟨htrue,?_⟩
  rw [hfalse, Matrix.sub_mulVec, Matrix.one_mulVec, htrue]

end TNLean.PEPS
