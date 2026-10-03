/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusThreePlaquetteFluxGeometry
import TNLean.PEPS.RegularThreePlaquetteDoubleExchange
import TNLean.PEPS.RegularTorusEntropy

/-!
# A double exchange on an actual eight-spin torus strip

The three literal upward transports are changed by a fixed original-spin
unitary on the actual translated four-column, two-row region. The same
unitary acts on every regional column and its identity extension acts on
every actual global contraction with common arbitrary exterior and crossing
operators. The surrounding flux product is unchanged.

Source: SCP10, arXiv:1001.3807, braiding passage, lines 2360–2415.

**Scope restriction (auxiliary double exchange):** Horizontal period at least
five and vertical period at least three, with regular four-leg G-isometry.
All starting positions and both seams are included. This constructed operation
realizes the double Hurwitz exchange of the three plaquette coordinates;
identification with prescribed physical string braiding and any
parent-Hamiltonian interpretation remain separate. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G]

/-- The directed vertical transports after the double exchange. Auxiliary
finite-strip operation for SCP10, braiding passage, lines 2360–2415. -/
def torusThreePlaquetteDoubleExchangeTransports (t : Fin 3 → G) : Fin 3 → G :=
  ![t 0, t 2 * (t 0)⁻¹ * t 1 * (t 2)⁻¹ * t 0, t 2]

private def sparseLabels {J : Type*} [DecidableEq J] (reversed : Bool)
    (e₀ e₁ e₂ : J) (t : Fin 3 → G) (e : J) : G :=
  let k := fun g : G => if reversed then g⁻¹ else g
  if e = e₀ then k (t 0) else if e = e₁ then k (t 1)
  else if e = e₂ then k (t 2) else 1

private theorem exchange_sparse {J : Type*} [DecidableEq J] (reversed : Bool)
    (e₀ e₁ e₂ : J) (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂)
    (t : Fin 3 → G) :
    regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
      (sparseLabels reversed e₀ e₁ e₂ t) =
      sparseLabels reversed e₀ e₁ e₂ (torusThreePlaquetteDoubleExchangeTransports t) := by
  apply (regularCycleOrientation (J := J) (G := G) reversed).injective
  apply (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).injective
  rw [regularOrientedThreePlaquetteDoubleExchange_coordinates]
  funext e
  by_cases h₀ : e = e₀
  · subst e
    rw [(regularTwoCycleExchange_twice_apply e₀ e₁ h₀₁ _).1]
    cases reversed <;>
      simp [regularThreeCyclePlaquetteCoordinates, regularCycleOrientation, sparseLabels,
        Ne.symm h₀₁, Ne.symm h₀₂, Ne.symm h₁₂,
        torusThreePlaquetteDoubleExchangeTransports] <;> group
  · by_cases h₁ : e = e₁
    · subst e
      rw [(regularTwoCycleExchange_twice_apply e₀ e₁ h₀₁ _).2]
      cases reversed <;>
        simp [regularThreeCyclePlaquetteCoordinates, regularCycleOrientation, sparseLabels,
          Ne.symm h₀₁, Ne.symm h₀₂, Ne.symm h₁₂,
          torusThreePlaquetteDoubleExchangeTransports] <;> group
    · rw [regularTwoCycleExchange_apply_other _ _ _ _ _ h₀ h₁,
        regularTwoCycleExchange_apply_other _ _ _ _ _ h₀ h₁]
      cases reversed <;>
        simp [regularThreeCyclePlaquetteCoordinates, regularCycleOrientation, sparseLabels,
          h₀, h₁, Ne.symm h₀₂, Ne.symm h₁₂,
          torusThreePlaquetteDoubleExchangeTransports]

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (2 < height)]
local instance threeExchangeWidthThree : Fact (3 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeExchangeWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeExchangeWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance threeExchangeHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
/-- The literal output has the double-exchanged plaquette holonomies and the
corresponding surrounding middle-right flux. Auxiliary finite-strip identity
for SCP10, braiding passage, lines 2360–2415. -/
theorem regularWalkHolonomy_torusThreePlaquetteDoubleExchange (v : X) (t : Fin 3 → G) :
    let a := (t 0)⁻¹ * t 1
    let b := (t 1)⁻¹ * t 2
    let c := (t 2)⁻¹
    let u := torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)
    regularWalkHolonomy u (torusPlaquetteWalk v) = (a * b) * a * (a * b)⁻¹ ∧
      regularWalkHolonomy u (torusPlaquetteWalk (v.1 + 1, v.2)) = a * b * a⁻¹ ∧
      regularWalkHolonomy u (torusPlaquetteWalk (v.1 + 2, v.2)) = c ∧
      regularWalkHolonomy u (torusTwoPlaquetteOuterWalk (v.1 + 1, v.2)) = a * b * a⁻¹ * c := by
  have h := regularWalkHolonomy_torusThreePlaquetteFluxAssignment v
    (torusThreePlaquetteDoubleExchangeTransports t)
  dsimp only
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  simp only [torusThreePlaquetteDoubleExchangeTransports, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  refine ⟨?_, ?_, True.intro, ?_⟩ <;> group

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- One original eight-spin unitary effects the literal double exchange on every
actual regional column and every global state with common exterior operators.
The same unitary is chosen before all transports and boundary configurations.
Auxiliary realization for SCP10, braiding passage, lines 2360–2415. -/
theorem IsGIsometric.exists_unitary_torusThreePlaquetteDoubleExchange
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    let R := translatedThreePlaquetteRegion v
    let A := torusIncidentSite (width := width) (height := height) a
    ∃ W : Matrix ({x : X // x ∈ R} → Fin d) ({x : X // x ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({x : X // x ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      (∀ (t : Fin 3 → G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite A
          (torusThreePlaquetteFluxAssignment v t))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite A
          (torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t)))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (t : Fin 3 → G) (u : Edge Γₜ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite A
          (regularRegionBondExtension R (torusThreePlaquetteFluxAssignment v t) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite A
          (regularRegionBondExtension R
            (torusThreePlaquetteFluxAssignment v (torusThreePlaquetteDoubleExchangeTransports t))
            u))) := by
  classical
  let R := translatedThreePlaquetteRegion v
  let T := translatedThreePlaquetteTree v
  let c := translatedThreePlaquetteCycleBond v
  have h₀₁ : c 0 ≠ c 1 := (translatedThreePlaquetteCycleBond_injective v).ne (by decide)
  have h₀₂ : c 0 ≠ c 2 := (translatedThreePlaquetteCycleBond_injective v).ne (by decide)
  have h₁₂ : c 1 ≠ c 2 := (translatedThreePlaquetteCycleBond_injective v).ne (by decide)
  let reversed := decide (¬ v.2.val < (v.2 + 1).val)
  let ω := sparseLabels (G := G) reversed (c 0) (c 1) (c 2)
  have htree (t : Fin 3 → G) : torusThreePlaquetteFluxAssignment v t =
      regularTreeCycleAssignment R T (ω t) := by
    rw [torusThreePlaquetteFluxAssignment_eq_treeCycleAssignment]
    congr 1
    funext e
    by_cases hd : v.2.val < (v.2 + 1).val <;>
      simp [ω, sparseLabels, reversed, hd, c]
  obtain ⟨W, hW, hWU, hlocal, hglobal⟩ :=
    exists_unitary_regularOrientedThreePlaquetteDoubleExchange R T
      (torusIncidentSite (width := width) (height := height) a)
      (fun x => ha.isGIsometric_torusIncidentSite x)
      (translatedThreePlaquetteTree_le v) (translatedThreePlaquetteTree_isTree v)
      (translatedThreePlaquetteVertexEquiv v 0) reversed (c 0) (c 1) (c 2) h₀₁ h₀₂ h₁₂
  refine ⟨W, hW, hWU, ?_, ?_⟩
  · intro t θ
    rw [htree t, htree (torusThreePlaquetteDoubleExchangeTransports t)]
    have h := hlocal (ω t) θ
    rw [exchange_sparse reversed (c 0) (c 1) (c 2) h₀₁ h₀₂ h₁₂ t] at h
    exact h
  · intro t u
    rw [htree t, htree (torusThreePlaquetteDoubleExchangeTransports t)]
    have h := hglobal (ω t) u
    rw [exchange_sparse reversed (c 0) (c 1) (c 2) h₀₁ h₀₂ h₁₂ t] at h
    exact h

end TNLean.PEPS
