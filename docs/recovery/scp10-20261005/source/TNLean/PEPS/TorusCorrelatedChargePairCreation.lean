/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCorrelatedChargeGlobalCreation
import TNLean.PEPS.TorusPhysicalChargePairCreation
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.RegularTwistedStateNonzero

/-!
# Six-site creation of the actual global correlated charge pair

The existing six-spin unitary acts on the full native PEPS contraction, with
arbitrary exterior bond operators and no supplied exterior factorization.

Source: SCP10, arXiv:1001.3807, charge-pair creation, lines 2505–2558.
**Scope restriction (finite torus and regular action):** The horizontal period
is at least three and the vertical period at least four. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (3 < height)]
local instance : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
private abbrev R (v : X) := verticalTwoPlaquetteRegion v
private abbrev e₀ (v : X) := (verticalTwoPlaquetteCycleBond v 0).1
private abbrev e₁ (v : X) := (verticalTwoPlaquetteCycleBond v 1).1
private abbrev A (a : G → G → G → G → Fin d → ℂ) :=
  torusIncidentSite (width := width) (height := height) a

/-- A unitary on six original spins creates the actual globally contracted
correlated charge pair while retaining the exterior background operators.
Source: SCP10, lines 2505–2558. -/
theorem IsGIsometric.exists_unitary_torusCorrelatedChargePairCreation
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X)
    (u : Edge Γₜ → G) (hu : ∀ e : Edge Γₜ, e.1.2 ∈ R v → u e = 1)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    ∃ W : Matrix ({w : X // w ∈ R v} → Fin d) ({w : X // w ∈ R v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup _ ℂ ∧
      regionLocalTerm (R v) W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      regionLocalTerm (R v) W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite (A a) u)) =
        regularCorrelatedChargeState (A a) u (e₀ v).1 (e₁ v).1 χ p 1 := by
  obtain ⟨W, hW, hcols⟩ := ha.exists_unitary_torusPhysicalChargePairCreation v χ hχ p
  refine ⟨W, hW, regionLocalTerm_mem_unitaryGroup (R v) W hW, ?_⟩
  exact regionLocalTerm_mulVec_regularCorrelatedChargeCreation (A a) (R v) u
    (regularTwistedSite_eq_on_of_head_eq_one (A a) (R v) u hu)
    (e₀ v) (e₁ v) χ p W hcols

/-- The actually prepared full charge-pair state is nonzero, including an
arbitrary exterior flux background. Source: SCP10, normalization of the prepared
state in lines 2594–2603; auxiliary nonvanishing. -/
theorem IsGIsometric.torusCorrelatedChargePairState_ne_zero
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X)
    (u : Edge Γₜ → G) (hu : ∀ e : Edge Γₜ, e.1.2 ∈ R v → u e = 1)
    (χ : G → ℂ) (hχ : χ ∈ regularChargeLabels (G := G)) (p : G) :
    regularCorrelatedChargeState (A a) u (e₀ v).1 (e₁ v).1 χ p 1 ≠ 0 := by
  obtain ⟨W, _, hW, hact⟩ := ha.exists_unitary_torusCorrelatedChargePairCreation v u hu χ hχ p
  intro hz
  have h := congrArg (fun ψ => (regionLocalTerm (R v) W).conjTranspose *ᵥ ψ) hact
  have hgram : (regionLocalTerm (R v) W).conjTranspose * regionLocalTerm (R v) W = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hW
  rw [Matrix.mulVec_mulVec, hgram, Matrix.one_mulVec, hz, Matrix.mulVec_zero] at h
  exact ha.stateCoeff_torusRegularTwistedSite_ne_zero u h

end TNLean.PEPS
