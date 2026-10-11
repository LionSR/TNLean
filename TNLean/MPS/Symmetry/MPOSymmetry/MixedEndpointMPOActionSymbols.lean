/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointTripleMaps
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusionMaps
import TNLean.MPS.MPDO.BoundaryActionLMatrix
import TNLean.MPS.MPDO.BoundaryActionTreeEntries

/-!
# The actual mixed action maps inherit the endpoint L symbols

The sequential-analysis/fusion-synthesis contraction of the chosen mixed
maps is the direct sum of the endpoint contractions. Consequently its raw
L matrix is the bond-dimension-weighted endpoint mean. Equal chosen endpoint
L matrices give that same L matrix for the mixed action maps.

The maps are precisely the parameter-independent action maps of the actual
mixed interpolation. The result therefore includes both endpoints of the
path; no injectivity of the mixed endpoint state is invoked. Empty
multiplicity spaces and zero endpoint bond dimensions are retained. The
common-value result also covers a zero total dimension, when both raw
matrices vanish.

Source: GLM23, `Agammasym` and `REsubmission.tex`, lines 1667--1685. The
source orientation is sequential rows `(z,i,j)` and fusion columns `(c,k,μ)`.
Gauge-class alignment is separate from equality of chosen raw symbols.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

variable {r D₀ D₁ : ℕ} {χ₀ χ₁ : Fin r → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {m : Fin r → ℕ}
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a, Fin (m a) → Matrix (Fin D₀) (Fin (χ₀ a * D₀)) ℂ)
  (WA₀ : ∀ a, Fin (m a) → Matrix (Fin (χ₀ a * D₀)) (Fin D₀) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a, Fin (m a) → Matrix (Fin D₁) (Fin (χ₁ a * D₁)) ℂ)
  (WA₁ : ∀ a, Fin (m a) → Matrix (Fin (χ₁ a * D₁)) (Fin D₁) ℂ)

/-- The actual sequential analysis retains only matching endpoint sectors
on all three incoming virtual legs. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpoint_sequentialActionAnalysis (a b : Fin r)
    (p : MPOTensor.SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0) :
    (MPOTensor.sequentialActionAnalysis
      (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i)) a b 0
      (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩)).submatrix finSumFinEquiv
        (mixedEndpointTripleEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b) D₀ D₁) =
      mixedEndpointTripleAnalysis
        ((MPOTensor.sequentialActionAnalysis (fun a (_ _ : Fin 1) ↦ VA₀ a) a b 0
          (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩)).submatrix id
            (fun v ↦ finProdFinEquiv (finProdFinEquiv v.1, v.2)))
        ((MPOTensor.sequentialActionAnalysis (fun a (_ _ : Fin 1) ↦ VA₁ a) a b 0
          (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩)).submatrix id
            (fun v ↦ finProdFinEquiv (finProdFinEquiv v.1, v.2))) := by
  classical
  rcases p with ⟨t, i, j⟩
  have ht : t = 0 := Subsingleton.elim _ _
  subst t
  ext z ⟨⟨α, β⟩, x⟩
  simp only [Matrix.submatrix_apply, mixedEndpointTripleEquiv, mixedEndpointActedEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    MPOTensor.sequentialActionPathEquiv, Equiv.coe_fn_mk,
    MPOTensor.sequentialActionAnalysis_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  cases z <;> cases α <;> cases β <;> cases x <;>
    simp [mixedEndpointMPOAnalysis, mixedEndpointActedEquiv,
      mixedEndpointAnalysis, mixedEndpointTripleAnalysis,
      MPOTensor.sequentialActionAnalysis_apply, Equiv.symm_trans]

/-- The actual fusion-then-action synthesis retains only matching endpoint
sectors on all three incoming virtual legs. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpoint_fusionThenActionSynthesis (a b : Fin r)
    (q : MPOTensor.FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0) :
    (MPOTensor.fusionThenActionSynthesis
      (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
      (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0
      (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)).submatrix
        (mixedEndpointTripleEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b) D₀ D₁) finSumFinEquiv =
      mixedEndpointTripleSynthesis
        ((MPOTensor.fusionThenActionSynthesis WF₀ (fun a (_ _ : Fin 1) ↦ WA₀ a) a b 0
          (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)).submatrix
            (fun v ↦ finProdFinEquiv (finProdFinEquiv v.1, v.2)) id)
        ((MPOTensor.fusionThenActionSynthesis WF₁ (fun a (_ _ : Fin 1) ↦ WA₁ a) a b 0
          (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)).submatrix
            (fun v ↦ finProdFinEquiv (finProdFinEquiv v.1, v.2)) id) := by
  classical
  rcases q with ⟨c, k, μ⟩
  ext ⟨⟨α, β⟩, x⟩ z
  simp only [Matrix.submatrix_apply, mixedEndpointTripleEquiv, mixedEndpointActedEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    MPOTensor.fusionActionPathEquiv, Equiv.coe_fn_mk,
    MPOTensor.fusionThenActionSynthesis_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  cases z <;> cases α <;> cases β <;> cases x <;>
    simp [mixedEndpointMPOSynthesis, mixedEndpointActedEquiv,
      mixedEndpointMPOFusionSynthesis, mixedEndpointFusionSynthesis,
      mixedEndpointSynthesis, mixedEndpointTripleSynthesis,
      MPOTensor.fusionThenActionSynthesis_apply, Equiv.symm_trans]

/-- The actual mixed action-tree cross product has the two endpoint cross
products as its diagonal blocks. Source: GLM23, lines 1667--1685. -/
theorem mixedEndpoint_actionTree_cross (a b : Fin r)
    (p : MPOTensor.SequentialActionMultiplicity (fun a (_ _ : Fin 1) ↦ m a) a b 0 0)
    (q : MPOTensor.FusionActionMultiplicity N (fun a (_ _ : Fin 1) ↦ m a) a b 0 0) :
    (MPOTensor.sequentialActionAnalysis
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i)) a b 0
        (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩) *
      MPOTensor.fusionThenActionSynthesis
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0
        (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)).submatrix
          finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks
        (MPOTensor.sequentialActionAnalysis (fun a (_ _ : Fin 1) ↦ VA₀ a) a b 0
            (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩) *
          MPOTensor.fusionThenActionSynthesis WF₀ (fun a (_ _ : Fin 1) ↦ WA₀ a) a b 0
            (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)) 0 0
        (MPOTensor.sequentialActionAnalysis (fun a (_ _ : Fin 1) ↦ VA₁ a) a b 0
            (MPOTensor.sequentialActionPathEquiv a b 0 ⟨0, p⟩) *
          MPOTensor.fusionThenActionSynthesis WF₁ (fun a (_ _ : Fin 1) ↦ WA₁ a) a b 0
            (MPOTensor.fusionActionPathEquiv a b 0 ⟨0, q⟩)) := by
  rw [← Matrix.submatrix_mul_equiv _ _ _
    (mixedEndpointTripleEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b) D₀ D₁)]
  rw [mixedEndpoint_sequentialActionAnalysis,
    mixedEndpoint_fusionThenActionSynthesis, mixedEndpointTripleAnalysis_mul_synthesis]
  congr 1 <;>
    exact Matrix.submatrix_mul_equiv _ _ id
      ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv) id

/-- The raw source-oriented L matrix of the chosen mixed action maps is
the dimension-weighted mean of the endpoint raw matrices. This identity
requires no tensor, normality, biorthogonality, or positive dimension.
Source: GLM23, lines 1667--1685. -/
theorem actionLMatrix_mixedEndpoint (a b : Fin r) :
    MPOTensor.actionLMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0 0 =
      ((D₀ + D₁ : ℕ) : ℂ)⁻¹ •
        ((D₀ : ℂ) • MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
            (fun a _ _ ↦ WA₀ a) a b 0 0 +
          (D₁ : ℂ) • MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
            (fun a _ _ ↦ WA₁ a) a b 0 0) := by
  classical
  ext p q
  simp only [MPOTensor.actionLMatrix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  have htrace := congrArg Matrix.trace
    (mixedEndpoint_actionTree_cross WF₀ VA₀ WA₀ WF₁ VA₁ WA₁ a b p q)
  rw [Matrix.trace_submatrix_equiv] at htrace
  rw [finDimension_mul_normalizedTrace, finDimension_mul_normalizedTrace]
  congr 1
  simpa only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂] using htrace

/-- Equal chosen endpoint raw L matrices are inherited by the actual
mixed action maps. The maps do not depend on the interpolation parameter,
so this holds along the entire path, including both endpoints.
Source: GLM23, lines 1667--1685. -/
theorem actionLMatrix_mixedEndpoint_eq_of_eq (a b : Fin r)
    (hL : MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 =
      MPOTensor.actionLMatrix WF₁ (fun a (_ _ : Fin 1) ↦ VA₁ a)
        (fun a _ _ ↦ WA₁ a) a b 0 0) :
    MPOTensor.actionLMatrix
        (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOAnalysis (VA₀ a i) (VA₁ a i))
        (fun a (_ _ : Fin 1) i ↦ mixedEndpointMPOSynthesis (WA₀ a i) (WA₁ a i)) a b 0 0 =
      MPOTensor.actionLMatrix WF₀ (fun a (_ _ : Fin 1) ↦ VA₀ a)
        (fun a _ _ ↦ WA₀ a) a b 0 0 := by
  by_cases hD : D₀ + D₁ = 0
  · obtain ⟨hD₀, hD₁⟩ := Nat.add_eq_zero_iff.mp hD
    subst D₀
    subst D₁
    ext p q
    simp [MPOTensor.actionLMatrix]
  · rw [actionLMatrix_mixedEndpoint, ← hL, ← add_smul, ← Nat.cast_add, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hD), one_smul]

end MPSTensor.MPOSymmetry
