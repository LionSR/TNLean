/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryMulVecInner
import TNLean.MPS.MPU.FiniteGroupDetectorLocalComparison
import TNLean.MPS.MPU.FiniteGroupDetectorTruncatedInterval

/-!
# Endpoint calibration on arbitrary multiwall chains

Source context: arXiv:2405.00439, `detectG`, lines 2108–2117, and
arXiv:2502.20257, `eq:truncsym`, lines 2062–2100. A comparison of the two
endpoint actions on the adjacent block tensors suffices to identify the
actual native interval and the canonical string on any trace state with
those endpoint tensors. The interior and exterior matrix-valued chains are
arbitrary and may contain other walls.

The pair-creation result has no scalar factor. For the actual simple
canonical-form-II source factors, unitarity on the common physical chain
therefore gives phase-free adjoint pair removal. The undo action itself is
not assumed.

**Scope restriction (local endpoint calibration):** the finite endpoint
identifications and endpoint-action equalities are explicit hypotheses.
Their derivation for a specified family of circuit truncations, and the
construction of every reference state in the complete detector geometry,
remain separate tasks. This is not the unrestricted source detection claim;
see https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.
-/

open Matrix
open scoped Matrix

namespace MPOTensor

variable {d D L k l n t m₁ m₂ m₃ m₄ : ℕ}

/-- Equal endpoint actions give equal string actions on a trace state with
arbitrary interior and exterior chains. This is the local comparison
needed for the multiwall states of GS24 `detectG`, lines 2108–2117. -/
theorem stringOperator_mulVec_eq_of_endpoint_actions (U : MPOTensor d D)
    (E E' : Fin d → Fin d → Matrix (Fin 1) (Fin D) ℂ)
    (F F' : Fin d → Fin d → Matrix (Fin D) (Fin 1) ℂ)
    (h : k + 1 + l + 1 + n = L)
    (P : (Fin k → Fin d) → Matrix (Fin t) (Fin m₁) ℂ)
    (C : Fin d → Matrix (Fin m₁) (Fin m₂) ℂ)
    (M : (Fin l → Fin d) → Matrix (Fin m₂) (Fin m₃) ℂ)
    (C' : Fin d → Matrix (Fin m₃) (Fin m₄) ℂ)
    (Q : (Fin n → Fin d) → Matrix (Fin m₄) (Fin t) ℂ)
    (ψ : (Fin L → Fin d) → ℂ)
    (hψ : ∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
      (P p * C a * M μ * C' b * Q q).trace)
    (hE : ∀ a, leftAct E C a = leftAct E' C a)
    (hF : ∀ b, rightAct F C' b = rightAct F' C' b) :
    stringOperator U E F k l n h *ᵥ ψ = stringOperator U E' F' k l n h *ᵥ ψ := by
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  rw [stringOperator_mulVec_trace U E F h P C M C' Q ψ hψ,
    stringOperator_mulVec_trace U E' F' h P C M C' Q ψ hψ, hE, hF]

namespace GroupFamily.BlockActionData

variable {G X : Type*} [Group G] {F : GroupFamily G d} [MulAction G X]
  {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)} (ad : BlockActionData F A) (g : G)
  {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}

/-- The actual source-triangle interval agrees with the canonical wall
string on arbitrary multiwall interiors and exteriors, assuming only the
two local endpoint calibrations on their adjacent block tensors.
Project corrected comparison for GS24 `detectG`, lines 2108–2117. -/
theorem physicalTruncatedInterval_mulVec_eq_groupWallString_of_endpoint_calibration
    [Fintype X] (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
    (hÂ : IsSeparatingLeftInverseFamily Â A)
    (el : Fin ℓ[F.tensor g] ≃ Fin d) (er : Fin r[F.tensor g] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[F.tensor g]) (Fin d × Fin (F.bondDim g)) ℂ)
    (Y₁ : Matrix (Fin r[F.tensor g]) (Fin (F.bondDim g) × Fin d) ℂ)
    (y z : X) (h : k + 1 + l + 1 + n = L)
    (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
    (M : (Fin l → Fin d) → Matrix (Fin (D y)) (Fin (D z)) ℂ)
    (Q : (Fin n → Fin d) → Matrix (Fin (D z)) (Fin t) ℂ)
    (ψ : (Fin L → Fin d) → ℂ)
    (hψ : ∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
      (P p * A y a * M μ * A z b * Q q).trace)
    (hleft : ∀ a, leftAct (FiniteGroupDetector.sourceStringLeftEndpoint (F.tensor g) el Y₂)
      (A y) a = e y (g • y) a * ad.V g y)
    (hright : ∀ b, rightAct (FiniteGroupDetector.sourceStringRightEndpoint (F.tensor g) er Y₁)
      (A z) b = ad.W g z * e (g • z) z b) :
    FiniteGroupDetector.physicalTruncatedInterval (F.tensor g) el er Y₂ Y₁ k l n h *ᵥ ψ =
      ad.groupWallString g Â e k l n h *ᵥ ψ := by
  rw [FiniteGroupDetector.physicalTruncatedInterval_eq_stringOperator, groupWallString]
  apply stringOperator_mulVec_eq_of_endpoint_actions _ _ _ _ _ h P (A y) M (A z) Q ψ hψ
  · intro a
    rw [hleft, leftAct_groupWallLeftEndpoint ad hÂ]
  · intro b
    rw [hright, rightAct_groupWallRightEndpoint ad hÂ]

/-- Every buffered interior wall, including each cyclic-orbit wall in the
multiwall sequence, acquires its actual B-coefficient under the native
interval once its two endpoint actions are calibrated. Exterior spectator
chains are arbitrary. Project corrected local step for GS24 `detectG`,
lines 2108–2117; no whole-vector truncation comparison is assumed. -/
theorem physicalTruncatedInterval_mulVec_trace_wall_of_endpoint_calibration
    [Fintype X] (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
    (hÂ : IsSeparatingLeftInverseFamily Â A) {B : G → X → X → ℂ}
    (hB : ad.IsDomainWallFamily e B)
    (el : Fin ℓ[F.tensor g] ≃ Fin d) (er : Fin r[F.tensor g] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[F.tensor g]) (Fin d × Fin (F.bondDim g)) ℂ)
    (Y₁ : Matrix (Fin r[F.tensor g]) (Fin (F.bondDim g) × Fin d) ℂ) (y z : X) :
    ∃ N : ℕ, ∀ (k v w n L : ℕ) (h : k + 1 + (v + 1 + w) + 1 + n = L),
      N ≤ v → N ≤ w → ∀ (t : ℕ)
      (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
      (Q : (Fin n → Fin d) → Matrix (Fin (D z)) (Fin t) ℂ)
      (ψ : (Fin L → Fin d) → ℂ),
      (∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
        (P p * A y a * wallChain (A y) (e y z) (A z) μ * A z b * Q q).trace) →
      (∀ a, leftAct (FiniteGroupDetector.sourceStringLeftEndpoint (F.tensor g) el Y₂)
        (A y) a = e y (g • y) a * ad.V g y) →
      (∀ b, rightAct (FiniteGroupDetector.sourceStringRightEndpoint (F.tensor g) er Y₁)
        (A z) b = ad.W g z * e (g • z) z b) → ∀ p a μ b q,
      (FiniteGroupDetector.physicalTruncatedInterval (F.tensor g) el er Y₂ Y₁
          k (v + 1 + w) n h *ᵥ ψ) (wallConfig h (p, a, μ, b, q)) =
        B g y z *
          (P p * e y (g • y) a * wallChain (A (g • y)) (e (g • y) (g • z))
            (A (g • z)) μ * e (g • z) z b * Q q).trace := by
  obtain ⟨N, hN⟩ := ad.groupWallString_mulVec_trace_wall g Â hÂ hB y z
  refine ⟨N, fun k v w n L h hv hw t P Q ψ hψ hleft hright p a μ b q ↦ ?_⟩
  rw [ad.physicalTruncatedInterval_mulVec_eq_groupWallString_of_endpoint_calibration
    g Â hÂ el er Y₂ Y₁ y z h P (wallChain (A y) (e y z) (A z)) Q ψ hψ hleft hright]
  exact hN k v w n L h hv hw t P Q ψ hψ p a μ b q

/-- An interval with calibrated endpoints creates exactly one pair of
walls in a homogeneous window, with arbitrary spectator chains outside.
There is no phase factor in this creation comparison. Source context:
GS24 `eq:DWophysG` and the undo sequence in `detectG`, lines 2108–2117. -/
theorem physicalTruncatedInterval_mulVec_trace_block_of_endpoint_calibration
    (el : Fin ℓ[F.tensor g] ≃ Fin d) (er : Fin r[F.tensor g] ≃ Fin d)
    (Y₂ : Matrix (Fin ℓ[F.tensor g]) (Fin d × Fin (F.bondDim g)) ℂ)
    (Y₁ : Matrix (Fin r[F.tensor g]) (Fin (F.bondDim g) × Fin d) ℂ)
    (y : X) (h : k + 1 + l + 1 + n = L)
    (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
    (Q : (Fin n → Fin d) → Matrix (Fin (D y)) (Fin t) ℂ)
    (ψ : (Fin L → Fin d) → ℂ)
    (hψ : ∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
      (P p * A y a * Kraus.evalWord (A y) (List.ofFn μ) * A y b * Q q).trace)
    (hleft : ∀ a, leftAct (FiniteGroupDetector.sourceStringLeftEndpoint (F.tensor g) el Y₂)
      (A y) a = e y (g • y) a * ad.V g y)
    (hright : ∀ b, rightAct (FiniteGroupDetector.sourceStringRightEndpoint (F.tensor g) er Y₁)
      (A y) b = ad.W g y * e (g • y) y b)
    (p : Fin k → Fin d) (a : Fin d) (μ : Fin l → Fin d) (b : Fin d) (q : Fin n → Fin d) :
    (FiniteGroupDetector.physicalTruncatedInterval (F.tensor g) el er Y₂ Y₁ k l n h *ᵥ ψ)
        (wallConfig h (p, a, μ, b, q)) =
      (P p * e y (g • y) a * Kraus.evalWord (A (g • y)) (List.ofFn μ) *
        e (g • y) y b * Q q).trace := by
  rw [FiniteGroupDetector.physicalTruncatedInterval_eq_stringOperator,
    stringOperator_mulVec_trace _ _ _ h P (A y)
      (fun μ ↦ Kraus.evalWord (A y) (List.ofFn μ)) (A y) Q ψ hψ,
    hleft, hright, physAct_evalWord]
  have hr := (ad.isReduction g y).evalWord (List.ofFn μ)
  calc
    _ = (P p * e y (g • y) a *
        (ad.V g y * Kraus.evalWord (actTensor (F.tensor g) (A y)) (List.ofFn μ) * ad.W g y) *
          e (g • y) y b * Q q).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hr]

/-- For the actual simple canonical source factors, the adjoint interval
removes a calibrated wall pair without an extra phase, on the same physical
chain and with arbitrary exterior spectators. Its action is derived from
the forward creation contraction and native unitarity, not assumed.
Project corrected undo comparison for GS24 `detectG`, lines 2108–2117. -/
theorem sourceFactors_physicalTruncatedInterval_conjTranspose_mulVec_of_endpoint_calibration
    (hU : IsMPUCanonicalFormII (F.tensor g)) (hsimple : IsMPUSimple (F.tensor g))
    (el : Fin ℓ[F.tensor g] ≃ Fin d) (er : Fin r[F.tensor g] ≃ Fin d)
    (y : X) (h : k + 1 + l + 1 + n = L)
    (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
    (Q : (Fin n → Fin d) → Matrix (Fin (D y)) (Fin t) ℂ)
    (ψ Φ : (Fin L → Fin d) → ℂ)
    (hψ : ∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
      (P p * A y a * Kraus.evalWord (A y) (List.ofFn μ) * A y b * Q q).trace)
    (hΦ : ∀ p a μ b q, Φ (wallConfig h (p, a, μ, b, q)) =
      (P p * e y (g • y) a * Kraus.evalWord (A (g • y)) (List.ofFn μ) *
        e (g • y) y b * Q q).trace)
    (hleft : ∀ a, leftAct (FiniteGroupDetector.sourceStringLeftEndpoint (F.tensor g) el
      (sourceFactors (F.tensor g) hU.ρ hU.ρ_posDef).Y₂) (A y) a =
        e y (g • y) a * ad.V g y)
    (hright : ∀ b, rightAct (FiniteGroupDetector.sourceStringRightEndpoint (F.tensor g) er
      (sourceFactors (F.tensor g) hU.ρ hU.ρ_posDef).Y₁) (A y) b =
        ad.W g y * e (g • y) y b) :
    (FiniteGroupDetector.physicalTruncatedInterval (F.tensor g) el er
      (sourceFactors (F.tensor g) hU.ρ hU.ρ_posDef).Y₂
      (sourceFactors (F.tensor g) hU.ρ hU.ρ_posDef).Y₁ k l n h)ᴴ *ᵥ Φ = ψ := by
  classical
  apply Matrix.conjTranspose_mulVec_eq_of_mulVec_eq
    (FiniteGroupDetector.sourceFactors_physicalTruncatedInterval_mem_unitaryGroup
      hU hsimple el er k l n h)
  funext τ
  obtain ⟨⟨p, a, μ, b, q⟩, rfl⟩ := (wallConfig h).surjective τ
  rw [ad.physicalTruncatedInterval_mulVec_trace_block_of_endpoint_calibration g el er _ _ y h
    P Q ψ hψ hleft hright, hΦ]

end GroupFamily.BlockActionData

end MPOTensor
