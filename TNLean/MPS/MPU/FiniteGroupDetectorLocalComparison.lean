/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWallStringGroup

/-!
# Canonical strings crossing one wall with arbitrary exterior chains

Source: arXiv:2405.00439, `eq:localcdefG` and `detectG`,
`Papers/2405.00439/MPU-DW.tex` lines 1896–1921 and 2108–2117.
A canonical string crossing one wall from `y` to `z` acquires the actual
coefficient `B g y z`. The exterior chains below are arbitrary rectangular
matrix-valued functions, so they can contain spectator walls and their
surrounding blocks. Only the interior wall and its two buffered regions are
acted on. This supplies a local contraction for every wall type, rather
than only for the first two-wall excitation.

**Scope restriction (canonical strings):** this result is for the canonical
string with separating left inverses and the nonzero wall family's blocked
local action. It does not identify that string's action with the action of
an arbitrary retained-circuit interval, nor construct the complete detector
sequence or calibrate its undo phases. The unrestricted `detectG` remains
open; see
https://sirui-lu.com/TNLean/paper-gaps/gs24_truncation_detector_endpoint_dependence.pdf.
-/

open Matrix
open scoped Matrix

namespace MPOTensor.GroupFamily.BlockActionData

variable {d : ℕ} {G X : Type*} [Group G] {F : GroupFamily G d}
  [MulAction G X] {D : X → ℕ} {A : (x : X) → MPSTensor d (D x)} [Fintype X]
  (ad : BlockActionData F A) (g : G)
  (Â : (x : X) → Fin d → Matrix (Fin (D x)) (Fin (D x)) ℂ)
  {e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ}
  {B : G → X → X → ℂ}

/-- A canonical string crossing a wall `e y z` in an arbitrary exterior trace
has coefficient `B g y z`. The exterior functions may contain other walls;
no assertion about actual circuit truncations is assumed or concluded.
Project local comparison for arXiv:2405.00439, `eq:localcdefG` and `detectG`,
lines 1896–1921 and 2108–2117. -/
theorem groupWallString_mulVec_trace_wall
    (hÂ : IsSeparatingLeftInverseFamily Â A) (hB : ad.IsDomainWallFamily e B) (y z : X) :
    ∃ N : ℕ, ∀ (k v w n L : ℕ) (h : k + 1 + (v + 1 + w) + 1 + n = L),
      N ≤ v → N ≤ w → ∀ (t : ℕ)
      (P : (Fin k → Fin d) → Matrix (Fin t) (Fin (D y)) ℂ)
      (Q : (Fin n → Fin d) → Matrix (Fin (D z)) (Fin t) ℂ)
      (ψ : (Fin L → Fin d) → ℂ),
      (∀ p a μ b q, ψ (wallConfig h (p, a, μ, b, q)) =
        (P p * A y a * wallChain (A y) (e y z) (A z) μ * A z b * Q q).trace) →
      ∀ p a μ b q,
      (ad.groupWallString g Â e k (v + 1 + w) n h *ᵥ ψ)
          (wallConfig h (p, a, μ, b, q)) =
        B g y z *
          (P p * e y (g • y) a * wallChain (A (g • y)) (e (g • y) (g • z))
            (A (g • z)) μ * e (g • z) z b * Q q).trace := by
  classical
  obtain ⟨N, hN⟩ := (hB g y z).physAct_eq
  refine ⟨N, fun k v w n L h hv hw t P Q ψ hψ p a μ b q ↦ ?_⟩
  rw [groupWallString, stringOperator_mulVec_trace _ _ _ h P (A y)
    (wallChain (A y) (e y z) (A z)) (A z) Q ψ hψ,
    leftAct_groupWallLeftEndpoint ad hÂ, rightAct_groupWallRightEndpoint ad hÂ]
  have hrel := hN v w hv hw μ
  simp only [castIndex_rfl, Matrix.one_mul, Matrix.mul_one] at hrel
  calc
    _ = (P p * e y (g • y) a *
        (ad.V g y * physAct (F.tensor g) (wallChain (A y) (e y z) (A z)) μ * ad.W g z) *
          e (g • z) z b * Q q).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hrel]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end MPOTensor.GroupFamily.BlockActionData
