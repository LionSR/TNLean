/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import TNLean.Algebra.ScalarThreeCocycle

/-!
# Inversion cochains of a scalar three-cocycle

This file proves the scalar inversion identities in arXiv:2502.20257,
`eq:introXi` and `lemma:omegaXi` (lines 5967--5979). The proofs name and combine
the cocycle substitutions listed in the source.
-/

namespace TNLean.Algebra

variable {G : Type*} [Group G]

/-- A multiplicative scalar one-cochain on a group. -/
abbrev ScalarOneCochain (G : Type*) := G → Units ℂ

namespace ScalarOneCochain

/-- The multiplicative coboundary of a scalar one-cochain,
`(dσ)(g,h) = σ(g) σ(h) / σ(gh)`, as in arXiv:2502.20257, line 5916. -/
def coboundary (σ : ScalarOneCochain G) : ScalarCocycle G :=
  fun g h => (σ g * σ h) / σ (g * h)

end ScalarOneCochain

namespace ScalarCocycle

/-- The hat operation on scalar two-cochains,
`hat β(g,h) = β(h⁻¹,g⁻¹)`, obtained from arXiv:2502.20257, line 5912. -/
def hat (β : ScalarCocycle G) : ScalarCocycle G :=
  fun g h => β h⁻¹ g⁻¹

/-- Applying the hat operation twice returns the original scalar two-cochain,
as stated after arXiv:2502.20257, line 5912. -/
@[simp]
theorem hat_hat (β : ScalarCocycle G) : hat (hat β) = β := by
  funext g h
  simp [hat]

end ScalarCocycle

namespace ScalarThreeCochain

/-- The hat operation on scalar three-cochains,
`hat ω(g,h,k) = ω(k⁻¹,h⁻¹,g⁻¹)`, obtained from arXiv:2502.20257, line 5912. -/
def hat (ω : ScalarThreeCochain G) : ScalarThreeCochain G :=
  fun g h k => ω k⁻¹ h⁻¹ g⁻¹

/-- Applying the hat operation twice returns the original scalar three-cochain,
as stated after arXiv:2502.20257, line 5912. -/
@[simp]
theorem hat_hat (ω : ScalarThreeCochain G) : hat (hat ω) = ω := by
  funext g h k
  simp [hat]

/-- The inversion two-cochain
`Xi(g,h) = ω(h⁻¹,g⁻¹,g) / ω(h⁻¹g⁻¹,g,h)` from arXiv:2502.20257,
`eq:introXi`. -/
def Xi (ω : ScalarThreeCochain G) : ScalarCocycle G :=
  fun g h => ω h⁻¹ g⁻¹ g / ω (h⁻¹ * g⁻¹) g h

/-- The inversion one-cochain `σ(g) = ω(g,g⁻¹,g)` from arXiv:2502.20257,
`eq:introXi`. -/
def sigma (ω : ScalarThreeCochain G) : ScalarOneCochain G :=
  fun g => ω g g⁻¹ g

/-- The second formula for the inversion cochain in arXiv:2502.20257,
`eq:introXi`:
`Xi(g,h) = ω(h⁻¹,g⁻¹,gh) / ω(g⁻¹,g,h)`.

This is the cocycle equation at `(h⁻¹,g⁻¹,g,h)`, not a definitional equality. -/
theorem Xi_eq_second_formula (ω : ScalarThreeCochain G) (hω : IsCocycle ω)
    (hωn : IsNormalized ω) (g h : G) :
    Xi ω g h = ω h⁻¹ g⁻¹ (g * h) / ω g⁻¹ g h := by
  have hCocycle := hω h⁻¹ g⁻¹ g h
  simp only [inv_mul_cancel, hωn.2.1] at hCocycle
  have hCocycle' :
      (↑(ω (h⁻¹ * g⁻¹) g h) : ℂ) * ↑(ω h⁻¹ g⁻¹ (g * h)) =
        ↑(ω h⁻¹ g⁻¹ g) * 1 * ↑(ω g⁻¹ g h) := by
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hCocycle
  simp only [Xi]
  apply Units.ext
  push_cast
  field_simp
  linear_combination -hCocycle'

/-- The inversion scalar satisfies `σ(g⁻¹) = σ(g)⁻¹`.

The proof is the normalized cocycle equation at `(g,g⁻¹,g,g⁻¹)`, the fourth
substitution listed for arXiv:2502.20257, `lemma:omegaXi`. -/
theorem sigma_inv (ω : ScalarThreeCochain G) (hω : IsCocycle ω)
    (hωn : IsNormalized ω) (g : G) :
    sigma ω g⁻¹ = (sigma ω g)⁻¹ := by
  have hCocycle := hω g g⁻¹ g g⁻¹
  simp only [mul_inv_cancel, inv_mul_cancel, hωn.1, hωn.2.1, hωn.2.2] at hCocycle
  simp only [sigma, inv_inv]
  rw [eq_inv_iff_mul_eq_one]
  simpa [mul_comm] using hCocycle.symm

/-- For a normalized scalar three-cocycle,
`hat ω = ω * dXi`, the first identity of arXiv:2502.20257,
`lemma:omegaXi`.

The proof combines exactly the source substitutions
`(k⁻¹,h⁻¹,g⁻¹,g)`, `(k⁻¹,h⁻¹g⁻¹,g,h)`, and
`(k⁻¹h⁻¹g⁻¹,g,h,k)`. -/
theorem hat_eq_mul_coboundary_Xi (ω : ScalarThreeCochain G)
    (hω : IsCocycle ω) (hωn : IsNormalized ω) :
    hat ω = ω * coboundary (Xi ω) := by
  funext g h k
  have hCocycle_kInv_hInv_gInv_g := hω k⁻¹ h⁻¹ g⁻¹ g
  have hCocycle_kInv_hInvMulGInv_g_h := hω k⁻¹ (h⁻¹ * g⁻¹) g h
  have hCocycle_kInvMulHInvMulGInv_g_h_k := hω (k⁻¹ * (h⁻¹ * g⁻¹)) g h k
  simp only [inv_mul_cancel, hωn.2.2, mul_one] at hCocycle_kInv_hInv_gInv_g
  simp only [inv_mul_cancel, mul_one, mul_assoc] at hCocycle_kInv_hInvMulGInv_g_h
  simp only [inv_mul_cancel, mul_one, mul_assoc] at hCocycle_kInvMulHInvMulGInv_g_h_k
  have hCocycle_kInv_hInv_gInv_g_val :
      (↑(ω (k⁻¹ * h⁻¹) g⁻¹ g) : ℂ) =
        ↑(ω k⁻¹ h⁻¹ g⁻¹) * ↑(ω k⁻¹ (h⁻¹ * g⁻¹) g) *
          ↑(ω h⁻¹ g⁻¹ g) := by
    simpa only [Units.val_mul] using congrArg Units.val hCocycle_kInv_hInv_gInv_g
  have hCocycle_kInv_hInvMulGInv_g_h_val :
      (↑(ω (k⁻¹ * (h⁻¹ * g⁻¹)) g h) : ℂ) *
          ↑(ω k⁻¹ (h⁻¹ * g⁻¹) (g * h)) =
        ↑(ω k⁻¹ (h⁻¹ * g⁻¹) g) * ↑(ω k⁻¹ h⁻¹ h) *
          ↑(ω (h⁻¹ * g⁻¹) g h) := by
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val hCocycle_kInv_hInvMulGInv_g_h
  have hCocycle_kInvMulHInvMulGInv_g_h_k_val :
      (↑(ω (k⁻¹ * h⁻¹) h k) : ℂ) *
          ↑(ω (k⁻¹ * (h⁻¹ * g⁻¹)) g (h * k)) =
        ↑(ω (k⁻¹ * (h⁻¹ * g⁻¹)) g h) *
          ↑(ω (k⁻¹ * (h⁻¹ * g⁻¹)) (g * h) k) * ↑(ω g h k) := by
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val hCocycle_kInvMulHInvMulGInv_g_h_k
  simp only [hat, coboundary, Xi, Pi.mul_apply, mul_inv_rev, mul_assoc]
  apply Units.ext
  push_cast
  field_simp
  linear_combination
    ((ω k⁻¹ h⁻¹ g⁻¹ : ℂ) * (ω h⁻¹ g⁻¹ g : ℂ) *
      (ω k⁻¹ (h⁻¹ * g⁻¹) (g * h) : ℂ)) * hCocycle_kInvMulHInvMulGInv_g_h_k_val +
    ((ω k⁻¹ h⁻¹ g⁻¹ : ℂ) * (ω h⁻¹ g⁻¹ g : ℂ) *
      (ω (k⁻¹ * (h⁻¹ * g⁻¹)) (g * h) k : ℂ) * (ω g h k : ℂ)) *
        hCocycle_kInv_hInvMulGInv_g_h_val -
    ((ω g h k : ℂ) * (ω k⁻¹ h⁻¹ h : ℂ) *
      (ω (h⁻¹ * g⁻¹) g h : ℂ) *
      (ω (k⁻¹ * (h⁻¹ * g⁻¹)) (g * h) k : ℂ)) * hCocycle_kInv_hInv_gInv_g_val

/-- For a normalized scalar three-cocycle,
`Xi = hat Xi * dσ`, the second identity of arXiv:2502.20257,
`lemma:omegaXi`.

After rewriting the hatted `Xi` by `Xi_eq_second_formula`, the proof uses the source
substitutions `(h⁻¹g⁻¹,g,h,h⁻¹g⁻¹)`, `(h⁻¹,h,h⁻¹,g⁻¹)`, and
`(h⁻¹,g⁻¹,g,g⁻¹)`. The fourth substitution `(u,u⁻¹,u,u⁻¹)` is used through
`sigma_inv` at `u = g`, `h`, and `gh`. -/
theorem Xi_eq_hat_mul_coboundary_sigma (ω : ScalarThreeCochain G)
    (hω : IsCocycle ω) (hωn : IsNormalized ω) :
    Xi ω = ScalarCocycle.hat (Xi ω) * ScalarOneCochain.coboundary (sigma ω) := by
  funext g h
  simp only [Pi.mul_apply]
  rw [show ScalarCocycle.hat (Xi ω) g h = Xi ω h⁻¹ g⁻¹ by rfl]
  nth_rewrite 2 [Xi_eq_second_formula ω hω hωn]
  have hCocycle_hInvMulGInv_g_h_hInvMulGInv_raw := hω (h⁻¹ * g⁻¹) g h (h⁻¹ * g⁻¹)
  have hCocycle_hInvMulGInv_g_h_hInvMulGInv :
      ω h⁻¹ h (h⁻¹ * g⁻¹) * ω (h⁻¹ * g⁻¹) g g⁻¹ =
        ω (h⁻¹ * g⁻¹) g h * ω (h⁻¹ * g⁻¹) (g * h) (h⁻¹ * g⁻¹) *
          ω g h (h⁻¹ * g⁻¹) := by
    convert hCocycle_hInvMulGInv_g_h_hInvMulGInv_raw using 1
    all_goals group
  have hCocycle_hInv_h_hInv_gInv :
      ω h⁻¹ h (h⁻¹ * g⁻¹) = ω h⁻¹ h h⁻¹ * ω h h⁻¹ g⁻¹ := by
    simpa only [inv_mul_cancel, mul_inv_cancel, hωn.1, hωn.2.1, one_mul, mul_one]
      using hω h⁻¹ h h⁻¹ g⁻¹
  have hCocycle_hInv_gInv_g_gInv :
      ω (h⁻¹ * g⁻¹) g g⁻¹ = ω h⁻¹ g⁻¹ g * ω g⁻¹ g g⁻¹ := by
    simpa only [inv_mul_cancel, mul_inv_cancel, hωn.2.1, hωn.2.2, mul_one]
      using hω h⁻¹ g⁻¹ g g⁻¹
  have hSigmaG : ω g⁻¹ g g⁻¹ * ω g g⁻¹ g = 1 := by
    have hInv := sigma_inv ω hω hωn g
    have hOne : sigma ω g⁻¹ * sigma ω g = 1 := by rw [hInv, inv_mul_cancel]
    simpa only [sigma, inv_inv] using hOne
  have hSigmaH : ω h⁻¹ h h⁻¹ * ω h h⁻¹ h = 1 := by
    have hInv := sigma_inv ω hω hωn h
    have hOne : sigma ω h⁻¹ * sigma ω h = 1 := by rw [hInv, inv_mul_cancel]
    simpa only [sigma, inv_inv] using hOne
  have hSigmaGH :
      ω (h⁻¹ * g⁻¹) (g * h) (h⁻¹ * g⁻¹) *
          ω (g * h) (h⁻¹ * g⁻¹) (g * h) = 1 := by
    have hInv := sigma_inv ω hω hωn (g * h)
    have hOne : sigma ω (g * h)⁻¹ * sigma ω (g * h) = 1 := by
      rw [hInv, inv_mul_cancel]
    simpa only [sigma, mul_inv_rev, inv_inv] using hOne
  have hA :
      ω h⁻¹ g⁻¹ g = ω (h⁻¹ * g⁻¹) g g⁻¹ * ω g g⁻¹ g := by
    calc
      ω h⁻¹ g⁻¹ g = ω h⁻¹ g⁻¹ g * (ω g⁻¹ g g⁻¹ * ω g g⁻¹ g) := by
        rw [hSigmaG, mul_one]
      _ = (ω h⁻¹ g⁻¹ g * ω g⁻¹ g g⁻¹) * ω g g⁻¹ g := by
        rw [mul_assoc]
      _ = ω (h⁻¹ * g⁻¹) g g⁻¹ * ω g g⁻¹ g := by rw [← hCocycle_hInv_gInv_g_gInv]
  have hP :
      ω h h⁻¹ g⁻¹ = ω h⁻¹ h (h⁻¹ * g⁻¹) * ω h h⁻¹ h := by
    calc
      ω h h⁻¹ g⁻¹ = (ω h⁻¹ h h⁻¹ * ω h h⁻¹ h) * ω h h⁻¹ g⁻¹ := by
        rw [hSigmaH, one_mul]
      _ = (ω h⁻¹ h h⁻¹ * ω h h⁻¹ g⁻¹) * ω h h⁻¹ h := by ac_rfl
      _ = ω h⁻¹ h (h⁻¹ * g⁻¹) * ω h h⁻¹ h := by rw [← hCocycle_hInv_h_hInv_gInv]
  have hCocycle_hInvMulGInv_g_h_hInvMulGInv_val :
      (↑(ω h⁻¹ h (h⁻¹ * g⁻¹)) : ℂ) * ↑(ω (h⁻¹ * g⁻¹) g g⁻¹) =
        ↑(ω (h⁻¹ * g⁻¹) g h) *
          ↑(ω (h⁻¹ * g⁻¹) (g * h) (h⁻¹ * g⁻¹)) *
            ↑(ω g h (h⁻¹ * g⁻¹)) := by
    simpa only [Units.val_mul, mul_assoc] using
      congrArg Units.val hCocycle_hInvMulGInv_g_h_hInvMulGInv
  have hSigmaGH' :
      (↑(ω (h⁻¹ * g⁻¹) (g * h) (h⁻¹ * g⁻¹)) : ℂ) *
          ↑(ω (g * h) (h⁻¹ * g⁻¹) (g * h)) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hSigmaGH
  have hA' :
      (↑(ω h⁻¹ g⁻¹ g) : ℂ) =
        ↑(ω (h⁻¹ * g⁻¹) g g⁻¹) * ↑(ω g g⁻¹ g) := by
    simpa only [Units.val_mul] using congrArg Units.val hA
  have hP' :
      (↑(ω h h⁻¹ g⁻¹) : ℂ) =
        ↑(ω h⁻¹ h (h⁻¹ * g⁻¹)) * ↑(ω h h⁻¹ h) := by
    simpa only [Units.val_mul] using congrArg Units.val hP
  simp only [Xi, ScalarOneCochain.coboundary, sigma, mul_inv_rev, inv_inv]
  apply Units.ext
  push_cast
  field_simp
  linear_combination
    ((ω h h⁻¹ g⁻¹ : ℂ) * (ω (g * h) (h⁻¹ * g⁻¹) (g * h) : ℂ)) * hA' +
    ((ω (h⁻¹ * g⁻¹) g g⁻¹ : ℂ) * (ω g g⁻¹ g : ℂ) *
      (ω (g * h) (h⁻¹ * g⁻¹) (g * h) : ℂ)) * hP' +
    ((ω g g⁻¹ g : ℂ) * (ω h h⁻¹ h : ℂ) *
      (ω (g * h) (h⁻¹ * g⁻¹) (g * h) : ℂ)) * hCocycle_hInvMulGInv_g_h_hInvMulGInv_val +
    ((ω (h⁻¹ * g⁻¹) g h : ℂ) * (ω g h (h⁻¹ * g⁻¹) : ℂ) *
      (ω g g⁻¹ g : ℂ) * (ω h h⁻¹ h : ℂ)) * hSigmaGH'

end ScalarThreeCochain

end TNLean.Algebra
