/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.MPSApproximation
import TNLean.MPS.AreaLaw.OpenMPSCutRank

/-!
# A polynomial-rank reference for bond trimming

The bond-trimming proof of Landau, Vazirani and Vidick uses a unit matrix product state with
overlap at least `47 / 48` with the ground vector. Its bond bound is fixed independently of the
ground vector. The existing chain approximation theorem supplies such a reference with bond
bound `chainBondDimension q 1 1 Δ (48 L)`, which is polynomial in `L`.

The reference enters only the error estimate for the independently trimmed family. It does
not replace the successive viable-set construction.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:mpsapprox`,
lines 325–328, and Claim `c:trim`, lines 549–559. The source explicitly permits a polynomial
rank bound for this use, in place of the sharper sub-polynomial estimate.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {Δ : ℝ}

/-- A ground-vector-independent polynomial bond budget for the reference used in LVV13,
`algo53.tex`, Claim `c:trim`, lines 549–559, from Lemma `l:mpsapprox`, lines 325–328. -/
noncomputable def lvvReferenceBond (q : ℕ) (Δ : ℝ) (L : ℕ) : ℕ :=
  chainBondDimension q 1 1 Δ (48 * L)

/-- A unit matrix product state of overlap at least `47 / 48` supplies the reference in
LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. Its polynomial bond bound is chosen before
the ground vector; the construction reuses the chain approximation theorem. -/
theorem exists_bond_trimming_reference (hq : 1 ≤ q) (hΔ : 0 < Δ) (hL : 1 ≤ L)
    (h : ChainHamiltonian L q 1 1) {E₀ : ℝ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Γ Δ) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q), ‖v‖ = 1 ∧
      IsOpenMPS L q (lvvReferenceBond q Δ L) (fun x ↦ v x) ∧
      1 - 1 / 48 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let ε : ℝ := 1 / ((48 : ℝ) ^ 2 * L)
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  obtain ⟨v, hv, hvMPS, hvdist⟩ :=
    exists_isOpenMPS_norm_sub_le_of_error hq (by norm_num) hΔ hL h hgs hε hε1
  have heq : 2 * (L : ℝ) * tailPrefactorRoot / ε =
      2 * ((48 * L : ℕ) : ℝ) ^ 2 * tailPrefactorRoot := by
    dsimp only [ε]
    push_cast
    field_simp [hL0]
  have hMPS : IsOpenMPS L q (lvvReferenceBond q Δ L) (fun x ↦ v x) := by
    simpa only [lvvReferenceBond, chainBondDimension, chainTruncationWidth, heq] using hvMPS
  have hε48 : ε ≤ 1 / 48 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hin : ‖⟪Γ, v - Γ⟫_ℂ‖ ≤ ε := by
    refine (norm_inner_le_norm (𝕜 := ℂ) Γ (v - Γ)).trans ?_
    rw [hgs.1, one_mul]
    exact hvdist
  have hΓΓ : ⟪Γ, Γ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hgs.1]
    norm_num
  have he : ⟪Γ, v⟫_ℂ - ⟪Γ, v - Γ⟫_ℂ = 1 := by
    rw [inner_sub_right, hΓΓ]
    ring
  have htri := norm_sub_le ⟪Γ, v⟫_ℂ ⟪Γ, v - Γ⟫_ℂ
  rw [he, norm_one] at htri
  exact ⟨v, hv, hMPS, by linarith⟩

end TNLean.MPS.AreaLaw
