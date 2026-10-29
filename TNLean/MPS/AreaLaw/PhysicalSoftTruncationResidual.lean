/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalExponentialMoment
import QICLean.Analysis.SoftHardTruncation
import QICLean.Analysis.MatrixBernsteinInputs

/-!
# The physical soft-truncation residual on the original spectral window

The actual regional exponential moment controls the defining soft-truncation
operator on the whole original low-energy window. The scalar remainder is
factored through an exponential of the same regional operator. No moment or
residual estimate is assumed in the physical theorem.

**Scope restriction (equal order and scale):** The order and scale are the
same positive integer. This is a corrected auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1175–1255,
rather than the printed first uniform energy estimate or the reverse
spectral comparison. See
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem norm_scalar_weighted_soft_remainder_le (m : ℕ) (hm : 0 < m)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖(x - Real.softTruncation (m : ℝ) m x) * Real.exp (-x / 8)‖ ≤
      16 * Real.exp (-(m : ℝ) / 16) := by
  have hnonneg : 0 ≤ x - Real.softTruncation (m : ℝ) m x :=
    sub_nonneg.mpr (Real.softTruncation_bounds (m : ℝ) m x
      (Nat.cast_pos.mpr hm) hm hx).2.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg (Real.exp_nonneg _))]
  have hb := Real.softTruncation_remainder_le_exp m hm (1 / 8) x
    (by norm_num) (by norm_num) hx
  calc
    _ ≤ ((2 / (1 / 8 : ℝ)) * Real.exp ((1 / 8 : ℝ) * x - (1 / 8 : ℝ) * m / 2)) *
        Real.exp (-x / 8) := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = 16 * Real.exp (-(m : ℝ) / 16) := by
      norm_num only [show (2 / (1 / 8 : ℝ)) = 16 by norm_num]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem norm_cfc_weighted_soft_remainder_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (m : ℕ) (hm : 0 < m) :
    ‖cfc (fun x : ℝ ↦ (x - Real.softTruncation (m : ℝ) m x) * Real.exp (-x / 8)) A‖ ≤
      16 * Real.exp (-(m : ℝ) / 16) := by
  refine norm_cfc_le (by positivity) ?_
  intro x hx
  exact norm_scalar_weighted_soft_remainder_le m hm x
    (spectrum_nonneg_of_nonneg hA.nonneg hx)

private theorem weighted_soft_remainder_mul_exp
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (m : ℕ) :
    cfc (fun x : ℝ ↦ (x - Real.softTruncation (m : ℝ) m x) * Real.exp (-x / 8)) A *
        NormedSpace.exp ((1 / 8 : ℝ) • A) =
      A - cfc (Real.softTruncation (m : ℝ) m) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  rw [hA.exp_smul_eq_cfc]
  rw [← _root_.cfc_mul _ _ A (hc _) (hc _)]
  have hf : (fun x : ℝ ↦ ((x - Real.softTruncation (m : ℝ) m x) *
      Real.exp (-x / 8)) * Real.exp ((1 / 8 : ℝ) * x)) =
      (fun x : ℝ ↦ x - Real.softTruncation (m : ℝ) m x) := by
    funext x
    rw [mul_assoc, ← Real.exp_add, show -x / 8 + (1 / 8 : ℝ) * x = 0 by ring,
      Real.exp_zero, mul_one]
  change cfc (fun x : ℝ ↦ ((x - Real.softTruncation (m : ℝ) m x) *
    Real.exp (-x / 8)) * Real.exp ((1 / 8 : ℝ) * x)) A = _
  rw [hf, cfc_sub _ _ A (hc _) (hc _), cfc_id' ℝ A hA.isSelfAdjoint]

private theorem norm_soft_remainder_domRestrict_le_exp_weight
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.PosSemidef) (m : ℕ) (hm : 0 < m)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
      (A - cfc (Real.softTruncation (m : ℝ) m) A)).domRestrict G‖ ≤
      (16 * Real.exp (-(m : ℝ) / 16)) *
        ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
          (NormedSpace.exp ((1 / 8 : ℝ) • A))).domRestrict G‖ := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)
  let B := cfc (fun x : ℝ ↦
    (x - Real.softTruncation (m : ℝ) m x) * Real.exp (-x / 8)) A
  let W := NormedSpace.exp ((1 / 8 : ℝ) • A)
  have hfactor : (T (A - cfc (Real.softTruncation (m : ℝ) m) A)).domRestrict G =
      (T B) ∘L (T W).domRestrict G := by
    rw [← weighted_soft_remainder_mul_exp A hA.isHermitian m, map_mul]
    rfl
  have hB : ‖T B‖ ≤ 16 * Real.exp (-(m : ℝ) / 16) := by
    rw [← Matrix.cstar_norm_def]
    exact norm_cfc_weighted_soft_remainder_le A hA m hm
  rw [hfactor]
  exact ((T B).opNorm_comp_le ((T W).domRestrict G)).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- The actual soft-truncated Hamiltonian has an exponentially small residual
on the actual original low-energy window. Regional minima and original ground
data are constructed before the approximate energy, bandwidth and order. No
moment or residual bound is supplied. ALVV, arXiv:1602.08828v2,
`def:soft-trunc` and `lem:exp-approx`, lines 1175–1255; this is the corrected
equal-order-and-scale residual, rather than the reverse spectral comparison. -/
theorem exists_interval_physical_soft_truncation_residual
    (L q p r : ℕ) (hq : 0 < q) (hpr : p ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, p, r, r, r, L]
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun j ↦
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    ∃ (e : Fin 5 → ℝ) (E0 : ℝ) (x z : (Fin L → Fin q) → ℂ),
      let H := ∑ i, h i
      let Hc := H - (((∑ j, e j) : ℝ) : ℂ) • 1
      ∃ hHc : Hc.IsHermitian,
        star x ⬝ᵥ x = 1 ∧
        (∀ j, A j *ᵥ x = (e j : ℂ) • x) ∧
        (∀ j, (A j - (e j : ℂ) • 1).PosSemidef) ∧
        star z ⬝ᵥ z = 1 ∧ Hc *ᵥ z = (E0 : ℂ) • z ∧
        (Hc - (E0 : ℂ) • 1).PosSemidef ∧ 0 ≤ E0 ∧ E0 ≤ 2 ∧
        ∀ (eps eta : ℝ) (m : ℕ), e 1 - 10 ≤ eps → eps ≤ e 1 → 0 ≤ eta → 0 < m →
          let G := Submodule.spectralSpanLE hHc.eigenvectorBasis hHc.eigenvalues (E0 + eta)
          let Hsoft := H - A 1 + (eps : ℂ) • 1 +
            cfc (Real.softTruncation (m : ℝ) m) (A 1 - (eps : ℂ) • 1)
          Hsoft.IsHermitian ∧ Hsoft ≤ H ∧
            ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
              (H - Hsoft)).domRestrict G‖ ≤
              80 * Real.exp ((17 + eta) / 8 - (m : ℝ) / 16) := by
  intro k A
  obtain ⟨e, E0, x, z, hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, hmoment⟩ :=
    exists_interval_regional_exponential_moment L q p r hq hpr hrL h hs h0 h1
  refine ⟨e, E0, x, z, ?_⟩
  intro H Hc
  refine ⟨hHc, hxunit, hx, he, hzunit, hz, hElow, hE0, hE2, ?_⟩
  intro eps eta m hepslo hepshi heta hm G Hsoft
  let U := A 1 - (eps : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
  have hmin : (e 1 : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A 1 := by
    simpa only [Complex.coe_smul] using Matrix.le_iff.mpr (he 1)
  have heps : eps • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ (e 1 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right hepshi zero_le_one
  have hU : U.PosSemidef := by
    apply Matrix.le_iff.mp
    simpa only [Complex.coe_smul] using heps.trans hmin
  have hdiff : H - Hsoft = U - cfc (Real.softTruncation (m : ℝ) m) U := by
    dsimp only [Hsoft, U]
    abel
  have hdpos : (H - Hsoft).PosSemidef := by
    rw [hdiff]
    exact Matrix.le_iff.mp
      (hU.softTruncation_hard_bounds (m : ℝ) m (Nat.cast_pos.mpr hm) hm).2
  have hH : H.IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hsoft : Hsoft.IsHermitian := by
    have heq : H - (H - Hsoft) = Hsoft := by abel
    exact heq ▸ hH.sub hdpos.isHermitian
  refine ⟨hsoft, Matrix.le_iff.mpr hdpos, ?_⟩
  rw [hdiff]
  have hweight : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
      (NormedSpace.exp ((1 / 8 : ℝ) • U))).domRestrict G‖ ≤
      5 * Real.exp ((17 + eta) / 8) := by
    simpa only [U, Complex.coe_smul] using hmoment eps eta hepslo hepshi heta
  refine (norm_soft_remainder_domRestrict_le_exp_weight U hU m hm G).trans ?_
  calc
    _ ≤ (16 * Real.exp (-(m : ℝ) / 16)) * (5 * Real.exp ((17 + eta) / 8)) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = 80 * (Real.exp (-(m : ℝ) / 16) * Real.exp ((17 + eta) / 8)) := by ring
    _ = 80 * Real.exp ((17 + eta) / 8 - (m : ℝ) / 16) := by
      rw [← Real.exp_add]
      congr 2
      ring

end TNLean.MPS.AreaLaw
