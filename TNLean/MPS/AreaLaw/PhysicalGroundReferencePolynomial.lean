/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalGroundReference
import QICLean.Analysis.RefinementOutputPolynomialBound

/-!
# A polynomial reference profile for the original ground space

For fixed local dimension and positive gap, the whole-exterior reference rank is
polynomial in chain length and ground multiplicity. All coefficients and exponents
are chosen before the Hamiltonian. The reference comes from the original area-law
approximation, including the exact flat-spectrum case, not from a sampled output.

This is an auxiliary to ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1801–1805.
The exponent is not asserted to have the source's sharp inverse-gap dependence.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- At fixed local dimension and gap, the squared whole-chain reference bond has
one polynomial bound in length and ground multiplicity. The reference has error
`1/100000` in both directions. Supporting ALVV, arXiv:1602.08828v2,
`t:alg1`, lines 1801–1805; this is an existence bound, not a running-time claim. -/
theorem exists_physical_ground_reference_polynomial
    (q : ℕ) (hq : 1 ≤ q) (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ,
      ∀ (L : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (_hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h i) (interval L i.val (i.val + 2)))
      (h0 : ∀ i, 0 ≤ h i) (_h1 : ∀ i, h i ≤ 1) (mu : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i, h i
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      let r := Module.finrank ℂ G
      ∃ B : ℕ, 1 ≤ B ∧
        (((r ^ 2 * B) ^ 2 : ℕ) : ℝ) ≤
          C * (((L : ℝ) + 1) * ((r : ℝ) + 1)) ^ P ∧
      ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
        Module.finrank ℂ U = r ∧
        Submodule.IsCloseTo (1 / 100000) U G ∧
        Submodule.IsCloseTo (1 / 100000) G U ∧
        ∀ v ∈ U, IsOpenMPS L q (r ^ 2 * B) (fun x ↦ v x) := by
  classical
  obtain ⟨K, hK, href⟩ := exists_physical_ground_isOpenMPS_reference_subspace
  let g := min gamma 1
  let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let b0 := 16 + Real.log (1 / g) + Real.log (3200000 : ℝ)
  let C0 := Real.exp (K * (a0 + 5 * a1) * b0)
  let p0 := Nat.ceil (K * (a0 + 5 * a1))
  refine ⟨1 + C0 ^ 2, by positivity, 4 + 2 * p0, ?_⟩
  intro L h hs h0 h1 mu H hH hmu hgap G r
  obtain ⟨B, hB, hlogB, U, hdim, hUG, hGU, hUMPS⟩ :=
    href L q hq h hs h0 h1 mu gamma hgamma hmu hgap
      (1 / 100000) (by norm_num) (by norm_num)
  have hr : 1 ≤ r := Submodule.one_le_finrank_iff.mpr
    (hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1)
  let b := 16 + Real.log (1 / g) +
    Real.log (32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000))
  have hg : 0 < g := lt_min hgamma (by norm_num)
  have hlogg : 0 ≤ Real.log (1 / g) :=
    Real.log_nonneg ((one_le_div hg).2 (min_le_right gamma 1))
  have hu : 0 ≤ u := by
    have hlogq := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
    dsimp only [u]
    linarith only [hlogq, hlogg]
  have ha0 : 0 ≤ a0 := by dsimp only [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hb0 : 1 ≤ b0 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 3200000 by norm_num)
    dsimp only [b0]
    linarith only [hlogg, hlog]
  have hZ : 1 ≤ Z := by
    dsimp only [Z]
    nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hb : 1 ≤ b := by
    have hlog := Real.log_nonneg (show
        1 ≤ 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000) by
      nlinarith only [hrR, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
    dsimp only [b]
    linarith only [hlogg, hlog]
  have hratio : 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000) ≤
      3200000 * Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hbx : b ≤ b0 + Real.log Z := by
    have hlog := Real.log_le_log (by positivity :
      0 < 32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 100000)) hratio
    rw [Real.log_mul (by norm_num : (3200000 : ℝ) ≠ 0)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hZ))] at hlog
    dsimp only [b, b0]
    linarith only [hlog]
  have hBP : (B : ℝ) ≤ C0 * Z ^ p0 := by
    apply Real.reference_profile_polynomial_bound hK.le le_rfl ha0 ha1 hb hb0
      (by exact_mod_cast (by omega : 0 < B)) hZ hbx
    dsimp only [a0, a1]
    convert hlogB using 1
    ring
  refine ⟨B, hB, ?_, U, hdim, hUG, hGU, hUMPS⟩
  have hrZ : (r : ℝ) ≤ Z := by
    dsimp only [Z]
    nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  calc
    (((r ^ 2 * B) ^ 2 : ℕ) : ℝ) ≤ (Z ^ 2 * (C0 * Z ^ p0)) ^ 2 := by
      push_cast
      gcongr
    _ = C0 ^ 2 * Z ^ (4 + 2 * p0) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ ≤ (1 + C0 ^ 2) * Z ^ (4 + 2 * p0) := by
      gcongr
      linarith only [sq_nonneg C0]

end TNLean.MPS.AreaLaw
