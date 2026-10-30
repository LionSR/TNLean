/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.NearestNeighbourImaginaryTime
import QICLean.Analysis.EnergyTruncation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Energy off-diagonal decay for a nearest-neighbour chain

The two boundary bonds in AKLV, arXiv:1301.1162v1, Lemma 6.6(2), have
exponentially small matrix elements between separated spectral subspaces of
the complementary Hamiltonian. The spectral threshold is strict on the low
side and closed on the high side, as in Section 6.3.

**Local fix (constant):** The printed Hadamard majorant sums to 4, whereas
the stated estimate has coefficient 2. Centering each positive contraction
at half the identity recovers coefficient 2: scalar matrices have zero
off-diagonal block. See `docs/paper-gaps/aklv13_robustness_constants.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real scalar exponentials expressed in the functional calculus of their
Hermitian generator. Auxiliary to AKLV, Lemma 6.6(2). -/
theorem IsHermitian.exp_real_smul_eq_cfc {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • B) = cfc (fun x : ℝ ↦ Real.exp (s * x)) B := by
  rw [Complex.coe_smul, ← CFC.real_exp_eq_normedSpace_exp
    ((IsSelfAdjoint.all s).smul hB.isSelfAdjoint),
    ← cfc_comp_const_mul s Real.exp B Real.continuous_exp.continuousOn
      hB.isSelfAdjoint]

/-- The inverse exponential suppresses the high-energy subspace.
Auxiliary to AKLV, arXiv:1301.1162v1, Lemmas 6.6 and 6.7. -/
theorem IsHermitian.norm_highProjection_mul_exp_neg_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s t : ℝ) (hs : 0 ≤ s) :
    ‖spectralProjectionGE B t * NormedSpace.exp (-((s : ℂ) • B))‖ ≤
      Real.exp (-s * t) := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [show -((s : ℂ) • B) = ((-s : ℝ) : ℂ) • B by simp,
    hB.exp_real_smul_eq_cfc, spectralProjectionGE,
    ← _root_.cfc_mul _ _ B (hcont _) (hcont _)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x _
  by_cases htx : t ≤ x
  · simp only [ite_eq_left htx, one_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htx (neg_nonpos.mpr hs))
  · simp only [ite_eq_right htx, zero_mul, norm_zero]
    exact (Real.exp_pos _).le

/-- The exponential on the strict low-energy subspace is bounded by the
exponential of the threshold. Auxiliary to AKLV, Lemma 6.7. -/
theorem IsHermitian.norm_exp_mul_lowProjection_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s c : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((s : ℂ) • B) * (1 - spectralProjectionGE B c)‖ ≤
      Real.exp (s * c) := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [hB.exp_real_smul_eq_cfc, spectralProjectionGE,
    ← cfc_one ℝ B hB.isSelfAdjoint, ← cfc_sub _ _ B (hcont _) (hcont _),
    ← _root_.cfc_mul _ _ B (hcont _) (hcont _)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x _
  by_cases hcx : c ≤ x
  · simp only [ite_eq_left hcx, Pi.one_apply, sub_self, mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  · simp only [ite_eq_right hcx, Pi.one_apply, sub_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hcx) hs)

/-- Imaginary time separates the high and low spectral subspaces, with no
dimension factor. The conjugated observable is left explicit. This is the
spectral step of AKLV, arXiv:1301.1162v1, Lemma 6.6(2). -/
theorem IsHermitian.norm_spectral_offDiagonal_le_exp_conjugation
    {B : Matrix n n ℂ} (hB : B.IsHermitian) (O : Matrix n n ℂ)
    (t u s : ℝ) (hs : 0 ≤ s) :
    ‖spectralProjectionGE B t * O * (1 - spectralProjectionGE B u)‖ ≤
      Real.exp (-s * (t - u)) *
        ‖NormedSpace.exp ((s : ℂ) • B) * O *
          NormedSpace.exp (-((s : ℂ) • B))‖ := by
  let Q := spectralProjectionGE B t
  let P := 1 - spectralProjectionGE B u
  let E := NormedSpace.exp ((s : ℂ) • B)
  let F := NormedSpace.exp (-((s : ℂ) • B))
  have hQF : ‖Q * F‖ ≤ Real.exp (-s * t) :=
    hB.norm_highProjection_mul_exp_neg_le s t hs
  have hEP : ‖E * P‖ ≤ Real.exp (s * u) :=
    hB.norm_exp_mul_lowProjection_le s u hs
  have hFE : F * E = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hfac : Q * O * P = (Q * F) * (E * O * F) * (E * P) := by
    simp only [mul_assoc, ← mul_assoc F E, hFE, one_mul]
  rw [hfac]
  calc
    _ ≤ (‖Q * F‖ * ‖E * O * F‖) * ‖E * P‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Real.exp (-s * t) * ‖E * O * F‖) * Real.exp (s * u) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hQF (norm_nonneg _)) hEP
        (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; congr 2; ring

/-- Scalar matrices have no block between separated energy windows.
Auxiliary to AKLV, arXiv:1301.1162v1, Lemma 6.6(2). -/
theorem IsHermitian.spectralProjectionGE_mul_one_sub_eq_zero
    {B : Matrix n n ℂ} (hB : B.IsHermitian) {u t : ℝ} (hut : u ≤ t) :
    spectralProjectionGE B t * (1 - spectralProjectionGE B u) = 0 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [spectralProjectionGE, spectralProjectionGE, ← cfc_one ℝ B hB.isSelfAdjoint,
    ← cfc_sub _ _ B (hc _) (hc _), ← _root_.cfc_mul _ _ B (hc _) (hc _)]
  rw [← cfc_zero ℝ B]
  apply cfc_congr
  intro x _
  by_cases htx : t ≤ x
  · simp [htx, hut.trans htx]
  · simp [htx]

/-- Adding the disconnected Hamiltonian does not change the off-diagonal
block between separated energy windows. AKLV, arXiv:1301.1162v1,
Lemma 6.6(2), the equality preceding its exponential estimate. -/
theorem IsHermitian.spectral_offDiagonal_add_eq {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) {u t : ℝ} (hut : u ≤ t) :
    spectralProjectionGE B t * (B + A) * (1 - spectralProjectionGE B u) =
      spectralProjectionGE B t * A * (1 - spectralProjectionGE B u) := by
  have hc : Commute B (1 - spectralProjectionGE B u) :=
    (Commute.one_right B).sub_right (hB.commute_spectralProjectionGE u)
  have hz : spectralProjectionGE B t * B * (1 - spectralProjectionGE B u) = 0 := by
    rw [mul_assoc, hc.eq, ← mul_assoc,
      hB.spectralProjectionGE_mul_one_sub_eq_zero hut, zero_mul]
  rw [mul_add, add_mul, hz, zero_add]

end Matrix

namespace TNLean.MPS.AreaLaw.AKLV

/-- A positive contraction centered at half the identity has norm at most
one half. This is the centering correction in AKLV, Lemma 6.6(2). -/
private theorem norm_sub_half_one_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h0 : 0 ≤ A) (h1 : A ≤ 1) :
    ‖A - (1 / 2 : ℂ) • 1‖ ≤ (1 / 2 : ℝ) := by
  let c : Matrix n n ℂ := (1 / 2 : ℂ) • 1
  have hsplit : (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ A - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : A - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit]
    exact h1
  have hc : IsSelfAdjoint c := by
    dsimp [c]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
    exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.one _)
  have hb := IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi
    ((IsSelfAdjoint.of_nonneg h0).sub hc)
  have hnorm : ‖c‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖c‖ = (1 / 2 : ℝ) * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        norm_num [norm_smul]
      _ ≤ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))) (by norm_num)
      _ = 1 / 2 := by ring
  exact hb.trans (by simpa only [norm_neg, max_self] using hnorm)

/-- A single unit boundary bond has an exponentially small block across
separated energies of any original nearest-neighbour regional sum. Scalar
shifts of that sum are allowed. Auxiliary to AKLV, arXiv:1301.1162v1,
Lemma 6.6(2); the coefficient is one after centering the boundary term. -/
theorem norm_boundary_spectral_offDiagonal_le {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a : Fin (L - 1)) (z t u : ℝ) (hut : u ≤ t) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := (∑ i ∈ I, h i) - (z : ℂ) • 1
    ‖Matrix.spectralProjectionGE B t * h a *
      (1 - Matrix.spectralProjectionGE B u)‖ ≤ Real.exp (-(t - u) / 8) := by
  intro B
  let O := h a - (1 / 2 : ℂ) • 1
  have hB : B.IsHermitian := by
    change IsSelfAdjoint B
    apply IsSelfAdjoint.sub
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)
    · rw [Complex.coe_smul]
      exact (IsSelfAdjoint.all z).smul (IsSelfAdjoint.one _)
  have hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O
      (interval L a.val (a.val + 2)) := by
    apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    exact Submodule.sub_mem _
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs a))
      (Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _))
  have hnorm : ‖O‖ ≤ (1 / 2 : ℝ) := norm_sub_half_one_le (h a) (h0 a) (h1 a)
  have hconj := norm_exp_conjugation_nearest_neighbour_shift_le_two I h
    (fun i _ ↦ hs i) (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) O hO (z : ℂ)
    (1 / 8) (by norm_num) le_rfl
  have hzero := hB.spectralProjectionGE_mul_one_sub_eq_zero hut
  have hcenter : Matrix.spectralProjectionGE B t * h a *
      (1 - Matrix.spectralProjectionGE B u) =
      Matrix.spectralProjectionGE B t * O * (1 - Matrix.spectralProjectionGE B u) := by
    dsimp [O]
    conv_rhs => lhs; rw [mul_sub]
    rw [sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hzero, smul_zero, sub_zero]
  rw [hcenter]
  calc
    _ ≤ Real.exp (-(1 / 8) * (t - u)) *
        ‖NormedSpace.exp (((1 / 8 : ℝ) : ℂ) • B) * O *
          NormedSpace.exp (-(((1 / 8 : ℝ) : ℂ) • B))‖ :=
      hB.norm_spectral_offDiagonal_le_exp_conjugation O t u (1 / 8) (by norm_num)
    _ ≤ Real.exp (-(1 / 8) * (t - u)) * (2 * ‖O‖) :=
      mul_le_mul_of_nonneg_left hconj (Real.exp_pos _).le
    _ ≤ Real.exp (-(t - u) / 8) := by
      have htwo : 2 * ‖O‖ ≤ 1 := by linarith
      simpa only [mul_one, show -(1 / 8 : ℝ) * (t - u) = -(t - u) / 8 by ring] using
        mul_le_mul_of_nonneg_left htwo (Real.exp_pos (-(1 / 8) * (t - u))).le

/-- The boundary coupling of AKLV has norm at most `2 exp(-(t-u)/8)`
between the two separated energy windows of the complementary Hamiltonian.
AKLV, arXiv:1301.1162v1, Lemma 6.6(2). The generator consists of original
positive unit nearest-neighbour terms and an arbitrary real scalar shift. -/
theorem norm_two_boundary_spectral_offDiagonal_le {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (z t u : ℝ) (hut : u ≤ t) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := (∑ i ∈ I, h i) - (z : ℂ) • 1
    ‖Matrix.spectralProjectionGE B t * (h a + h b) *
      (1 - Matrix.spectralProjectionGE B u)‖ ≤ 2 * Real.exp (-(t - u) / 8) := by
  intro B
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (by
    have ha := norm_boundary_spectral_offDiagonal_le I h hs h0 h1 a z t u hut
    have hb := norm_boundary_spectral_offDiagonal_le I h hs h0 h1 b z t u hut
    dsimp only at ha hb
    linarith)

end TNLean.MPS.AreaLaw.AKLV
