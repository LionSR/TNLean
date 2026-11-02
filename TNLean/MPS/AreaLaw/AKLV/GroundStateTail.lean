/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.SpectralTail

/-!
# Exponential energy tails of an eigenvector

The imaginary-time bound controls the exponential moment of an eigenvector
of the full Hamiltonian. A spectral inverse above a fixed energy gives a
bound for that moment, and hence an exponentially small high-energy tail.
This supplies an alternative proof of the truncation lemma in AKLV,
arXiv:1301.1162v1, Lemma 6.7, with explicit constants.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The high spectral projection is controlled by the energy norm.
This is the spectral-inverse estimate used in the exponential-moment
proof of AKLV, arXiv:1301.1162v1, Lemma 6.7. -/
theorem IsHermitian.norm_highProjection_apply_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (c : ℝ) (hc : 0 < c) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (spectralProjectionGE B c) x‖ ≤
      c⁻¹ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) B x‖ := by
  let R := cfc (fun z : ℝ ↦ if c ≤ z then z⁻¹ else 0) B
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  have hRB : R * B = spectralProjectionGE B c := by
    conv_lhs => rhs; rw [← cfc_id' ℝ B hB.isSelfAdjoint]
    change cfc (fun z : ℝ ↦ if c ≤ z then z⁻¹ else 0) B *
      cfc (fun z : ℝ ↦ z) B = _
    rw [← _root_.cfc_mul _ _ B (hcont _) (hcont _), spectralProjectionGE]
    apply cfc_congr
    intro z _
    by_cases hcz : c ≤ z
    · simp [hcz, ne_of_gt (hc.trans_le hcz)]
    · simp [hcz]
  have hR : ‖R‖ ≤ c⁻¹ := by
    apply norm_cfc_le (inv_nonneg.mpr hc.le)
    intro z _
    by_cases hcz : c ≤ z
    · simp only [ite_eq_left hcz, norm_inv, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hcz)]
      exact inv_anti₀ hc hcz
    · simp only [ite_eq_right hcz, norm_zero]
      exact inv_nonneg.mpr hc.le
  rw [← hRB, map_mul]
  exact ((toEuclideanCLM (n := n) (𝕜 := ℂ) R).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

/-- A short imaginary-time bound on the perturbation controls every
eigenvector's exponential moment. This is an auxiliary estimate for the
truncation lemma of AKLV, arXiv:1301.1162v1, Lemma 6.7; the chain-local
conjugation estimate is established independently in `SpectralTail`.
No bound on the norm of the complementary Hamiltonian is used. -/
theorem IsHermitian.norm_exp_apply_eigenvector_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (e s c C : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (he : toEuclideanCLM (n := n) (𝕜 := ℂ) (B + A) x = (e : ℂ) • x)
    (hC : ‖NormedSpace.exp ((s : ℂ) • B) * A *
      NormedSpace.exp (-((s : ℂ) • B))‖ ≤ C)
    (hsmall : |e| + C ≤ c / 2) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (NormedSpace.exp ((s : ℂ) • B)) x‖ ≤
      2 * Real.exp (s * c) * ‖x‖ := by
  let W := NormedSpace.exp ((s : ℂ) • B)
  let V := NormedSpace.exp (-((s : ℂ) • B))
  let D := W * A * V
  let Q := spectralProjectionGE B c
  let ι := toEuclideanCLM (n := n) (𝕜 := ℂ)
  let y := ι W x
  have hVW : V * W = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hBW : Commute B W := ((Commute.refl B).smul_right (s : ℂ)).exp_right
  have hWQ : Commute W Q := by
    rw [show W = cfc (fun z : ℝ ↦ Real.exp (s * z)) B from hB.exp_real_smul_eq_cfc s]
    exact cfc_commute_cfc _ _ B
  have he' : ι B x = (e : ℂ) • x - ι A x := by
    have h := he
    rw [map_add, _root_.add_apply] at h
    exact eq_sub_of_add_eq h
  have hBy : ι B y = (e : ℂ) • y - ι D y := by
    have hcancel : D * W = W * A := by
      dsimp [D]
      rw [mul_assoc, mul_assoc, hVW, mul_one]
    change ι B (ι W x) = _
    rw [← mul_apply_eq_comp, ← map_mul, hBW.eq, map_mul,
      mul_apply_eq_comp, he', map_sub, map_smul]
    change (e : ℂ) • y - ι W (ι A x) = (e : ℂ) • y - ι D (ι W x)
    conv_rhs => rhs; rw [← mul_apply_eq_comp, ← map_mul, hcancel, map_mul,
      mul_apply_eq_comp]
  have henergy : ‖ι B y‖ ≤ (c / 2) * ‖y‖ := by
    rw [hBy]
    calc
      _ ≤ ‖(e : ℂ) • y‖ + ‖ι D y‖ := norm_sub_le _ _
      _ ≤ |e| * ‖y‖ + C * ‖y‖ := by
        apply add_le_add
        · simp [norm_smul, Real.norm_eq_abs]
        · exact ((ι D).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
      _ ≤ (c / 2) * ‖y‖ := by nlinarith [norm_nonneg y]
  have hhigh : ‖ι Q y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    calc
      _ ≤ c⁻¹ * ‖ι B y‖ := hB.norm_highProjection_apply_le c hc y
      _ ≤ c⁻¹ * ((c / 2) * ‖y‖) :=
        mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hc.le)
      _ = _ := by field_simp
  have hlow : ‖ι (1 - Q) y‖ ≤ Real.exp (s * c) * ‖x‖ := by
    have hcomm : (1 - Q) * W = W * (1 - Q) :=
      ((Commute.one_left W).sub_left hWQ.symm).eq
    change ‖ι (1 - Q) (ι W x)‖ ≤ _
    rw [← mul_apply_eq_comp, ← map_mul, hcomm]
    exact ((ι (W * (1 - Q))).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hB.norm_exp_mul_lowProjection_le s c hs)
        (norm_nonneg _))
  have hsplit : y = ι (1 - Q) y + ι Q y := by
    rw [← _root_.add_apply, ← map_add, sub_add_cancel, map_one,
      one_apply_eq_self]
  have htriangle : ‖y‖ ≤ ‖ι (1 - Q) y‖ + ‖ι Q y‖ := by
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  change ‖y‖ ≤ _
  linarith

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponential energy tails follow from the actual imaginary-time
perturbation estimate. Auxiliary to AKLV, arXiv:1301.1162v1, Lemma 6.7.
The conclusion applies to every eigenvector, without normalization. -/
theorem IsHermitian.norm_highProjection_eigenvector_le_exp {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (e s c C t : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (he : toEuclideanCLM (n := n) (𝕜 := ℂ) (B + A) x = (e : ℂ) • x)
    (hC : ‖NormedSpace.exp ((s : ℂ) • B) * A *
      NormedSpace.exp (-((s : ℂ) • B))‖ ≤ C)
    (hsmall : |e| + C ≤ c / 2) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (spectralProjectionGE B t) x‖ ≤
      2 * Real.exp (-s * (t - c)) * ‖x‖ := by
  let W := NormedSpace.exp ((s : ℂ) • B)
  let V := NormedSpace.exp (-((s : ℂ) • B))
  let ι := toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hVW : V * W = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hfactor : ι (spectralProjectionGE B t) x =
      ι (spectralProjectionGE B t * V) (ι W x) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_assoc, hVW, mul_one]
  rw [hfactor]
  calc
    _ ≤ ‖ι (spectralProjectionGE B t * V)‖ * ‖ι W x‖ :=
      (ι (spectralProjectionGE B t * V)).le_opNorm _
    _ ≤ Real.exp (-s * t) * (2 * Real.exp (s * c) * ‖x‖) :=
      mul_le_mul (hB.norm_highProjection_mul_exp_neg_le s t hs)
        (hB.norm_exp_apply_eigenvector_le A x e s c C hs hc he hC hsmall)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [show -s * (t - c) = -s * t + s * c by ring, Real.exp_add]
      ring

end Matrix

namespace TNLean.MPS.AreaLaw.AKLV

/-- The boundary perturbation has a short imaginary-time norm bound
independent of the chain length. This is derived from the original local
positive unit terms, as required by AKLV, arXiv:1301.1162v1, Lemma 6.6. -/
theorem norm_exp_conjugation_two_boundary_le_four {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (z : ℝ) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      (∑ i ∈ I, h i) - (z : ℂ) • 1
    ‖NormedSpace.exp (((1 / 8 : ℝ) : ℂ) • B) * (h a + h b) *
      NormedSpace.exp (-(((1 / 8 : ℝ) : ℂ) • B))‖ ≤ 4 := by
  intro B
  have hbound (i : Fin (L - 1)) :=
    norm_exp_conjugation_nearest_neighbour_shift_le_two I h
      (fun j _ ↦ hs j) (fun j _ ↦ h0 j) (fun j _ ↦ h1 j)
      (h i) (hs i) (z : ℂ) (1 / 8) (by norm_num) le_rfl
  have hnorm (i : Fin (L - 1)) : ‖h i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (h i) (h0 i)).mpr (h1 i)
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (by
    have ha := hbound a
    have hb := hbound b
    dsimp only at ha hb
    linarith [hnorm a, hnorm b])

/-- **Explicit AKLV truncation lemma.** An eigenvector of the normalized
chain with energy in `[0,6]` has high-energy tail at most
`2 exp(-(t-20)/8)` for the complementary Hamiltonian. In particular this
applies to the ground vector after the normalization of Section 6.1.
AKLV, arXiv:1301.1162v1, Lemma 6.7; this proof uses an exponential moment
instead of the printed shell induction. No energy-tail estimate is assumed. -/
theorem norm_groundState_highProjection_le_exp {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (z e t : ℝ)
    (x : EuclideanSpace ℂ (Fin L → Fin q))
    (he0 : 0 ≤ e) (he6 : e ≤ 6) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      (∑ i ∈ I, h i) - (z : ℂ) • 1
    Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (B + (h a + h b)) x = (e : ℂ) • x →
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (Matrix.spectralProjectionGE B t) x‖ ≤
        2 * Real.exp (-(t - 20) / 8) * ‖x‖ := by
  intro B he
  have hB : B.IsHermitian := by
    change IsSelfAdjoint B
    apply IsSelfAdjoint.sub
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)
    · rw [Complex.coe_smul]
      exact (IsSelfAdjoint.all z).smul (IsSelfAdjoint.one _)
  have hC := norm_exp_conjugation_two_boundary_le_four I h hs h0 h1 a b z
  have hsmall : |e| + 4 ≤ (20 : ℝ) / 2 := by rw [abs_of_nonneg he0]; linarith
  simpa only [show -(1 / 8 : ℝ) * (t - 20) = -(t - 20) / 8 by ring] using
    hB.norm_highProjection_eigenvector_le_exp (h a + h b) x e (1 / 8) 20 4 t
      (by norm_num) (by norm_num) he hC hsmall

end TNLean.MPS.AreaLaw.AKLV
