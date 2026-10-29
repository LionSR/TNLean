/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.InverseGapRobustness
import TNLean.MPS.AreaLaw.AKLV.SingleWindowPolynomialRank
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy
import QICLean.Analysis.ChebyshevSpectralFilter
import QICLean.Analysis.GroundProjection

/-!
# Chebyshev filters of a truncated chain

The normalized real Chebyshev polynomial fixes the unique ground vector,
preserves its orthogonal complement, and contracts squared norms there.
The Hamiltonian is the separate exterior clipping used by AKLV,
arXiv:1301.1162v1, Definition 3.1 and Sections 4 and 6.1.
The unsquared polynomial is Hermitian; positivity is not required.
The sign distinction is recorded at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
The favorable parameter optimization in the source is not asserted here;
the explicit rank certificate retains its logarithmic degree dependence.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- A rank-one gap and an upper spectral bound give the invariant-vector
Chebyshev filter of AKLV, arXiv:1301.1162v1, Lemma 4.1.
The shrinking coefficient bounds squared norms. -/
theorem exists_chebyshev_ground_filter
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g u : ℝ) (hg : 0 < g) (hgu : e + g ≤ u)
    (heig : Matrix.toEuclideanLin H Ω = (e : ℂ) • Ω)
    (hgap : (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hupper : H ≤ (u : ℂ) • 1) (k : ℕ) :
    ∃ p : Polynomial ℝ, p.natDegree = k ∧ p.eval e = 1 ∧
      let K : Matrix n n ℂ := Polynomial.aeval H p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt (g / (u - e)))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K Ω = Ω ∧
        ‖K - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
          2 * Real.exp (-2 * (k : ℝ) * Real.sqrt (g / (u - e))) ∧
        ∀ ψ : EuclideanSpace ℂ n, ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
          ⟪Ω, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
            ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ := by
  have hmul : H *ᵥ WithLp.ofLp Ω = (e : ℂ) • WithLp.ofLp Ω :=
    congrArg WithLp.ofLp heig
  have hspectrum : ∀ t ∈ spectrum ℝ H, t = e ∨ t ∈ Set.Icc (e + g) u := by
    intro t ht
    have hbound : t ≤ u := (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp
      (by simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using hupper) t ht
    obtain ⟨j, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ ht
    exact (GaussianFilter.eigenvector_ground_or_gap hH hΩ hmul hgap hg j).elim
      (fun he ↦ Or.inl he.1) (fun hx ↦ Or.inr ⟨by linarith [hx.1], hbound⟩)
  obtain ⟨p, hdegree, hpe, hP, hKP, _hPK, herr⟩ :=
    hH.exists_polynomial_approximating_isolated_energy_projection k
      (by linarith : e < e + g) hgu hspectrum
  have hcanonical := hH.complement_spectralProjectionGE_eq_rankOne hΩ hmul hgap hg
  rw [hcanonical] at hKP herr
  have hKHerm : (Polynomial.aeval H p).IsHermitian := by
    rw [← cfc_polynomial p H hH.isSelfAdjoint]
    exact cfc_predicate p.eval H
  have hPΩ : Matrix.toEuclideanLin
      (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) Ω = Ω := by
    simp [Matrix.toEuclideanLin_vecMulVec_star_self_apply,
      inner_self_eq_norm_sq_to_K, hΩ]
  have hfix : Matrix.toEuclideanLin (Polynomial.aeval H p) Ω = Ω := by
    simpa only [Matrix.toEuclideanLin_mul, LinearMap.comp_apply, hPΩ] using
      congrArg (fun T : Matrix n n ℂ ↦ Matrix.toEuclideanLin T Ω) hKP
  have hsub : e + g - e = g := by ring
  rw [hsub] at herr
  refine ⟨p, hdegree, hpe, hKHerm, hfix, herr, ?_⟩
  intro ψ hψ horth
  have hPψ : Matrix.toEuclideanLin
      (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ = 0 := by
    simp [Matrix.toEuclideanLin_vecMulVec_star_self_apply, horth]
  have hnorm : ‖Matrix.toEuclideanLin (Polynomial.aeval H p -
      Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ‖ ≤
      ‖Polynomial.aeval H p - Matrix.vecMulVec (WithLp.ofLp Ω)
        (star (WithLp.ofLp Ω))‖ * ‖ψ‖ :=
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
      (Polynomial.aeval H p - Matrix.vecMulVec (WithLp.ofLp Ω)
        (star (WithLp.ofLp Ω)))).le_opNorm ψ
  have hnorm' : ‖Matrix.toEuclideanLin (Polynomial.aeval H p) ψ‖ ≤
      2 * Real.exp (-2 * (k : ℝ) * Real.sqrt (g / (u - e))) := by
    apply le_trans ?_ herr
    simpa only [map_sub, LinearMap.sub_apply, hPψ, sub_zero, hψ, mul_one] using hnorm
  refine ⟨?_, pow_le_pow_left₀ (norm_nonneg _) hnorm' 2⟩
  rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hKHerm) Ω ψ, hfix, horth]

/-- The middle budget counts its original unit bonds and the absolute
value of its scalar energy shift. -/
def middleCutBudget {L : ℕ} (a b : Fin (L - 1)) (m : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)).card : ℝ) +
    2 + |m|

/-- For a window of `2*w` consecutive unit bonds the middle budget is
exactly `2*w + |m|`. In particular the frustration-free budget is the
number of untruncated middle bonds. -/
theorem middleCutBudget_eq {L w : ℕ} (a b : Fin (L - 1))
    (hab : a.val < b.val) (hwindow : b.val + 1 = a.val + 2 * w) (m : ℝ) :
    middleCutBudget a b m = (2 * w : ℕ) + |m| := by
  classical
  have hset : Finset.univ.filter (fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val) =
      Finset.Ioo a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, Fin.lt_def]
  unfold middleCutBudget
  rw [hset, Fin.card_Ioo]
  congr 1
  have hcount : b.val - a.val - 1 + 2 = 2 * w := by omega
  exact_mod_cast hcount

/-- The actual separately clipped chain has norm at most twice the
cutoff plus the middle unit-bond budget. AKLV, Definition 3.1 and
Section 6.1, with the scalar middle shift displayed explicitly. -/
theorem normalized_chain_truncation_bounds {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (x m y t : ℝ)
    (hX : (leftCutBlock h a x).PosSemidef)
    (hN : (middleCutBlock h a b m).PosSemidef)
    (hY : (rightCutBlock h b y).PosSemidef) (ht : 0 ≤ t) :
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    Ht.PosSemidef ∧ Ht ≤ ((2 * t + middleCutBudget a b m : ℝ) : ℂ) • 1 ∧
      ‖Ht‖ ≤ 2 * t + middleCutBudget a b m := by
  intro Ht
  classical
  let S := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val
  have hsum : (∑ i ∈ S, h i) ≤ (S.card : ℂ) • 1 := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul ℂ] using
      (show (∑ i ∈ S, h i) ≤ ∑ _i ∈ S, (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        from Finset.sum_le_sum fun i _ ↦ h1 i)
  have hscalar : (-(m : ℂ)) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤
      ((|m| : ℝ) : ℂ) • 1 := by
    rw [← Complex.ofReal_neg, Complex.coe_smul, Complex.coe_smul]
    exact
      (smul_le_smul_of_nonneg_right (neg_le_abs m)
        ((Matrix.PosSemidef.one :
          (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ).PosSemidef).nonneg))
  have hcap : middleCutBlock h a b m + (h a + h b) ≤
      (middleCutBudget a b m : ℂ) • 1 := by
    have h := add_le_add (add_le_add hsum hscalar) (add_le_add (h1 a) (h1 b))
    simpa only [middleCutBlock, S, sub_eq_add_neg, ← neg_smul, middleCutBudget,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      add_smul, two_smul, add_assoc, add_left_comm, add_comm] using h
  have hM : (middleCutBlock h a b m + (h a + h b)).PosSemidef :=
    hN.add (Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b)))
  obtain ⟨hpos, _hle, hbudget⟩ := twoSidedEnergyTruncation_bounds
    (leftCutBlock h a x) _ (rightCutBlock h b y) hX hM hY t
    (middleCutBudget a b m) ht hcap
  refine ⟨hpos, hbudget, ?_⟩
  apply (CStarAlgebra.norm_le_iff_le_algebraMap Ht (by
    dsimp [middleCutBudget]
    positivity) hpos.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using hbudget

/-- For every degree and every cutoff above the explicit robustness
threshold, the actual clipped normalized chain has a Chebyshev filter
fixing its unit ground vector, with invariant orthogonal complement and
squared shrinking. The ground vector is exponentially close, up to
phase, to the original one. AKLV, Lemma 4.1 and Theorem 6.1.
The operator-Schmidt estimate is a separate geometric assertion. -/
theorem exists_normalized_chain_chebyshev_filter {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y e g t : ℝ)
    (hX : (leftCutBlock h a x).PosSemidef)
    (hN : (middleCutBlock h a b m).PosSemidef)
    (hY : (rightCutBlock h b y).PosSemidef)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 * (e + g) / g ^ 2 ≤ t) (k : ℕ) :
    let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    let u := 2 * t + middleCutBudget a b m
    Matrix.toEuclideanLin H Ω = (e : ℂ) • Ω →
    (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ),
      ‖φ‖ = 1 ∧ 0 ≤ e' ∧ e' ≤ e ∧
      Matrix.toEuclideanLin Ht φ = (e' : ℂ) • φ ∧
      (Ht - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
      ‖Ht‖ ≤ u ∧ p.natDegree = k ∧ p.eval e' = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval Ht p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (u - e')))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K φ = φ ∧
      (∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
        ⟪φ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ) ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro H Ht u heig hgap
  have hcut : 32768 * (e + g) ≤ t * g ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hg)).mp ht
  have ht0 : 0 < t := by nlinarith [sq_pos_of_pos hg]
  have htg : 32768 ≤ t * g := by
    have h : (32768 : ℝ) * g ≤ (t * g) * g := by nlinarith
    exact le_of_mul_le_mul_right h hg
  have htlarge : 32768 ≤ t := htg.trans (mul_le_of_le_one_right ht0.le hg1)
  obtain ⟨e', φ, hφ, heig', he'0, he'e, hgap', hphase⟩ :=
    normalized_chain_robustness h hs h0 h1 a b hab x m y e g t
      hX hN hY Ω hΩ he0 he6 hg hg1 ht heig hgap
  obtain ⟨hpos, hupper, hnorm⟩ :=
    normalized_chain_truncation_bounds h h0 h1 a b x m y t hX hN hY ht0.le
  have hendpoint : e' + g / 2 ≤ u := by
    have hbudget : 2 ≤ middleCutBudget a b m := by
      dsimp [middleCutBudget]
      linarith [Nat.cast_nonneg (α := ℝ)
        (Finset.univ.filter (fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)).card,
        abs_nonneg m]
    dsimp [u]
    linarith
  obtain ⟨p, hdegree, hpe, hKHerm, hfix, _herr, hperp⟩ :=
    exists_chebyshev_ground_filter Ht hpos.isHermitian φ hφ e' (g / 2) u
      (by positivity) hendpoint heig' hgap' hupper k
  exact ⟨e', φ, p, hφ, he'0, he'e, heig', hgap', hnorm, hdegree, hpe,
    hKHerm, hfix, hperp, hphase⟩

/-- In the frustration-free case the original zero-energy ground vector
is retained exactly by exterior truncation. The gap is at least half
the original one for the explicit cutoff `32768/g`.
AKLV, arXiv:1301.1162v1, Section 4 following Lemma 4.2 and Theorem 6.1.
Positivity of the unit bonds and zero total ground energy express the
frustration-free qualification. -/
theorem exists_frustrationFree_chain_chebyshev_filter {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 32768 / g ≤ t) (k : ℕ) :
    let H := ∑ i, h i
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a 0)
      (middleCutBlock h a b 0 + (h a + h b)) (rightCutBlock h b 0) t
    let u := 2 * t + middleCutBudget a b 0
    Matrix.toEuclideanLin H Ω = 0 →
    (H - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    Matrix.toEuclideanLin Ht Ω = 0 ∧
    (Ht - ((g / 2 : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef ∧
    ‖Ht‖ ≤ u ∧
    ∃ p : Polynomial ℝ, p.natDegree = k ∧ p.eval 0 = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval Ht p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / u))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K Ω = Ω ∧
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
          ⟪Ω, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
            ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ := by
  intro H Ht u heig hgap
  have hX : (leftCutBlock h a 0).PosSemidef := by
    simpa only [leftCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      Matrix.posSemidef_sum (Finset.univ.filter fun i : Fin (L - 1) ↦ i.val < a.val)
        (fun i _ ↦ Matrix.nonneg_iff_posSemidef.mp (h0 i))
  have hN : (middleCutBlock h a b 0).PosSemidef := by
    simpa only [middleCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      Matrix.posSemidef_sum
        (Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)
        (fun i _ ↦ Matrix.nonneg_iff_posSemidef.mp (h0 i))
  have hY : (rightCutBlock h b 0).PosSemidef := by
    simpa only [rightCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      Matrix.posSemidef_sum (Finset.univ.filter fun i : Fin (L - 1) ↦ b.val < i.val)
        (fun i _ ↦ Matrix.nonneg_iff_posSemidef.mp (h0 i))
  have hcut : 32768 * ((0 : ℝ) + g) / g ^ 2 ≤ t := by
    convert ht using 1
    field_simp
    ring
  have ht0 : 0 ≤ t := (by positivity : 0 < (32768 : ℝ) / g).le.trans ht
  obtain ⟨e', φ, hφ, heig', he'0, he'e, hgap', _hphase⟩ :=
    normalized_chain_robustness h hs h0 h1 a b hab 0 0 0 0 g t
      hX hN hY Ω hΩ (le_refl 0) (by norm_num) hg hg1 hcut
      (by
        simp only [zero_add, Complex.ofReal_zero, zero_smul, sub_zero]
        change Matrix.toEuclideanLin H Ω = 0
        exact heig)
      (by simpa only [zero_add, Complex.ofReal_zero, zero_smul, sub_zero] using hgap)
  have he' : e' = 0 := le_antisymm he'e he'0
  subst e'
  simp only [Complex.ofReal_zero, zero_smul, sub_zero] at heig' hgap'
  obtain ⟨hpos, hupper, hnorm⟩ :=
    normalized_chain_truncation_bounds h h0 h1 a b 0 0 0 t hX hN hY ht0
  have hbelow : Ht ≤ H := by
    have hb := (twoSidedEnergyTruncation_posSemidef_le _ _ _ hX
      (hN.add (Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b)))) hY t ht0).2
    have hsum := normalizedCutBlock_sum h a b hab 0 0 0
    simp only [zero_add, Complex.ofReal_zero, zero_smul, sub_zero] at hsum
    apply hb.trans_eq
    dsimp [H]
    rw [← hsum]
    abel
  have hΩmul : Ht *ᵥ WithLp.ofLp Ω = 0 := by
    simpa only [Complex.ofReal_zero, zero_smul] using
      Matrix.mulVec_eq_smul_of_order_sandwich H Ht 0 (WithLp.ofLp Ω)
        (by simpa only [Complex.ofReal_zero, zero_smul] using hpos.nonneg) hbelow
        (by simpa only [Complex.ofReal_zero, zero_smul] using (show H *ᵥ WithLp.ofLp Ω = 0 from
          (congrArg WithLp.ofLp heig).trans (WithLp.ofLp_zero 2)))
  have hΩzero : Matrix.toEuclideanLin Ht Ω = 0 := by
    apply WithLp.ofLp_injective 2
    exact hΩmul
  have heq : Ω = ⟪φ, Ω⟫_ℂ • φ :=
    Matrix.PosSemidef.eq_inner_smul_of_gap (H := Ht) (E₀ := 0) (Δ := g / 2)
      (Ω := φ) (ψ := Ω) (by simpa using hgap') (by positivity) hφ
      (by simpa using hΩmul)
  have hcoef : ‖⟪φ, Ω⟫_ℂ‖ = 1 := by
    have hn := congrArg norm heq
    simpa only [norm_smul, hΩ, hφ, mul_one] using hn.symm
  have hscalar : star ⟪φ, Ω⟫_ℂ * ⟪φ, Ω⟫_ℂ = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hcoef]
    norm_num
  have hproj : Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) =
      Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) := by
    conv_lhs => rw [heq]
    simp only [WithLp.ofLp_smul, star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
      smul_smul, hscalar, one_smul]
  have hgapΩ : (Ht - ((g / 2 : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    rw [hproj]
    exact hgap'
  have hlarge : 32768 ≤ t := by
    have htg := (div_le_iff₀ hg).mp ht
    exact htg.trans (mul_le_of_le_one_right ht0 hg1)
  have hendpoint : 0 + g / 2 ≤ u := by
    have hbudget : 0 ≤ middleCutBudget a b 0 := by
      unfold middleCutBudget
      exact add_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num)) (abs_nonneg _)
    dsimp [u]
    linarith
  obtain ⟨p, hdegree, hpe, hKHerm, hfix, _herr, hperp⟩ :=
    exists_chebyshev_ground_filter Ht hpos.isHermitian Ω hΩ 0 (g / 2) u
      (by positivity) hendpoint (by simpa using hΩzero)
      (by simpa using hgapΩ) hupper k
  exact ⟨hΩzero, hgapΩ, hnorm, p, hdegree, hpe, hKHerm, hfix,
    by simpa only [sub_zero] using hperp⟩

/-- The sum of the middle unit bonds is the consecutive window of the
chain, with its scalar normalization shift removed. -/
private theorem middleCutBlock_window {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (a b : Fin (L - 1)) (hab : a.val < b.val)
    (hwindow : b.val + 1 = a.val + 2 * w) (m : ℝ) :
    middleCutBlock h a b m + (h a + h b) =
      (∑ r : Fin (2 * w), h ⟨a.val + r.val, by omega⟩) - (m : ℂ) • 1 := by
  classical
  let S := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val ≤ i.val ∧ i.val ≤ b.val
  let M := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val
  have hsum : (∑ r : Fin (2 * w), h ⟨a.val + r.val, by omega⟩) = ∑ i ∈ S, h i := by
    apply Finset.sum_bij (fun r _ ↦ (⟨a.val + r.val, by omega⟩ : Fin (L - 1)))
    · intro r _
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro r _ s _ hrs
      apply Fin.ext
      have := congrArg Fin.val hrs
      dsimp at this
      omega
    · intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨⟨i.val - a.val, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp
      omega
    · intro r _
      rfl
  have hS : S = insert a (insert b M) := by
    ext i
    simp only [S, M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have ha : a ∉ insert b M := by
    simp only [M, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.ext_iff]
    omega
  have hb : b ∉ M := by simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [hsum, hS, Finset.sum_insert ha, Finset.sum_insert hb]
  dsimp [middleCutBlock, M]
  abel

/-- A polynomial of the actual separately clipped normalized chain has
a single-cut operator-Schmidt bound. All support and polynomial
certificates are derived from the original nearest-neighbour terms.
Supporting AKLV, arXiv:1301.1162v1, Lemma 4.2. -/
theorem normalized_chain_polynomial_rank {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (a b : Fin (L - 1)) (hab : a.val < b.val) (hw : 1 ≤ w)
    (hwindow : b.val + 1 = a.val + 2 * w)
    (x m y t : ℝ) (τ : Fin q) (k : ℕ) (hk : 1 ≤ k)
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k) :
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    let A := interval L 0 (a.val + w + 1)
    Matrix.operatorSchmidtRank ((Polynomial.aeval Ht P).reindex
      (TNLean.Lattice.sheetSplit q A) (TNLean.Lattice.sheetSplit q A)) ≤
      (q * k) ^ (17 * (w + k / (2 * w))) := by
  intro Ht A
  classical
  let W : Fin (2 * w) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun r ↦ h ⟨a.val + r.val, by omega⟩
  have hW (r : Fin (2 * w)) : W r ∈ QuantumCircuit.supportedOperators q
      (interval L (a.val + r.val) (a.val + r.val + 2) : Set (Fin L)) :=
    QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs _)
  have hX : leftCutBlock h a x ∈ QuantumCircuit.supportedOperators q
      (interval L 0 (a.val + 1) : Set (Fin L)) := by
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact QuantumCircuit.supportedOperators_mono
        (Finset.coe_subset.mpr (interval_mono (by omega) (by omega)))
        (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))
    · exact Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _)
  have hY : rightCutBlock h b y ∈ QuantumCircuit.supportedOperators q
      (interval L (a.val + 2 * w) L : Set (Fin L)) := by
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact QuantumCircuit.supportedOperators_mono
        (Finset.coe_subset.mpr (interval_mono (a := i.val) (b := i.val + 2)
          (a' := a.val + 2 * w) (b' := L) (by omega) (by omega)))
        (QuantumCircuit.mem_supportedOperators_of_isSupportedOn (hs i))
    · exact Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _)
  let PL := Matrix.energyTruncation (leftCutBlock h a x) t - (m : ℂ) • 1
  let PR := Matrix.energyTruncation (rightCutBlock h b y) t
  have hPL : PL ∈ QuantumCircuit.supportedOperators q
      (interval L 0 (a.val + 1) : Set (Fin L)) :=
    Submodule.sub_mem _ (LocalSolution.cfc_mem_supportedOperators _ hX)
      (Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _))
  have hPR : PR ∈ QuantumCircuit.supportedOperators q
      (interval L (a.val + 2 * w) L : Set (Fin L)) :=
    LocalSolution.cfc_mem_supportedOperators _ hY
  have hHt : Ht = (∑ r, W r) + PL + PR := by
    dsimp [Ht, twoSidedEnergyTruncation, PL, PR]
    rw [middleCutBlock_window h a b hab hwindow m]
    dsimp [W]
    abel
  rw [hHt]
  exact operatorSchmidtRank_aeval_single_window_le_pow W PL PR hW hPL hPR
    hw (by omega) τ k hk P hdeg

/-- The single-cut polynomial estimate in the real-polynomial and
entropy cut coordinates used by the Chebyshev construction. -/
theorem normalized_chain_real_polynomial_rank {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (a b : Fin (L - 1)) (hab : a.val < b.val) (hw : 1 ≤ w)
    (hwindow : b.val + 1 = a.val + 2 * w)
    (x m y t : ℝ) (τ : Fin q) (k : ℕ) (hk : 1 ≤ k)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ k) :
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    let A := interval L 0 (a.val + w + 1)
    Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ ↦ q) A
      (Polynomial.aeval Ht p)) ≤ (q * k) ^ (17 * (w + k / (2 * w))) := by
  intro Ht A
  have hmap : Polynomial.aeval Ht p =
      Polynomial.aeval Ht (p.map (algebraMap ℝ ℂ)) :=
    Polynomial.aeval_eq_aeval_map (by
      ext z
      simp only [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]) p Ht
  rw [hmap, ← operatorSchmidtRank_sheetSplit_eq_cutOperator]
  exact normalized_chain_polynomial_rank h hs a b hab hw hwindow x m y t τ k hk
    (p.map (algebraMap ℝ ℂ)) (Polynomial.natDegree_map_le.trans hdeg)

/-- The physical Chebyshev approximate ground-state projector of a
normalized truncated chain, for every positive degree and every cutoff
above the explicit robustness threshold. The gap, norm, unit ground
vector, invariant complement, squared shrinking and single-cut rank are
all derived. AKLV, arXiv:1301.1162v1, Sections 4 and 6.1.

The stated rank is the explicit single-window consequence of the proved
two-window polynomial estimate. No favorable parameter schedule or
positivity of the unsquared filter is asserted. -/
theorem exists_normalized_chain_chebyshev_agsp {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (hw : 1 ≤ w)
    (hwindow : b.val + 1 = a.val + 2 * w) (x m y e g t : ℝ)
    (hX : (leftCutBlock h a x).PosSemidef)
    (hN : (middleCutBlock h a b m).PosSemidef)
    (hY : (rightCutBlock h b y).PosSemidef)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 * (e + g) / g ^ 2 ≤ t) (k : ℕ) (hk : 1 ≤ k) :
    let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    let u := 2 * t + middleCutBudget a b m
    let A := interval L 0 (a.val + w + 1)
    let D := (q * k) ^ (17 * (w + k / (2 * w)))
    Matrix.toEuclideanLin H Ω = (e : ℂ) • Ω →
    (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ),
      ‖φ‖ = 1 ∧ 0 ≤ e' ∧ e' ≤ e ∧
      Matrix.toEuclideanLin Ht φ = (e' : ℂ) • φ ∧
      (Ht - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
      ‖Ht‖ ≤ u ∧ p.natDegree = k ∧ p.eval e' = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval Ht p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (u - e')))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K φ = φ ∧
      (∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
        ⟪φ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ) ∧
      Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ ↦ q) A K) ≤ D ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro H Ht u A D heig hgap
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp
    ((WithLp.ofLp_eq_zero (x := Ω)).not.mpr (norm_ne_zero_iff.mp (by simp [hΩ])))
  let τ : Fin q := σ₀ ⟨0, by omega⟩
  obtain ⟨e', φ, p, hφ, he'0, he'e, heig', hgap', hnorm, hdegree, hpe,
      hKHerm, hfix, hperp, hphase⟩ :=
    exists_normalized_chain_chebyshev_filter h hs h0 h1 a b hab x m y e g t
      hX hN hY Ω hΩ he0 he6 hg hg1 ht k heig hgap
  exact ⟨e', φ, p, hφ, he'0, he'e, heig', hgap', hnorm, hdegree, hpe,
    hKHerm, hfix, hperp,
    normalized_chain_real_polynomial_rank h hs a b hab hw hwindow x m y t τ k hk p hdegree.le,
    hphase⟩

/-- The same physical Chebyshev projector exists already at cutoff `32768/g`.
The refined robustness comparison retains the positive high-energy diagonal;
all spectral and single-cut rank conclusions refer to the unchanged actual
clipping and polynomial. Refinement of AKLV, arXiv:1301.1162v1,
Theorem 6.1 and Section 4. The original normalized energy may be positive. -/
theorem exists_normalized_chain_chebyshev_agsp_of_inverse_gap_cutoff {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (hw : 1 ≤ w)
    (hwindow : b.val + 1 = a.val + 2 * w) (x m y e g t : ℝ)
    (hX : (leftCutBlock h a x).PosSemidef)
    (hN : (middleCutBlock h a b m).PosSemidef)
    (hY : (rightCutBlock h b y).PosSemidef)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 / g ≤ t) (k : ℕ) (hk : 1 ≤ k) :
    let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a x)
      (middleCutBlock h a b m + (h a + h b)) (rightCutBlock h b y) t
    let u := 2 * t + middleCutBudget a b m
    let A := interval L 0 (a.val + w + 1)
    let D := (q * k) ^ (17 * (w + k / (2 * w)))
    Matrix.toEuclideanLin H Ω = (e : ℂ) • Ω →
    (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)) (p : Polynomial ℝ),
      ‖φ‖ = 1 ∧ 0 ≤ e' ∧ e' ≤ e ∧
      Matrix.toEuclideanLin Ht φ = (e' : ℂ) • φ ∧
      (Ht - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
      ‖Ht‖ ≤ u ∧ p.natDegree = k ∧ p.eval e' = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval Ht p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / (u - e')))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K φ = φ ∧
      (∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪φ, ψ⟫_ℂ = 0 →
        ⟪φ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ) ∧
      Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ ↦ q) A K) ≤ D ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro H Ht u A D heig hgap
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp
    ((WithLp.ofLp_eq_zero (x := Ω)).not.mpr (norm_ne_zero_iff.mp (by simp [hΩ])))
  let τ : Fin q := σ₀ ⟨0, by omega⟩
  have ht0 : 0 ≤ t := (by positivity : 0 < (32768 : ℝ) / g).le.trans ht
  have htlarge : 32768 ≤ t :=
    ((div_le_iff₀ hg).mp ht).trans (mul_le_of_le_one_right ht0 hg1)
  obtain ⟨e', φ, hφ, heig', he'0, he'e, hgap', hphase⟩ :=
    normalized_chain_robustness_of_inverse_gap_cutoff h hs h0 h1 a b hab x m y e g t
      hX hN hY Ω hΩ he0 he6 hg hg1 ht heig hgap
  obtain ⟨hpos, hupper, hnorm⟩ :=
    normalized_chain_truncation_bounds h h0 h1 a b x m y t hX hN hY ht0
  have hendpoint : e' + g / 2 ≤ u := by
    have hbudget : 2 ≤ middleCutBudget a b m := by
      unfold middleCutBudget
      linarith [Nat.cast_nonneg (α := ℝ)
        (Finset.univ.filter (fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)).card,
        abs_nonneg m]
    dsimp [u]
    linarith
  obtain ⟨p, hdegree, hpe, hKHerm, hfix, _herr, hperp⟩ :=
    exists_chebyshev_ground_filter Ht hpos.isHermitian φ hφ e' (g / 2) u
      (by positivity) hendpoint heig' hgap' hupper k
  exact ⟨e', φ, p, hφ, he'0, he'e, heig', hgap', hnorm, hdegree, hpe,
    hKHerm, hfix, hperp,
    normalized_chain_real_polynomial_rank h hs a b hab hw hwindow x m y t τ k hk p hdegree.le,
    hphase⟩

/-- In a frustration-free chain the actual Chebyshev filter fixes the
original unit ground vector exactly and has the explicit single-cut
rank bound. AKLV, arXiv:1301.1162v1, Section 4.
The shrinking factor is for squared norms of unit perpendicular vectors. -/
theorem exists_frustrationFree_chain_chebyshev_agsp {L q w : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (hw : 1 ≤ w)
    (hwindow : b.val + 1 = a.val + 2 * w)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 32768 / g ≤ t)
    (k : ℕ) (hk : 1 ≤ k) :
    let H := ∑ i, h i
    let Ht := twoSidedEnergyTruncation (leftCutBlock h a 0)
      (middleCutBlock h a b 0 + (h a + h b)) (rightCutBlock h b 0) t
    let u := 2 * t + middleCutBudget a b 0
    let A := interval L 0 (a.val + w + 1)
    let D := (q * k) ^ (17 * (w + k / (2 * w)))
    Matrix.toEuclideanLin H Ω = 0 →
    (H - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    Matrix.toEuclideanLin Ht Ω = 0 ∧
    (Ht - ((g / 2 : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef ∧
    ‖Ht‖ ≤ u ∧
    ∃ p : Polynomial ℝ, p.natDegree = k ∧ p.eval 0 = 1 ∧
      let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval Ht p
      let δ := (2 * Real.exp (-2 * (k : ℝ) * Real.sqrt ((g / 2) / u))) ^ 2
      K.IsHermitian ∧ Matrix.toEuclideanLin K Ω = Ω ∧
      (∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
        ⟪Ω, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ) ∧
      Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ ↦ q) A K) ≤ D := by
  intro H Ht u A D heig hgap
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp
    ((WithLp.ofLp_eq_zero (x := Ω)).not.mpr (norm_ne_zero_iff.mp (by simp [hΩ])))
  let τ : Fin q := σ₀ ⟨0, by omega⟩
  obtain ⟨heig', hgap', hnorm, p, hdegree, hpe, hKHerm, hfix, hperp⟩ :=
    exists_frustrationFree_chain_chebyshev_filter h hs h0 h1 a b hab Ω hΩ
      g t hg hg1 ht k heig hgap
  exact ⟨heig', hgap', hnorm, p, hdegree, hpe, hKHerm, hfix, hperp,
    normalized_chain_real_polynomial_rank h hs a b hab hw hwindow 0 0 0 t τ k hk p hdegree.le⟩

end TNLean.MPS.AreaLaw.AKLV
