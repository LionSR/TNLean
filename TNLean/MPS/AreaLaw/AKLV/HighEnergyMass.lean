/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.Truncation
import QICLean.Analysis.OrthogonalResolutionCfc
import QICLean.Analysis.DetectabilityLemma

/-!
# High-energy mass under separate exterior clipping

Three commuting positive regional operators describe the disconnected
Hamiltonian in AKLV, arXiv:1301.1162v1, Section 6.3. Separate clipping of
the two exterior operators still costs at least the cutoff on the high
spectral subspace of their original sum. This is the order input to
Lemma 6.5(1).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Separate exterior clipping dominates the high-energy spectral
projection of the disconnected sum. AKLV, arXiv:1301.1162v1,
Lemma 6.5(1). All positivity and commutation assumptions are on the
original regional operators, before clipping. -/
theorem cutoff_smul_highProjection_le_twoSidedEnergyTruncation
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) (ht : 0 ≤ t) :
    (t : ℂ) • Matrix.spectralProjectionGE (L + N + R) t ≤
      twoSidedEnergyTruncation L N R t := by
  classical
  let l := hL.isHermitian
  let m := hN.isHermitian
  let r := hR.isHermitian
  let PL := l.isOrthogonalResolution_spectralProj
  let PN := m.isOrthogonalResolution_spectralProj
  let PR := r.isOrthogonalResolution_spectralProj
  have hcLN (a : l.eigenvalueSet) (b : m.eigenvalueSet) :
      Commute (l.spectralProj a) (m.spectralProj b) :=
    (m.commute_spectralProj (l.commute_spectralProj hLN a).symm b).symm
  let PLN := PL.prod PN hcLN
  have hcR (p : l.eigenvalueSet × m.eigenvalueSet) (c : r.eigenvalueSet) :
      Commute (l.spectralProj p.1 * m.spectralProj p.2) (r.spectralProj c) :=
    ((r.commute_spectralProj (l.commute_spectralProj hLR p.1).symm c).symm).mul_left
      ((r.commute_spectralProj (m.commute_spectralProj hNR p.2).symm c).symm)
  let P := PLN.prod PR hcR
  have hherm (p : (l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) :
      ((l.spectralProj p.1.1 * m.spectralProj p.1.2) * r.spectralProj p.2).IsHermitian :=
    (((l.isHermitian_spectralProj p.1.1).commute_iff
      (m.isHermitian_spectralProj p.1.2)).mp (hcLN p.1.1 p.1.2)).commute_iff
      (r.isHermitian_spectralProj p.2) |>.mp (hcR p.1 p.2)
  have hLhom : P.hom (fun p ↦ ((p.1.1 : ℝ) : ℂ)) = L :=
    (PLN.prod_hom_fst PR P _).trans ((PL.prod_hom_fst PN PLN _).trans l.eq_hom.symm)
  have hNhom : P.hom (fun p ↦ ((p.1.2 : ℝ) : ℂ)) = N :=
    (PLN.prod_hom_fst PR P _).trans ((PL.prod_hom_snd PN PLN _).trans m.eq_hom.symm)
  have hRhom : P.hom (fun p ↦ ((p.2 : ℝ) : ℂ)) = R :=
    (PLN.prod_hom_snd PR P _).trans r.eq_hom.symm
  let b : ((l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) → ℝ :=
    fun p ↦ (p.1.1 : ℝ) + (p.1.2 : ℝ) + (p.2 : ℝ)
  let k : ((l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) → ℝ :=
    fun p ↦ min (p.1.1 : ℝ) t + (p.1.2 : ℝ) + min (p.2 : ℝ) t
  let J := (l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet
  have hBhom : P.hom (fun p ↦ (b p : ℂ)) = L + N + R := by
    have hfun : (fun p ↦ (b p : ℂ)) =
        (((fun p : J ↦ ((p.1.1 : ℝ) : ℂ)) +
          (fun p ↦ ((p.1.2 : ℝ) : ℂ))) + (fun p ↦ ((p.2 : ℝ) : ℂ))) := by
      ext p
      simp only [b, Pi.add_apply, Complex.ofReal_add]
    rw [hfun, map_add, map_add, hLhom, hNhom, hRhom]
  have hKhom : P.hom (fun p ↦ (k p : ℂ)) = twoSidedEnergyTruncation L N R t := by
    have hLt : P.hom (fun p ↦ ((min (p.1.1 : ℝ) t : ℝ) : ℂ)) =
        Matrix.energyTruncation L t :=
      (P.cfc_hom hherm (fun x ↦ min x t) (fun p ↦ (p.1.1 : ℝ))).symm.trans
        (congrArg (cfc (fun x : ℝ ↦ min x t)) hLhom)
    have hRt : P.hom (fun p ↦ ((min (p.2 : ℝ) t : ℝ) : ℂ)) =
        Matrix.energyTruncation R t :=
      (P.cfc_hom hherm (fun x ↦ min x t) (fun p ↦ (p.2 : ℝ))).symm.trans
        (congrArg (cfc (fun x : ℝ ↦ min x t)) hRhom)
    have hfun : (fun p ↦ (k p : ℂ)) =
        (((fun p : J ↦ ((min (p.1.1 : ℝ) t : ℝ) : ℂ)) +
          (fun p ↦ ((p.1.2 : ℝ) : ℂ))) +
          (fun p ↦ ((min (p.2 : ℝ) t : ℝ) : ℂ))) := by
      ext p
      simp only [k, Pi.add_apply, Complex.ofReal_add]
    rw [hfun, map_add, map_add, hLt, hNhom, hRt, twoSidedEnergyTruncation]
  have hQhom : Matrix.spectralProjectionGE (L + N + R) t =
      P.hom (fun p ↦ ((if t ≤ b p then 1 else 0 : ℝ) : ℂ)) := by
    rw [Matrix.spectralProjectionGE, ← hBhom, P.cfc_hom hherm]
  have hnonneg (A : Matrix n n ℂ) (hA : A.PosSemidef)
      (u : hA.isHermitian.eigenvalueSet) : 0 ≤ (u : ℝ) := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp u.property
    rw [← hi]
    exact spectrum_nonneg_of_nonneg hA.nonneg (hA.isHermitian.eigenvalues_mem_spectrum_real i)
  rw [hQhom, ← hKhom, Matrix.le_iff]
  have hscale : (t : ℂ) • P.hom (fun p ↦ ((if t ≤ b p then 1 else 0 : ℝ) : ℂ)) =
      P.hom (fun p ↦ ((t * if t ≤ b p then 1 else 0 : ℝ) : ℂ)) := by
    rw [← map_smul]
    congr 1
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [hscale, ← map_sub]
  convert P.posSemidef_hom hherm (f := fun p ↦ k p - t * if t ≤ b p then 1 else 0) ?_ using 1
  · congr 1
    ext p
    simp only [Pi.sub_apply, Complex.ofReal_sub]
  · intro p
    have hl0 := hnonneg L hL p.1.1
    have hn0 := hnonneg N hN p.1.2
    have hr0 := hnonneg R hR p.2
    dsimp only [k, b]
    split_ifs with hsum
    · by_cases hl : t ≤ (p.1.1 : ℝ)
      · rw [min_eq_right hl]
        have hmin := le_min hr0 ht
        linarith
      · by_cases hr : t ≤ (p.2 : ℝ)
        · rw [min_eq_right hr]
          have hmin := le_min hl0 ht
          linarith
        · rw [min_eq_left (le_of_not_ge hl), min_eq_left (le_of_not_ge hr)]
          linarith
    · have hl := le_min hl0 ht
      have hr := le_min hr0 ht
      linarith

end TNLean.MPS.AreaLaw.AKLV

namespace TNLean.MPS.AreaLaw.AKLV

/-- The high-energy mass of any vector is bounded by its actual clipped
energy. This is AKLV, arXiv:1301.1162v1, Lemma 6.5(1), before division
by the cutoff. The positive boundary coupling need not commute with any
of the three disconnected blocks. -/
theorem cutoff_mul_sq_norm_highProjection_le_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℂ n) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := twoSidedEnergyTruncation L (N + A) R t
    t * ‖ι Q x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re := by
  intro ι Q K
  have hbase := cutoff_smul_highProjection_le_twoSidedEnergyTruncation
    L N R hL hN hR hLN hLR hNR t ht
  have hK : K = twoSidedEnergyTruncation L N R t + A := by
    dsimp [K, twoSidedEnergyTruncation]
    abel
  have hle : (t : ℂ) • Q ≤ K :=
    hbase.trans (by rw [hK]; exact le_add_of_nonneg_right hA.nonneg)
  have hQ : IsStarProjection (ι Q) :=
    ((hL.isHermitian.add hN.isHermitian).add hR.isHermitian
      |>.isStarProjection_spectralProjectionGE t).map ι
  have hpositive : (ι (K - (t : ℂ) • Q)).IsPositive :=
    (Matrix.le_iff.mp hle).isPositive_toEuclideanCLM
  have h := hpositive.re_inner_nonneg_right x
  rw [map_sub, map_smul] at h
  change 0 ≤ (⟪x, ι K x - (t : ℂ) • ι Q x⟫_ℂ).re at h
  rw [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul] at h
  have hinner := ContinuousLinearMap.IsStarProjection.re_inner_apply_self hQ x
  change (⟪x, ι Q x⟫_ℂ).re = ‖ι Q x‖ ^ 2 at hinner
  rw [hinner] at h
  linarith

/-- The high-energy norm bound of AKLV, arXiv:1301.1162v1, Lemma 6.5(1),
for the actual two-sided energy truncation. No normalization is needed. -/
theorem norm_highProjection_le_sqrt_clipped_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℂ n) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := twoSidedEnergyTruncation L (N + A) R t
    ‖ι Q x‖ ≤ Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι Q K
  have h := cutoff_mul_sq_norm_highProjection_le_energy
    L N R A hL hN hR hA hLN hLR hNR t ht.le x
  have hsq : ‖ι Q x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re / t :=
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)
  calc
    _ = Real.sqrt (‖ι Q x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- The corrected Cauchy--Schwarz bound in AKLV, arXiv:1301.1162v1,
the proof of Lemma 6.5(2): the unsquared modulus is at most twice the
square root of clipped energy divided by the cutoff. The source typo is
recorded in `docs/paper-gaps/aklv13_robustness_constants.tex`. -/
theorem norm_low_high_boundary_inner_le_sqrt_clipped_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := twoSidedEnergyTruncation L (N + A) R t
    ‖⟪ι (1 - Q) x, ι A (ι Q x)⟫_ℂ‖ ≤
      2 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι Q K
  have hQ : IsStarProjection (ι (1 - Q)) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian
      |>.isStarProjection_spectralProjectionGE t).one_sub).map ι
  have hlow : ‖ι (1 - Q) x‖ ≤ 1 := by
    simpa only [hx] using ContinuousLinearMap.IsStarProjection.norm_apply_le hQ x
  have hnormA : ‖A‖ ≤ 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap A (by norm_num) hA.nonneg).mpr
    simpa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using hAcap
  have hhigh := norm_highProjection_le_sqrt_clipped_energy
    L N R A hL hN hR hA hLN hLR hNR t ht x
  calc
    _ ≤ ‖ι (1 - Q) x‖ * ‖ι A (ι Q x)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (2 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t)) := by
      apply mul_le_mul hlow
        (((ι A).le_opNorm _).trans (mul_le_mul hnormA hhigh (norm_nonneg _) (by norm_num)))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end TNLean.MPS.AreaLaw.AKLV
