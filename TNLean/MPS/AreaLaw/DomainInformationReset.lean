/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainSupportedGaussianIntegral
import TNLean.Circuit.LiebRobinson.SupportSeparation
import TNLean.Lattice.PhysicalBufferCoordinates
import TNLean.Lattice.RegionalResetEntropy

/-!
# Information reset on finite integer domains

The original global ground-state gap, localized Gaussian averaging, and a
regional replica swap imply polynomially small mutual information between
sufficiently deep cores. Distances are intrinsic extended graph distances;
distinct connected components require no finite distance bound.

Extension of the chain lemma in the TNLean one-dimensional note, `lem:reset`,
`part2a_mps_information.tex`, lines 319–435, in the finite-domain setting of
`part0_preamble.tex`, lines 191–215.
-/

open Matrix QuantumCircuit MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix.Norms.L2Operator NNReal
open TNLean.Lattice (exists_regional_physicalBuffer_filter
  exists_supported_unitary_of_two_sided norm_two_sided_le_of_norm_sub_le
  reindex_physicalBuffer_eq_siteLift reset_entropy_scalar sheetSwapOp
  siteLift_mem_supportedOperators)

namespace TNLean.MPS.AreaLaw

/-- Information reset on an actual finite induced integer domain, using its
intrinsic extended graph distance. This extends the chain lemma in the TNLean
note, Lemma lem:reset,
part2a_mps_information.tex, lines 319–435, to the finite domains defined in
part0_preamble.tex, lines 191–215. Infinite distances impose no finite margin
condition. No restricted spectral gap or product marginal is assumed. -/
theorem DomainHamiltonian.information_reset (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) (p : ℝ) (hp : 0 < p) :
    ∃ (Cp : ℝ) (L₀ : ℕ), 0 < Cp ∧ 1 ≤ L₀ ∧
      ∀ (Λ : Finset ℤ), L₀ ≤ Λ.card →
      ∀ (h : DomainHamiltonian Λ q R J)
        (Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
        ∀ (D C R₀ C₀ : Finset (Fin Λ.card)), Disjoint D C → R₀ ⊆ D → C₀ ⊆ C →
        ∀ b : ℝ,
          FiniteProduct.mutualInformation (fun _ : Fin Λ.card ↦ Fin q) Ω D C ≤ b →
          let w := Cp * (1 + b + Real.log (Λ.card : ℝ))
          (∀ x ∈ R₀, ∀ y : Fin Λ.card, y ∉ D → ∀ d : ℕ,
            (domainGraph Λ).edist x y = (d : ℕ∞) → w < (d : ℝ)) →
          (∀ x ∈ C₀, ∀ y : Fin Λ.card, y ∉ C → ∀ d : ℕ,
            (domainGraph Λ).edist x y = (d : ℕ∞) → w < (d : ℝ)) →
          FiniteProduct.mutualInformation (fun _ : Fin Λ.card ↦ Fin q) Ω R₀ C₀ ≤
            (Λ.card : ℝ) ^ (-p) := by
  classical
  let r := 2 * p + 10
  have hr : 0 ≤ r := by dsimp [r]; linarith
  obtain ⟨Cint, v, hCint, hv, hlocal⟩ := exists_supported_gaussian_integral_domain R J
  obtain ⟨A, T₀, hA, hT₀, hfilter⟩ := exists_regional_physicalBuffer_filter hΔ hr
  let P := Cint * (1 + T₀)
  have hP : 0 < P := by positivity
  let Kloc := 4 * (v * T₀ + 15 + r + P)
  have hKloc : 0 < Kloc := by positivity
  let Cp := Kloc + (R : ℝ) + 4
  have hCp : 0 < Cp := by positivity
  let L₀ := max 1 ⌈8 * Real.sqrt 8 * (1 + Real.log (q : ℝ))⌉₊
  refine ⟨Cp, L₀, hCp, le_max_left _ _, ?_⟩
  intro Λ hL h Ω E₀ hgs D C R₀ C₀ hDC hR₀ hC₀ b hI w hRw hCw
  let L := Λ.card
  have hLn : 1 ≤ L := (le_max_left _ _).trans hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLn
  have hLthreshold : 8 * Real.sqrt 8 * (1 + Real.log (q : ℝ)) ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hL)
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have hb : 0 ≤ b := (FiniteProduct.mutualInformation_nonneg _ Ω hΩ D C hDC).trans hI
  let B := 1 + b + Real.log (L : ℝ)
  have hB : 1 ≤ B := by dsimp [B]; linarith [Real.log_nonneg hL1]
  let ℓ := Nat.ceil (Kloc * B)
  have hround : Kloc * B ≤ (ℓ : ℝ) := Nat.le_ceil _
  have hround' : (ℓ : ℝ) < Kloc * B + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hKloc.le (zero_le_one.trans hB))
  have hsepRadius : (ℓ : ℝ) + R < w := by
    change (ℓ : ℝ) + R < (Kloc + (R : ℝ) + 4) * B
    have hBR := mul_le_mul_of_nonneg_right hB (show 0 ≤ (R : ℝ) + 4 by positivity)
    nlinarith
  let ε := Real.exp (-10 * b) * (L : ℝ) ^ (-r)
  have hε : 0 ≤ ε := by positivity
  have hcoef : v * T₀ + 15 + r ≤ (1 / 4 : ℝ) * Kloc := by
    dsimp [Kloc]
    linarith
  have hreserve : P ≤ (ℓ : ℝ) / 4 := by
    have hKR : 4 * P ≤ Kloc := by dsimp [Kloc]; nlinarith [mul_pos hv hT₀]
    have hKB := mul_le_mul_of_nonneg_left hB hKloc.le
    nlinarith
  have hbase : Cint * (L : ℝ) ^ 4 * (1 + T₀ * B) *
      Real.exp (v * T₀ * B - (ℓ : ℝ) / 4) ≤ P * ε := by
    have hnum := GaussianFilter.localization_error_bound_of_parameter_constant
      hT₀.le (show 0 ≤ (1 / 4 : ℝ) by norm_num) hr hcoef hb hL1 hCint.le
    change Cint * (L : ℝ) ^ 4 * (1 + T₀ * B) *
      Real.exp (v * T₀ * B - (1 / 4 : ℝ) * ℓ) ≤
        Cint * (1 + T₀) * Real.exp (-10 * b) * (L : ℝ) ^ (-r) at hnum
    simpa only [P, ε, mul_assoc,
      show (1 / 4 : ℝ) * (ℓ : ℝ) = (ℓ : ℝ) / 4 by ring] using hnum
  have hsmall : Real.exp (-(ℓ : ℝ) / 4) * P ≤ 1 := by
    calc
      _ ≤ Real.exp (-P) * P :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith)) hP.le
      _ = P * Real.exp (-P) := mul_comm _ _
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one P
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hlocalError : Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
      Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2) ≤ ε := by
    have hLpow : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := pow_le_pow_right₀ hL1 (by decide)
    have hexp : Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2) =
        Real.exp (-(ℓ : ℝ) / 4) * Real.exp (v * T₀ * B - (ℓ : ℝ) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.exp (-(ℓ : ℝ) / 4) *
          (Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
            Real.exp (v * T₀ * B - (ℓ : ℝ) / 4)) := by rw [hexp]; ring
      _ ≤ Real.exp (-(ℓ : ℝ) / 4) *
          (Cint * (L : ℝ) ^ 4 * (1 + T₀ * B) *
            Real.exp (v * T₀ * B - (ℓ : ℝ) / 4)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hLpow hCint.le
      _ ≤ Real.exp (-(ℓ : ℝ) / 4) * (P * ε) :=
        mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
      _ = (Real.exp (-(ℓ : ℝ) / 4) * P) * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hsmall hε
      _ = ε := one_mul _
  let e := sitePairConfigurationEquiv (Fin L) q q
  let Q := (D ∪ C)ᶜ
  let Pconf := Fin (Fintype.card (D → Fin q)) × Fin (Fintype.card (C → Fin q))
  let s := FiniteProduct.splitTwoRegionsEquiv (fun _ : Fin L ↦ Fin q) D C hDC
  let g := (s.prodCongr s).trans (Equiv.doubledRegroup Pconf (Q → Fin q))
  let F := Matrix.reindex e e (sheetSwapOp q D)
  let ψ := fun c ↦ Ω (e.symm c).1 * Ω (e.symm c).2
  obtain ⟨hψn, hφn, W, z, hW, hz, hgauss⟩ :=
    hfilter q D C hDC e h.operator E₀ Ω b hgs hb hI
  let V := Matrix.reindex (g.symm.trans e) (g.symm.trans e)
    ((1 : Matrix (Pconf × Pconf) (Pconf × Pconf) ℂ) ⊗ₖ W)
  have hVsupp : V ∈ supportedOperators (q * q) (Q : Set (Fin L)) := by
    have hs := siteLift_mem_supportedOperators Q
      (Matrix.reindex (sitePairConfigurationEquiv Q q q) (sitePairConfigurationEquiv Q q q) W)
    rw [← reindex_physicalBuffer_eq_siteLift q D C hDC W] at hs
    exact hs
  have hV : ‖V‖ ≤ 1 :=
    ((Matrix.l2_opNorm_reindex_equiv (g.symm.trans e) _).trans_le
      (Matrix.l2_opNorm_one_kronecker_rect_le W)).trans hW
  let η := Real.toNNReal (A * B)
  let K := h.doubled.operator
  let K' := (h.swappedDoubled D).operator
  let M₀ := GaussianFilter.gaussianIntertwinerTruncated η (T₀ * B) K' K V
  obtain ⟨hT, hfwd, hrev⟩ := hgauss (L : ℝ) hL1
  have hK : Matrix.reindex e e (doubledHamiltonian h.operator) = K :=
    h.doubled_operator.symm
  have hK' : F * K * Fᴴ = K' := (h.swappedDoubled_operator D).symm
  change ‖WithLp.toLp 2
    (GaussianFilter.gaussianIntertwinerTruncated η (T₀ * B)
      (F * Matrix.reindex e e (doubledHamiltonian h.operator) * Fᴴ)
      (Matrix.reindex e e (doubledHamiltonian h.operator)) V *ᵥ ψ) -
        (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
          3 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) at hfwd
  change ‖WithLp.toLp 2
    ((GaussianFilter.gaussianIntertwinerTruncated η (T₀ * B)
      (F * Matrix.reindex e e (doubledHamiltonian h.operator) * Fᴴ)
      (Matrix.reindex e e (doubledHamiltonian h.operator)) V)ᴴ *ᵥ (F *ᵥ ψ)) -
        (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
          3 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) at hrev
  rw [hK, hK'] at hfwd hrev
  let crossing := Entropy.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
  let Z := crossing.biUnion (fun X ↦ X.1)
  let N := fun A : Finset (Fin L) ↦
    A.biUnion (fun x ↦ graphBall (domainGraph Λ) x ℓ)
  let S := N (Q ∪ Z)
  obtain ⟨path, _, _, _, _, hpathIntegral⟩ :=
    hlocal q hq Λ h D ℓ
  let M := ∫ t : ℝ in Set.Icc (-(T₀ * B)) (T₀ * B),
    siteExpectation (q * q) (N Q) (heisenbergEvolution K' t V) * path t ∂gaussianReal 0 η
  obtain ⟨hMs, _, hMerr⟩ := hpathIntegral Q V hVsupp η (T₀ * B) hT
  have hMclose : ‖M - M₀‖ ≤ ε := by
    calc
      _ ≤ ‖V‖ * (Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
          Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2)) := by
        simpa only [mul_assoc] using hMerr
      _ ≤ 1 * (Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
          Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hV (by positivity)
      _ ≤ ε := by simpa only [one_mul] using hlocalError
  obtain ⟨hMfwd, hMrev⟩ :=
    norm_two_sided_le_of_norm_sub_le hψn hφn hMclose hfwd hrev
  have hresidual : ε + 3 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) =
      4 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by dsimp only [ε]; ring
  rw [hresidual] at hMfwd hMrev
  obtain ⟨U, hUu, hUs, hUerr⟩ := exists_supported_unitary_of_two_sided
    (C := 4) (ε := (L : ℝ) ^ (-r)) S hMs hb hz hMfwd hMrev
    (by norm_num) (by positivity)
  have hUerr' : ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
      8 * (L : ℝ) ^ (-r) := by
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hUerr
  have hrad : ((ℓ + R : ℕ) : ℝ) ≤ w := by
    simpa only [Nat.cast_add] using hsepRadius.le
  have hS : Disjoint S (R₀ ∪ C₀) := by
    exact reset_graphNeighborhood_disjoint_cores (domainGraph Λ)
      (fun X : DomainSupport Λ R ↦ X.1) R ℓ
      (fun X x hx y hy ↦ X.2.2 x hx y hy) D C R₀ C₀ hDC
      (fun x hx ↦ graphBall_subset_of_finite_distance_margin
        (domainGraph Λ) D x w (ℓ + R) hrad (hRw x hx))
      (fun x hx ↦ graphBall_subset_of_finite_distance_margin
        (domainGraph Λ) C x w (ℓ + R) hrad (hCw x hx))
  have hent := TNLean.Lattice.mutualInformation_cores_le_of_reset_unitary q hq hΩ
    D R₀ C₀ hR₀ (Finset.disjoint_of_subset_left hC₀ hDC.symm) S hS U hUu hUs
    (8 * (L : ℝ) ^ (-r)) hUerr'
  refine hent.trans (reset_entropy_scalar (C := 8) (p := p)
    (lq := Real.log (q : ℝ)) (by norm_num) hL1 hLthreshold (le_refl _) ?_ ?_)
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
      (one_le_pow₀ hq1))
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have hcardNat : R₀.card ≤ L := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ R₀
    have hcard : (R₀.card : ℝ) ≤ (L : ℝ) ^ 2 := by
      have hc : (R₀.card : ℝ) ≤ L := by exact_mod_cast hcardNat
      have hsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := le_self_pow₀ hL1 (by decide)
      exact hc.trans hsq
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    exact add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_right hcard hlogq)

end TNLean.MPS.AreaLaw
