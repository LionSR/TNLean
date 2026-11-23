/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Entropy.SupportedGaussianIntegral
import TNLean.MPS.AreaLaw.Entropy.ResetSupportSeparation
import QICLean.ManyBody.Sites.GraphBall
import QICLean.ManyBody.Replica.RegionalReset
import QICLean.ManyBody.Replica.RegionalResetEntropy
import QICLean.ManyBody.Sites.ReplicaSwap
import QICLean.ManyBody.Entropy.MutualInformationPerturbation
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.Analysis.Norm.MatrixKroneckerContraction
import QICLean.Analysis.Parameter.LocalizationParameters
import QICLean.ManyBody.Sites.SupportedUnitary
import QICLean.Analysis.Real.InformationResetScalar
import QICLean.Spectral.Perturbation.ResidualComparison

/-!
# Information reset

A global spectral gap and small mutual information between two disjoint outer
regions imply a polynomially small mutual information between sufficiently
deep cores. The proof constructs the physical-buffer filter, its supported
localization and polar correction from the original ground-state data.

The argument is carried out once, on the sites of any finite system, from a
supported localization of the truncated Gaussian filter at every natural radius and a
separation of its support from the cores. The contiguous chain and the finite integer
domains supply these two inputs, with chain distances and with intrinsic extended graph
distances respectively; on a domain, distinct connected components require no finite
distance bound.

## Main results

* `information_reset_of_supported_localization`: polynomial decay of the mutual
  information of the cores from a supported localization and a core separation.
* `ManyBody.ChainInteraction.information_reset`: polynomial decay of the mutual
  information of the cores, with uniform constants chosen before the system,
  state, regions and original mutual-information upper bound.
* `ManyBody.DomainInteraction.information_reset`: the same on finite integer domains.

**Source convention (contiguous chains):** The note fixes a contiguous chain in
`part1_arealaw.tex`, lines 91–93, before the Part II argument. The sites here
are `Fin L`, as in that argument. The finite-domain statement extends it to the domains of
`part0_preamble.tex`, lines 191–215; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, Lemma `lem:reset`,
`part2a_mps_information.tex`, lines 319–435.
-/

open ManyBody (ChainSupport DomainSupport lineDomainGraph ChainInteraction DomainInteraction)

open Matrix QuantumCircuit MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix.Norms.L2Operator NNReal

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- Information reset from a supported localization of the truncated Gaussian filter and a
separation of its support from the cores. For the doubled Hamiltonian `K` of `H` and its
regional swap `K'`, the hypothesis `hlocal` provides at every natural radius `ℓ` a path whose
averages are supported on `N ℓ (Q ∪ Z)` and approximate the truncated filter with error
`‖W‖ C_int L² (1 + T) e^{vT - ℓ/2}`; the hypothesis `hsep` keeps that support off the cores
when `ℓ + R ≤ w`. The constants are chosen before the system, state, regions and
mutual-information bound. TNLean note, Lemma `lem:reset`, `part2a_mps_information.tex`,
lines 319–435. -/
theorem information_reset_of_supported_localization (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) (p : ℝ) (hp : 0 < p) (Cint v : ℝ) (hCint : 0 < Cint)
    (hv : 0 < v) :
    ∃ (Cp : ℝ) (L₀ : ℕ), 0 < Cp ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], L₀ ≤ Fintype.card ι →
      ∀ (H : Matrix (ι → Fin q) (ι → Fin q) ℂ)
        (Ω : EuclideanSpace ℂ (ι → Fin q)) (E₀ : ℝ),
        H.IsHermitian → ‖Ω‖ = 1 → IsGapped H E₀ Δ →
        groundSpace H E₀ = Submodule.span ℂ {Ω} →
        ∀ (D C R₀ C₀ : Finset (ι)), Disjoint D C → R₀ ⊆ D → C₀ ⊆ C →
        ∀ b : ℝ,
          ManyBody.regionMutualInformation Ω D C ≤ b →
          let w := Cp * (1 + b + Real.log (Fintype.card ι : ℝ))
          let pr := Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q
          let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl ι) finProdFinEquiv)
          let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
          let K := Matrix.reindex e e (doubledHamiltonian H)
          let K' := F * K * Fᴴ
          ∀ (N : ℕ → Finset (ι) → Finset (ι)) (Z : Finset (ι)),
          (∀ ℓ : ℕ, ∃ path : ℝ → Matrix (ι → Fin (q * q)) (ι → Fin (q * q)) ℂ,
            ∀ (Q : Finset (ι))
              (W : Matrix (ι → Fin (q * q)) (ι → Fin (q * q)) ℂ),
              W ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q →
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  ManyBody.regionExpectation (N ℓ Q) (ManyBody.heisenbergEvolution K' t W) *
                    path t ∂gaussianReal 0 η
                M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) (N ℓ (Q ∪ Z) : Finset (ι)) ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                  ‖W‖ * Cint * (Fintype.card ι : ℝ) ^ 2 * (1 + T) * Real.exp (v * T - ℓ / 2)) →
          (∀ ℓ : ℕ, (ℓ : ℝ) + R ≤ w → Disjoint (N ℓ ((D ∪ C)ᶜ ∪ Z)) (R₀ ∪ C₀)) →
          ManyBody.regionMutualInformation Ω R₀ C₀ ≤
            (Fintype.card ι : ℝ) ^ (-p) := by
  classical
  let r := 2 * p + 10
  have hr : 0 ≤ r := by dsimp [r]; linarith
  obtain ⟨A, T₀, hA, hT₀, hfilter⟩ := GaussianFilter.exists_regional_physicalBuffer_filter hΔ hr
  let P := Cint * (1 + T₀)
  have hP : 0 < P := by positivity
  let Kloc := 4 * (v * T₀ + 15 + r + P)
  have hKloc : 0 < Kloc := by positivity
  let Cp := Kloc + (R : ℝ) + 4
  have hCp : 0 < Cp := by positivity
  let L₀ := max 1 ⌈8 * Real.sqrt 8 * (1 + Real.log (q : ℝ))⌉₊
  refine ⟨Cp, L₀, hCp, le_max_left _ _, ?_⟩
  intro ι _ _ hL H Ω E₀ hH hΩ hgap hspan D C R₀ C₀ hDC hR₀ hC₀ b hI w pr e F K K' N Z hlocal hsep
  set L := Fintype.card ι with hLdef
  have hLn : 1 ≤ L := (le_max_left _ _).trans hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLn
  have hLthreshold : 8 * Real.sqrt 8 * (1 + Real.log (q : ℝ)) ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hL)
  have hb : 0 ≤ b := (ManyBody.regionMutualInformation_nonneg _ Ω hΩ D C hDC).trans hI
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
  let Q := (D ∪ C)ᶜ
  -- The filter is constructed on the sites `ι ⊕ ι` of two replicas; `φ` pairs the two copies of
  -- every site and encodes each pair along `finProdFinEquiv`, giving the coordinates of `F`, `K`.
  let φ := (ManyBody.replicaPairEquiv ι (Fin q)).trans
    (ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
      fun _ ↦ finProdFinEquiv)
  let KV := Matrix.reindex (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).symm
    (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).symm (doubledHamiltonian H)
  let FV := ManyBody.replicaSwapOp (Fin q) D
  let Ψ := ManyBody.sumSitesProduct (X := fun _ : ι ⊕ ι ↦ Fin q) Ω Ω
  have hK : Matrix.reindex φ φ KV = K := rfl
  have hF : Matrix.reindex φ φ FV = F := rfl
  have hK' : Matrix.reindex φ φ (FV * KV * FVᴴ) = K' := by
    change _ = F * K * Fᴴ
    rw [← hK, ← hF]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  obtain ⟨W, z, -, hW, hz, hgauss⟩ := hfilter hH hΩ hgap hspan hDC hI
  let V := Matrix.reindex φ φ (ManyBody.place (Q.disjSum Q) W)
  have hVsupp : V ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl ι)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      ((ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff (S := Q)).mpr
        (ManyBody.place_mem_supportedOperators W))
    convert hs using 1
    ext x y
    rfl
  have hV : ‖V‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv φ _).trans_le ((ManyBody.norm_place_le W).trans hW)
  let η := Real.toNNReal (A * B)
  let M₀V := GaussianFilter.gaussianIntertwinerTruncated η (T₀ * B) (FV * KV * FVᴴ) KV
    (ManyBody.place (Q.disjSum Q) W)
  let M₀ := GaussianFilter.gaussianIntertwinerTruncated η (T₀ * B) K' K V
  have hM₀ : M₀ = Matrix.reindex φ φ M₀V := by
    rw [GaussianFilter.reindex_gaussianIntertwinerTruncated, hK', hK]
  have hT : 0 ≤ T₀ * B := mul_nonneg hT₀.le (zero_le_one.trans hB)
  obtain ⟨-, hfwd, hrev⟩ := hgauss (L : ℝ) hL1
  let S := N ℓ (Q ∪ Z)
  obtain ⟨path, hpathIntegral⟩ := hlocal ℓ
  let M := ∫ t : ℝ in Set.Icc (-(T₀ * B)) (T₀ * B),
    ManyBody.regionExpectation (N ℓ Q) (ManyBody.heisenbergEvolution K' t V) * path t
      ∂gaussianReal 0 η
  obtain ⟨hMs, hMerr⟩ := hpathIntegral Q V hVsupp η (T₀ * B) hT
  have hMclose : ‖M - M₀‖ ≤ ε := by
    calc
      _ ≤ ‖V‖ * (Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
          Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2)) := by
        simpa only [mul_assoc] using hMerr
      _ ≤ 1 * (Cint * (L : ℝ) ^ 2 * (1 + T₀ * B) *
          Real.exp (v * (T₀ * B) - (ℓ : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hV (by positivity)
      _ ≤ ε := by simpa only [one_mul] using hlocalError
  -- the localized average, read on the two replicas
  let MV := Matrix.reindex φ.symm φ.symm M
  have hMVs : MV ∈ ManyBody.supportedOperators (fun _ : ι ⊕ ι ↦ Fin q) (S.disjSum S) := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl ι)
      (X' := fun _ ↦ Fin q × Fin q) (fun _ ↦ finProdFinEquiv.symm) (fun _ ↦ Iff.rfl) hMs
    refine (ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff (A := MV)).mp ?_
    convert hs using 1
    ext x y
    rfl
  have hMVclose : ‖MV - M₀V‖ ≤ ε := by
    have h : MV - M₀V = Matrix.reindex φ.symm φ.symm (M - M₀) := by
      ext i j
      simp [MV, hM₀]
    rw [h, Matrix.l2_opNorm_reindex_equiv]
    exact hMclose
  have hΨ : ‖Ψ‖ = 1 := by
    rw [ManyBody.norm_sumSitesProduct, hΩ, mul_one]
  have hFΨ : ‖Matrix.toEuclideanLin FV Ψ‖ = 1 := by
    have h := ManyBody.sitePermOp_mulVec_eq_relabelVector (α := Fin q) (ManyBody.replicaSwap D) Ψ
    rw [ManyBody.sitePermOp_replicaSwap] at h
    change ‖WithLp.toLp 2 (FV *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [h, ManyBody.norm_relabelVector, hΨ]
  obtain ⟨hMfwd, hMrev⟩ := Matrix.norm_two_sided_le_of_norm_sub_le hΨ hFΨ hMVclose hfwd hrev
  have hresidual : ε + 3 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) =
      4 * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by dsimp only [ε]; ring
  rw [hresidual] at hMfwd hMrev
  obtain ⟨U, hUu, hUs, hUerr⟩ := ManyBody.exists_supported_unitary_of_two_sided
    (C := 4) (ε := (L : ℝ) ^ (-r)) hMVs hb hz hMfwd hMrev
  have hUerr' : ‖Matrix.toEuclideanLin U Ψ - Matrix.toEuclideanLin FV Ψ‖ ≤
      8 * (L : ℝ) ^ (-r) := by
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hUerr
  have hS : Disjoint S (R₀ ∪ C₀) := hsep ℓ hsepRadius.le
  have hS' : Disjoint (S.disjSum S) ((R₀ ∪ C₀).disjSum (∅ : Finset ι)) := by
    refine Finset.disjoint_left.mpr ?_
    rintro (x | x) hx hx'
    · simp only [Finset.inl_mem_disjSum] at hx hx'
      exact Finset.disjoint_left.mp hS hx hx'
    · simp at hx'
  have hent := ManyBody.regionMutualInformation_cores_le_of_reset_unitary hΩ hR₀
    (Finset.disjoint_of_subset_left hC₀ hDC.symm) hS' hUu hUs hUerr'
  rw [Fintype.card_fin] at hent
  refine hent.trans (Real.eight_mul_sqrt_mul_le_rpow_neg (C := 8) (p := p)
    (l := Real.log (q : ℝ)) hL1 hLthreshold (le_refl _) ?_)
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have hcardNat : R₀.card ≤ L := Finset.card_le_univ R₀
    have hcard : (R₀.card : ℝ) ≤ (L : ℝ) ^ 2 := by
      have hc : (R₀.card : ℝ) ≤ L := by exact_mod_cast hcardNat
      have hsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := le_self_pow₀ hL1 (by decide)
      exact hc.trans hsq
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    exact add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_right hcard hlogq)


/-- Contiguous-chain information reset from the original full-system gap.
Source: TNLean note, Lemma `lem:reset`, `part2a_mps_information.tex`, lines 319–435. -/
theorem _root_.ManyBody.ChainInteraction.information_reset (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) (p : ℝ) (hp : 0 < p) :
    ∃ (Cp : ℝ) (L₀ : ℕ), 0 < Cp ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (D C R₀ C₀ : Finset (Fin L)), Disjoint D C → R₀ ⊆ D → C₀ ⊆ C →
        ∀ b : ℝ,
          ManyBody.regionMutualInformation Ω D C ≤ b →
          let w := Cp * (1 + b + Real.log (L : ℝ))
          (∀ x ∈ R₀, ∀ y : Fin L, y ∉ D →
            w < (Nat.dist x.val y.val : ℝ)) →
          (∀ x ∈ C₀, ∀ y : Fin L, y ∉ C →
            w < (Nat.dist x.val y.val : ℝ)) →
          ManyBody.regionMutualInformation Ω R₀ C₀ ≤
            (L : ℝ) ^ (-p) := by
  classical
  obtain ⟨Cint, v, hCint, hv, hlocal⟩ := exists_supported_gaussian_integral R J
  obtain ⟨Cp, L₀, hCp, hL₀, hreset⟩ :=
    information_reset_of_supported_localization q hq R Δ hΔ p hp Cint v hCint hv
  refine ⟨Cp, L₀, hCp, hL₀, ?_⟩
  intro L hL h hh hhJ Ω E₀ hΩ hgap hspan D C R₀ C₀ hDC hR₀ hC₀ b hI w hRw hCw
  have hK : Matrix.reindex
      ((Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
      (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv))
      ((Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
          (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv))
          (doubledHamiltonian h.hamiltonian) =
        h.doubledFin.hamiltonian := h.hamiltonian_doubledFin.symm
  let Z := (ManyBody.crossingTerms (fun X : ChainSupport L R ↦ X.1) D).biUnion (fun X ↦ X.1)
  have hreset' := hreset (Fin L) (by simpa only [Fintype.card_fin] using hL)
  simp only [Fintype.card_fin] at hreset'
  refine hreset' h.hamiltonian Ω E₀ (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hgap hspan
      D C R₀ C₀ hDC hR₀ hC₀ b hI
    (fun ℓ A ↦ chainNeighborhood A (ℓ : ℝ)) Z (fun ℓ ↦ ?_)
    (fun ℓ hℓ ↦ (chain_reset_support_separation D C R₀ C₀ hDC w hRw hCw).2 (ℓ : ℝ) hℓ)
  obtain ⟨path, -, -, -, -, hint⟩ := hlocal q hq L h hh hhJ D (ℓ : ℝ) (Nat.cast_nonneg _)
  refine ⟨path, fun Q W hW η T hT ↦ ?_⟩
  obtain ⟨hs, -, herr⟩ := hint Q W hW η T hT
  rw [hK]
  exact ⟨hs, herr⟩

/-- Information reset on an actual finite induced integer domain, using its
intrinsic extended graph distance. This extends the chain lemma in the TNLean
note, Lemma lem:reset,
part2a_mps_information.tex, lines 319–435, to the finite domains defined in
part0_preamble.tex, lines 191–215. Infinite distances impose no finite margin
condition. No restricted spectral gap or product marginal is assumed. -/
theorem _root_.ManyBody.DomainInteraction.information_reset (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) (p : ℝ) (hp : 0 < p) :
    ∃ (Cp : ℝ) (L₀ : ℕ), 0 < Cp ∧ 1 ≤ L₀ ∧
      ∀ (Λ : Finset ℤ), L₀ ≤ Λ.card →
      ∀ (h : DomainInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)) (E₀ : ℝ),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (D C R₀ C₀ : Finset (Fin Λ.card)), Disjoint D C → R₀ ⊆ D → C₀ ⊆ C →
        ∀ b : ℝ,
          ManyBody.regionMutualInformation Ω D C ≤ b →
          let w := Cp * (1 + b + Real.log (Λ.card : ℝ))
          (∀ x ∈ R₀, ∀ y : Fin Λ.card, y ∉ D → ∀ d : ℕ,
            (lineDomainGraph Λ).edist x y = (d : ℕ∞) → w < (d : ℝ)) →
          (∀ x ∈ C₀, ∀ y : Fin Λ.card, y ∉ C → ∀ d : ℕ,
            (lineDomainGraph Λ).edist x y = (d : ℕ∞) → w < (d : ℝ)) →
          ManyBody.regionMutualInformation Ω R₀ C₀ ≤
            (Λ.card : ℝ) ^ (-p) := by
  classical
  obtain ⟨Cint, v, hCint, hv, hlocal⟩ := exists_supported_gaussian_integral_domain R J
  obtain ⟨Cp, L₀, hCp, hL₀, hreset⟩ :=
    information_reset_of_supported_localization q hq R Δ hΔ p hp Cint v hCint hv
  refine ⟨Cp, L₀, hCp, hL₀, ?_⟩
  intro Λ hL h hh hhJ Ω E₀ hΩ hgap hspan D C R₀ C₀ hDC hR₀ hC₀ b hI w hRw hCw
  have hK : Matrix.reindex
      ((Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
      (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv))
      ((Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q).symm.trans
          (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv))
          (doubledHamiltonian h.hamiltonian) =
        h.doubledFin.hamiltonian := h.hamiltonian_doubledFin.symm
  let Z := (ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).biUnion (fun X ↦ X.1)
  have hreset' := hreset (Fin Λ.card) (by simpa only [Fintype.card_fin] using hL)
  simp only [Fintype.card_fin] at hreset'
  refine hreset' h.hamiltonian Ω E₀ (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hgap hspan
      D C R₀ C₀ hDC hR₀ hC₀ b hI
    (fun ℓ A ↦ ManyBody.graphNeighborhood (lineDomainGraph Λ) A ℓ) Z
    (fun ℓ ↦ ?_) (fun ℓ hℓ ↦ ?_)
  · obtain ⟨path, -, -, -, -, hint⟩ := hlocal q hq Λ h hh hhJ D ℓ
    refine ⟨path, fun Q W hW η T hT ↦ ?_⟩
    obtain ⟨hs, -, herr⟩ := hint Q W hW η T hT
    rw [hK]
    exact ⟨hs, herr⟩
  · have hrad : ((ℓ + R : ℕ) : ℝ) ≤ w := by simpa only [Nat.cast_add] using hℓ
    exact ManyBody.reset_graphNeighborhood_disjoint_cores (lineDomainGraph Λ)
      (fun X : DomainSupport Λ R ↦ X.1) R ℓ
      (fun X x hx y hy ↦ X.2.2 x hx y hy) D C R₀ C₀ hDC
      (fun x hx ↦ ManyBody.graphBall_subset_of_finite_distance_margin
        (lineDomainGraph Λ) D x w (ℓ + R) hrad (hRw x hx))
      (fun x hx ↦ ManyBody.graphBall_subset_of_finite_distance_margin
        (lineDomainGraph Λ) C x w (ℓ + R) hrad (hCw x hx))

end TNLean.MPS.AreaLaw
