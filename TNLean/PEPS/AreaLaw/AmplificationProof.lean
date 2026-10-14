/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AmplificationCutClearance
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordLists
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordTruncation
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelSpatialOmission
import TNLean.PEPS.AreaLaw.Amplification.LatticeExcitedDecay
import TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaSites
import TNLean.PEPS.AreaLaw.Amplification.SupportedPolarCorrection
import TNLean.PEPS.AreaLaw.Amplification.RadiusBound
import TNLean.PEPS.AreaLaw.Amplification.EntropyComparison
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows

/-!
# Proposition 10.2: amplification

This module proves Proposition 10.2 of the two-dimensional area-law manuscript
(`prop:amplification`) for every gapped finite-domain Hamiltonian: under the collar
hypotheses, at every large scale there is a radius `r ≤ C_M n^((1-ε)/α)` such that every
part of the target `X = A ∩ T` has mutual information at most `C_M n^(-M)` with every
physical set avoiding the graph neighborhood `N_{2r}(S₀)`, and the neighborhood lies in the
cut when the target is far from the cut endpoints.

The proof follows the source. At the scale `n`, the typical projections of `X`, `Y` and `S₀`
give the restoring operator `R₀` and the column operator `B₀` on the physical system and two
ancillary copies `s', e'` of `X`, with `‖R₀‖, ‖B₀‖ ≤ M₀ = e^{(𝓘+3w)/2}`. The clocks run for
the time `t_*` and the radius `r` of `eq:amplification-time-choice`. On one clock
realization, the excited-state decay bounds the excited component of `R₀ φ`, the omission
estimate of the local-products lemma, applied through the column identity `R₀ φ = B₀ (Ω ⊗ ξ)`,
bounds the omitted events, and the truncation estimate bounds the radius truncation. Markov's
inequality and a union bound select a realization on which all three are at most `n^{-K}`.
The polar correction of `L' R₀` then gives a unitary acting on `s'` and `N_{2r}(S₀)` that
moves `φ` to within `9 n^{-K/2}` of the restored vector `η`. On the sites enlarged by the two
copies, `φ` carries the original reduction of the target on `e'`, and `η` has no mutual
information between `e'` and any physical set. Continuity of mutual information then gives
the output bound, with `K = 4(M + 2)`.

## Main statements

* `TNLean.PEPS.AreaLaw.amplificationBound`: Proposition 10.2.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 261–296 (statement)
  and 298–576 (proof); Lemma 10.1 (`lem:amplification-local-products`), lines 42–72, and
  `eq:amplification-excited-decay`, lines 237–253.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix MeasureTheory SpectralFilter QuantumCircuit
open scoped Kronecker NNReal ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

/-- The square root of `(n^K)⁻¹` is `n^(-K/2)`. -/
private theorem sqrt_inv_pow_eq_rpow (n K : ℕ) :
    √(((n : ℝ) ^ K)⁻¹) = (n : ℝ) ^ (-(K : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg n),
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

/-- The square root of `n^(-2K)` is `(n^K)⁻¹`. -/
private theorem sqrt_rpow_neg_two_mul' (n K : ℕ) :
    √((n : ℝ) ^ (-(2 * K : ℝ))) = ((n : ℝ) ^ K)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n),
    show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul',
    ← inv_pow, Real.sqrt_sq (by positivity)]

/-- A unit blank vector on a nonempty finite set. -/
private theorem norm_toLp_single_eq_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ‖WithLp.toLp 2 (fun x : α => if x = a then (1 : ℂ) else 0)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The final scale estimate: `4ε + √(14ε + 9ε²) ≤ 9 √ε` for `0 ≤ ε ≤ 1`. -/
private theorem unitary_error_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (3 * ε + ε) + √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 9 * √ε := by
  have hs : ε ≤ √ε := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq : √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 5 * √ε := by
    rw [show (5 : ℝ) * √ε = √(25 * ε) by
      rw [Real.sqrt_mul (by norm_num), show √(25 : ℝ) = 5 by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- **Proposition 10.2** (`prop:amplification`, `09-amplification.tex` lines 261–296, proof at
lines 298–576), for the Hamiltonian parameters `q, R` with interaction strength `J ≥ 0` and
gap `Δ > 0`. Fix `C₀ > 0` and an integer `M ≥ 1`. Beyond a threshold chosen before the domain,
the Hamiltonian, the cut and the target, the collar hypotheses give an integer radius
`r ≤ C_M n^((1-ε)/α)` such that every part of `X = A ∩ T` has mutual information at most
`C_M n^(-M)` with every set avoiding `N_{2r}(S₀)`, and `N_{2r}(S₀) ⊆ A` under the cut clearance
`dist_∞(T, Z) > L + n^β`. -/
theorem amplificationBound {q R : ℕ} {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    AmplificationBound q R J Δ := by
  apply amplificationBound_of_radius_output
  intro C₀ hC₀ M hM
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- With no local states, a unit vector exists only on the empty domain.
    subst hq0
    refine ⟨0, 0, fun n _ _ Λ h E₀ Ω hgs A T _ _ _ _ _ => ⟨0, by simp, ?_⟩⟩
    intro X' _ Jset _
    obtain ⟨hΩ, -, -⟩ := Matrix.isGappedGroundState_iff.mp hgs
    have hempty : IsEmpty (Site Λ) := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨v⟩ := hne
      have : IsEmpty (Configuration Λ 0) := ⟨fun c => (c v).elim0⟩
      have hz : Ω = 0 := by
        ext c
        exact (IsEmpty.false c).elim
      rw [hz, norm_zero] at hΩ
      exact zero_ne_one hΩ
    rw [Finset.eq_empty_of_isEmpty X']
    simp [FiniteProduct.mutualInformation, FiniteProduct.entropy_empty _ Ω hΩ]
  have : NeZero q := ⟨hqpos.ne'⟩
  have hq : 1 ≤ q := hqpos
  -- The fixed exponent `α = p / (p + 1)` and the integer `K = 4 (M + 2)`.
  set pw := Exponents.amplificationPower with hpwdef
  have hpw : 1 ≤ pw := by norm_num [hpwdef, Exponents.amplificationPower]
  set α := kernelExponent pw with hαdef
  have hα : 0 < α := kernelExponent_pos hpw
  set K := 4 * (M + 2) with hKdef
  have hK1 : 1 ≤ K := by omega
  -- Constants of the local-products lemma, the gap and the scales.
  obtain ⟨Ct, ct, hCt, hct, htr⟩ := exists_latticeConstraintWord_truncation hpw R hJ hΔ
  obtain ⟨Ao, vo, γ, hAo, hvo, hγ, hom⟩ := exists_latticeConstraintWord_omission.{0} hpw R hJ hΔ
  obtain ⟨Cpc, cpc, -, -, hpos⟩ := exists_latticePositiveConstraints hpw R hJ hΔ
  set cs := positiveNormalization pw (Δ / 2) J with hcsdef
  have hcs : 0 < cs := positiveNormalization_pos pw _ J
  set g := Δ / cs with hgdef
  have hg : 0 < g := div_pos hΔ hcs
  set c := min ct γ with hcdef
  have hc : 0 < c := lt_min hct hγ
  set Cg := Ct + Ao with hCgdef
  have hCg : 0 ≤ Cg := add_nonneg hCt hAo
  obtain ⟨C', hC', Ng, hNg2, hgood⟩ :=
    exists_good_realization.{0} (C₀ := C₀) hg hvo.le hc hCg hC₀.le hα hK1
  obtain ⟨Nt, hNt1, hNt⟩ := exists_typicalProjectors_three_cuts (J := J) hq R hJ hΔ hC₀.le K
  obtain ⟨Crad, hCrad, hrad⟩ := exists_amplificationRadius_le (ε := Exponents.amplificationEpsilon)
    hg hC'.le hC₀.le hα (by norm_num [Exponents.amplificationEpsilon])
    (by norm_num [Exponents.amplificationEpsilon]) K
  set C₂ := C₀ * Real.log q with hC₂def
  have hC₂ : 0 ≤ C₂ := mul_nonneg hC₀.le (Real.log_nonneg (by exact_mod_cast hq))
  refine ⟨max Crad (8 * √9 * (1 + C₂)), max Ng Nt, ?_⟩
  intro n hn2 hnN Λ h E₀ Ω hgs A T hcard hXcut hYcut hScut hI
  obtain ⟨hΩ, -, -⟩ := Matrix.isGappedGroundState_iff.mp hgs
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- The regions of Proposition 10.2.
  set L := ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ with hLdef
  set X := A.filter fun x ↦ x.val ∈ T with hXdef
  set S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T L with hS₀def
  set Y := S₀ \ X with hYdef
  have hXS : X ⊆ S₀ := by
    intro x hx
    simp only [hXdef, hS₀def, Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, mem_ambientDilation_iff.mpr ⟨x.val, hx.2, ?_, ?_, ?_, ?_⟩⟩ <;> omega
  have hXY : Disjoint X Y := Finset.disjoint_sdiff
  have hXYS : X ∪ Y = S₀ := Finset.union_sdiff_of_subset hXS
  -- The scales `w = n^{3/5}`, `t_*` and `r`.
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5) with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg hn0.le _
  set I := FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X (X ∪ Y)ᶜ with hIdef
  have hII : I ≤ C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
    rw [hIdef, hXYS]
    exact hI
  have hI0 : 0 ≤ I := FiniteProduct.mutualInformation_nonneg _ Ω hΩ _ _
    (disjoint_compl_right.mono_left Finset.subset_union_left)
  set t : ℝ := amplificationTime g I w K n with htdef
  have hKlog : 0 ≤ (K : ℝ) * Real.log n :=
    mul_nonneg (Nat.cast_nonneg K) (Real.log_nonneg (by exact_mod_cast hn1))
  have ht0 : 0 ≤ t := mul_nonneg (div_nonneg (by norm_num) hg.le) (by linarith)
  set r := amplificationRadius C' α t K n with hrdef
  set M₀ := Real.exp ((I + 3 * w) / 2) with hM₀def
  have hM₀ : 1 ≤ M₀ := Real.one_le_exp (by positivity)
  refine ⟨r, ?_, ?_⟩
  · have hr := hrad n hn1 I hI0 hII
    have hexp : ((Exponents.radiusExponent : ℚ) : ℝ) =
        (1 - (Exponents.amplificationEpsilon : ℝ)) / α := by
      simp only [Exponents.radiusExponent, Exponents.alpha, hαdef, kernelExponent, hpwdef]
      push_cast
      ring
    rw [hexp]
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  intro X' hX' Jset hJset
  -- The typical projections and the restoring operator, with the ancillas as spectators.
  have hfail := hNt n ((le_max_right _ _).trans hnN) Λ h E₀ Ω hgs X Y (X ∪ Y) hXcut hYcut
    (by rw [hXYS]; exact hScut)
  set x₀ : RegionalConfiguration q X := fun _ => 0
  set blank : RegionalConfiguration q X → ℂ := fun x => if x = x₀ then 1 else 0 with hblankdef
  have hblank : ‖WithLp.toLp 2 blank‖ = 1 := norm_toLp_single_eq_one x₀
  set U := restoringEigenbasis Ω X with hUdef
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ω X
  set 𝒲 := restoringTransport Ω X Y hXY with h𝒲def
  set p := (reducedState_isHermitian Λ q Ω X).eigenvalues with hpdef
  set E := Entropy.typicalSet p (regionalEntropy Λ q Ω X) w with hEdef
  set Tq := typicalProjection Λ q Ω Y w with hTqdef
  set Q := restoringCutProjection Ω X Y hXY w with hQdef
  set ψ := restoringVector Ω X Y hXY with hψdef
  set Rp := 𝒲 * Entropy.restoringGlobal E p blank blank Q Tq * 𝒲ᴴ with hRpdef
  set Bp := 𝒲 * Entropy.restoringColumnGlobal E p blank blank Q Tq * 𝒲ᴴ with hBpdef
  set φ := 𝒲 *ᵥ (Entropy.restoringCopy blank blank ψ).ofLp with hφdef
  set η := 𝒲 *ᵥ (Entropy.restoringRestored p ψ).ofLp with hηdef
  set ξb : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun c => blank c.1 * (U *ᵥ blank) c.2 with hξbdef
  obtain ⟨hφ1, hη1, hRn, hBn, hcol, hgr, hadj⟩ := restoringTransport_estimates Ω hΩ X Y hXY w
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 blank blank blank hblank hblank hblank
  have hφ1 : ‖WithLp.toLp 2 φ‖ = 1 := hφ1
  have hη1 : ‖WithLp.toLp 2 η‖ = 1 := hη1
  have hRn : ‖Rp‖ ≤ M₀ := hRn
  have hBn : ‖Bp‖ ≤ M₀ := hBn
  have hcol : Rp *ᵥ φ = Bp *ᵥ fun c => Ω c.1 * ξb c.2 := hcol
  rw [sqrt_rpow_neg_two_mul'] at hadj
  -- The supports of `B₀` and `R₀`.
  obtain ⟨PB, AB, hPB, hBsum⟩ :=
    restoringTransport_restoringColumnGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hBsum : Bp = ∑ i ∈ E ×ˢ Finset.univ, PB i ⊗ₖ AB i := hBsum
  have hBblocks : ∀ x y : RegionalConfiguration q X × RegionalConfiguration q X,
      (Matrix.of fun σ τ => Bp (σ, x) (τ, y)) ∈ supportedOperators q (S₀ : Set (Site Λ)) := by
    intro x y
    have hblock : (Matrix.of fun σ τ => Bp (σ, x) (τ, y)) =
        ∑ i ∈ E ×ˢ Finset.univ, AB i x y • PB i := by
      ext σ τ
      simp [hBsum, Matrix.sum_apply, kroneckerMap_apply, mul_comm]
    rw [hblock, ← hXYS]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hPB i)
  obtain ⟨PR, hPR, hRsum⟩ :=
    restoringTransport_restoringGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hRsum : Rp = ∑ x ∈ E, PR x ⊗ₖ (Entropy.basisColumn x blank ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := hRsum
  -- Anchors and the exact positive constraints.
  set a : AdmissibleSupport Λ R → Site Λ := fun Z => Z.2.1.choose with hadef
  have ha : ∀ Z, a Z ∈ Z.1 := fun Z => Z.2.1.choose_spec
  set k := fun i : AdmissibleSupport Λ R =>
    positiveConstraint cs (centeredFilter pw (Δ / 2) h.operator Ω (h.term i)) with hkdef
  obtain ⟨-, hk, -⟩ := hpos Λ h a ha E₀ Ω hgs
  have hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0 := hk
  set Pr := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood Λ r S₀ with hPrdef
  set tt : ℝ≥0 := ⟨t, ht0⟩ with httdef
  have htt : (tt : ℝ) = t := rfl
  set μ := PoissonWord.measure (AdmissibleSupport Λ R) tt with hμdef
  -- The vector `ζ = R₀ φ`, its excited component and the blank pair `ξ`.
  set ζ : Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ :=
    Rp *ᵥ φ with hζdef
  set Pg := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) with hPgdef
  set ξe : EuclideanSpace ℂ (Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) :=
    toEuclideanLin ((1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ))
        (WithLp.toLp 2 ζ) with hξedef
  have hζn : ‖WithLp.toLp 2 ζ‖ ≤ M₀ := by
    have h := Rp.l2_opNorm_mulVec (WithLp.toLp 2 φ)
    rw [hφ1, mul_one] at h
    exact h.trans hRn
  have hPg : IsStarProjection Pg :=
    Entropy.blankOuterProduct_isStarProjection _ (by simpa using hΩ)
  have hξen : ‖ξe‖ ≤ M₀ := by
    have h := ((1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)).l2_opNorm_mulVec
        (WithLp.toLp 2 ζ)
    have h1 : ‖(1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)‖ ≤ 1 :=
      (l2_opNorm_kronecker_one_le _).trans hPg.one_sub.norm_le
    calc ‖ξe‖ ≤ _ := h
      _ ≤ 1 * M₀ := mul_le_mul h1 hζn (norm_nonneg _) zero_le_one
      _ = M₀ := one_mul _
  have hξb : ‖WithLp.toLp 2 ξb‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron (WithLp.toLp 2 blank) (WithLp.toLp 2 (U *ᵥ blank))
    have hUb : ‖WithLp.toLp 2 (U *ᵥ blank)‖ = 1 := by
      rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU', hblank]
    rw [hblank, hUb, mul_one] at h
    exact h
  -- The three random variables on one clock realization.
  set Xrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u =>
    ‖toEuclideanLin (contractionWord k u.1 u.2 ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) ξe‖
    with hXrvdef
  set Dl : List (AdmissibleSupport Λ R) → Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ := fun l =>
    ((l.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (Bp *ᵥ fun x => WithLp.ofLp Ω x.1 * ξb x.2) with hDldef
  set Yrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u =>
    ‖WithLp.toLp 2 (Dl (List.ofFn u.2) - Dl ((List.ofFn u.2).filter fun i => decide (Pr i)))‖
    with hYrvdef
  set Dret : PoissonWord.Word (AdmissibleSupport Λ R) →
      Matrix (Configuration Λ q) (Configuration Λ q) ℂ := fun u =>
    contractionWord (fun i : {i // Pr i} => k i) (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2 with hDretdef
  set kr := fun i : {i // Pr i} => siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
    with hkrdef
  set Lt : PoissonWord.Word (AdmissibleSupport Λ R) →
      Matrix (Configuration Λ q) (Configuration Λ q) ℂ := fun u =>
    contractionWord kr (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2 with hLtdef
  set Zrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u => M₀ * ‖Dret u - Lt u‖
    with hZrvdef
  obtain ⟨hXint, hXle⟩ := latticeConstraintWord_excitedProjection_decay hpw R hJ hΔ Λ h E₀ Ω
    hgs (WithLp.toLp 2 ζ) tt
  have hXint : Integrable (fun u => Xrv u ^ 2) μ := hXint
  have hXle : (∫ u, Xrv u ^ 2 ∂μ) ≤ Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 := hXle
  obtain ⟨hYint, hYle⟩ := hom Λ h a ha E₀ Ω hgs _ S₀ Bp hBblocks ξb hξb r tt
  have hYint : Integrable Yrv μ := hYint
  have hYle : (∫ u, Yrv u ∂μ) ≤ Ao * t * S₀.card * ‖Bp‖ *
      Real.exp (vo * t - γ * (r : ℝ) ^ α) := hYle
  obtain ⟨hZint, hZle, hLt⟩ := htr Λ h a ha E₀ Ω hgs S₀ r tt
  have hZint : Integrable (fun u => ‖Dret u - Lt u‖) μ := hZint
  have hZle : (∫ u, ‖Dret u - Lt u‖ ∂μ) ≤ Ct * t * S₀.card * (1 + (r : ℝ)) ^ 2 *
      Real.exp (-(ct * (r : ℝ) ^ α)) := hZle
  have hLt : ∀ u, ‖Lt u‖ ≤ 1 ∧ Lt u ∈ supportedOperators q
      (graphNeighborhood Λ (2 * r) S₀ : Set (Site Λ)) := hLt
  -- Markov's inequality and a union bound: a good realization.
  have hrα : 0 ≤ (r : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg r) α
  have hS0 : (0 : ℝ) ≤ S₀.card := Nat.cast_nonneg _
  have hM₀0 : 0 ≤ M₀ := (Real.exp_pos _).le
  obtain ⟨u0, hXu, hYu, hZu⟩ := hgood n ((le_max_left _ _).trans hnN) I w hI0 hw0 S₀.card
    hcard μ Xrv Yrv Zrv hXint (Filter.Eventually.of_forall fun u => norm_nonneg _) hYint
    (Filter.Eventually.of_forall fun u => mul_nonneg hM₀0 (norm_nonneg _))
    (hZint.const_mul M₀)
    (by
      have h1 : Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 ≤ Real.exp (-(g * t)) * M₀ ^ 2 := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξen 2)
          (Real.exp_pos _).le
      exact (hXle.trans h1).trans_eq (mul_comm _ _))
    (by
      have hCgt : 0 ≤ Cg * t * S₀.card := mul_nonneg (mul_nonneg hCg ht0) hS0
      have e1 : Real.exp (vo * t - γ * (r : ℝ) ^ α) ≤ Real.exp (vo * t - c * (r : ℝ) ^ α) :=
        Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right (min_le_right ct γ) hrα])
      have e2 : Ao * t * S₀.card * ‖Bp‖ ≤ Cg * t * S₀.card * M₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht0)
          hS0) hBn (norm_nonneg _) hCgt
      exact hYle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le (mul_nonneg hCgt hM₀0)))
    (by
      rw [integral_const_mul]
      have hr2 : (0 : ℝ) ≤ (1 + (r : ℝ)) ^ 2 := sq_nonneg _
      have hCgt : 0 ≤ Cg * t * S₀.card * (1 + (r : ℝ)) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg hCg ht0) hS0) hr2
      have e1 : Real.exp (-(ct * (r : ℝ) ^ α)) ≤ Real.exp (-(c * (r : ℝ) ^ α)) :=
        Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right (min_le_left ct γ) hrα])
      have e2 : Ct * t * S₀.card * (1 + (r : ℝ)) ^ 2 ≤ Cg * t * S₀.card * (1 + (r : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) ht0) hS0) hr2
      have e3 := mul_le_mul_of_nonneg_left (hZle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le
        hCgt)) hM₀0
      exact e3.trans_eq (by ring))
  set ε : ℝ := ((n : ℝ) ^ K)⁻¹ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn1))
  -- The enlarged sites and the transported operators and vectors.
  set sp := ancillaSplit q X with hspdef
  set N := graphNeighborhood Λ (2 * r) S₀ with hNdef
  set N'' : Finset (AncillaSites Λ X) := N.disjSum (Finset.univ.disjSum ∅) with hN''def
  have hS₀N : S₀ ⊆ N := by
    classical
    exact fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, SimpleGraph.Walk.nil,
      by simp⟩
  have hT (A : Matrix (Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) (Configuration Λ q × (RegionalConfiguration q X ×
        RegionalConfiguration q X)) ℂ)
      (v : Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ) :
      A.submatrix sp sp *ᵥ (v ∘ sp) = (A *ᵥ v) ∘ sp := by
    rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hTn (v : Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ) : ‖WithLp.toLp 2 (v ∘ sp)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv sp v
  set I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) with hI₂def
  have hsubk (A B : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp [kroneckerMap_apply, sub_mul]
  set Dfull := contractionWord k u0.1 u0.2 with hDfulldef
  have hkle : ∀ i, k i ≤ 1 := fun i => (hk i).2.1
  have hkΩ : ∀ i, k i *ᵥ WithLp.ofLp Ω = 0 := fun i => (hk i).2.2
  obtain ⟨U₁, hU₁supp, hU₁unit, hU₁err⟩ := exists_supported_unitary_of_good_realization N''
    (R₀ := Rp.submatrix sp sp) (L' := (Lt u0 ⊗ₖ I₂).submatrix sp sp)
    (D := (Dfull ⊗ₖ I₂).submatrix sp sp) (Dret := (Dret u0 ⊗ₖ I₂).submatrix sp sp)
    (φ := φ ∘ sp) (η := η ∘ sp) (g := ((Pg ⊗ₖ I₂) *ᵥ ζ) ∘ sp) (M₀ := M₀) (ε := ε)
    (a := 3 * ε + ε)
    (by
      have hsum : Rp.submatrix sp sp = ∑ x ∈ E, (PR x ⊗ₖ (Entropy.basisColumn x blank ⊗ₖ
          (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
            sp sp := by
        rw [hRsum]
        ext i j
        simp [Matrix.sum_apply]
      rw [hsum]
      refine Submodule.sum_mem _ fun x _ => supportedOperators_mono ?_
        (kronecker_submatrix_ancillaSplit_mem_supportedOperators (hPR x) _)
      exact Finset.coe_subset.mpr (Finset.disjSum_mono (hXYS ▸ hS₀N) le_rfl))
    (kronecker_one_submatrix_ancillaSplit_mem_supportedOperators (hLt u0).2)
    (by rw [hTn]; exact hφ1) (by rw [hTn]; exact hη1)
    (by rw [hT, hTn]; exact hζn)
    (by
      rw [hT, mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul,
        contractionWord_mul_vecMulVec_self k hkle hkΩ])
    (by rw [hTn]; exact hgr)
    (by
      have hsub : Rp.submatrix sp sp *ᵥ (φ ∘ sp) - ((Pg ⊗ₖ I₂) *ᵥ ζ) ∘ sp =
          (((1 - Pg) ⊗ₖ I₂) *ᵥ ζ) ∘ sp := by
        rw [hT, hsubk, sub_mulVec, one_kronecker_one, one_mulVec]
        rfl
      rw [hsub, hT, hTn]
      exact hXu)
    (by
      have hsub : (Dfull ⊗ₖ I₂).submatrix sp sp - (Dret u0 ⊗ₖ I₂).submatrix sp sp =
          ((Dfull - Dret u0) ⊗ₖ I₂).submatrix sp sp := by
        rw [hsubk]
        rfl
      rw [hT, hsub, hT, hTn, hsubk, sub_mulVec, ← hζdef, hcol]
      have h1 : Dfull = ((List.ofFn u0.2).reverse.map fun i => CFC.sqrt (1 - k i)).prod :=
        contractionWord_eq_prod_reverse k _ _
      have h2 : Dret u0 = (((List.ofFn u0.2).filter fun i => decide (Pr i)).reverse.map
          fun i => CFC.sqrt (1 - k i)).prod := contractionWord_partitionWords_fst Pr k u0
      rw [h1, h2]
      exact hYu)
    (by
      have hsub : (Dret u0 ⊗ₖ I₂).submatrix sp sp - (Lt u0 ⊗ₖ I₂).submatrix sp sp =
          ((Dret u0 - Lt u0) ⊗ₖ I₂).submatrix sp sp := by
        rw [hsubk]
        rfl
      rw [hsub]
      exact (mul_le_mul_of_nonneg_left ((norm_submatrix_equiv_le _ _).trans
        (l2_opNorm_kronecker_one_le _)) hM₀0).trans hZu)
    (by
      have hfix : toEuclideanCLM (𝕜 := ℂ) (Dret u0)ᴴ Ω = Ω := by
        apply WithLp.ofLp_injective 2
        rw [ofLp_toEuclideanCLM]
        exact conjTranspose_contractionWord_mulVec_self (fun i : {i // Pr i} => k i)
          (fun i => hkle i) (fun i => hkΩ i) _ _
      have hLΩ := norm_truncated_adjoint_sub_le (L' := Lt u0) hfix hΩ.le hM₀ hZu
      have hprod : (Lt u0 ⊗ₖ I₂).submatrix sp sp * Rp.submatrix sp sp =
          ((Lt u0 ⊗ₖ I₂) * Rp).submatrix sp sp := by
        rw [submatrix_mul_equiv]
      rw [hprod, conjTranspose_submatrix, hT, ← WithLp.toLp_sub]
      have hcomp : (((Lt u0 ⊗ₖ I₂) * Rp)ᴴ *ᵥ η) ∘ sp - φ ∘ sp =
          (((Lt u0 ⊗ₖ I₂) * Rp)ᴴ *ᵥ η - φ) ∘ sp := rfl
      rw [hcomp, hTn, WithLp.toLp_sub]
      have h := hadj (Lt u0)
      have hLΩ' : ‖WithLp.toLp 2 ((Lt u0)ᴴ *ᵥ WithLp.ofLp Ω) - Ω‖ ≤ ε := hLΩ
      linarith)
  -- The entropy comparison on the enlarged sites.
  set copyAll := ancillaCopyRegion (Finset.univ : Finset ↥X) with hcopyAll
  set physJ := ancillaPhysicalRegion X Jset with hphysJ
  have hJX : Disjoint Jset X :=
    Finset.disjoint_of_subset_right (hXS.trans hS₀N) hJset
  have hcopyJ : Disjoint copyAll physJ := by
    rw [Finset.disjoint_left]
    rintro (v | x | x) h1 h2 <;> simp [hcopyAll, hphysJ, ancillaCopyRegion,
      ancillaPhysicalRegion] at h1 h2
  have hN''disj : Disjoint (N'' : Set (AncillaSites Λ X)) ((copyAll ∪ physJ :
      Finset (AncillaSites Λ X)) : Set (AncillaSites Λ X)) := by
    rw [Finset.disjoint_coe, Finset.disjoint_left]
    rintro (v | x | x) h1 h2
    · simp only [hN''def, Finset.inl_mem_disjSum] at h1
      simp only [hcopyAll, hphysJ, ancillaCopyRegion, ancillaPhysicalRegion, Finset.mem_union,
        Finset.inl_mem_disjSum, Finset.notMem_empty, false_or] at h2
      exact Finset.disjoint_left.mp hJset h2 h1
    · simp [hcopyAll, hphysJ, ancillaCopyRegion, ancillaPhysicalRegion] at h2
    · simp [hN''def] at h1
  -- `η` is `Ω` tensored with a unit ancillary vector.
  set χ0 : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0
  set χ := ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ U) *ᵥ χ0
  have hηform : η = fun c => Ω c.1 * χ c.2 := restoringTransport_restored Ω X Y hXY p
  have hχ : ‖WithLp.toLp 2 χ‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron Ω (WithLp.toLp 2 χ)
    rw [hΩ, one_mul] at h
    rw [← h, ← hη1, hηform]
    rfl
  have hprod : FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q) (WithLp.toLp 2 (η ∘ sp)) copyAll physJ = 0 := by
    rw [hηform]
    exact mutualInformation_ancillaProduct_copy_eq_zero hΩ hχ _ _
  have hδ : ‖WithLp.toLp 2 (U₁ *ᵥ WithLp.ofLp (WithLp.toLp 2 (φ ∘ sp))) -
      WithLp.toLp 2 (η ∘ sp)‖ ≤ 9 * (n : ℝ) ^ (-(K : ℝ) / 2) := by
    rw [← sqrt_inv_pow_eq_rpow]
    exact hU₁err.trans (unitary_error_le hε0 hε1)
  have hdim : Real.log (Fintype.card (FiniteProduct.Configuration
      (fun _ : AncillaSites Λ X => Fin q) copyAll)) ≤
      C₂ * (n : ℝ) ^ 2 := by
    have hcardC : Fintype.card (FiniteProduct.Configuration (fun _ : AncillaSites Λ X => Fin q)
        copyAll) = q ^ X.card := by
      have hc : copyAll.card = X.card := by
        rw [hcopyAll, ancillaCopyRegion, Finset.card_disjSum, Finset.card_disjSum,
          Finset.card_empty, Finset.card_empty, Finset.card_univ, Fintype.card_coe]
        simp
      rw [Fintype.card_pi, Finset.prod_const, Fintype.card_fin,
        Finset.card_univ, Fintype.card_coe, hc]
    rw [hcardC, Nat.cast_pow, Real.log_pow]
    have hX : (X.card : ℝ) ≤ C₀ * (n : ℝ) ^ 2 :=
      (Nat.cast_le.mpr (Finset.card_le_card hXS)).trans hcard
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    calc (X.card : ℝ) * Real.log q ≤ C₀ * (n : ℝ) ^ 2 * Real.log q :=
          mul_le_mul_of_nonneg_right hX hlogq
      _ = C₂ * (n : ℝ) ^ 2 := by rw [hC₂def]; ring
  have t1 := mutualInformation_le_inv_pow_of_supported_unitary (φ := WithLp.toLp 2 (φ ∘ sp))
    (η := WithLp.toLp 2 (η ∘ sp)) (by rw [hTn]; exact hφ1) (by rw [hTn]; exact hη1) hcopyJ
    hN''disj hU₁supp hU₁unit hprod (C₁ := 9) (C₂ := C₂) (n := n) (M := M) (K := K)
  have hfinal := t1 hn1 le_rfl hδ hdim
  -- Back to `Ω` and the part `X'` of the target.
  set X'' : Finset ↥X := X'.subtype (· ∈ X)
  have hX''map : X''.map (Function.Embedding.subtype _) = X' :=
    Finset.subtype_map_of_mem fun x hx => hX' hx
  have hcopy := mutualInformation_ancillaCopy_eq hXY hΩ hblank
    (by rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU', hblank]) X'' hJX
  have hφform : φ = fun c => blank c.2.1 * (U *ᵥ blank) (restoringSplit q X Y hXY c.1).1.1 *
      Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
        (restoringSplit q X Y hXY c.1).2)) := restoringTransport_copy Ω X Y hXY blank blank
  rw [hX''map, ← hφform] at hcopy
  rw [← hcopy]
  refine (hfinal _ (Finset.disjSum_mono le_rfl (Finset.disjSum_mono le_rfl
    (Finset.subset_univ _)))).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end TNLean.PEPS.AreaLaw
