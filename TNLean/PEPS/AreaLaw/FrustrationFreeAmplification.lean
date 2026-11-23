/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FrustrationFree.Sweep
import TNLean.PEPS.AreaLaw.RestoringOperator.AmplificationProofSteps
import TNLean.PEPS.AreaLaw.AmplificationCutClearance
import TNLean.PEPS.AreaLaw.RestoringOperator.TypicalProjectors
import TNLean.PEPS.AreaLaw.RestoringOperator.LatticeAncillaTransport
import TNLean.PEPS.AreaLaw.Scales.RadiusScales

/-!
# Amplification for frustration-free terms

The amplification step of the frustration-free area-law note, "Amplification with the original
frustration-free terms": under the collar hypotheses of Proposition 10.2, for every instance of
the frustration-free model `eq:model` and every large scale `n`, there is a radius
`r ≤ C n^{(1-ε)/α}` such that every part of the target `X = A ∩ T` has mutual information at
most `C n^{-M}` with every set avoiding `N_{2r}(S₀)` (`eq:far`), and `N_{2r}(S₀) ⊆ A` when the
target is far from the cut.

The proof follows the note. The typical projections and the restoring operator `R₀` with
`‖R₀‖ ≤ M₀ = e^{(𝓘 + 3w)/2}` are those of the general proof (`eq:restore`). The sweep `D` of the
range projections of the terms replaces the filtered clocks: for
`t = ⌈(log M₀ + K log n) / |log θ|⌉`, the excited part of `R₀ φ` is at most `θ^t M₀ ≤ n^{-K}`
after `D^t` (`eq:sweep`), and `D^t R₀ φ = L_t R₀ φ` exactly for a product `L_t` of the kept
factors on `N_{R χ t}(S₀)` that fixes `Ω` with its adjoint (`eq:cone`). So the omission and
truncation errors of the general proof are zero, and the polar correction and the entropy
comparison of the general proof give `eq:far`.

## Main statements

* `TNLean.PEPS.AreaLaw.FrustrationFree.frustrationFreeAmplificationBound`: the amplification
  bound for the frustration-free model, with the explicit constant
  `frustrationFreeAmplificationConstant` and threshold `frustrationFreeAmplificationThreshold`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  Section "Amplification with the original frustration-free terms", `eq:restore`, `eq:sweep`,
  `eq:cone` and `eq:far`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`09-amplification.tex`, lines 261–296), whose restoring, polar and
  continuity steps (lines 330–364, 501–561) are reused.
-/

open Matrix TNLean.Lattice
open ManyBody (PlaneInteraction Config edgeBoundary graphNeighborhood ambientDilation
  mem_ambientDilation_iff planeDomainGraph)
open scoped InnerProductSpace Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.FrustrationFree

/-! ### Spectator registers -/

section Spectator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {α : Type*} [Fintype α] [DecidableEq α]

omit [∀ v, DecidableEq (X v)] in
/-- **A bound survives tensoring with a spectator register** (`eq:sweep`: "The inequalities
persist after tensoring with spectator registers"). If `‖A w_a‖ ≤ c ‖w_a‖` for every slice
`w_a = w(·, a)`, then `‖(A ⊗ 1) w‖ ≤ c ‖w‖`. -/
theorem norm_kronecker_one_mulVec_le_of_slices (A : Matrix (Config X) (Config X) ℂ) {c : ℝ}
    (hc : 0 ≤ c) (w : Config X × α → ℂ)
    (h : ∀ a, ‖WithLp.toLp 2 (A *ᵥ fun σ ↦ w (σ, a))‖ ≤ c * ‖WithLp.toLp 2 fun σ ↦ w (σ, a)‖) :
    ‖WithLp.toLp 2 ((A ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ w)‖ ≤ c * ‖WithLp.toLp 2 w‖ := by
  have hsq (v : Config X × α → ℂ) : ‖WithLp.toLp 2 v‖ ^ 2 =
      ∑ a, ‖WithLp.toLp 2 fun σ ↦ v (σ, a)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, hsq, hsq, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have hslice : (fun σ ↦ ((A ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ w) (σ, a)) = A *ᵥ fun σ ↦ w (σ, a) := by
    ext σ
    exact kronecker_one_mulVec_apply A w σ a
  rw [hslice, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2

end Spectator

/-! ### The number of sweeps -/

/-- **The number of sweeps** `t = ⌈(log M₀ + K log n) / |log θ|⌉` makes the excited part small:
`θ^t M₀ ≤ n^{-K}`. Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
"Exact localization on the perturbed vector". -/
theorem pow_ceil_mul_le {θ M₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hM : 0 < M₀) {n : ℕ}
    (hn : 1 ≤ n) (K : ℕ) :
    θ ^ ⌈(Real.log M₀ + K * Real.log n) / (-Real.log θ)⌉₊ * M₀ ≤ ((n : ℝ) ^ K)⁻¹ := by
  set x := Real.log M₀ + K * Real.log n
  set lam := -Real.log θ
  have hlam : 0 < lam := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  set t := ⌈x / lam⌉₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have htx : x ≤ t * lam := (div_le_iff₀ hlam).mp (Nat.le_ceil _)
  have hθt : θ ^ t = Real.exp (-(t * lam)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hθ0]
    congr 1
    simp only [lam]
    ring
  have hx : Real.exp (-x) = (M₀ * (n : ℝ) ^ K)⁻¹ := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hM, ← Real.log_pow, Real.exp_log (by positivity)]
  calc θ ^ t * M₀ ≤ Real.exp (-x) * M₀ := by
        rw [hθt]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hM.le
    _ = ((n : ℝ) ^ K)⁻¹ := by
        rw [hx, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]

/-- The radius constant of the frustration-free amplification:
`R χ ((C₀/2 + 3/2 + 2K)/|log θ| + 1)`, `χ = d_R + 1`. -/
noncomputable def frustrationFreeRadiusConstant (R : ℕ) (J Δ C₀ : ℝ) (K : ℕ) : ℝ :=
  (R * (overlapDegreeBound R + 1) : ℕ) *
    ((C₀ / 2 + 3 / 2 + 2 * K) / (-Real.log (sweepContraction R J Δ)) + 1)

/-- **The radius bound.** With `M₀ = e^{(𝓘 + 3w)/2}`, `w = n^{3/5}`, `𝓘 ≤ C₀ n^{1-ε}`, the radius
`r = R χ t` of `t` sweeps is at most `frustrationFreeRadiusConstant · n^{(1-ε)/α}`. -/
theorem radius_le_frustrationFreeRadiusConstant {R : ℕ} {J Δ C₀ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hC₀ : 0 ≤ C₀) (K : ℕ)
    {n : ℕ} (hn : 1 ≤ n) {I : ℝ} (hI0 : 0 ≤ I)
    (hI : I ≤ C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))) :
    ((R * (overlapDegreeBound R + 1) * ⌈(Real.log (Real.exp ((I + 3 * (n : ℝ) ^ ((3 : ℝ) / 5)) / 2))
        + K * Real.log n) / (-Real.log (sweepContraction R J Δ))⌉₊ : ℕ) : ℝ) ≤
      frustrationFreeRadiusConstant R J Δ C₀ K * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) := by
  set θ := sweepContraction R J Δ
  set lam := -Real.log θ
  have hlam : 0 < lam := neg_pos.mpr (Real.log_neg (sweepContraction_pos hJ hΔ)
    (sweepContraction_lt_one hJ hΔ))
  set ρ : ℝ := (Exponents.radiusExponent : ℝ)
  obtain ⟨-, hρε, -⟩ := Exponents.radius_exponent_gaps
  have hρε' : 1 - (Exponents.amplificationEpsilon : ℝ) ≤ ρ := by
    have := (Rat.cast_le (K := ℝ)).mpr hρε.le
    push_cast at this
    exact this
  have hε35 : (3 : ℝ) / 5 ≤ 1 - (Exponents.amplificationEpsilon : ℝ) := by
    norm_num [Exponents.amplificationEpsilon]
  have hρ : (3 : ℝ) / 5 ≤ ρ := hε35.trans hρε'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpow : ∀ a : ℝ, a ≤ ρ → (n : ℝ) ^ a ≤ (n : ℝ) ^ ρ := fun a ha ↦
    Real.rpow_le_rpow_of_exponent_le hn1 ha
  have hnρ : 1 ≤ (n : ℝ) ^ ρ := Real.one_le_rpow hn1 (by linarith)
  have hlog : Real.log n ≤ 2 * (n : ℝ) ^ ρ := by
    have h := Real.log_le_rpow_div hn0 (show (0 : ℝ) < 3 / 5 by norm_num)
    have h2 : (n : ℝ) ^ ((3 : ℝ) / 5) / (3 / 5) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
      linarith
    linarith [hpow _ hρ]
  set x := Real.log (Real.exp ((I + 3 * (n : ℝ) ^ ((3 : ℝ) / 5)) / 2)) + K * Real.log n
  have hxeq : x = (I + 3 * (n : ℝ) ^ ((3 : ℝ) / 5)) / 2 + K * Real.log n := by
    simp only [x, Real.log_exp]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hw0 : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
  have hx0 : 0 ≤ x := by
    rw [hxeq]
    positivity
  have hxle : x ≤ (C₀ / 2 + 3 / 2 + 2 * K) * (n : ℝ) ^ ρ := by
    rw [hxeq]
    have h1 := hI.trans (mul_le_mul_of_nonneg_left (hpow _ hρε') hC₀)
    have h2 := hpow _ hρ
    have h3 : (K : ℝ) * Real.log n ≤ K * (2 * (n : ℝ) ^ ρ) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K)
    nlinarith
  have hC₀' : 0 ≤ C₀ / 2 + 3 / 2 + 2 * K := by positivity
  have ht : (⌈x / lam⌉₊ : ℝ) ≤ ((C₀ / 2 + 3 / 2 + 2 * K) / lam + 1) * (n : ℝ) ^ ρ := by
    have h1 : (⌈x / lam⌉₊ : ℝ) ≤ x / lam + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : x / lam ≤ (C₀ / 2 + 3 / 2 + 2 * K) / lam * (n : ℝ) ^ ρ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxle hlam.le
    nlinarith [div_nonneg hC₀' hlam.le]
  rw [frustrationFreeRadiusConstant, Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)

/-! ### The amplification bound -/

/-- The constant of the frustration-free amplification bound at the integer `M`, with
`K = 4(M + 2)`: the larger of the radius constant and the entropy-comparison constant
`8 √9 (1 + C₀ log q)` of the general proof. -/
noncomputable def frustrationFreeAmplificationConstant (q R : ℕ) (J Δ C₀ : ℝ) (M : ℕ) : ℝ :=
  max (frustrationFreeRadiusConstant R J Δ C₀ (4 * (M + 2))) (8 * √9 * (1 + C₀ * Real.log q))

/-- The threshold of the frustration-free amplification bound: that of the typical projections and
that of the collar clearance. -/
noncomputable def frustrationFreeAmplificationThreshold (q R : ℕ) (J Δ C₀ : ℝ) (M : ℕ) : ℕ :=
  max (typicalProjectionThreshold q R J Δ C₀ (4 * (M + 2)))
    (Exponents.collarRadiusThreshold (frustrationFreeAmplificationConstant q R J Δ C₀ M) 1)

open SimpleGraph in
/-- **Amplification for frustration-free terms** (`eq:far` of the frustration-free area-law note).
Fix `C₀ > 0` and an integer `M`. For every instance of the frustration-free model `eq:model`, an
ambient target `T` with `L = ⌊n^{1-ε}⌋`, `X = A ∩ T`, `S₀ = A ∩ T_L`, `Y = S₀ ∖ X`, if
`|S₀| ≤ C₀ n²`, the cuts of `X, Y, S₀` have at most `C₀ n` edges and `I_Ω(X : Λ ∖ S₀) ≤ C₀ n^{1-ε}`,
then at every `n ≥ max 2 N` there is a radius `r ≤ C n^{(1-ε)/α}` such that every subset of `X`
has mutual information at most `C n^{-M}` with every set avoiding `N_{2r}(S₀)`, and
`N_{2r}(S₀) ⊆ A` when `dist_∞(T, Z) > L + n^β`. The constant
`C = frustrationFreeAmplificationConstant` and the threshold
`N = frustrationFreeAmplificationThreshold` are chosen before `n, Λ, h, A, T`. This is the
conclusion of Proposition 10.2 for the model `eq:model`, with the sweep of the note in place of the
time-filtered clocks. Source: `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
Section "Amplification with the original frustration-free terms". -/
theorem frustrationFreeAmplificationBound {q R : ℕ} (hq : 1 ≤ q) {J Δ C₀ : ℝ} (hJ : 0 < J)
    (hΔ : 0 < Δ) (hC₀ : 0 < C₀) (M : ℕ) :
    ∀ n : ℕ, 2 ≤ n → frustrationFreeAmplificationThreshold q R J Δ C₀ M ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : PlaneInteraction Λ q R, ∀ Ω : EuclideanSpace ℂ (↥Λ → Fin q),
        IsFrustrationFreeGapped h J Δ Ω →
          ∀ (A : Finset ↥Λ) (T : Finset (ℤ × ℤ)),
            ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              C₀ * (n : ℝ) ^ 2 →
            ((edgeBoundary (planeDomainGraph Λ) (A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary (planeDomainGraph Λ) ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary (planeDomainGraph Λ) (A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              C₀ * n →
            ManyBody.regionMutualInformation Ω
                (A.filter fun x ↦ x.val ∈ T)
                (A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) →
            ∃ r : ℕ, (r : ℝ) ≤ frustrationFreeAmplificationConstant q R J Δ C₀ M *
                (n : ℝ) ^ (Exponents.radiusExponent : ℝ) ∧
              (∀ X ⊆ A.filter (fun x ↦ x.val ∈ T), ∀ Jset : Finset ↥Λ,
                Disjoint Jset (graphNeighborhood (planeDomainGraph Λ)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) (2 * r)) →
                ManyBody.regionMutualInformation Ω X Jset ≤
                  frustrationFreeAmplificationConstant q R J Δ C₀ M * ((n : ℝ) ^ M)⁻¹) ∧
              ((∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                  (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) +
                      (n : ℝ) ^ (Exponents.beta : ℝ) <
                    (Scan.ambientSupDistance t z : ℝ)) →
                graphNeighborhood (planeDomainGraph Λ)
                    (A.filter fun x ↦ x.val ∈ ambientDilation T
                      ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) (2 * r) ⊆ A) := by
  intro n hn2 hnN Λ h Ω hff A T hcard hXcut hYcut hScut hI
  have hh := fun X ↦ (hff.posSemidef X).1
  have hhJ := hff.norm_term_le hJ.le
  have hgap := hff.isGapped
  have hspan := hff.groundSpace_eq
  have hΩ := hff.norm_eq_one
  set C := frustrationFreeAmplificationConstant q R J Δ C₀ M with hCdef
  have hcolr := fun r hr ↦ graphNeighborhood_collar_subset_of_threshold_le C
    ((le_max_right _ _).trans hnN) r hr Λ A T
  have hNt : typicalProjectionThreshold q R J Δ C₀ (4 * (M + 2)) ≤ n :=
    (le_max_left _ _).trans hnN
  have : NeZero q := ⟨by omega⟩
  set K := 4 * (M + 2) with hKdef
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- The regions.
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
  -- The scales `w = n^{3/5}`, `M₀ = e^{(𝓘 + 3w)/2}`, the number of sweeps `t` and `r = R χ t`.
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5) with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg hn0.le _
  set I := ManyBody.regionMutualInformation Ω X (X ∪ Y)ᶜ with hIdef
  have hII : I ≤ C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
    rw [hIdef, hXYS]
    exact hI
  have hI0 : 0 ≤ I := ManyBody.regionMutualInformation_nonneg _ Ω hΩ _ _
    (disjoint_compl_right.mono_left Finset.subset_union_left)
  set M₀ := Real.exp ((I + 3 * w) / 2) with hM₀def
  have hM₀ : 1 ≤ M₀ := Real.one_le_exp (by positivity)
  set θ := sweepContraction R J Δ
  set t := ⌈(Real.log M₀ + K * Real.log n) / (-Real.log θ)⌉₊ with htdef
  set r := R * (overlapDegreeBound R + 1) * t with hrdef
  have hr : (r : ℝ) ≤ C * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) :=
    (radius_le_frustrationFreeRadiusConstant hJ hΔ hC₀.le K hn1 hI0 hII).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine ⟨r, hr, ?_, hcolr r hr⟩
  intro X' hX' Jset hJset
  -- The typical projections and the restoring operator, with the ancillas as spectators.
  have hfail := typicalProjectors_three_cuts_of_threshold_le hq R hJ.le hΔ hC₀.le K n hNt
      Λ h hh hhJ 0 Ω hΩ hgap hspan X Y (X ∪ Y) hXcut hYcut (by rw [hXYS]; exact hScut)
  let x₀ : RegionalConfiguration q X := fun _ => 0
  let blank : RegionalConfiguration q X → ℂ := fun x => if x = x₀ then 1 else 0
  have hblank : ‖WithLp.toLp 2 blank‖ = 1 := norm_toLp_single_eq_one x₀
  let U := restoringEigenbasis Ω X
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ω X
  let 𝒲 := restoringTransport Ω X Y hXY
  let p := (ManyBody.regionState_isHermitian X Ω).eigenvalues
  let E := Entropy.typicalSet p (ManyBody.regionEntropy Ω X) w
  let Tq := typicalProjection Λ q Ω Y w
  let Q := restoringCutProjection Ω X Y hXY w
  let ψ := restoringVector Ω X Y hXY
  let Rp := 𝒲 * Entropy.restoringGlobal E p blank blank Q Tq * 𝒲ᴴ
  let Bp := 𝒲 * Entropy.restoringColumnGlobal E p blank blank Q Tq * 𝒲ᴴ
  let φ := 𝒲 *ᵥ (Entropy.restoringCopy blank blank ψ).ofLp
  let η := 𝒲 *ᵥ (Entropy.restoringRestored p ψ).ofLp
  let ξb : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun c => blank c.1 * (U *ᵥ blank) c.2
  obtain ⟨hφ1, hη1, hRn, -, hcol, hgr, hadj⟩ := restoringTransport_estimates Ω hΩ X Y hXY w
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 blank blank blank hblank hblank hblank
  have hφ1 : ‖WithLp.toLp 2 φ‖ = 1 := hφ1
  have hη1 : ‖WithLp.toLp 2 η‖ = 1 := hη1
  have hRn : ‖Rp‖ ≤ M₀ := hRn
  have hcol : Rp *ᵥ φ = Bp *ᵥ fun c => Ω c.1 * ξb c.2 := hcol
  rw [sqrt_rpow_neg_two_mul] at hadj
  -- The supports of `B₀` and `R₀`.
  obtain ⟨PB, AB, hPB, hBsum⟩ :=
    restoringTransport_restoringColumnGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hBsum : Bp = ∑ i ∈ E ×ˢ Finset.univ, PB i ⊗ₖ AB i := hBsum
  have hBblocks : ∀ a b, Bp.submatrix (fun σ ↦ (σ, a)) (fun τ ↦ (τ, b)) ∈
      ManyBody.supportedOperators (fun _ : ↥Λ ↦ Fin q) S₀ := by
    intro x y
    have h := block_mem_supportedOperators_of_eq_sum (E ×ˢ Finset.univ) hPB AB x y
    rw [← hBsum, hXYS] at h
    exact h
  obtain ⟨PR, hPR, hRsum⟩ :=
    restoringTransport_restoringGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hRsum : Rp = ∑ x ∈ E, PR x ⊗ₖ (Entropy.basisColumn x blank ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := hRsum
  -- The sweep and its light cone.
  obtain ⟨c⟩ := exists_overlapColoring (Λ := Λ) (R := R)
  set D := hff.sweepOp c ^ t
  obtain ⟨Lt, hLsupp, -, hLadj, hcone⟩ := hff.exists_sweepOp_pow_lightCone c t hBblocks ξb
  let N := graphNeighborhood (planeDomainGraph Λ) S₀ (2 * r)
  have hLN : Lt ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) N :=
    ManyBody.supportedOperators_mono (ManyBody.graphNeighborhood_mono _ _ (by omega)) hLsupp
  have hS₀N : S₀ ⊆ N := ManyBody.subset_graphNeighborhood
  -- The vector `ζ = R₀ φ` and its excited component.
  let ζ : (↥Λ → Fin q) × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ :=
    Rp *ᵥ φ
  let Pg := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  let I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)
  have hsubk (A B : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  have hζn : ‖WithLp.toLp 2 ζ‖ ≤ M₀ := by
    have h := Rp.l2_opNorm_mulVec (WithLp.toLp 2 φ)
    rw [hφ1, mul_one] at h
    exact h.trans hRn
  have hPg : IsStarProjection Pg :=
    Entropy.blankOuterProduct_isStarProjection _ (by simpa using hΩ)
  have hξen : ‖WithLp.toLp 2 (((1 - Pg) ⊗ₖ I₂) *ᵥ ζ)‖ ≤ M₀ := by
    have h := ((1 - Pg) ⊗ₖ I₂).l2_opNorm_mulVec (WithLp.toLp 2 ζ)
    have h1 : ‖(1 - Pg) ⊗ₖ I₂‖ ≤ 1 :=
      (l2_opNorm_kronecker_one_le _).trans hPg.one_sub.norm_le
    calc _ ≤ _ := h
      _ ≤ 1 * M₀ := mul_le_mul h1 hζn (norm_nonneg _) zero_le_one
      _ = M₀ := one_mul _
  set ε : ℝ := ((n : ℝ) ^ K)⁻¹ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn1))
  have hθ0 := sweepContraction_pos (R := R) hJ hΔ
  have hθ1 := sweepContraction_lt_one (R := R) hJ hΔ
  have hexc : ‖WithLp.toLp 2 ((D ⊗ₖ I₂) *ᵥ (ζ - (Pg ⊗ₖ I₂) *ᵥ ζ))‖ ≤ ε := by
    have hsub : ζ - (Pg ⊗ₖ I₂) *ᵥ ζ = ((1 - Pg) ⊗ₖ I₂) *ᵥ ζ := by
      rw [hsubk, sub_mulVec, one_kronecker_one, one_mulVec]
    rw [hsub]
    refine (norm_kronecker_one_mulVec_le_of_slices D (pow_nonneg hθ0.le t) _ fun a ↦ ?_).trans
      ((mul_le_mul_of_nonneg_left hξen (pow_nonneg hθ0.le t)).trans
        (pow_ceil_mul_le hθ0 hθ1 (by positivity) hn1 K))
    have hslice : (fun σ ↦ (((1 - Pg) ⊗ₖ I₂) *ᵥ ζ) (σ, a)) =
        (1 - Pg) *ᵥ fun σ ↦ ζ (σ, a) := by
      ext σ
      exact kronecker_one_mulVec_apply (1 - Pg) ζ σ a
    rw [hslice]
    have horth : ⟪Ω, WithLp.toLp 2 ((1 - Pg) *ᵥ fun σ ↦ ζ (σ, a))⟫_ℂ = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, sub_mulVec, one_mulVec, vecMulVec_mulVec]
      simp only [op_smul_eq_smul]
      rw [sub_dotProduct, smul_dotProduct, dotProduct_comm (WithLp.ofLp Ω)]
      have hΩΩ : WithLp.ofLp Ω ⬝ᵥ star (WithLp.ofLp Ω) = 1 := by
        have := EuclideanSpace.inner_eq_star_dotProduct Ω Ω
        rw [inner_self_eq_norm_sq_to_K, hΩ] at this
        simpa using this.symm
      rw [dotProduct_comm] at hΩΩ
      rw [hΩΩ, smul_eq_mul, mul_one, dotProduct_comm, sub_self]
    have key := hff.norm_sweepOp_pow_apply_le hJ hΔ c t horth
    rw [Matrix.toEuclideanCLM_toLp] at key
    exact key
  have hret : ‖WithLp.toLp 2 (((D - Lt) ⊗ₖ I₂) *ᵥ ζ)‖ ≤ ε := by
    rw [hsubk, sub_mulVec]
    have : (D ⊗ₖ I₂) *ᵥ ζ = (Lt ⊗ₖ I₂) *ᵥ ζ := by
      change (D ⊗ₖ I₂) *ᵥ (Rp *ᵥ φ) = (Lt ⊗ₖ I₂) *ᵥ (Rp *ᵥ φ)
      rw [hcol]
      exact hcone
    rw [this, sub_self, WithLp.toLp_zero, norm_zero]
    exact hε0
  obtain ⟨U₁, hU₁supp, hU₁unit, hU₁err⟩ := exists_ancilla_unitary_of_good_realization
    (ManyBody.supportedOperators_mono (Finset.coe_subset.mpr
      (Finset.disjSum_mono (hXYS ▸ hS₀N) le_rfl))
      (hRsum ▸ sum_kronecker_submatrix_ancillaSplit_mem_supportedOperators E hPR _))
    hLN (D := D) (Dret := Lt) (g := (Pg ⊗ₖ I₂) *ᵥ ζ) (M₀ := M₀) (ε := ε)
    (a := 3 * ε + ε) hφ1 hη1 hζn
    (by
      rw [mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul, mul_vecMulVec,
        hff.sweepOp_pow_mulVec_self])
    hgr hexc hret
    (by rw [sub_self, norm_zero, mul_zero]; exact hε0)
    (by
      have h := hadj Lt
      rw [hLadj, WithLp.toLp_ofLp, sub_self, norm_zero, add_zero] at h
      linarith only [h, hε0])
  -- The entropy comparison on the enlarged sites.
  have hδ : ‖WithLp.toLp 2 (U₁ *ᵥ (φ ∘ ancillaSplit q X)) -
      WithLp.toLp 2 (η ∘ ancillaSplit q X)‖ ≤ 9 * (n : ℝ) ^ (-(K : ℝ) / 2) := by
    rw [← sqrt_inv_pow_eq_rpow]
    exact hU₁err.trans (unitary_error_le hε0 hε1)
  have hdim : (X.card : ℝ) * Real.log q ≤ C₀ * Real.log q * (n : ℝ) ^ 2 := by
    have hX : (X.card : ℝ) ≤ C₀ * (n : ℝ) ^ 2 :=
      (Nat.cast_le.mpr (Finset.card_le_card hXS)).trans hcard
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    calc (X.card : ℝ) * Real.log q ≤ C₀ * (n : ℝ) ^ 2 * Real.log q :=
          mul_le_mul_of_nonneg_right hX hlogq
      _ = C₀ * Real.log q * (n : ℝ) ^ 2 := by ring
  refine (mutualInformation_le_of_ancilla_unitary hΩ hXY (hXS.trans hS₀N) hJset hblank hblank
    hφ1 hη1 hU₁supp hU₁unit hn1 le_rfl hδ hdim X' hX').trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end TNLean.PEPS.AreaLaw.FrustrationFree
