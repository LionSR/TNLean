/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedPath.ExactMPSGappedPhase
import QICLean.ManyBody.Hamiltonian.RingGaussianFilter
import QICLean.ManyBody.Hamiltonian.GaussianFilter
import QICLean.ManyBody.Hamiltonian.NegativeFrequency
import QICLean.Analysis.Calculus.CauchyTransform

/-!
# Gaussian ground estimates derived from an exact physical path

One physical Hamiltonian gap supplies a single Gaussian decay constant at
every path parameter and ring length. The least energy supplied by the gap
condition agrees with the energy of the exact MPS ground line. Its spectral
gap and unique ground line therefore supply the hypotheses of the existing
Gaussian ground estimates, without assumptions on transfer operators or
continuous canonical representatives.

The first bound controls the excited component of the filtered observable
acting on the actual periodic MPS vector. The second controls a centered
observable by its Hamiltonian commutator. Both hold for the unnormalized MPS
vector, so no parameter-dependent normalization or phase is chosen.

These are necessary filter estimates for the physical-gap argument. They do
not convert a symmetric low-pass filter into an ordinary connected
correlation bound. Positive-frequency separation, exponential clustering
and the resulting uniform minimal-transfer spectral bound remain separate.

## References

* Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953,
  and Appendix C, lines 2653–2717: the exact MPS separation problem.
* Hastings, arXiv:cond-mat/0508554v3, equation `gs`, lines 237–243:
  suppression of the excited component of a Gaussian-filtered observable.
* Hastings, arXiv:0705.2024v4, equations `tighter` and `tighter2`, lines
  794–815: the centered ground-vector estimate through a commutator.

## Ordinary centered correlations derived from the physical MPS gap

One physical gap gives one positive Gaussian spectral constant at every
parameter and ring length. The actual finite-ring Lieb–Robinson estimate
and actual Gaussian/Cauchy frequency separation then bound the ordinary
centered correlation of the periodic MPS vector. No filtered-to-ordinary
comparison, transfer-gap condition or continuous canonical gauge is given
as input.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; applied to the
exact MPS path of SPC11, arXiv:1010.3732, Section II.F, lines 929–953.

## Ordinary exponential clustering from the actual physical MPS gap

The actual uniform physical gap and finite-ring propagation bound imply one
positive exponential rate for ordinary connected correlations at every
parameter and ring length. The Gaussian frequency comparison, observable
centering and regularizer limit are derived, not supplied as estimates.
The original periodic MPS vector is normalized only through its explicit
expectation quotient.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3; applied to
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. Passing these finite
correlations to limiting minimal transfer contractions remains separate.

## Actual finite-ring correlations as negative-frequency commutators

For an exact MPS ground path, the actual Hamiltonian and ground-line
conditions give the negative-frequency identity for its ordinary connected
correlations. The original, unnormalized periodic MPS vector is used.
No correlation estimate, transfer bound or continuous minimal gauge is
assumed. The quantitative regularization and locality bound remain open.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6); applied to the physical-path argument of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953.
-/

section

open ManyBody GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The physical path's uniform gap and exact ground lines give a uniform
eigenvalue dichotomy at the actual MPS ground energy. The energy in the two
path conditions is identified by their least-energy properties.
Source: arXiv:1010.3732, Section II.F, lines 929–953; this is auxiliary
spectral data for the physical-gap argument, not its transfer conclusion. -/
theorem ExactMPSGroundPath.exists_uniform_ground_line_spectral_gap
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩; ∃ E : ℝ, ∃ hH :
          (Interaction.translationInvariant N (P.interaction γ)).hamiltonian.IsHermitian,
        ManyBody.groundSpace (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
            E = Submodule.span ℂ {mpvState (Q.tensor γ) N} ∧
          ∀ k, hH.eigenvalues k = E ∨ E + Δ ≤ hH.eigenvalues k := by
  obtain ⟨Δ, hΔ, hgap⟩ := P.gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN
  have : NeZero N := ⟨by omega⟩
  obtain ⟨E, hEspec, hEmin, hline⟩ := Q.ground_line γ hγ N hN
  obtain ⟨E', hE'⟩ := hgap γ hγ N hN
  let H := (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
  have hmem (μ : ℂ) : μ ∈ spectrum ℂ H ↔ Module.End.HasEigenvalue (Matrix.toEuclideanLin H) μ :=
    Matrix.hasEigenvalue_toEuclideanLin_iff_mem_spectrum.symm
  have hEE : E' = E := by
    refine le_antisymm ?_ ?_
    · rcases hE'.2 E ((hmem E).mp hEspec) with h | h
      · exact (Complex.ofReal_inj.mp h).ge
      · linarith [Complex.real_le_real.mp h]
    · simpa using hEmin _ ((hmem E').mpr (Module.End.hasEigenvalue_iff.mpr hE'.1))
  subst E'
  have hH : H.IsHermitian := Interaction.isHermitian_hamiltonian
    (Interaction.isHermitian_translationInvariant_term (P.hermitian γ hγ))
  refine ⟨E, hH, ?_, ((isGapped_iff_eigenvalues hH).mp hE').2⟩
  have hker : ManyBody.groundSpace H E =
      LinearMap.ker (Matrix.toEuclideanLin (H - (E : ℂ) • 1)) := by
    ext x
    rw [ManyBody.mem_groundSpace_iff]
    simp only [LinearMap.mem_ker, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply, sub_eq_zero]
  rw [hker]
  exact hline

/-- The physical gap of an exact MPS path implies Gaussian suppression of
excited ground-vector components and of centered observables, with the same
positive gap constant for every parameter and finite ring. The spectral
conditions are derived from the path; no transfer bound or clustering is
assumed. Source: Hastings, arXiv:cond-mat/0508554v3, equation `gs`, and
arXiv:0705.2024v4, equations `tighter` and `tighter2`; used as supporting
estimates for the SPC11 separation problem, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_gaussian_ground_bounds
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      ∀ (q : ℝ), 0 ≤ q → ∀ W : MPOTensor.ChainOperator d N,
        haveI : NeZero N := ⟨by omega⟩
        let H := (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
        let ψ := mpvState (Q.tensor γ) N
        let y := Matrix.toEuclideanLin (ManyBody.gaussianFilteredTerm q Δ H W) ψ
        ‖y - (Submodule.span ℂ {ψ}).starProjection y‖ ≤
            ‖W‖ * Real.exp (-q / 2) * ‖ψ‖ ∧
          (⟪ψ, Matrix.toEuclideanLin W ψ⟫_ℂ = 0 →
            ‖y‖ ≤ Δ⁻¹ * Real.exp (-q / 2) *
              ‖Matrix.toEuclideanLin (H * W - W * H) ψ‖) := by
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN q hq W
  have : NeZero N := ⟨by omega⟩
  obtain ⟨E, hH, hline, hgap⟩ := hdata γ hγ N hN
  let H := (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
  let ψ := mpvState (Q.tensor γ) N
  have hψ : ψ ∈ ManyBody.groundSpace H E := by
    rw [hline]
    exact Submodule.mem_span_singleton_self ψ
  constructor
  · simpa only [hline] using
      ManyBody.norm_sub_starProjection_gaussianFilteredTerm_le hq hΔ hH hgap W hψ
  · intro hcenter
    apply ManyBody.norm_gaussianFilteredTerm_apply_le_commutator hq hΔ hH hgap W hψ
    intro φ hφ
    rw [hline, Submodule.mem_span_singleton] at hφ
    obtain ⟨c, rfl⟩ := hφ
    rw [inner_smul_left, hcenter, mul_zero]

end MPSTensor

end

section

open ManyBody Matrix GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The actual physical gap implies an ordinary centered-correlation
bound with uniform Gaussian/propagation parameters. Both the spectral and
propagation estimates are derived from the actual physical path, so no
ordinary clustering or transfer conclusion is hidden as a premise.
The original unnormalized periodic MPS vector is retained.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_centered_correlation_gaussian_bound
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X →
          B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ⟪mpvState (Q.tensor γ) N,
        toEuclideanCLM (𝕜 := ℂ) A (mpvState (Q.tensor γ) N)⟫_ℂ = 0 →
      ∀ (q T a : ℝ), 0 < q → 0 < T → 0 ≤ a →
        let ψ := mpvState (Q.tensor γ) N
        let s := (q / Δ ^ 2).toNNReal
        let C := 2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)
        let v := 8 * Real.exp a
        ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ‖ ≤
          (2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ +
            kernel s⁻¹ 0 * (C * v * Real.exp (v * T) +
              (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))) * ‖ψ‖ ^ 2 := by
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN A B X Y hX hY hA hB hXY hcenter q T a hq hT ha
  have : NeZero N := ⟨by omega⟩
  obtain ⟨E₀, hH, hline, hgap⟩ := hdata γ hγ N hN
  have hne : ManyBody.groundSpace
      (Interaction.translationInvariant N (P.interaction γ)).hamiltonian E₀ ≠ ⊥ := by
    rw [hline, Ne, Submodule.span_singleton_eq_bot]
    exact ((EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm.map_eq_zero_iff).not.mpr
      (Q.nonzero γ hγ N (by omega))
  apply ManyBody.norm_centered_ground_correlation_le_gaussian hq hΔ hT (by positivity)
    (by positivity) hH ((ManyBody.isGapped_iff_eigenvalues hH).mpr ⟨hne, hgap⟩) hline A B hcenter
  intro t
  exact Interaction.norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint
    (P.interaction γ) (P.hermitian γ hγ) (P.norm_le_one γ hγ) A B X Y hX hY hA hB hXY a ha t

/-- The physical gap bounds ordinary connected correlations of arbitrary
supported observables. Centering, its norm bound and support preservation
are derived from the actual periodic MPS vector; no centering condition
is added to the public physical hypotheses.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_connected_correlation_gaussian_bound
    (Q : ExactMPSGroundPath P) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X →
          B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ∀ (q T a : ℝ), 0 < q → 0 < T → 0 ≤ a →
        let ψ := mpvState (Q.tensor γ) N
        let s := (q / Δ ^ 2).toNNReal
        let v := 8 * Real.exp a
        ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) -
          ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) *
            (⟪ψ, toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ))‖ ≤
          2 * ‖A‖ * ‖B‖ * (2 * Real.exp (-q / 2) +
            kernel s⁻¹ 0 *
              ((2 * X.card *
                Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
                v * Real.exp (v * T) +
                (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))) := by
  obtain ⟨Δ, hΔ, hEst⟩ := Q.exists_uniform_centered_correlation_gaussian_bound
  refine ⟨Δ, hΔ, ?_⟩
  intro γ hγ N hN A B X Y hX hY hA hB hXY q T a hq hT ha
  have : NeZero N := ⟨by omega⟩
  let ψ := mpvState (Q.tensor γ) N
  have hψne : ψ ≠ 0 := by
    exact ((EuclideanSpace.equiv (ι := Cfg d N) (𝕜 := ℂ)).symm.map_eq_zero_iff).not.mpr
      (Q.nonzero γ hγ N (by omega))
  let A₀ := ManyBody.centeredObservable ψ A
  have hA₀ : A₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X :=
    ManyBody.centeredObservable_mem ψ
      (S := Subalgebra.toSubmodule (ManyBody.supportedOperators (fun _ ↦ Fin d) X).toSubalgebra)
      (one_mem (ManyBody.supportedOperators _ _)) hA
  have hcenter : ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A₀ ψ⟫_ℂ = 0 :=
    ManyBody.inner_centeredObservable_eq_zero hψne A
  have hNormA : ‖A₀‖ ≤ 2 * ‖A‖ := ManyBody.norm_centeredObservable_le hψne A
  let s := (q / Δ ^ 2).toNNReal
  let v := 8 * Real.exp a
  let B₀ := 2 * Real.exp (-q / 2) + kernel s⁻¹ 0 *
    ((2 * X.card *
      Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
      v * Real.exp (v * T) + (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ))))
  have hB₀ : 0 ≤ B₀ := by
    have hk := kernel_nonneg s⁻¹ 0
    dsimp only [B₀, v]
    positivity
  have hraw : ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A₀ * B) ψ⟫_ℂ‖ ≤
      (‖A₀‖ * ‖B‖ * B₀) * ‖ψ‖ ^ 2 := by
    have h := hEst γ hγ N hN A₀ B X Y hX hY hA₀ hB hXY hcenter q T a hq hT ha
    convert h using 1
    dsimp only [B₀, s, v]
    ring
  have hcov : ⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) -
      ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) *
        (⟪ψ, toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) =
        ⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A₀ * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    dsimp only [A₀]
    rw [ManyBody.inner_centeredObservable_mul]
    simp only [sub_div, mul_div_assoc]
  change ‖⟪ψ, toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) -
      ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) *
        (⟪ψ, toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ))‖ ≤
    2 * ‖A‖ * ‖B‖ * B₀
  rw [hcov, norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hψne) 2)).mpr
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right ?_ hB₀
  exact mul_le_mul_of_nonneg_right hNormA (norm_nonneg B)

end MPSTensor

end

section

noncomputable section

open ManyBody Matrix GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- A physical uniform gap gives ordinary connected exponential clustering
for the actual periodic MPS vectors, uniformly in the parameter and ring
length. There is no clustering, transfer-gap, chosen minimal gauge or
frequency-separation premise. The displayed separation starts at one;
this is the range required for the limiting-correlation rate argument.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3;
SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_connected_exponential_clustering
    (Q : ExactMPSGroundPath P) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ (N : ℕ) (hN : 2 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ (A B : MPOTensor.ChainOperator d N) (X Y : Finset (Fin N)),
      ∀ (hX : X.Nonempty) (hY : Y.Nonempty),
      A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X →
          B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y →
      Disjoint (X : Set (Fin N)) (Y : Set (Fin N)) →
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ℓ ≤ ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY →
        let ψ := mpvState (Q.tensor γ) N
        ‖⟪ψ, Matrix.toEuclideanCLM (𝕜 := ℂ) (A * B) ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) -
          ⟪ψ, Matrix.toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) *
            (⟪ψ, Matrix.toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ))‖ ≤
            K * ((X.card : ℝ) + 1) * ‖A‖ * ‖B‖ * Real.exp (-κ * ℓ) := by
  obtain ⟨Δ, hΔ, hEst⟩ := Q.exists_uniform_connected_correlation_gaussian_bound
  let v := 8 * Real.exp (1 : ℝ)
  have hv : 0 < v := by dsimp only [v]; positivity
  obtain ⟨C, κ, hC, hκ, hRate⟩ := GaussianFilter.exists_gaussianFrequencyClusteringRate Δ v hΔ hv
  refine ⟨2 * C, κ, mul_pos (by norm_num) hC, hκ, ?_⟩
  intro γ hγ N hN A B X Y hX hY hA hB hXY ℓ hℓ hDist
  have : NeZero N := ⟨by omega⟩
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  let T := ℓ / (2 * v)
  let q := T * Δ
  let s := (q / Δ ^ 2).toNNReal
  have hT : 0 < T := div_pos hℓpos (by positivity)
  have hq : 0 < q := mul_pos hT hΔ
  have hs : (s : ℝ) = T / Δ := by
    dsimp only [s]
    rw [Real.coe_toNNReal _ (div_nonneg hq.le (sq_nonneg Δ))]
    dsimp only [q]
    field_simp [hΔ.ne']
  have htime : v * T = ℓ / 2 := by
    dsimp only [T]
    field_simp [hv.ne']
  have hqexp : Real.exp (-q / 2) = Real.exp (-ℓ * Δ / (4 * v)) := by
    congr 1
    dsimp only [q, T]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have htail : Real.exp (-T ^ 2 / (2 * (s : ℝ))) = Real.exp (-q / 2) := by
    rw [hs]
    congr 1
    dsimp only [q]
    field_simp [hT.ne', hΔ.ne']
  have hc : kernel s⁻¹ 0 = Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) := by
    rw [GaussianFilter.kernel_inv_zero_eq_sqrt, hs]
    congr 1
    dsimp only [T]
    field_simp [hv.ne', hΔ.ne', Real.pi_ne_zero]
    ring
  have hrecip : 2 / T = 4 * v / ℓ := by
    dsimp only [T]
    field_simp [hℓpos.ne', hv.ne']
    ring
  have hshort :
      (2 * (X.card : ℝ) * Real.exp (-ℓ)) * v * Real.exp (v * T) =
        2 * X.card * v * Real.exp (-ℓ / 2) := by
    rw [htime]
    calc
      _ = (2 * X.card * v) * (Real.exp (-ℓ) * Real.exp (ℓ / 2)) := by ring
      _ = _ := by
        rw [← Real.exp_add, show -ℓ + ℓ / 2 = -ℓ / 2 by ring]
  have hBracket :
      2 * Real.exp (-q / 2) + kernel s⁻¹ 0 *
        ((2 * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
          v * Real.exp (v * T) + (2 / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ)))) ≤
      2 * Real.exp (-ℓ * Δ / (4 * v)) +
        Real.sqrt (ℓ / (4 * Real.pi * v * Δ)) *
          (2 * X.card * v * Real.exp (-ℓ / 2) +
            (4 * v / ℓ) * Real.exp (-ℓ * Δ / (4 * v))) := by
    simp only [hc, htail, hqexp, hrecip]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply add_le_add _ le_rfl
    calc
      _ ≤ (2 * (X.card : ℝ) * Real.exp (-ℓ)) * v * Real.exp (v * T) := by
        have hDecay :
            Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) ≤
              Real.exp (-ℓ) := Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDecay (by positivity)) hv.le) (Real.exp_pos _).le
      _ = _ := hshort
  have h := hEst γ hγ N hN A B X Y hX hY hA hB hXY q T 1 hq hT (by norm_num)
  apply h.trans
  calc
    _ ≤ (2 * ‖A‖ * ‖B‖) *
        (C * ((X.card : ℝ) + 1) * Real.exp (-κ * ℓ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hBracket.trans (hRate X.card (by positivity) ℓ hℓ)
    _ = _ := by ring

end MPSTensor
end

end

section

open ManyBody Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- Ordinary connected correlations of the actual periodic MPS vector equal
the corresponding actual negative-frequency commutators. Ground energy,
least-energy ordering and the full ground line are derived from the
physical path. This is the exact spectral step of Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6); no exponential bound is
asserted without the remaining regularized time-integral argument. -/
theorem ExactMPSGroundPath.negativeFrequency_connected_identity
    (Q : ExactMPSGroundPath P) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (hN : 2 ≤ N) (A B : MPOTensor.ChainOperator d N) :
    haveI : NeZero N := ⟨by omega⟩
    let ψ := mpvState (Q.tensor γ) N
    let H := (Interaction.translationInvariant N (P.interaction γ)).hamiltonian
    let hH : H.IsHermitian := Interaction.isHermitian_hamiltonian
      (Interaction.isHermitian_translationInvariant_term (P.hermitian γ hγ))
    ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A (toEuclideanCLM (𝕜 := ℂ) B ψ)⟫_ℂ -
        ⟪ψ, toEuclideanCLM (𝕜 := ℂ) A ψ⟫_ℂ *
          ⟪ψ, toEuclideanCLM (𝕜 := ℂ) B ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ) =
      ⟪ψ, toEuclideanCLM (𝕜 := ℂ) (ManyBody.negativeFrequencyPart (H := H) hH A * B -
        B * ManyBody.negativeFrequencyPart hH A) ψ⟫_ℂ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨Δ, hΔ, hdata⟩ := Q.exists_uniform_ground_line_spectral_gap
  obtain ⟨E₀, hH, hline, hgap⟩ := hdata γ hγ N hN
  have hmin (i) : E₀ ≤ hH.eigenvalues i := by
    rcases hgap i with hi | hi
    · exact hi.ge
    · linarith
  apply ManyBody.inner_ground_connected_eq_negativeFrequency_commutator hH hmin A B
  rw [hline]

end MPSTensor

end
