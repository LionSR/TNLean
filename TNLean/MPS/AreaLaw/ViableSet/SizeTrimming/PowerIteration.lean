/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNet
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNetPolynomial
import TNLean.MPS.AreaLaw.ViableSet.FiniteBoundarySelection
import TNLean.MPS.AreaLaw.ViableSet.BoundaryTraceNormSDP
import TNLean.MPS.AreaLaw.ViableSet.LeadingPower
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingBounds
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.LeadingVectorPrecision

/-!
# Coordinate-start power iteration for viable vectors

Normalized coordinate-start powers of an approximate compressed density supply
a viable physical vector at an explicit polynomial iteration count.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (physical viability applications):** The size-trimming viability
conclusions for physical chains assume `0 < L` and `2 ≤ q`, as recorded in
`docs/paper-gaps/lvv13_nontrivial_chain.tex`, and use the library's
uniform cut bound rather than the sharper AKLV dependence; see
`docs/paper-gaps/lvv13_constant_bond.tex`. Taking the union over actual bond dimensions
avoids extending a bond isometry beyond the dimension of the right physical space.
The boundary nets use the corrected matrix-space exponent recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- End-to-end finite-precision form of the LVV leading-vector step.  A positive
compressed density approximation at trace-norm precision `Δ / (97344 L)` determines
an exact dominant eigenpair, including its normalized compressed-coordinate vector
and isometric reconstruction.  Every normalized numerical vector for the resulting
compressed density whose residual is at most `11 Δ / (389376 L)` then gives a physical
viable vector with the original LVV energy and overlap bounds.  Isometric expansion
preserves its norm and residual and places it in the retained support.  The theorem also
constructs such a vector by the normalized coordinate-start power method at the explicit
polynomial iteration count `ceil (n / (11 Δ / (778752 L))²)`. -/
theorem ChainHamiltonian.exists_viable_vector_of_approximate_density_and_eigenresidual
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    (x₀ : Fin n) (τ σ : Matrix (Fin n) (Fin n) ℂ) {ε : ℝ}
    (hτtrace : τ.trace = 1) (hσpsd : σ.PosSemidef)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (hτenergy : (τ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hτboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (hε : ε ≤ Δ / (97344 * L)) :
    ∃ (σ₀ : Matrix (Fin n) (Fin n) ℂ)
      (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
        ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
      (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
      (z₀ : EuclideanSpace ℂ (Fin n)) (μ : ℝ),
      σ₀.PosSemidef ∧ σ₀.trace = 1 ∧ ρ = Z * σ₀ * Zᴴ ∧
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ ‖u‖ = 1 ∧
      ρ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 23 / 24 ≤ μ ∧
      ‖z₀‖ = 1 ∧ σ₀ *ᵥ WithLp.ofLp z₀ = (μ : ℂ) • WithLp.ofLp z₀ ∧
      WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z₀) = u ∧
      let v₀ := WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z₀))) ∘ gluingCut L q k)
      ‖v₀‖ = 1 ∧
      1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, v₀⟫_ℂ‖ ∧
      (∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 →
        ‖toEuclideanLin σ₀ z - (μ : ℂ) • z‖ ≤ 11 * Δ / (389376 * L) →
        let u' := WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
        let v' := WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
              gluingCut L q k)
        ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
          (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
          1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖) ∧
      let η := 11 * Δ / (778752 * L)
      let t := ⌈(n : ℝ) / η ^ 2⌉₊
      ∃ i : Fin n,
        let e := EuclideanSpace.basisFun (Fin n) ℂ i
        let K := ((μ : ℂ)⁻¹ • σ₀) ^ t
        toEuclideanLin K e ≠ 0 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧
          let z := c • (‖toEuclideanLin K e‖⁻¹ : ℂ) • toEuclideanLin K e
          let u' := WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
          let v' := WithLp.toLp 2
            ((((1 : Matrix (CutLeft L q k × CutSite L q k)
              (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
                gluingCut L q k)
          ‖z‖ = 1 ∧ ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
            (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
            1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  let ζ := Δ / (16224 * L)
  have hζ : ζ ≤ Δ / (16224 * L) := le_rfl
  have hcombined : 24 * L * ε + 4 * L * ζ ≤ Δ / 2028 :=
    density_and_vector_precision_of_separate_bounds hL hε hζ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hζ0 : 0 ≤ ζ := (div_pos hΔ (mul_pos (by norm_num) hLreal)).le
  have hdensity : 24 * L * ε ≤ Δ / 2028 := by
    calc
      24 * L * ε ≤ 24 * L * ε + 4 * L * ζ :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hLreal.le) hζ0)
      _ ≤ Δ / 2028 := hcombined
  obtain ⟨ρ, u, μ, hρ, hρtr, hρP, -, hu, huρ, -, hbounds⟩ :=
    h.exists_leading_vector_of_approximate_compressed_boundary_solution hL hq hΔ
      HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ x₀ τ σ
        hτtrace hσpsd hclose hτenergy hτboundary hdensity
  dsimp only at hbounds
  rcases hbounds with ⟨-, huP, hvunit, -, -, -, hE, ha, -, hμ⟩
  let σ₀ := Zᴴ * ρ * Z
  have hσ₀ : σ₀.PosSemidef := hρ.conjTranspose_mul_mul_same Z
  have hρQ : (Z * Zᴴ) * ρ = ρ := by rw [hZZ]; exact hρP
  have hρright : ρ * (Z * Zᴴ) = ρ := by
    have hh := congrArg Matrix.conjTranspose hρQ
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hρ.isHermitian.eq] using hh
  have hρexpand : ρ = Z * σ₀ * Zᴴ := by
    calc
      ρ = (Z * Zᴴ) * ρ * (Z * Zᴴ) := by rw [hρQ, hρright]
      _ = Z * σ₀ * Zᴴ := by simp only [σ₀, Matrix.mul_assoc]
  have hσ₀tr : σ₀.trace = 1 := by
    have ht := isometricDensityExpansion_trace_and_energy Z hZ ρ σ₀ hρexpand
      (1 : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
        ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    exact ht.1.trans hρtr
  let z₀ : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Zᴴ *ᵥ WithLp.ofLp u)
  have hcoords := isometricDensityExpansion_eigenvector_coordinates
    Z hZ ρ σ₀ hρexpand u (μ : ℂ) (by rw [hZZ]; exact huP) huρ
  have hz₀ : ‖z₀‖ = 1 := hcoords.1.trans hu
  have hZz₀ : WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z₀) = u := hcoords.2.1
  have hz₀eig : σ₀ *ᵥ WithLp.ofLp z₀ = (μ : ℂ) • WithLp.ofLp z₀ := hcoords.2.2
  have hv₀unit : ‖WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
          WithLp.ofLp (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z₀))) ∘ gluingCut L q k)‖ = 1 := by
    rw [hZz₀]
    exact hvunit
  have hv₀overlap : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤
      ‖⟪Γ, WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z₀))) ∘
              gluingCut L q k)⟫_ℂ‖ := by
    rw [hZz₀]
    exact ha
  have hcertificate : ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 →
      ‖toEuclideanLin σ₀ z - (μ : ℂ) • z‖ ≤ 11 * Δ / (389376 * L) →
      let u' := WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
      let v' := WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
            gluingCut L q k)
      ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
        (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
        1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
    intro z hz hres
    let u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m) :=
      WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
    have hu' : ‖u'‖ = 1 := by
      rw [show ‖u'‖ = ‖z‖ from Matrix.norm_toLp_mulVec_of_isometry Z hZ z, hz]
    have hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
          WithLp.ofLp u' := by
      rw [← hZZ]
      change (Z * Zᴴ) *ᵥ (Z *ᵥ WithLp.ofLp z) = Z *ᵥ WithLp.ofLp z
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hZ, Matrix.mul_one]
    have hresambient : ‖toEuclideanLin ρ u' - (μ : ℂ) • u'‖ ≤
        11 * Δ / (389376 * L) := by
      rw [show ‖toEuclideanLin ρ u' - (μ : ℂ) • u'‖ =
        ‖WithLp.toLp 2
          (ρ *ᵥ (Z *ᵥ WithLp.ofLp z) - (μ : ℂ) • (Z *ᵥ WithLp.ofLp z))‖ from rfl,
        isometricDensityExpansion_eigenresidual_norm Z hZ ρ σ₀ hρexpand z (μ : ℂ)]
      exact hres
    have hres' : ‖toEuclideanLin ρ u' - (μ : ℂ) • u'‖ ≤ (11 / 24) * ζ :=
      residual_precision_of_lvv_vector_tolerance hL hresambient
    exact h.nearby_glued_vector_viable_of_density_and_vector_residual hL hq hΔ hgs
      W hW hρ hρtr u u' hu hu' huρ hμ hu'P hE ha hres' hcombined
  refine ⟨σ₀, ρ, u, z₀, μ, hσ₀, hσ₀tr, hρexpand, hρ, hρtr, hu, huρ, hμ,
    hz₀, hz₀eig, hZz₀, hv₀unit, hv₀overlap, hcertificate, ?_⟩
  let η := 11 * Δ / (778752 * L)
  have hη : 0 < η := by
    exact div_pos (mul_pos (by norm_num) hΔ) (mul_pos (by norm_num) hLreal)
  let P : EuclideanSpace ℂ (Fin n) → Prop := fun z ↦
    let u' := WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖
  have hcert : ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 →
      ‖toEuclideanLin σ₀ z - (μ : ℂ) • z‖ ≤ 2 * η → P z := by
    intro z hz hres
    apply hcertificate z hz
    calc
      _ ≤ 2 * η := hres
      _ = 11 * Δ / (389376 * L) := by
        dsimp only [η]
        field_simp [ne_of_gt hLreal]
        ring
  simpa only [η, P] using
    (Matrix.PosSemidef.exists_basisVector_scaled_power_of_residual_certificate
      (by have := x₀.isLt; omega : 0 < n) hσ₀ hσ₀tr hz₀ hz₀eig hμ hη P hcert)

/-- End-to-end rational-output form of the finite-precision LVV leading-vector step.
From an approximate compressed density at the standard trace-norm precision, it extracts
the exact compressed leading coordinates and returns a compact rational MPS family that
is directly `1/12`-viable.  Its coefficient height retains the mesh-independent support
coordinate radius, whose polynomial control is the remaining runtime issue. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_approximate_density
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (S : Finset (LeftBlockVector L q k)) {b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {m n : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (x₀ : Fin n) (τ σ : Matrix (Fin n) (Fin n) ℂ) {ε : ℝ}
    (hτtrace : τ.trace = 1) (hσpsd : σ.PosSemidef)
    (hclose : rectangularTraceNorm (σ - τ) ≤ ε)
    (hτenergy : (τ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hτboundary : rectangularTraceNorm (compressedBoundaryLM Z τ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (hε : ε ≤ Δ / (97344 * L)) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 8112 : ℝ) / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m c)) := by
  obtain ⟨σ₀, ρ, u, z₀, μ, hσ₀, hσ₀tr, hρexpand, hρ, hρtr, hu, huρ, hμ,
      hz₀, hz₀eig, hZz₀, hv₀unit, hv₀overlap, hcertificate, hpower⟩ :=
    h.exists_viable_vector_of_approximate_density_and_eigenresidual hL hq hΔ
      HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ x₀ τ σ
        hτtrace hσpsd hclose hτenergy hτboundary hε
  exact exists_rationalSpanViableMPSData_of_leadingCoordinates hL hΔ hε S hS hgs.1
    Z hZ hZZ z₀ hz₀ W hW hv₀unit hv₀overlap


end TNLean.MPS.AreaLaw
