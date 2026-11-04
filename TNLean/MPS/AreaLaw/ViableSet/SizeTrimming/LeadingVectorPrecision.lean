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
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.CompressedSolutions

/-!
# Precision bounds for compressed leading vectors

Trace-norm accuracy of a compressed density and norm or residual accuracy of its
leading vector determine explicit physical energy and ground-state overlap bounds.

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

/-- A positive approximate solution of the compressed boundary program yields a physical
LVV viable vector.  If the compressed trace-norm error is `ε`, normalization and expansion
produce objective error `2 ‖Zᴴ H_L Z‖ ε` and additional boundary error `2 ε`.
The displayed precision condition places their combined contribution inside the exact
` Δ / 2028` margin of the viable-vector estimate. -/
theorem ChainHamiltonian.exists_leading_vector_of_approximate_compressed_boundary_solution
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
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
    (hprecision : 24 * L * ε ≤ Δ / 2028) :
    ∃ (ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
        ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
      (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) (μ : ℝ),
      ρ.PosSemidef ∧ ρ.trace = 1 ∧
      (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤
        ((Δ / 169) ^ 2) / (2 * L) + 2 * ε ∧
      ‖u‖ = 1 ∧ ρ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧
      (∀ (ν : ℝ) (z : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)),
        z ≠ 0 → ρ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) ∧
      let P := reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S)
      let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
      1 / 2 < μ ∧ (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
        ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
        (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
        1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ ∧
        (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤
          E₀ + 14 * (Δ / 169) + 24 * L * ε ∧
        1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, v⟫_ℂ‖ ∧
        1 - (7 * (Δ / 169) + 12 * L * ε) / Δ ≤ μ ∧
        23 / 24 ≤ μ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let E := (vecMulVec x (star x) * Hleft).trace.re
  let η := ((Δ / 169) ^ 2) / (2 * L)
  obtain ⟨σ₀, hσ₀psd, hσ₀trace, hσ₀energy, hσ₀boundary⟩ :=
    exists_normalizedPositiveMatrix_approximate_program x₀ Z hZ τ σ K X E η ε
      hτtrace hσpsd hclose hτenergy hτboundary
  let ρ := Z * σ₀ * Zᴴ
  have hρpsd : ρ.PosSemidef := hσ₀psd.mul_mul_conjTranspose_same Z
  have htransport := isometricDensityExpansion_trace_and_energy Z hZ ρ σ₀ rfl Hleft
  have hρtrace : ρ.trace = 1 := htransport.1.symm.trans hσ₀trace
  have hρP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ := by
    rw [← hZZ]
    change (Z * Zᴴ) * (Z * σ₀ * Zᴴ) = Z * σ₀ * Zᴴ
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Z Zᴴ (Z * σ₀),
      ← Matrix.mul_assoc Zᴴ Z σ₀, hZ, Matrix.one_mul]
  have hρboundary : rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η + 2 * ε := by
    rw [isometricDensityExpansion_boundary_distance Z ρ σ₀ rfl X]
    exact hσ₀boundary
  have hρenergy : (ρ * Hleft).trace.re ≤ E + 2 * ‖K‖ * ε := by
    rw [htransport.2]
    exact hσ₀energy
  obtain ⟨u, μ, hu, huρ, -, hmax⟩ := hρpsd.exists_unit_eigenvector_max_eigenvalue hρtrace
  have hnum : 2 * (2 * ‖K‖ * ε + ‖B‖ * (2 * ε)) ≤ 24 * L * ε := by
    have hKn : ‖K‖ ≤ ‖Hleft‖ := l2_opNorm_isometricCompression_le Z hZ Hleft
    have hε0 : 0 ≤ ε := (rectangularTraceNorm_nonneg _).trans hclose
    have hHleft : ‖Hleft‖ ≤ 4 * L :=
      (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
    have hsum : ‖Hleft‖ + ‖B‖ ≤ 6 * L := by linarith only [hHleft, hBn]
    calc
      2 * (2 * ‖K‖ * ε + ‖B‖ * (2 * ε)) = 4 * (‖K‖ + ‖B‖) * ε := by ring
      _ ≤ 4 * (‖Hleft‖ + ‖B‖) * ε :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hKn le_rfl) (by norm_num)) hε0
      _ ≤ 24 * L * ε := by
        have hscaled : 4 * (‖Hleft‖ + ‖B‖) ≤ 24 * L := by linarith only [hsum]
        exact mul_le_mul_of_nonneg_right hscaled hε0
  have herr : 2 * (2 * ‖K‖ * ε + ‖B‖ * (2 * ε)) ≤ Δ / 2028 :=
    hnum.trans hprecision
  have hbounds := h.leading_bounds_of_approximate_boundary_solution hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX herr hρpsd hρtrace hρP
      hρboundary hρenergy u μ hu huρ hmax
  have hbase : 2 * (6 * (Δ / 169) + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)))) ≤ 14 * (Δ / 169) := by
    have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
    have hΔ4 : Δ ≤ 4 := by
      simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
    have hcr : 2 * (Δ / 169) ^ 2 ≤ Δ / 169 := by
      nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ4), hΔ]
    have hBτ : ‖B‖ * (2 * (((Δ / 169) ^ 2) / (2 * L))) ≤
        2 * (Δ / 169) ^ 2 := by
      calc
        ‖B‖ * (2 * (((Δ / 169) ^ 2) / (2 * L))) ≤
            (2 * L) * (2 * (((Δ / 169) ^ 2) / (2 * L))) :=
          mul_le_mul_of_nonneg_right hBn (by positivity)
        _ = 2 * (Δ / 169) ^ 2 := by field_simp [hL0]
    linarith only [hBτ, hcr]
  have htotal : 2 * (6 * (Δ / 169) + 2 * ‖K‖ * ε + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)) + 2 * ε)) ≤
      14 * (Δ / 169) + 24 * L * ε := by
    calc
      2 * (6 * (Δ / 169) + 2 * ‖K‖ * ε + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + 2 * ε)) =
          2 * (6 * (Δ / 169) + ‖B‖ *
            (2 * (((Δ / 169) ^ 2) / (2 * L)))) +
            2 * (2 * ‖K‖ * ε + ‖B‖ * (2 * ε)) := by ring
      _ ≤ 14 * (Δ / 169) + 24 * L * ε := add_le_add hbase hnum
  refine ⟨ρ, u, μ, hρpsd, hρtrace, hρP, hρboundary, hu, huρ, hmax, ?_⟩
  dsimp only
  refine ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2.1,
    hbounds.2.2.2.2.1, hbounds.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · have hsharp := hbounds.2.2.2.2.2.2.1
    calc
      _ ≤ E₀ + 2 * (6 * (Δ / 169) + 2 * ‖K‖ * ε + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + 2 * ε)) := hsharp
      _ ≤ E₀ + (14 * (Δ / 169) + 24 * L * ε) := by
        simpa only [add_comm] using add_le_add_left htotal E₀
      _ = E₀ + 14 * (Δ / 169) + 24 * L * ε := by ring
  · have hsharp := hbounds.2.2.2.2.2.2.2.1
    have := div_le_div_of_nonneg_right htotal hΔ.le
    linarith only [hsharp, this]
  · have hsharp := hbounds.2.2.2.2.2.2.2.2
    have hhalf : 6 * (Δ / 169) + 2 * ‖K‖ * ε + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + 2 * ε) ≤
        7 * (Δ / 169) + 12 * L * ε := by
      nlinarith only [htotal]
    have := div_le_div_of_nonneg_right hhalf hΔ.le
    linarith only [hsharp, this]
  · have hsharp := hbounds.2.2.2.2.2.2.2.2
    have hdeficit : 6 * (Δ / 169) + 2 * ‖K‖ * ε + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + 2 * ε) ≤ Δ / 24 := by
      nlinarith only [htotal, hprecision]
    have hratio := div_le_div_of_nonneg_right hdeficit hΔ.le
    have heq : (Δ / 24) / Δ = (1 : ℝ) / 24 := by
      field_simp [ne_of_gt hΔ]
    rw [heq] at hratio
    linarith only [hsharp, hratio]

/-- The density precision `ε` and compressed-vector precision `ζ` share the unused LVV
margin.  Under `24 L ε + 4 L ζ ≤ Δ / 2028`, the numerical physical vector retains the
original energy, overlap, normalization, and left-support conclusions. -/
theorem ChainHamiltonian.nearby_glued_vector_viable_of_density_and_vector_precision
    {L q k m : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ ε ζ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    {S : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
      WithLp.ofLp u')
    (hE : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤
        E₀ + 14 * (Δ / 169) + 24 * L * ε)
    (ha : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖)
    (hdist : ‖u' - u‖ ≤ ζ)
    (hprecision : 24 * L * ε + 4 * L * ζ ≤ Δ / 2028) :
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  have hΔ4 : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hζ0 : 0 ≤ ζ := (norm_nonneg (u' - u)).trans hdist
  have hΔL : Δ * ζ ≤ 4 * L * ζ := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith only [hΔ4, hL1, hζ0]
  have hmargin : Δ / 2028 = Δ / 12 - 14 * (Δ / 169) := by ring
  have hEreserve : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤ E₀ + Δ / 12 - 4 * L * ζ := by
    rw [hmargin] at hprecision
    linarith only [hE, hprecision]
  have hareserve : 1 - 1 / 12 + ζ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖ := by
    rw [hmargin] at hprecision
    have hscaled : 24 * L * ε + Δ * ζ ≤ Δ / 12 - 14 * (Δ / 169) :=
      by linarith only [hΔL, hprecision]
    apply ha.trans'
    field_simp [ne_of_gt hΔ]
    nlinarith only [hscaled, hΔ]
  exact h.nearby_glued_vector_viable_bounds hgs.1 W hW u u' hu hu' hu'P
    hEreserve hareserve hdist

/-- The finite-precision LVV conclusion depends only on the ray of the exact leading
vector.  Thus a numerical vector may be close to any phase representative of it. -/
theorem ChainHamiltonian.nearby_glued_vector_viable_of_phase_distance
    {L q k m : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ ε ζ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    {S : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
      WithLp.ofLp u')
    (hE : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤
        E₀ + 14 * (Δ / 169) + 24 * L * ε)
    (ha : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖)
    (hdist : ∃ θ : ℝ, ‖u' - Complex.exp (θ * Complex.I) • u‖ ≤ ζ)
    (hprecision : 24 * L * ε + 4 * L * ζ ≤ Δ / 2028) :
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  obtain ⟨θ, hθ⟩ := hdist
  let c := Complex.exp (θ * Complex.I)
  have hc : ‖c‖ = 1 := by
    dsimp only [c]
    rw [Complex.norm_exp]
    norm_num
  have hcu : ‖c • u‖ = 1 := by rw [norm_smul, hc, hu, one_mul]
  have hinv := gluedVector_phase_invariants W u θ h.operator Γ
  have hEθ : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp (c • u)) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp (c • u)) ∘
              gluingCut L q k))⟫_ℂ).re ≤
        E₀ + 14 * (Δ / 169) + 24 * L * ε := by
    rw [show c = Complex.exp (θ * Complex.I) from rfl, hinv.1]
    exact hE
  have haθ : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp (c • u)) ∘
          gluingCut L q k)⟫_ℂ‖ := by
    rw [show c = Complex.exp (θ * Complex.I) from rfl, hinv.2]
    exact ha
  exact h.nearby_glued_vector_viable_of_density_and_vector_precision hL hq hΔ hgs
    W hW (c • u) u' hcu hu' hu'P hEθ haθ hθ hprecision

/-- A normalized numerical vector may be supplied by an eigensolver through its
residual rather than through an a priori distance to the exact leading vector.  At
the LVV spectral separation `μ ≥ 23 / 24`, residual at most `11 ζ / 24` gives the
same physical viability conclusion. -/
theorem ChainHamiltonian.nearby_glued_vector_viable_of_density_and_vector_residual
    {L q k m : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1)
    (hL : 0 < L) (hq : 2 ≤ q) {E₀ Δ ε ζ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    {S : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    {ρ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (u u' : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))
    {μ : ℝ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (huρ : ρ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ)
    (hu'P : (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ WithLp.ofLp u' =
      WithLp.ofLp u')
    (hE : (⟪WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k),
        toEuclideanLin h.operator (WithLp.toLp 2
          ((((1 : Matrix (CutLeft L q k × CutSite L q k)
            (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
              gluingCut L q k))⟫_ℂ).re ≤
        E₀ + 14 * (Δ / 169) + 24 * L * ε)
    (ha : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤ ‖⟪Γ, WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
          gluingCut L q k)⟫_ℂ‖)
    (hres : ‖toEuclideanLin ρ u' - (μ : ℂ) • u'‖ ≤ (11 / 24) * ζ)
    (hprecision : 24 * L * ε + 4 * L * ζ ≤ Δ / 2028) :
    let v' := WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u') ∘
          gluingCut L q k)
    ‖v'‖ = 1 ∧ v' ∈ leftSupportSubmodule S ∧
      (⟪v', toEuclideanLin h.operator v'⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v'⟫_ℂ‖ := by
  have hζ : 0 ≤ ζ := by
    have hscaled : 0 ≤ (11 / 24) * ζ := (norm_nonneg _).trans hres
    nlinarith only [hscaled]
  obtain ⟨θ, hθ⟩ := Matrix.PosSemidef.exists_phase_distance_le_of_residual_le
    hρ hρtr hu hu' huρ hμ hζ hres
  exact h.nearby_glued_vector_viable_of_phase_distance hL hq hΔ hgs W hW u u'
    hu hu' hu'P hE ha ⟨θ, hθ⟩ hprecision

/-- Splitting the unused LVV margin equally between the density approximation and the
compressed leading-vector approximation gives explicit independent precision targets.
Thus it suffices to solve the compressed density problem to trace-norm error
`Δ / (97344 L)` and the compressed vector problem to Hilbert-space error
`Δ / (16224 L)`. -/
theorem density_and_vector_precision_of_separate_bounds {L : ℕ} (hL : 0 < L)
    {Δ ε ζ : ℝ} (hε : ε ≤ Δ / (97344 * L)) (hζ : ζ ≤ Δ / (16224 * L)) :
    24 * L * ε + 4 * L * ζ ≤ Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hεscaled : 24 * L * ε ≤ Δ / 4056 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4056)).2
    have hε' := (le_div_iff₀ (mul_pos (by norm_num) hLreal)).1 hε
    nlinarith only [hε']
  have hζscaled : 4 * L * ζ ≤ Δ / 4056 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4056)).2
    have hζ' := (le_div_iff₀ (mul_pos (by norm_num) hLreal)).1 hζ
    nlinarith only [hζ']
  linarith only [hεscaled, hζscaled]

/-- The same density precision leaves exactly half of the unused LVV overlap margin for
rationalizing the support columns.  With rationalization parameter `ξ = 1 / 8112`, the
exact leading-vector error and the additional `2ξ` remain within the target `1 / 12`.
This is the budget needed by the rational column construction following LVV13,
`algo53.tex`, lines 493--527. -/
theorem density_and_rationalization_overlap_budget {L : ℕ} (hL : 0 < L)
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : ε ≤ Δ / (97344 * L)) :
    (14 * (Δ / 169) + 24 * L * ε) / Δ + 2 * (1 / 8112) ≤ 1 / 12 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hεscaled : 24 * L * ε ≤ Δ / 4056 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4056)).2
    have hε' := (le_div_iff₀ (mul_pos (by norm_num) hLreal)).1 hε
    nlinarith only [hε']
  have hratio : (24 * L * ε) / Δ ≤ 1 / 4056 := by
    apply (div_le_iff₀ hΔ).2
    nlinarith only [hεscaled]
  rw [add_div]
  have hbase : (14 * (Δ / 169)) / Δ = 14 / 169 := by
    field_simp [ne_of_gt hΔ]
  rw [hbase]
  norm_num at hratio ⊢
  linarith only [hratio]

/-- An exact leading vector in compressed coordinates, together with the standard LVV
density precision, yields compact rational MPS data that is directly `1/12`-viable.
The rationalization share is fixed to `ξ = 1/8112`; its mesh is chosen after the
mesh-independent support-coordinate radius.  This connects the leading-vector theorem
to the rational output representation of LVV13, `algo53.tex`, lines 493--527. -/
theorem exists_rationalSpanViableMPSData_of_leadingCoordinates
    {L q k : ℕ} [NeZero q] (hL : 0 < L) {Δ ε : ℝ} (hΔ : 0 < Δ)
    (hε : ε ≤ Δ / (97344 * L))
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖WithLp.toLp 2
      ((((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
          WithLp.ofLp (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))) ∘ gluingCut L q k)‖ = 1)
    (hoverlap : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤
      ‖⟪Γ, WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))) ∘
              gluingCut L q k)⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 8112 : ℝ) / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m c)) := by
  let u := WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)
  have hu : ‖physicalRightApply W (gluingLeftCoordinates L q k m u)‖ = 1 := by
    rw [physicalRightApply_gluingLeftCoordinates]
    exact hunit
  have ha : 1 - (14 * (Δ / 169) + 24 * L * ε) / Δ ≤
      ‖⟪physicalRightApply W (gluingLeftCoordinates L q k m u), Γ⟫_ℂ‖ := by
    rw [physicalRightApply_gluingLeftCoordinates, norm_inner_symm]
    exact hoverlap
  exact exists_rationalSpanViableMPSData_of_mulVec_atTarget S hS hΓ
    (by norm_num : (0 : ℝ) < 1 / 8112) (by norm_num : (1 : ℝ) / 8112 < 1)
    (density_and_rationalization_overlap_budget hL hΔ hε) Z hZ hZZ z hz W hW hu ha

end TNLean.MPS.AreaLaw
