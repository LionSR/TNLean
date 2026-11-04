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

/-!
# Compressed boundary solutions and finite density approximation

Exact compressed boundary densities with objective and boundary slack produce viable vectors.
Finite trace-norm nets provide explicit approximate densities at the required precision.

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

/-- The canonical density-mesh radius which uses exactly the unused LVV numerical margin. -/
noncomputable def lvvFiniteDensityMesh (L : ℕ) (Δ : ℝ) : ℝ := Δ / (48672 * L)

/-- The canonical finite-density mesh is positive for a nontrivial chain and positive gap. -/
theorem lvvFiniteDensityMesh_pos {L : ℕ} {Δ : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) :
    0 < lvvFiniteDensityMesh L Δ := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  exact div_pos hΔ (mul_pos (by norm_num) hLreal)

/-- The canonical finite-density mesh saturates the available LVV error budget. -/
theorem lvvFiniteDensityMesh_fits {L : ℕ} {Δ : ℝ} (hL : 0 < L) :
    24 * L * lvvFiniteDensityMesh L Δ = Δ / 2028 := by
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  dsimp only [lvvFiniteDensityMesh]
  field_simp [hLreal]
  ring

/-- An exact compressed density satisfying objective and boundary constraints with slack
produces a physical LVV viable vector.  This separates the numerical repair of a
semidefinite certificate from its physical use. -/
theorem ChainHamiltonian.exists_viable_vector_of_compressed_boundary_solution_with_slack
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
    (σ : Matrix (Fin n) (Fin n) ℂ) (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    {ξ δ : ℝ}
    (hσenergy : (σ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (hσboundary : rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ)
    (herr : 2 * (ξ + ‖B‖ * δ) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let ρ := Z * σ * Zᴴ
  have hρ : ρ.PosSemidef := hσ.mul_mul_conjTranspose_same Z
  have htransport := isometricDensityExpansion_trace_and_energy Z hZ ρ σ rfl Hleft
  have hρtrace : ρ.trace = 1 := htransport.1.symm.trans hσtrace
  have hρP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ := by
    rw [← hZZ]
    change (Z * Zᴴ) * (Z * σ * Zᴴ) = Z * σ * Zᴴ
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Z Zᴴ (Z * σ),
      ← Matrix.mul_assoc Zᴴ Z σ, hZ, Matrix.one_mul]
  have hρboundary : rectangularTraceNorm (partialTraceFirst ρ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ := by
    rw [isometricDensityExpansion_boundary_distance Z ρ σ rfl X]
    exact hσboundary
  have hρenergy : (ρ * Hleft).trace.re ≤
      (vecMulVec x (star x) * Hleft).trace.re + ξ := by
    rw [htransport.2]
    exact hσenergy
  obtain ⟨u, μ, hu, huρ, -, hmax⟩ := hρ.exists_unit_eigenvector_max_eigenvalue hρtrace
  have hbounds := h.leading_bounds_of_approximate_boundary_solution hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX herr hρ hρtrace hρP
      hρboundary hρenergy u μ hu huρ hmax
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection S)
  let v : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2
    ((((1 : Matrix (CutLeft L q k × CutSite L q k)
      (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘ gluingCut L q k)
  exact ⟨v, hbounds.2.2.1, hbounds.2.2.2.1, hbounds.2.2.2.2.1,
    hbounds.2.2.2.2.2.1⟩

/-- An exact compressed boundary solution whose sharp leading-vector overlap leaves a
rationalization reserve produces compact rational viable MPS data.  The dominant
eigenvector is pulled back through the support isometry before its physical left columns
are rationalized.  This is the rational-output form of the size-trimming step in LVV13,
`algo53.tex`, lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_compressed_boundary_solution_with_slack
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
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
    (σ : Matrix (Fin n) (Fin n) ℂ) (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    {ξ δ ξrat : ℝ}
    (hσenergy : (σ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (hσboundary : rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ)
    (herr : 2 * (ξ + ‖B‖ * δ) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hbudget : 2 * (6 * (Δ / 169) + ξ + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let ρ := Z * σ * Zᴴ
  have hρ : ρ.PosSemidef := hσ.mul_mul_conjTranspose_same Z
  have htransport := isometricDensityExpansion_trace_and_energy Z hZ ρ σ rfl Hleft
  have hρtrace : ρ.trace = 1 := htransport.1.symm.trans hσtrace
  have hρP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ := by
    rw [← hZZ]
    change (Z * Zᴴ) * (Z * σ * Zᴴ) = Z * σ * Zᴴ
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Z Zᴴ (Z * σ),
      ← Matrix.mul_assoc Zᴴ Z σ, hZ, Matrix.one_mul]
  have hρboundary : rectangularTraceNorm (partialTraceFirst ρ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ := by
    rw [isometricDensityExpansion_boundary_distance Z ρ σ rfl X]
    exact hσboundary
  have hρenergy : (ρ * Hleft).trace.re ≤
      (vecMulVec x (star x) * Hleft).trace.re + ξ := by
    rw [htransport.2]
    exact hσenergy
  obtain ⟨u, μ, hu, huρ, -, hmax⟩ := hρ.exists_unit_eigenvector_max_eigenvalue hρtrace
  have hbounds := h.leading_bounds_of_approximate_boundary_solution hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX herr hρ hρtrace hρP
      hρboundary hρenergy u μ hu huρ hmax
  let z : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Zᴴ *ᵥ WithLp.ofLp u)
  have hcoords := isometricDensityExpansion_eigenvector_coordinates
    Z hZ ρ σ rfl u (μ : ℂ) (by rw [hZZ]; exact hbounds.2.1) huρ
  have hz : ‖z‖ = 1 := hcoords.1.trans hu
  have hZz : WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z) = u := hcoords.2.1
  have hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1 := by
    rw [physicalRightApply_gluingLeftCoordinates, hZz]
    exact hbounds.2.2.1
  have hoverlap : 1 - 2 * (6 * (Δ / 169) + ξ + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ ≤
      ‖⟪physicalRightApply W
        (gluingLeftCoordinates L q k m
          (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖ := by
    rw [physicalRightApply_gluingLeftCoordinates, hZz, norm_inner_symm]
    exact hbounds.2.2.2.2.2.2.2.1
  exact exists_rationalSpanViableMPSData_of_mulVec_atTarget S hS hgs.1
    hξrat hξrat1 hbudget Z hZ hZZ z hz W hW hunit hoverlap

/-- Coordinate-rational form of the exact compressed boundary-solution theorem.  It
can consume the compact output invariant from a preceding LVV iteration. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_compressed_boundary_solution_with_slack
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (S : Finset (LeftBlockVector L q k)) {s₀ b Hv : ℕ} {δin : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δin S)
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
    (σ : Matrix (Fin n) (Fin n) ℂ) (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    {ξ δ ξrat : ℝ}
    (hσenergy : (σ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + ξ)
    (hσboundary : rectangularTraceNorm (compressedBoundaryLM Z σ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ)
    (herr : 2 * (ξ + ‖B‖ * δ) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hbudget : 2 * (6 * (Δ / 169) + ξ + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12) (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let ρ := Z * σ * Zᴴ
  have hρ : ρ.PosSemidef := hσ.mul_mul_conjTranspose_same Z
  have htransport := isometricDensityExpansion_trace_and_energy Z hZ ρ σ rfl Hleft
  have hρtrace : ρ.trace = 1 := htransport.1.symm.trans hσtrace
  have hρP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * ρ = ρ := by
    rw [← hZZ]
    change (Z * Zᴴ) * (Z * σ * Zᴴ) = Z * σ * Zᴴ
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Z Zᴴ (Z * σ),
      ← Matrix.mul_assoc Zᴴ Z σ, hZ, Matrix.one_mul]
  have hρboundary : rectangularTraceNorm (partialTraceFirst ρ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) + δ := by
    rw [isometricDensityExpansion_boundary_distance Z ρ σ rfl X]
    exact hσboundary
  have hρenergy : (ρ * Hleft).trace.re ≤
      (vecMulVec x (star x) * Hleft).trace.re + ξ := by
    rw [htransport.2]
    exact hσenergy
  obtain ⟨u, μ, hu, huρ, -, hmax⟩ := hρ.exists_unit_eigenvector_max_eigenvalue hρtrace
  have hbounds := h.leading_bounds_of_approximate_boundary_solution hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX herr hρ hρtrace hρP
      hρboundary hρenergy u μ hu huρ hmax
  let z : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Zᴴ *ᵥ WithLp.ofLp u)
  have hcoords := isometricDensityExpansion_eigenvector_coordinates
    Z hZ ρ σ rfl u (μ : ℂ) (by rw [hZZ]; exact hbounds.2.1) huρ
  have hz : ‖z‖ = 1 := hcoords.1.trans hu
  have hZz : WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z) = u := hcoords.2.1
  have hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1 := by
    rw [physicalRightApply_gluingLeftCoordinates, hZz]
    exact hbounds.2.2.1
  have hoverlap : 1 - 2 * (6 * (Δ / 169) + ξ + ‖B‖ *
      (2 * (((Δ / 169) ^ 2) / (2 * L)) + δ)) / Δ ≤
      ‖⟪physicalRightApply W
        (gluingLeftCoordinates L q k m
          (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖ := by
    rw [physicalRightApply_gluingLeftCoordinates, hZz, norm_inner_symm]
    exact hbounds.2.2.2.2.2.2.2.1
  exact exists_rationalCoordinateViableMPSData_of_mulVec_atTarget S D hgs.1
    hξrat hξrat1 hbudget Z hZ hZZ z hz W hW hunit hoverlap

/-- A finite exact-density search has a least-energy relaxed-feasible certificate whose
physical expansion is an LVV viable vector.  Starting from one exactly feasible density,
a mesh of radius `δ` increases the boundary tolerance by `2 δ` and the compressed energy
by `2 ‖K‖ δ`.  The condition `24 L δ ≤ Δ / 2028` places both losses inside the
unused margin of the leading-vector estimate.

This is an existence theorem for the finite family; it does not assert that its exact-density
representatives are effectively enumerable. -/
theorem ChainHamiltonian.exists_finite_density_search_viable_vector
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
    (hXHermitian : X.IsHermitian)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    (τ₀ : Matrix (Fin n) (Fin n) ℂ) (hτ₀ : τ₀.PosSemidef) (hτ₀trace : τ₀.trace = 1)
    (hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (hτ₀energy : (τ₀ * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    {δ : ℝ} (hδ : 0 < δ) (hprecision : 24 * L * δ ≤ Δ / 2028) :
    ∃ N : Finset (Matrix (Fin n) (Fin n) ℂ),
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ σ ∈ N,
        (∀ ρ ∈ N,
          rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤
              ((Δ / 169) ^ 2) / (2 * L) + 2 * δ →
          (σ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
          (ρ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re) ∧
        ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
        ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
        (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
        1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let E := (vecMulVec x (star x) * Hleft).trace.re
  let η := ((Δ / 169) ^ 2) / (2 * L)
  obtain ⟨N, hNcard, hNdensity, σ, hσN, hσboundary, hσenergy, hσmin⟩ :=
    exists_finset_minimizing_approx_compressed_boundary_solution_at_energy
      Z hZ K X hXHermitian hδ
      hτ₀ hτ₀trace (by simpa only [η] using hτ₀boundary)
        (by simpa only [K, E, Hleft] using hτ₀energy)
  have hop : ‖h.operator‖ ≤ 2 * L := by
    simpa only [mul_one] using h.norm_operator_le_of_range_one
  have hHLn : ‖HL‖ ≤ 4 * L := by
    have heq : HL = h.operator - B := by rw [hsplit]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith only [hop, hBn])
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (l2_opNorm_kronecker_one_le (leftCutOperator k HL)).trans
      ((norm_leftCutOperator_eq hHL).le.trans hHLn)
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have hcombined : 2 * (‖K‖ * (2 * δ) + ‖B‖ * (2 * δ)) ≤ 24 * L * δ := by
    have hδ0 : 0 ≤ δ := hδ.le
    calc
      2 * (‖K‖ * (2 * δ) + ‖B‖ * (2 * δ)) = 4 * (‖K‖ + ‖B‖) * δ := by ring
      _ ≤ 4 * (4 * L + 2 * L) * δ := by gcongr
      _ = 24 * L * δ := by ring
  have herr : 2 * (‖K‖ * (2 * δ) + ‖B‖ * (2 * δ)) ≤ Δ / 2028 :=
    hcombined.trans hprecision
  obtain ⟨v, hvnorm, hvS, hvenergy, hvoverlap⟩ :=
    h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
      HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ
        (hNdensity σ hσN).1 (hNdensity σ hσN).2
        (ξ := ‖K‖ * (2 * δ)) (δ := 2 * δ)
        (by simpa only [K, E, Hleft] using hσenergy)
        (by simpa only [η] using hσboundary) herr
  exact ⟨N, hNcard, hNdensity, σ, hσN, by
    intro ρ hρN hρboundary
    exact hσmin ρ hρN (by simpa only [η] using hρboundary),
    v, hvnorm, hvS, hvenergy, hvoverlap⟩

/-- The normalized supported glued vector supplies both the coordinate isometry and the
initial feasible compressed density needed by the finite LVV search.  The resulting
coordinate order is at most `|S| m`, and the returned viable vector comes from a
least-energy relaxed-feasible member of the finite density family.  No compressed support
data are assumed separately. -/
theorem ChainHamiltonian.exists_coordinate_finite_density_search_viable_vector
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) (S : Finset (LeftBlockVector L q k))
    {m : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    (hxnorm : ‖WithLp.toLp 2 x‖ = 1)
    (hxP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXHermitian : X.IsHermitian)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    {δ : ℝ} (hδ : 0 < δ) (hprecision : 24 * L * δ ≤ Δ / 2028) :
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (N : Finset (Matrix (Fin n) (Fin n) ℂ)),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧
      Z * Zᴴ = reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) ∧
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ σ ∈ N,
        (∀ ρ ∈ N,
          rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤
              ((Δ / 169) ^ 2) / (2 * L) + 2 * δ →
          (σ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
          (ρ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re) ∧
        ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
        ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q k)) ∧
        (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
        1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  obtain ⟨n, Z, τ₀, hnpos, hn, hZ, hZZ, hτ₀, hτ₀trace, hρxexpand⟩ :=
    exists_boundarySupportedVectorDensityCompression S m x hxnorm hxP
  let ρx := vecMulVec x (star x)
  have hρxexpand' : ρx = Z * τ₀ * Zᴴ := by simpa only [ρx] using hρxexpand
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  have htransport := isometricDensityExpansion_trace_and_energy Z hZ ρx τ₀ hρxexpand' Hleft
  have hτ₀boundary : rectangularTraceNorm (compressedBoundaryLM Z τ₀ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) := by
    rw [← isometricDensityExpansion_boundary_distance Z ρx τ₀ hρxexpand' X]
    simpa only [ρx] using hX
  have hτ₀energy : (τ₀ * (Zᴴ * Hleft * Z)).trace.re ≤
      (vecMulVec x (star x) * Hleft).trace.re := by
    rw [← htransport.2]
  obtain ⟨N, hNcard, hNdensity, σ, hσN, hσmin,
      v, hvnorm, hvS, hvenergy, hvoverlap⟩ :=
    h.exists_finite_density_search_viable_vector hL hq hΔ HL B hsplit hHL hBS hBn
      hgs (S := (S : Set (LeftBlockVector L q k))) W hW x hwx hwE X hXHermitian hX
        Z hZ hZZ τ₀ hτ₀ hτ₀trace
        (by simpa only [Hleft] using hτ₀boundary)
        (by simpa only [Hleft] using hτ₀energy) hδ hprecision
  exact ⟨n, Z, N, hnpos, hn, hZ, hZZ, hNcard, hNdensity, σ, hσN, hσmin, v,
    hvnorm, hvS, hvenergy, hvoverlap⟩

/-- At the canonical LVV mesh, the supported glued vector determines the compressed
coordinates, the finite least-energy relaxed-feasible density, and its physical viable
vector without any further precision choice. -/
theorem ChainHamiltonian.exists_canonical_coordinate_finite_density_search_viable_vector
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) (S : Finset (LeftBlockVector L q k))
    {m : ℕ} (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    (hxnorm : ‖WithLp.toLp 2 x‖ = 1)
    (hxP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXHermitian : X.IsHermitian)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L)) :
    ∃ (n : ℕ) (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (N : Finset (Matrix (Fin n) (Fin n) ℂ)),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧
      Z * Zᴴ = reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) ∧
      N.card ≤ (2 * ⌈(n : ℝ) ^ 2 / lvvFiniteDensityMesh L Δ⌉₊ + 1) ^ (2 * n ^ 2) ∧
      (∀ ρ ∈ N, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∃ σ ∈ N,
        (∀ ρ ∈ N,
          rectangularTraceNorm (compressedBoundaryLM Z ρ - X) ≤
              ((Δ / 169) ^ 2) / (2 * L) + 2 * lvvFiniteDensityMesh L Δ →
          (σ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
          (ρ * (Zᴴ * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re) ∧
        ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
          ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q k)) ∧
          (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
          1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  exact h.exists_coordinate_finite_density_search_viable_vector hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S W hW x hxnorm hxP hwx hwE X hXHermitian hX
      (lvvFiniteDensityMesh_pos hL hΔ) (lvvFiniteDensityMesh_fits hL).le

end TNLean.MPS.AreaLaw
