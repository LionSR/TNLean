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
# The size-trimming selection, chosen before the ground state

Fix the Hamiltonian, the gap parameter and a finite left family. For every actual bond
dimension up to the uniform cut bound, take the chosen boundary net and minimize the left
energy at each feasible point. The union of the resulting left columns is the named
selection `sizeTrimmingSelection`, a function of the Hamiltonian, the gap parameter and
the input family alone. Whenever the input family is viable, one of these optimization
problems supplies a unit vector witnessing viability of the selection with error `1 / 12`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (nontrivial chains and bond bound):** The result assumes `0 < L` and
`2 ≤ q`, as recorded in `docs/paper-gaps/lvv13_nontrivial_chain.tex`, and uses the library's
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

/-- A fully approximate numerical semidefinite certificate, at the independent precision
targets of `fullyApproxSDP_errors_fit_lvv_margin`, produces the physical LVV viable
vector.  This composes spectral repair of all cone variables, trace repair, the inexact
boundary equation, support expansion, and the leading-vector argument. -/
theorem ChainHamiltonian.exists_viable_vector_of_all_spectral_approx_sdp_certificate
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hP : P.IsHermitian) (hN : N.IsHermitian)
    {κ ε εb δ : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hεb : 0 ≤ εb) (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ ((Δ / 169) ^ 2) / (2 * L))
    (henergy : (A * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hκbound : κ ≤ Δ / (64896 * L))
    (hεbound : 2 * n * ε ≤ Δ / (64896 * L))
    (hεbbound : 2 * Fintype.card (CutSite L q k × Fin m) * εb ≤
      Δ / (64896 * L))
    (hδbound : δ ≤ Δ / (64896 * L)) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ :=
    exists_density_of_all_spectral_approx_sdp_certificate
      Z hZ K X hA hP hN htrace hε hmin hPmin hNmin hresidual htraces henergy
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans htrace
  have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hresidual
  have hrepair0 : 0 ≤ repair := by dsimp only [repair]; positivity
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    positivity
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
  have harith := fullyApproxSDP_errors_fit_lvv_margin hL
    hκbound hεbound hεbbound hδbound
  have hnum : 2 * (‖K‖ * repair + ‖B‖ * boundaryError) ≤
      2 * (4 * L * repair + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * (‖K‖ * repair + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by simpa only [repair, boundaryError, add_assoc] using harith)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- A unified approximate certificate yields the physical LVV viable vector whenever
its total repaired energy and boundary error fits the available margin.  This form is
suited to certificates transferred from rational approximations of the fixed matrices,
whose rounding losses need not be assigned to one of the four original tolerances. -/
theorem ChainHamiltonian.exists_viable_vector_of_approx_sdp_error_budget
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    {κ ε εb δ eK : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L))
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hbudget : 2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((2 * Fintype.card (CutSite L q k × Fin m) * εb + δ) +
        (κ + 2 * n * ε))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hcert.htrace
    exact add_nonneg hκ0 (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hcert.hresidual
    exact add_nonneg
      (add_nonneg (mul_nonneg (by positivity) hcert.hεb) hδ0) hrepair0
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
  have hnum : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
      2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by
      convert hbudget using 1
      simp only [repair, boundaryError]
      ring)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- The error-budget theorem with an additional auxiliary-trace allowance.  A
certificate with trace budget `η + eη` incurs the extra boundary error `eη`; this is the
form needed for certificates obtained by finite rational search. -/
theorem ChainHamiltonian.exists_viable_vector_of_approx_sdp_error_budget_with_trace_slack
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    {κ ε εb δ eK eη : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (heη : 0 ≤ eη)
    (hbudget : 2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ) +
        (κ + 2 * n * ε))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hcert.htrace
    exact add_nonneg hκ0 (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hcert.hresidual
    exact add_nonneg
      (add_nonneg (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb)) hδ0)
      hrepair0
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
  have hnum : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
      2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by
      convert hbudget using 1
      simp only [repair, boundaryError]
      ring)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- A repaired approximate semidefinite certificate produces rational viable MPS data
once the sharp leading-vector deficit and the rationalization reserve fit the target.
The statement includes the auxiliary trace slack used by the executable rational search.
It is the certificate-level rational-output step of LVV13, `algo53.tex`, lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_approx_sdp_error_budget_with_trace_slack
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    {κ ε εb δ eK eη ξrat : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hleading : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  apply h.exists_rationalViableMPSData_of_compressed_boundary_solution_with_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hX Z hZ hZZ
      σ hσ hσtrace (hξrat := hξrat) (hξrat1 := hξrat1)
      (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · simpa only [K, Hleft, repair, boundaryError] using hleading
  · simpa only [K, Hleft, repair, boundaryError] using hrational

/-- A repaired approximate semidefinite certificate transports the compact
coordinate-rational invariant from one LVV iteration to the next. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_approx_sdp_error_budget_with_trace_slack
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    {κ ε εb δ eK eη ξrat : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hleading : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12) (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  apply h.exists_rationalCoordinateData_of_compressed_boundary_solution_with_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hX Z hZ hZZ
      σ hσ hσtrace (hξrat := hξrat) (hξrat1 := hξrat1)
      (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · simpa only [K, Hleft, repair, boundaryError] using hleading
  · simpa only [K, Hleft, repair, boundaryError] using hrational

/-- A code returned by the executable rational search yields the physical LVV viable
vector once its exact-data error budget fits the available margin.  The differences
between the rational trace and energy thresholds and their physical targets are charged
as `eη` and `eK`. -/
theorem ChainHamiltonian.exists_viable_vector_of_rational_search_result
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hbudget : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Ephys := (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
    (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, δ', r, C] <;> ring
  apply h.exists_viable_vector_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ hcert
  · exact heη
  · simpa only [eη, eK, Ephys, δ', r, C, K] using hbudget

/-- A code returned by the executable rational certificate search directly produces
compact rational viable MPS data.  Besides the ordinary repaired-certificate margin,
the sharp overlap budget reserves `2 * ξrat` for rationalizing the physical left columns.
This is the executable rational-output step of LVV13, `algo53.tex`, lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_rational_search_result
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX ξrat : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hleading : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
      let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
      2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m coeff)) := by
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let Ephys := (vecMulVec x (star x) * Hleft).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
  let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K, Hleft] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, Hleft, δ', r, C] <;> ring
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    exact add_nonneg ((abs_nonneg _).trans hcert.htrace)
      (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    exact add_nonneg
      (add_nonneg
        (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb))
        ((rectangularTraceNorm_nonneg _).trans hcert.hresidual))
      hrepair0
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
  have hleadingExact :
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 := by
    calc
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
          2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by gcongr
      _ ≤ Δ / 2028 := by
        convert hleading using 1
        simp only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError]
        ring
  have hrationalExact :
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12 := by
    have hinner : 6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) ≤
        6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) := by
      gcongr
    have hscaled := div_le_div_of_nonneg_right hinner hΔ.le
    have hrational' :
        2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat ≤ 1 / 12 := by
      simpa only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError] using hrational
    calc
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat =
          2 * ((6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
            (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
              2 * ξrat := by ring
      _ ≤ 2 * ((6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
            2 * ξrat := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2))
                (2 * ξrat)
      _ = 2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat := by ring
      _ ≤ 1 / 12 := hrational'
  apply h.exists_rationalViableMPSData_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hX Z hZ hZZ
      hcert hleadingExact hξrat hξrat1
  simpa only [K, Hleft, repair, boundaryError] using hrationalExact

/-- A code returned by the executable rational certificate search transports the
coordinate-rational viable-MPS invariant through the repaired certificate and column
rationalization.  This is the successive-iteration form of LVV13, `algo53.tex`,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_rational_search_result
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX ξrat : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hleading : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
      let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
      2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12)
          (spanColumnFamily S m coeff)) := by
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let Ephys := (vecMulVec x (star x) * Hleft).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
  let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K, Hleft] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, Hleft, δ', r, C] <;> ring
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    exact add_nonneg ((abs_nonneg _).trans hcert.htrace)
      (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    exact add_nonneg
      (add_nonneg
        (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb))
        ((rectangularTraceNorm_nonneg _).trans hcert.hresidual))
      hrepair0
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
  have hleadingExact :
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 := by
    calc
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
          2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by gcongr
      _ ≤ Δ / 2028 := by
        convert hleading using 1
        simp only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError]
        ring
  have hrationalExact :
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12 := by
    have hinner : 6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) ≤
        6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) := by
      gcongr
    have hscaled := div_le_div_of_nonneg_right hinner hΔ.le
    have hrational' :
        2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat ≤ 1 / 12 := by
      simpa only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError] using hrational
    calc
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat =
          2 * ((6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
            (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
              2 * ξrat := by ring
      _ ≤ 2 * ((6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
            2 * ξrat := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2))
                (2 * ξrat)
      _ = 2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat := by ring
      _ ≤ 1 / 12 := hrational'
  apply h.exists_rationalCoordinateData_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hX Z hZ hZZ
      hcert hleadingExact hξrat hξrat1
  simpa only [K, Hleft, repair, boundaryError] using hrationalExact


/-- For the physical cut coordinates, the explicit coordinate map contributes two
rational scalars for each of its `q ^ |leftBlock L (k - 1)| * r * n` complex entries.
Thus the ambient factor in the encoding obstruction is the full left-block Hilbert-space
dimension, rather than the compressed order `n`. -/
theorem cutLeft_coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
    (L q k n r H : ℕ) :
    2 * (((q ^ min L (k - 1)) * r) * n) ≤
      compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q k)) n r H := by
  rw [card_cutLeft]
  exact coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound _ _ _ _

/-- At the last cut of a chain with local dimension at least two, the explicit
coordinate-map encoding bound already contains a factor `2 ^ (L - 1)`. -/
theorem twoPow_mul_le_cutLeft_compressedSDPInputBitSizeBound
    (L q n r H : ℕ) (hq : 2 ≤ q) :
    2 * (((2 ^ (L - 1)) * r) * n) ≤
      compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H := by
  calc
    2 * (((2 ^ (L - 1)) * r) * n) ≤ 2 * (((q ^ (L - 1)) * r) * n) := by
      gcongr
    _ = 2 * (((q ^ min L (L - 1)) * r) * n) := by
      rw [min_eq_right (Nat.sub_le L 1)]
    _ ≤ compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H :=
      cutLeft_coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
        L q L n r H

/-- For positive compressed and boundary orders, the explicit last-cut input has bit-size
at least `2 ^ L`.  This is the direct exponential obstruction for the ambient-coordinate
encoding used by the rational search. -/
theorem twoPow_le_cutLeft_compressedSDPInputBitSizeBound
    (L q n r H : ℕ) (hL : 0 < L) (hq : 2 ≤ q) (hn : 0 < n) (hr : 0 < r) :
    2 ^ L ≤ compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  calc
    2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; omega
    _ ≤ 2 * (((2 ^ L) * r) * n) := by
      calc
        2 * 2 ^ L = (2 * 2 ^ L) * 1 := by omega
        _ ≤ (2 * 2 ^ L) * (r * n) :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr.ne' hn.ne'))
        _ = 2 * (((2 ^ L) * r) * n) := by ring
    _ ≤ compressedSDPInputBitSizeBound
        (Fintype.card (CutLeft (L + 1) q (L + 1))) n r H :=
      twoPow_mul_le_cutLeft_compressedSDPInputBitSizeBound (L + 1) q n r H hq

/-- The canonical approximate-certificate thresholds leave enough of the sharp LVV
overlap margin to rationalize the selected columns with parameter `1 / 16224`.
For normalized range-one chains the required gap bound `Δ ≤ 4` follows from the
Hamiltonian norm estimate. -/
theorem canonical_search_rationalization_overlap_budget
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hΔ : 0 < Δ) (hΔ₄ : Δ ≤ 4)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    let repair := κ + 2 * n * ε
    let boundaryError := eη + 2 * r * εb + δ + repair
    2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
        2 * (1 / 16224) ≤ 1 / 12 := by
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * r * εb + δ + repair
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hcr : 2 * (Δ / 169) ^ 2 ≤ Δ / 169 := by
    nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ₄), hΔ]
  have hbase : 2 * (6 * (Δ / 169) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)))) ≤ 14 * (Δ / 169) := by
    have heq : 2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L))) =
        2 * (Δ / 169) ^ 2 := by field_simp [hL0]
    rw [heq]
    linarith only [hcr]
  have herr := fullyApproxSDP_errors_with_trace_energy_slack_fit_rationalization_margin
    hL hκ hε hεb hδ heη heK
  have htotal : 2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) ≤
      14 * (Δ / 169) + Δ / 2704 := by
    calc
      2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) =
          2 * (6 * (Δ / 169) +
            2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)))) +
          2 * ((4 * L * repair + eK) + 2 * L * boundaryError) := by ring
      _ ≤ 14 * (Δ / 169) + Δ / 2704 := add_le_add hbase (by
        simpa only [repair, boundaryError, add_assoc] using herr)
  have hscaled := div_le_div_of_nonneg_right htotal hΔ.le
  have hleft : (2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError))) / Δ ≤
      (14 * (Δ / 169) + Δ / 2704) / Δ := by
    exact hscaled
  have hright : (14 * (Δ / 169) + Δ / 2704) / Δ +
      2 * (1 / 16224) = 1 / 12 := by
    field_simp [ne_of_gt hΔ]
    ring
  calc
    2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
        2 * (1 / 16224) ≤
        (14 * (Δ / 169) + Δ / 2704) / Δ + 2 * (1 / 16224) :=
      add_le_add_left hleft _
    _ = 1 / 12 := hright

/-- Exact feasible compressed data, bounded fixed matrices, and positive rationalization
meshes determine an executable rational search whose returned code produces the physical
LVV viable vector.  The objective and boundary thresholds are chosen canonically, and
the conclusion retains the selected rational codes, their height and approximation
bounds, the returned certificate, exact search equation, decoded exact-data feasibility
certificate, the comparison between actual and canonical operand lengths, and the
resulting comparison between actual and canonical schoolbook costs, together with the
direct explicit bit-cost bound and canonical compressed-input bit-size bound for the
selected codes. -/
theorem ChainHamiltonian.exists_viable_vector_of_canonical_rational_search
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    let r := Fintype.card (CutSite L q k × Fin m)
    let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let inputBitSizeBound := compressedSDPInputBitSizeBound
      (Fintype.card (CutLeft L q k)) n r
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
    let bitLength := rationalCertificateOperandBitLength
      (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
      ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    let costBound := uniformCertificateSearchCardBound (CutSite L q k × Fin m)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
      ((n ^ 2 + 3 * r ^ 2 + 3) +
        (2 * n ^ 3 + 2 * r ^ 3 +
          (Fintype.card (CutLeft L q k) * r) * n ^ 2 +
            (Fintype.card (CutLeft L q k) * r) ^ 2 * n)) *
        rationalSchoolbookOperationCost bitLength
    uniformCertificateSearchSchoolbookBitCost
        (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
      costBound ∧
    ∃ QZ : RationalRectMatrixCode
        ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode
            (CutSite L q k × Fin m) (CutSite L q k × Fin m),
          let actualBitLength := rationalCertificateOperandBitLength
            (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
            (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
            (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb)
            ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          ∃ c : RationalCertificateCode (CutSite L q k × Fin m) n,
            actualBitLength ≤ bitLength ∧
            uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) actualBitLength ≤
              uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ∧
            uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) actualBitLength ≤
              costBound ∧
            compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q k)) n r
                (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb) ≤
              inputBitSizeBound ∧
            rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
                rationalCompressedSDPApproximationCodeHeight
                  RK RX θZ θK θX ε εb ∧
            (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
            (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
            (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
            searchRationalCertificateCodeGridOfTolerances η κ ε εb ρ
              QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c ∧
            IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
              (((η + ρ : ℚ) : ℝ))
              ((Et : ℝ) + (n : ℝ) ^ 2 *
                approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
                  (((ε + ρ : ℚ) : ℝ)) * θK)
              (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
              (((εb + ρ : ℚ) : ℝ))
              (((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
                (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 *
                  θZ * approxSDPDensityEntryBound n
                    (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)))
              c.1.decode c.2.1.decode c.2.2.1.decode ∧
            ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
              ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
              (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
              1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, hheight, hZclose, hKclose, hXclose, hfind, hcost⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hbudget := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt
      (2 * rationalUniformCertificateRoundingMesh n ρ)
      (2 * rationalUniformCertificateRoundingMesh r ρ)
      (2 * rationalUniformCertificateRoundingMesh r ρ) hfind Z K X hZ hθZ.le
      hZclose (by simpa only [K] using hKclose) hXclose
  have hbitLength := rationalCertificateOperandBitLength_mono_height
    (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
    (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
    ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hheight
  have hactualCost := uniformCertificateSearchSchoolbookBitCost_mono_operand
    (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
    (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) hbitLength
  have hactualBound := hactualCost.trans hcost
  have hinputSize := compressedSDPInputBitSizeBound_mono_height
    (Fintype.card (CutLeft L q k)) n r hheight
  refine ⟨?_, QZ, QK, QX, c, ?_, ?_, ?_, ?_, hheight, hZclose, ?_, hXclose,
    ?_, ?_, ?_⟩
  · simpa only [r, K, Et, Dt] using hcost
  · simpa only [r, K, Et, Dt] using hbitLength
  · simpa only [r, K, Et, Dt] using hactualCost
  · simpa only [r, K, Et, Dt] using hactualBound
  · simpa only [r] using hinputSize
  · simpa only [K] using hKclose
  · simpa only [r, K, Et, Dt] using hfind
  · simpa only [r, K, Et, Dt] using hexact
  apply h.exists_viable_vector_of_rational_search_result hL hq hΔ HL B hsplit
    hHL hBS hBn hgs W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
  simpa only [r, K, Et, Dt] using hbudget

/-- The canonical executable rational search directly returns compact rational
one-twelfth-viable MPS data when the retained finite family already has rational MPS
representations.  The canonical numerical thresholds leave rationalization share
one over 16224.  This is the rational-output form of LVV13, algo53.tex,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_canonical_rational_search
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 16224 : ℝ) / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m coeff)) := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, -, hZclose, hKclose, hXclose, hfind, -⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hleading := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hΔ₄ : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hrational := canonical_search_rationalization_overlap_budget hL hΔ hΔ₄
    hκfit hεfit hεbfit hδfit' heηfit heKfit'
  apply h.exists_rationalViableMPSData_of_rational_search_result hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
    (by simpa only [r, K, Et, Dt] using hleading)
    (by norm_num : (0 : ℝ) < 1 / 16224) (by norm_num : (1 : ℝ) / 16224 < 1)
  convert hrational using 1
  simp only [r, K, Et, Dt]
  ring_nf

/-- The canonical executable rational search transports the compact coordinate-rational
invariant from one LVV cut to the next, with the canonical rationalization share
`1 / 16224`.  This is the successive-iteration form of LVV13, `algo53.tex`,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_canonical_rational_search
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
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 16224 : ℝ) / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12)
          (spanColumnFamily S m coeff)) := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, -, hZclose, hKclose, hXclose, hfind, -⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hleading := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hΔ₄ : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hrational := canonical_search_rationalization_overlap_budget hL hΔ hΔ₄
    hκfit hεfit hεbfit hδfit' heηfit heKfit'
  apply h.exists_rationalCoordinateData_of_rational_search_result hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
    (by simpa only [r, K, Et, Dt] using hleading)
    (by norm_num : (0 : ℝ) < 1 / 16224) (by norm_num : (1 : ℝ) / 16224 < 1)
  convert hrational using 1
  simp only [r, K, Et, Dt]
  ring_nf


/-- A certificate checked entirely against rational approximations of the coordinate
map, compressed objective, and boundary center transfers to the exact physical data and
produces the LVV viable vector.  The hypotheses use the canonical fixed-data meshes and
the explicit coordinate-map trace allowance. -/
theorem ChainHamiltonian.exists_viable_vector_of_rational_fixed_data_sdp_certificate
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X QX : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z QZ : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    (QK : Matrix (Fin n) (Fin n) ℂ)
    {κ ε εb δ θZ θK θX : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy QZ QK QX
      (((Δ / 169) ^ 2) / (2 * L))
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) κ ε εb δ A P N)
    (hZclose : ∀ i j, ‖(Z - QZ) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) - QK)
        i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX) i j‖ ≤ θX)
    (hθZ : 0 ≤ θZ)
    (hκbound : κ ≤ Δ / (129792 * L))
    (hεbound : 2 * n * ε ≤ Δ / (129792 * L))
    (hεbbound : 2 * Fintype.card (CutSite L q k × Fin m) * εb ≤
      Δ / (129792 * L))
    (hδbound : δ ≤ Δ / (129792 * L))
    (hθKbound : θK ≤ rationalObjectiveApproximationTarget n
      (approxSDPDensityEntryBound n κ ε) Δ)
    (hθXbound : θX ≤ rationalBoundaryCenterApproximationTarget L
      (Fintype.card (CutSite L q k × Fin m)) Δ)
    (hθZbound : (Fintype.card (CutSite L q k × Fin m) : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n κ ε * (2 + θZ)) ≤ Δ / (64896 * L)) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let C := approxSDPDensityEntryBound n κ ε
  let eK := (n : ℝ) ^ 2 * C * θK
  let eX := (Fintype.card (CutSite L q k × Fin m) : ℝ) ^ 2 * θX
  let ω := (Fintype.card (CutSite L q k × Fin m) : ℝ) ^ 2 *
    (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C *
      (2 + θZ))
  have hfixed := hcert.of_fixed_data_approximation hKclose hXclose
  have hexact := hfixed.of_coordinate_approximation hZ hθZ hZclose
  have hbudget : 2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((((2 * Fintype.card (CutSite L q k × Fin m) * εb + δ) + eX) + ω) +
        (κ + 2 * n * ε))) ≤ Δ / 2028 := by
    have hC : 0 ≤ approxSDPDensityEntryBound n κ ε := by
      unfold approxSDPDensityEntryBound
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg n) (gramCertificateBound_pos _).le) hcert.hε
    apply fullyApproxSDP_errors_fit_lvv_margin_of_fixed_data_meshes hL hΔ.le
      hC hκbound hεbound hεbbound hδbound
        hθKbound hθXbound
    simpa only [ω, C] using hθZbound
  apply h.exists_viable_vector_of_approx_sdp_error_budget hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ hexact
  simpa only [K, C, eK, eX, ω, add_assoc] using hbudget

/-- A priori support-size tolerances suffice for the fully approximate compressed SDP.
The density-cone tolerance is chosen using `|S| m`, and the two boundary-cone tolerances
using `q m`; hence these precisions can be fixed before the support coordinates `Z` and
their realized order `n` are constructed. -/
theorem ChainHamiltonian.exists_viable_vector_of_uniformly_approx_sdp_certificate
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) (S : Finset (LeftBlockVector L q k))
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (hn : n ≤ S.card * m)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hP : P.IsHermitian) (hN : N.IsHermitian)
    {κ ε εb δ : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hεb : 0 ≤ εb) (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ ((Δ / 169) ^ 2) / (2 * L))
    (henergy : (A * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hκbound : κ ≤ Δ / (64896 * L))
    (hεbound : ε ≤ Δ / ((129792 : ℝ) * L * (S.card * m)))
    (hεbbound : εb ≤ Δ / ((129792 : ℝ) * L * (q * m)))
    (hδbound : δ ≤ Δ / (64896 * L)) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q k)) ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  have hnpos : 0 < n := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_pos_iff.mpr (show Nonempty (Fin n) from inferInstance))
  let r := Fintype.card (CutSite L q k × Fin m)
  have hrpos : 0 < r := Fintype.card_pos_iff.mpr inferInstance
  have hr : r ≤ q * m := by
    simpa only [r, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) (by omega : 1 ≤ q))
        (Nat.le_refl m)
  obtain ⟨hεrealized, hεbrealized⟩ := fullyApproxSDP_scaled_errors_of_order_bounds
    hL hnpos hrpos hn hr hε hεb
      (by simpa only [Nat.cast_mul] using hεbound)
      (by simpa only [Nat.cast_mul] using hεbbound)
  apply h.exists_viable_vector_of_all_spectral_approx_sdp_certificate hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ A hA P N hP hN
      htrace hε hmin hεb hPmin hNmin hresidual htraces henergy hκbound
  · exact hεrealized
  · simpa only [r] using hεbrealized
  · exact hδbound

/-- A fully approximate feasible compressed SDP certificate, expressed by the unified
feasibility predicate and the a priori support-size tolerances, yields the physical LVV
viable vector. -/
theorem ChainHamiltonian.exists_viable_vector_of_uniform_approx_sdp_feasible
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) (S : Finset (LeftBlockVector L q k))
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (hn : n ≤ S.card * m)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    {κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L))
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) κ ε εb δ A P N)
    (hκbound : κ ≤ Δ / (64896 * L))
    (hεbound : ε ≤ Δ / ((129792 : ℝ) * L * (S.card * m)))
    (hεbbound : εb ≤ Δ / ((129792 : ℝ) * L * (q * m)))
    (hδbound : δ ≤ Δ / (64896 * L)) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q k)) ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  rcases hcert with ⟨hA, hP, hN, htrace, hε, hmin, hεb, hPmin, hNmin,
    hresidual, htraces, henergy⟩
  exact h.exists_viable_vector_of_uniformly_approx_sdp_certificate hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S hn W hW x hwx hwE X hX Z hZ hZZ
      A hA P N hP hN htrace hε hmin hεb hPmin hNmin hresidual htraces henergy
        hκbound hεbound hεbbound hδbound

/-- A normalized supported glued vector determines positive-dimensional compressed
coordinates containing an exact zero-error SDP certificate and in which every uniformly
accurate certificate is physically sound.  Thus the numerical solver need only return
matrices in the nonempty coordinate problem constructed here; it does not need to supply
or certify the support isometry itself. -/
theorem ChainHamiltonian.exists_boundary_coordinates_with_uniform_approx_sdp_soundness
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) (S : Finset (LeftBlockVector L q k))
    {m : ℕ} [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
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
    ∃ (n : ℕ) (_ : Nonempty (Fin n))
      (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (A₀ : Matrix (Fin n) (Fin n) ℂ)
      (P₀ N₀ : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧
      Z * Zᴴ = reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) ∧
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
        (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
        (((Δ / 169) ^ 2) / (2 * L))
        ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) 0 0 0 0 A₀ P₀ N₀ ∧
      ∀ {κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
        {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ},
        IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
          (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
          (((Δ / 169) ^ 2) / (2 * L))
          ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
            (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) κ ε εb δ A P N →
        κ ≤ Δ / (64896 * L) →
        ε ≤ Δ / ((129792 : ℝ) * L * (S.card * m)) →
        εb ≤ Δ / ((129792 : ℝ) * L * (q * m)) →
        δ ≤ Δ / (64896 * L) →
        ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
          ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule (S : Set (LeftBlockVector L q k)) ∧
          (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
          1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  obtain ⟨n, Z, A₀, hnpos, hn, hZ, hZZ, hA₀, hA₀trace, hρexpand⟩ :=
    exists_boundarySupportedVectorDensityCompression S m x hxnorm hxP
  have hnonempty : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_fin] using hnpos)
  let _ : Nonempty (Fin n) := hnonempty
  let ρ := vecMulVec x (star x)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let E := (ρ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
      ((Δ / 169) ^ 2) / (2 * L) := by
    rw [← isometricDensityExpansion_boundary_distance Z ρ A₀ (by
      simpa only [ρ] using hρexpand) X]
    simpa only [ρ] using hX
  have henergy : (A₀ * K).trace.re ≤ E := by
    have ht := isometricDensityExpansion_trace_and_energy Z hZ ρ A₀ (by
      simpa only [ρ] using hρexpand)
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    exact le_of_eq (by simpa only [K, E] using congrArg Complex.re ht.2.symm)
  obtain ⟨P₀, N₀, hzero⟩ :=
    exists_allSpectralApproxCompressedBoundarySDPFeasibleAtEnergy_zero
      Z K X hXHermitian hA₀ hA₀trace hboundary henergy
  refine ⟨n, hnonempty, Z, A₀, P₀, N₀, hnpos, hn, hZ, hZZ,
    by simpa only [K, E, ρ] using hzero, ?_⟩
  intro κ ε εb δ A P N hcert hκbound hεbound hεbbound hδbound
  exact h.exists_viable_vector_of_uniform_approx_sdp_feasible hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S hn W hW x hwx hwE X hX Z hZ hZZ
      hcert hκbound hεbound hεbbound hδbound

/-- A normalized vector in the retained support also supplies an exact feasible point
in its compressed boundary coordinates.  Thus the coordinate system used by the
finite-precision soundness theorem is not merely sound: its zero-error feasible set is
nonempty. -/
theorem exists_boundary_coordinates_with_zero_error_sdp_certificate
    {L q k : ℕ} [NeZero q] (HL : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (S : Finset (LeftBlockVector L q k)) {m : ℕ}
    [Nonempty (CutSite L q k × Fin m)]
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    (hxnorm : ‖WithLp.toLp 2 x‖ = 1)
    (hxP : (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ x = x)
    {X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hXHermitian : X.IsHermitian) {η : ℝ}
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤ η) :
    ∃ (n : ℕ) (_ : Nonempty (Fin n))
      (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
      (A : Matrix (Fin n) (Fin n) ℂ)
      (P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ),
      0 < n ∧ n ≤ S.card * m ∧ Zᴴ * Z = 1 ∧
      Z * Zᴴ = reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) ∧
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
        (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X η
        ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re) 0 0 0 0 A P N := by
  classical
  obtain ⟨n, Z, A, hnpos, hn, hZ, hZZ, hA, hAtrace, hρexpand⟩ :=
    exists_boundarySupportedVectorDensityCompression S m x hxnorm hxP
  have hnonempty : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by
    simpa only [Fintype.card_fin] using hnpos)
  let _ : Nonempty (Fin n) := hnonempty
  let ρ := vecMulVec x (star x)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let E := (ρ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re
  have hboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η := by
    rw [← isometricDensityExpansion_boundary_distance Z ρ A (by
      simpa only [ρ] using hρexpand) X]
    simpa only [ρ] using hX
  have henergy : (A * K).trace.re ≤ E := by
    have ht := isometricDensityExpansion_trace_and_energy Z hZ ρ A (by
      simpa only [ρ] using hρexpand)
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    exact le_of_eq (by simpa only [K, E] using congrArg Complex.re ht.2.symm)
  obtain ⟨P, N, hcert⟩ :=
    exists_allSpectralApproxCompressedBoundarySDPFeasibleAtEnergy_zero
      Z K X hXHermitian hA hAtrace hboundary henergy
  exact ⟨n, hnonempty, Z, A, P, N, hnpos, hn, hZ, hZZ,
    by simpa only [K, E, ρ] using hcert⟩

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
    have hop : ‖h.operator‖ ≤ 2 * L := by
      simpa only [mul_one] using h.norm_operator_le_of_range_one
    have hHLn : ‖HL‖ ≤ 4 * L := by
      have heq : HL = h.operator - B := by rw [hsplit]; abel
      rw [heq]
      exact (norm_sub_le _ _).trans (by linarith only [hop, hBn])
    have hHleft : ‖Hleft‖ ≤ 4 * L :=
      (l2_opNorm_kronecker_one_le (leftCutOperator k HL)).trans
        ((norm_leftCutOperator_eq hHL).le.trans hHLn)
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


/-- **The size-trimming selection.** For every bond dimension `m ≤ D`, take the chosen
trace-norm net of radius `c / (2L)` on the boundary space of the bond, and at each of its
feasible points the left columns of the leading vector of a chosen density of least left
energy supported on `span S`. The selection depends only on the Hamiltonian, the gap
parameter and the family `S`; no ground pair enters. LVV13, `algo53.tex`, equation
`eq:conv`, lines 472–478, and Claim `c:2`, lines 520–527, using all actual bond dimensions
up to the uniform cut bound. -/
noncomputable def ChainHamiltonian.sizeTrimmingSelection {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    Finset (LeftBlockVector L q k) :=
  haveI : NeZero q := ⟨by omega⟩
  let c : ℝ := (Δ / 169) ^ 2
  let D := constantCutBond q 1 1 Δ c
  open Classical in Finset.univ.biUnion fun m : Fin (D + 1) ↦
    boundaryMinimizerFamily (S : Set (LeftBlockVector L q k)) (leftCutOperator k (h.cutLeftPart k))
      m.val (c / (2 * L)) (rectangularTraceNormNet (CutSite L q k × Fin m.val) (c / (2 * L)))

/-- The selection lies in the span of the input family.
LVV13, `algo53.tex`, Claim `c:2`, line 526. -/
theorem ChainHamiltonian.sizeTrimmingSelection_subset_span {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hq : 2 ≤ q) (Δ : ℝ) (S : Finset (LeftBlockVector L q k)) :
    (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) ⊆
      Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
  classical
  intro v hv
  simp only [ChainHamiltonian.sizeTrimmingSelection, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at hv
  obtain ⟨m, hm⟩ := hv
  exact boundaryMinimizerFamily_subset_span _ _ _ _ _ hm

/-- The selection has at most `(D + 1) D K` members, with `K` the net bound.
LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelection_le {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let K : ℕ := (2 * ⌈((q * D : ℕ) : ℝ) ^ 2 / (c / (2 * L))⌉₊ + 1) ^
      (2 * (q * D) ^ 2)
    (h.sizeTrimmingSelection hq Δ S).card ≤ (D + 1) * D * K := by
  classical
  intro c D K
  let : NeZero q := ⟨by omega⟩
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  have hm (m : Fin (D + 1)) : (boundaryMinimizerFamily (S : Set (LeftBlockVector L q k))
      (leftCutOperator k (h.cutLeftPart k)) m.val (c / (2 * L))
      (rectangularTraceNormNet (CutSite L q k × Fin m.val) (c / (2 * L)))).card ≤ D * K :=
    (card_boundaryMinimizerFamily_le _ _ _ _ _).trans
      (Nat.mul_le_mul (Nat.le_of_lt_succ m.isLt)
        (card_boundary_rectangularTraceNormNet_le (by omega) hη (Nat.le_of_lt_succ m.isLt)))
  simpa only [ChainHamiltonian.sizeTrimmingSelection, Finset.card_univ, Fintype.card_fin,
    Nat.mul_assoc] using Finset.card_biUnion_le_card_mul Finset.univ _ (D * K) fun m _ ↦ hm m

/-- The selection has explicit polynomial cardinality in the chain length, with coefficient
and degree independent of that length. LVV13, `algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.card_sizeTrimmingSelection_le_polynomial {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    let p := 2 * (q * D) ^ 2
    let A := ⌈2 * ((q * D : ℕ) : ℝ) ^ 2 / c⌉₊
    let C := (D + 1) * D * (2 * A + 1) ^ p
    (h.sizeTrimmingSelection hq Δ S).card ≤ C * L ^ p := by
  intro c D p A C
  have hnet := boundaryNet_card_bound_le_polynomial (q := q) (D := D) (c := c)
    (by omega : 1 ≤ L) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
  simpa only [C, Nat.mul_assoc] using
    (h.card_sizeTrimmingSelection_le hL hq hΔ S).trans (Nat.mul_le_mul_left ((D + 1) * D) hnet)

/-- **Size trimming is chosen before the ground state.** Whenever the input family is
`c / L`-viable for a ground pair with gap at least `Δ`, the selection is `1 / 12`-viable
for it, with a witness given by an isometry `W` on a bond of dimension `m ≤ D` and a unit
vector `u` all of whose columns belong to the selection. Library-bond version of LVV13,
`algo53.tex`, Claim `c:2`, lines 520–527. -/
theorem ChainHamiltonian.isViable_sizeTrimmingSelection {L q k : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef)
    (hL : 0 < L) (hq : 2 ≤ q) {Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (LeftBlockVector L q k)) (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q))
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (hviable : IsViable Γ ((Δ / 169) ^ 2 / L) (S : Set (LeftBlockVector L q k))) :
    let c : ℝ := (Δ / 169) ^ 2
    let D := constantCutBond q 1 1 Δ c
    IsViable Γ (1 / 12) (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) ∧
      ∃ (m : ℕ) (W : Matrix (CutRight L q k) (Fin m) ℂ)
        (u : EuclideanSpace ℂ
          (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)),
        Wᴴ * W = 1 ∧ m ≤ D ∧ ‖u‖ = 1 ∧
        (∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ h.sizeTrimmingSelection hq Δ S) ∧
        1 - 1 / 12 ≤ ‖⟪Γ, WithLp.toLp 2 (fun z ↦ rightApply W u
          (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z))⟫_ℂ‖ := by
  classical
  intro c D
  let : NeZero q := ⟨by omega⟩
  let P := reindex
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
    (spanProjection (S : Set (LeftBlockVector L q k)))
  have hc : 0 < c := sq_pos_of_pos (div_pos hΔ (by norm_num))
  have hη : 0 < c / (2 * L) :=
    div_pos hc (mul_pos (by norm_num) (by exact_mod_cast hL))
  let HL := leftCutOperator k (h.cutLeftPart k)
  let N := fun m : ℕ ↦ rectangularTraceNormNet (CutSite L q k × Fin m) (c / (2 * L))
  let T := fun m : ℕ ↦ boundaryMinimizerFamily (S : Set (LeftBlockVector L q k)) HL m
    (c / (2 * L)) (N m)
  have hTtotal : h.sizeTrimmingSelection hq Δ S = Finset.univ.biUnion fun m : Fin (D + 1) ↦
      T m.val := rfl
  obtain ⟨_, m, W, x, -, -, -, -, hW, hmD, -, hxnorm, hxP, huniform⟩ :=
    h.exists_uniform_leading_bounds_of_isViable hpos hL hq hΔ
      (h.cutLeftPart k) (h.cutBoundaryPart k) (h.cutLeftPart_add_cutBoundaryPart k)
      (h.cutLeftPart_isSupportedOn k) (h.cutBoundaryPart_isSupportedOn k)
      (h.norm_cutBoundaryPart_le k) hgs hviable
  let ρx := vecMulVec x (star x)
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star x
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp (WithLp.toLp 2 x))
      (star (WithLp.ofLp (WithLp.toLp 2 x)))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  have hρxP : (P ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * ρx = ρx := by
    dsimp only [ρx]
    rw [mul_vecMulVec, hxP]
  let e := Equiv.prodAssoc (CutLeft L q k) (CutSite L q k) (Fin m)
  have hYp : (partialTraceFirst ρx).PosSemidef :=
    (hρxp.submatrix e.symm).partialTraceLeft
  have hYt : (partialTraceFirst ρx).trace = 1 := by
    rw [partialTraceFirst, trace_partialTraceLeft]
    exact (e.symm.sum_comp (fun i ↦ ρx i i)).trans hρxt
  have hYnorm : rectangularTraceNorm (partialTraceFirst ρx) = 1 := by
    rw [rectangularTraceNorm_eq_re_trace_abs, CFC.abs_of_nonneg _ hYp.nonneg, hYt]
    norm_num
  let i : Fin (D + 1) := ⟨m, Nat.lt_succ_of_le hmD⟩
  obtain ⟨X, hXN, hX⟩ := exists_mem_rectangularTraceNormNet hη (partialTraceFirst ρx) hYnorm.le
  have hXfeasible : (feasibleBoundaryDensities (S : Set (LeftBlockVector L q k)) m
      (c / (2 * L)) X).Nonempty := ⟨ρx, hρxp, hρxt, hρxP, hX⟩
  have hXmem : X ∈ feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L))
      (N m) := mem_feasibleBoundaryPoints.mpr ⟨hXN, hXfeasible⟩
  obtain ⟨hσ, htr, hσP, hσX, hmin, hu, -, heig, -, hmax⟩ :=
    boundaryMinimizer_spec (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) hXfeasible
  set σ := boundaryMinimizer (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  set u := boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  set μ := boundaryLeadingValue (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) X
  obtain ⟨_, _, hvnorm, _, _, hvΓ⟩ := huniform X hX σ hσ htr hσP hσX hmin u μ hu heig hmax
  have hsubset : (T m : Set (LeftBlockVector L q k)) ⊆
      (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) := by
    rw [hTtotal]
    exact fun z hz ↦ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩
  have hviable' : IsViable Γ (1 / 12)
      (h.sizeTrimmingSelection hq Δ S : Set (LeftBlockVector L q k)) := by
    refine ⟨_, hvnorm, ?_, ?_⟩
    · rw [norm_inner_symm]
      exact hvΓ
    · rw [gluingLeftCoordinates_rightApply W u]
      have hvT := rightApply_mem_leftSupportSubmodule_leftColumns
        (feasibleBoundaryPoints (S : Set (LeftBlockVector L q k)) m (c / (2 * L)) (N m))
        (fun z ↦ gluingLeftCoordinates L q k m
          (boundaryLeadingVector (S : Set (LeftBlockVector L q k)) HL m (c / (2 * L)) z))
        hXmem W
      exact mem_leftSupportSubmodule.mpr fun β ↦
        Submodule.span_mono hsubset ((mem_leftSupportSubmodule.mp hvT) β)
  refine ⟨hviable', m, W, gluingLeftCoordinates L q k m u, hW, hmD, ?_, ?_, ?_⟩
  · rw [(gluingLeftCoordinates L q k m).norm_map]
    exact hu
  · intro a
    apply hsubset
    unfold T boundaryMinimizerFamily leftColumns
    exact Finset.mem_image.mpr ⟨(X, a), Finset.mem_product.mpr
      ⟨hXmem, Finset.mem_univ a⟩, rfl⟩
  · rw [← gluingLeftCoordinates_rightApply W u]
    exact hvΓ

end TNLean.MPS.AreaLaw
