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
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.ApproximateCertificates

/-!
# Uniform approximation of compressed boundary programs

Rational approximations of the fixed coordinate, objective and boundary matrices
transfer checked certificates to physical viable vectors. Support coordinates admit
a zero-error certificate whenever the exact boundary problem has a feasible witness.

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

end TNLean.MPS.AreaLaw
