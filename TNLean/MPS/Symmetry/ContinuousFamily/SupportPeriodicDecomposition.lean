/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.IsometricBondCompression
import TNLean.MPS.Tensor.DirectSum.InvariantSubspaceDecomp
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import TNLean.MPS.Tensor.Defs
import QICLean.Kraus.Transfer
import QICLean.Channel.KoashiImoto.MeanErgodicProjection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import TNLean.MPS.Symmetry.ContinuousFamily.StationarySupportedDensityPhaseInvariance
import TNLean.MPS.CanonicalForm.Definitions
import QICLean.Channel.Peripheral.Spectrum.SpectralRadius
import QICLean.Channel.KrausMap.KrausCornerCompression
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Algebra.Hermitian.OrthogonalProjection
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TNLean.MPS.Transfer.Spectrum.MPVOverlapTrace
import TNLean.MPS.CanonicalForm.FixedPointApproximation.SecondOrderOverlap
import TNLean.MPS.Transfer.Spectrum.AsymptoticDecomposition
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import TNLean.MPS.Tensor.Gauge.TPGauge
import QICLean.Channel.Irreducible.KrausGauge

/-!
# Periodic decomposition along a one-sided invariant support

An isometric support compression of a triangular tensor contributes one
summand to every positive-length periodic coefficient. The other summand
is the complementary diagonal corner. Off-diagonal letters make no trace
contribution. Neither summand is required to have the same periodic ray
as the ambient tensor.

Source context: arXiv:quant-ph/0608197, proof of the TI canonical-form theorem,
Th:TIcanonical, lines 785–815, and arXiv:1010.3732, Appendix C, lines 2653–2717.

It also contains the following results.

* `MPSTensor.finrank_adjointFixedSpace_eq_transferFixedSpace`: equality of transfer and adjoint
  fixed-space dimensions.
* `MPSTensor.normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one`,
  `MPSTensor.exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap`: identification of a
  stationary support from a limiting overlap.
* `MPSTensor.prepare_stationary_support_compression`,
  `MPSTensor.isNormalTensor_of_unital_stationary_support_compression`: preparation on the full
  stationary support.
* `MPSTensor.spectrum_transferMap_transientCorner_norm_le`,
  `MPSTensor.norm_mpvState_transientCorner_tendsto_zero_of_transfer_spectrum`: decay of a
  complementary diagonal tensor corner.
* `MPSTensor.exists_dim_eq_gaugePhase_of_vanishing_periodic_remainder`: identification after removal
  of a transient periodic component.
-/

section SupportPeriodicDecomposition

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace MPSTensor

private theorem evalWord_add_of_cross_products_zero
    {d k : ℕ} (L R : MPSTensor d k)
    (hLR : ∀ i j, L i * R j = 0) (hRL : ∀ i j, R i * L j = 0)
    (w : List (Fin d)) (hw : w ≠ []) :
    Kraus.evalWord (fun i => L i + R i) w = Kraus.evalWord L w + Kraus.evalWord R w := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    cases w with
    | nil => simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
    | cons j w =>
      rw [Kraus.evalWord_cons, ih (by simp)]
      simp only [Kraus.evalWord_cons, Matrix.add_mul, Matrix.mul_add,
        ← Matrix.mul_assoc, hLR, hRL, zero_add, add_zero]

/-- A triangular support compression splits every positive-length periodic
coefficient into the supported tensor and the complementary diagonal corner.
Source context: arXiv:quant-ph/0608197, Th:TIcanonical, lines 785–815. -/
theorem mpv_eq_compression_add_transient_of_upperZero
    {d k D N : ℕ} (B : MPSTensor d k) (C : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hC : ∀ i, C i = Kᴴ * B i * K)
    (hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0)
    (hN : 0 < N) (x : Fin N → Fin d) :
    mpv B x = mpv C x + mpv (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) x := by
  let P := K * Kᴴ
  let Q := 1 - P
  let L : MPSTensor d k := fun i => P * B i * P
  let R : MPSTensor d k := fun i => Q * B i * Q
  have hP : IsOrthogonalProjection P := ⟨Matrix.isHermitian_mul_conjTranspose_self K, by
    simp only [P, Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul]⟩
  have hInt : ∀ i, L i * K = K * C i := by
    intro i
    simp only [L, P, hC, Matrix.mul_assoc, show Kᴴ * K = 1 from hK, Matrix.mul_one]
  have hRow : ∀ i, K * Kᴴ * L i = L i := by
    intro i
    change P * (P * B i * P) = P * B i * P
    calc
      P * (P * B i * P) = (P * P) * B i * P := by simp only [Matrix.mul_assoc]
      _ = P * B i * P := by rw [hP.2]
  have hCoefficientsL : mpv L x = mpv C x :=
    mpv_eq_of_supported_isometric_bond_intertwiner L C K hK hInt hRow hN x
  have hPQ : P * Q = 0 := IsIdempotentElem.mul_one_sub_self hP.2
  have hQP : Q * P = 0 := IsIdempotentElem.one_sub_mul_self hP.2
  have hLR : ∀ i j, L i * R j = 0 := by
    intro i j
    calc
      L i * R j = P * B i * (P * Q) * B j * Q := by simp only [L, R, Matrix.mul_assoc]
      _ = 0 := by rw [hPQ]; simp only [Matrix.mul_zero, Matrix.zero_mul]
  have hRL : ∀ i j, R i * L j = 0 := by
    intro i j
    calc
      R i * L j = Q * B i * (Q * P) * B j * P := by simp only [L, R, Matrix.mul_assoc]
      _ = 0 := by rw [hQP]; simp only [Matrix.mul_zero, Matrix.zero_mul]
  have hQ : IsOrthogonalProjection Q :=
    hP.isStarProjection.one_sub.isOrthogonalProjection
  have hDiag : mpv B x = mpv (fun i => R i + L i) x := by
    have h := sameMPV_diagPart_of_lowerZero B Q hQ
      (fun i => by simpa only [Q, P, sub_sub_cancel] using hUpper i) N x
    change mpv B x = mpv (fun i => Q * B i * Q + (1 - Q) * B i * (1 - Q)) x at h
    simpa only [Q, sub_sub_cancel, L, R] using h
  have hw : List.ofFn x ≠ [] := mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hN)
  rw [hDiag, ← hCoefficientsL]
  change (Kraus.evalWord (fun i => R i + L i) (List.ofFn x)).trace =
    (Kraus.evalWord L (List.ofFn x)).trace + (Kraus.evalWord R (List.ofFn x)).trace
  rw [evalWord_add_of_cross_products_zero R L hRL hLR _ hw, Matrix.trace_add, add_comm]

end MPSTensor

end SupportPeriodicDecomposition

section AdjointFixedSpaceDimension

/-!
## Equality of transfer and adjoint fixed-space dimensions

The transfer map and its trace adjoint have fixed spaces of equal dimension.
In matrix-unit coordinates the trace adjoint is a transpose, so its rank and
nullity agree with those of the original map. No positivity, unitality or
spectral simplicity is required for this finite-dimensional identity.

This identity is used in the stationary-support argument of arXiv:1010.3732,
Appendix C, lines 2653–2717. It does not derive a transfer spectral bound from
a physical Hamiltonian gap.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

private theorem finrank_ker_traceAdjointMap_eq
    {n : Type*} [Fintype n]
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Module.finrank ℂ (Matrix.traceAdjointMap E).ker = Module.finrank ℂ E.ker := by
  classical
  let b := Matrix.stdBasis ℂ n n
  let bT := b.reindex (Equiv.prodComm n n)
  have hRange : Module.finrank ℂ (Matrix.traceAdjointMap E).range =
      Module.finrank ℂ E.range := by
    calc
      _ = (LinearMap.toMatrix bT bT (Matrix.traceAdjointMap E)).rank := by
        rw [Matrix.rank_eq_finrank_range_toLin _ bT bT, Matrix.toLin_toMatrix]
      _ = (LinearMap.toMatrix b b E).rank := by
        rw [Matrix.traceAdjointMap_toMatrix_transpose E, Matrix.rank_transpose]
      _ = Module.finrank ℂ E.range := by
        rw [Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix]
  have hAdj := LinearMap.finrank_range_add_finrank_ker (Matrix.traceAdjointMap E)
  have hOrig := LinearMap.finrank_range_add_finrank_ker E
  rw [hRange] at hAdj
  exact Nat.add_left_cancel (hAdj.trans hOrig.symm)

namespace MPSTensor

/-- The adjoint stationary space and the transfer fixed space have equal
complex dimension. This finite-dimensional trace-duality identity requires
no positivity, normalization, irreducibility or nonzero dimension assumption.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem finrank_adjointFixedSpace_eq_transferFixedSpace
    {d D : ℕ} (B : MPSTensor d D) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM B)) =
      Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) := by
  have hId : Matrix.traceAdjointMap
      (LinearMap.id : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) =
        LinearMap.id := by
    ext X i j
    simp only [Matrix.traceAdjointMap_apply_apply, LinearMap.id_apply,
      Matrix.trace_mul_single, MulOpposite.op_one, one_smul]
  have hEq := finrank_ker_traceAdjointMap_eq (LinearMap.id - Kraus.mapLM B)
  rw [Matrix.traceAdjointMap_sub, hId, Kraus.traceAdjointMap_mapLM] at hEq
  rw [Module.End.eigenspace_def, one_smul, Module.End.one_eq_id]
  change Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM B)) =
    Module.finrank ℂ (LinearMap.ker (Kraus.mapLM B - LinearMap.id))
  rw [← neg_sub (LinearMap.id) (Kraus.mapLM B), LinearMap.ker_neg]
  exact hEq

end MPSTensor

end AdjointFixedSpaceDimension

section StationarySupportPreparation

/-!
## Preparation on the full stationary support

A unital tensor with a unique normalized adjoint stationary density restricts
to a unital irreducible tensor on the entire support of that density. The
compressed density is faithful, normalized, and adjoint stationary. Stationarity
supplies the required one-sided letter invariance; no periodic-ray identity is
asserted. A supplied spectral bound below one on all nontrivial ambient
transfer eigenvalues further implies normality of the support compression.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. This module proves
auxiliary preparation and spectral consequences and does not derive stationary support data
from a physical Hamiltonian path.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder

namespace MPSTensor

/-- An isometric compression of a unital tensor is unital when the orthogonal
complement of its range is invariant under every letter. Equivalently, the
range is invariant under every adjoint letter. This finite-dimensional
auxiliary result is used in the support reduction of arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
private theorem isUnital_compression_of_isUnital_of_upperZero
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0) :
    Kraus.IsUnital A := by
  change Kᴴ * K = 1 at hK
  let P := K * Kᴴ
  have hKP : Kᴴ * P = Kᴴ := by
    change Kᴴ * (K * Kᴴ) = Kᴴ
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hPB : ∀ i, P * B i * P = P * B i := fun i =>
    (sub_eq_zero.mp (by simpa only [Matrix.mul_sub, Matrix.mul_one] using hUpper i)).symm
  have hKB : ∀ i, Kᴴ * B i * P = Kᴴ * B i := fun i => by
    simpa only [← Matrix.mul_assoc, hKP] using
      congrArg (fun X => Kᴴ * X) (hPB i)
  have hterm : ∀ i, A i * (A i)ᴴ = Kᴴ * B i * (B i)ᴴ * K := fun i => by
    calc
      _ = (Kᴴ * B i * P) * (B i)ᴴ * K := by
        simp only [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          P, Matrix.mul_assoc]
      _ = Kᴴ * B i * (B i)ᴴ * K := by
        rw [hKB]
  simpa only [Kraus.IsUnital, Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_assoc,
    ← hterm, Matrix.mul_one, hK] using congrArg (fun X => Kᴴ * X * K) hB

/-- The full support compression of a unital tensor with a unique normalized
adjoint stationary density is unital and irreducible. Its compressed density
is faithful, normalized, and adjoint stationary. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717; stationary support invariance
and irreducibility are Wolf, Lemma 6.4 and Theorem 6.3. This is an auxiliary
preparation result; it asserts no equality of finite periodic rays. -/
theorem prepare_stationary_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ) :
    Kraus.IsUnital A ∧ IsIrreducibleMap (Kraus.mapLM A) ∧
      (Kᴴ * σ * K).PosDef ∧ (Kᴴ * σ * K).trace = 1 ∧
      Kraus.adjointMap A (Kᴴ * σ * K) = Kᴴ * σ * K := by
  have hfix' : Kraus.map (fun i => (B i)ᴴ) σ = σ := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using hfix
  have hInv := Kraus.lowerZero_of_posSemidef_fixedPoint
    (fun i => (B i)ᴴ) σ hσ hfix'
  have hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0 := fun i => by
    simpa only [Kraus.stationaryProj, ← hsupport, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.mul_assoc]
      using congrArg Matrix.conjTranspose (hInv.2 i)
  have hUnital := isUnital_compression_of_isUnital_of_upperZero B A K hK hA hB hUpper
  have hD := Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  have hIrr := isIrreducibleMap_of_unital_support_compression
    B A K hK hA hUnital σ hσ hsupport hfix htrace huniq
  obtain ⟨hρfix, hρtrace, _⟩ := stationaryMatrix_compression_unique
    B A K hK hA σ hσ hsupport hfix htrace huniq
  refine ⟨hUnital, hIrr, ?_, hρtrace, hρfix⟩
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hσ.compression_on_support_posDef (V := Kᴴ)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using
        (show Kᴴ * K = 1 from hK))
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hsupport)

/-- Isometric support expansion preserves nonzero adjoint eigenvectors. -/
private theorem hasEigenvalue_adjointMap_compression_lift
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Kraus.adjointMapLM A) μ) :
    Module.End.HasEigenvalue (Kraus.adjointMapLM B) μ := by
  obtain ⟨Z, hZ⟩ := hμ.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := K * Z * Kᴴ) ?_
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · simpa only [Kraus.adjointMapLM_apply, Matrix.mul_smul, Matrix.smul_mul] using
      (adjointMap_compression_lift B A K hK hA σ hσ hsupport hfix Z).trans
        (congrArg (fun X => K * X * Kᴴ) hZ.apply_eq_smul)
  · intro hzero
    apply hZ.2
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul] using
      congrArg (fun X => Kᴴ * X * K) hzero

/-- The transfer spectrum on a stationary support lies in the ambient spectrum. -/
private theorem hasEigenvalue_mapLM_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Kraus.mapLM A) μ) :
    Module.End.HasEigenvalue (Kraus.mapLM B) μ := by
  apply (Matrix.traceAdjointMap_hasEigenvalue_iff (Kraus.mapLM B) μ).mp
  rw [Kraus.traceAdjointMap_mapLM]
  apply hasEigenvalue_adjointMap_compression_lift B A K hK hA σ hσ hsupport hfix μ
  simpa only [Kraus.traceAdjointMap_mapLM] using
    (Matrix.traceAdjointMap_hasEigenvalue_iff (Kraus.mapLM A) μ).mpr hμ

/-- A full stationary support compression is a normal tensor when every
ambient transfer eigenvalue other than one has modulus bounded by a fixed
number below one. The spectral bound is supplied, not inferred from a physical
Hamiltonian gap. Source context: Wolf, Proposition 6.1 and Theorem 6.8;
arXiv:1606.00608, lines 231–235; arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isNormalTensor_of_unital_stationary_support_compression
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hB : Kraus.IsUnital B)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ)
    (q : ℝ) (hq : q < 1)
    (hspec : ∀ μ ∈ spectrum ℂ (Kraus.mapLM B), μ ≠ 1 → ‖μ‖ ≤ q) :
    IsNormalTensor A := by
  obtain ⟨hUnital, hIrr, _, _, _⟩ := prepare_stationary_support_compression
    B A K hK hA hB σ hσ hsupport hfix htrace huniq
  let : NeZero D := ⟨Nat.ne_of_gt
    (Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace)⟩
  have hOne : Kraus.mapLM A 1 = 1 := Kraus.map_one_of_isUnital A hUnital
  refine ⟨Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hIrr,
    (Kraus.isPositiveMap_mapLM A).spectralRadius_eq_one_of_map_one_eq_one hOne, ?_⟩
  change peripheralEigenvalues (Kraus.mapLM A) = {1}
  ext μ
  change (Module.End.HasEigenvalue (Kraus.mapLM A) μ ∧ ‖μ‖ = 1) ↔ μ = 1
  constructor
  · rintro ⟨hμ, hnorm⟩
    by_contra hne
    exact (not_le_of_gt hq) (by
      simpa only [hnorm] using hspec μ (Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (hasEigenvalue_mapLM_support_compression B A K hK hA σ hσ hsupport hfix μ hμ)) hne)
  · rintro rfl
    exact ⟨eigenvalue_one_of_map_one_eq_one hOne, norm_one⟩

end MPSTensor

end StationarySupportPreparation

section TransientCornerSpectrum

/-!
## Decay of a complementary diagonal tensor corner

Let a unital MPS tensor have a one-dimensional transfer fixed space. For a
nonzero orthogonal projection `P` satisfying `P Aᵢ (1 - P) = 0`, every nonzero
transfer eigenvector of the complementary corner is supported on that corner
and lifts to an ambient transfer eigenvector. The eigenvalue one is excluded:
an ambient fixed vector is a scalar identity, which cannot be supported on the
complement of a nonzero projection.

Consequently, a bound below one on the ambient nonunit spectrum implies decay
of the complementary periodic MPS norm. The complementary letters may be
nonzero, and no equality of the recurrent and ambient finite-ring rays is
assumed or concluded.

Source context: Pérez-García, Verstraete, Wolf, and Cirac,
arXiv:quant-ph/0608197, proof of the TI canonical-form theorem,
`Th:TIcanonical`, lines 785–815. The statements below are auxiliary spectral
estimates for the explicit triangular corner used in that trace decomposition.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators Matrix.Norms.Operator

attribute [local instance]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toSeminormedRing

namespace MPSTensor

private theorem map_corner_supported {d D : ℕ} (A : MPSTensor d D)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Q * Kraus.map (fun i => Q * A i * Q) X * Q =
      Kraus.map (fun i => Q * A i * Q) X := by
  classical
  simp only [Kraus.map_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, hQ.1.eq]
  simp only [← Matrix.mul_assoc, hQ.2]
  simp only [Matrix.mul_assoc, hQ.2]

private theorem map_corner_eq_of_supported {d D : ℕ} (A : MPSTensor d D)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (hUpper : ∀ i, (1 - Q) * A i * Q = 0)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : Q * X * Q = X) :
    Kraus.map (fun i => Q * A i * Q) X = Kraus.map A X := by
  classical
  have hAQ : ∀ i, Q * A i * Q = A i * Q := by
    intro i
    have h := hUpper i
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h.symm
  simp only [Kraus.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hAQ, Matrix.conjTranspose_mul, hQ.1.eq]
  calc
    A i * Q * X * (Q * (A i)ᴴ) = A i * (Q * X * Q) * (A i)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = A i * X * (A i)ᴴ := by rw [hX]

/-- The transfer spectrum of a transient diagonal corner inherits the bound
on the ambient nonunit spectrum. A one-dimensional ambient fixed space rules
out eigenvalue one in the corner complementary to a nonzero projection. -/
theorem spectrum_transferMap_transientCorner_norm_le
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P) (hPZero : P ≠ 0)
    (hUpper : ∀ i, P * A i * (1 - P) = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    ∀ z ∈ spectrum ℂ (Kraus.transferMap (fun i => (1 - P) * A i * (1 - P))),
      ‖z‖ ≤ q := by
  let Q : Matrix (Fin D) (Fin D) ℂ := 1 - P
  have hQ : IsOrthogonalProjection Q :=
    hP.isStarProjection.one_sub.isOrthogonalProjection
  have hUpperQ : ∀ i, (1 - Q) * A i * Q = 0 := by
    simpa only [Q, sub_sub_cancel] using hUpper
  intro z hz
  by_cases hzZero : z = 0
  · simpa only [hzZero, norm_zero] using hq
  obtain ⟨X, hX⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  have hEigen : Kraus.map (fun i => Q * A i * Q) X = z • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  have hSupport : Q * X * Q = X := by
    apply (smul_right_injective (Matrix (Fin D) (Fin D) ℂ) hzZero)
    calc
      z • (Q * X * Q) = Q * (z • X) * Q := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = Q * Kraus.map (fun i => Q * A i * Q) X * Q := by rw [hEigen]
      _ = Kraus.map (fun i => Q * A i * Q) X := map_corner_supported A Q hQ X
      _ = z • X := hEigen
  have hAmbient : Kraus.transferMap A X = z • X := by
    change Kraus.map A X = z • X
    rw [← map_corner_eq_of_supported A Q hQ hUpperQ X hSupport]
    exact hEigen
  have hzOne : z ≠ 1 := by
    intro hzOne
    have hOne : Kraus.transferMap A 1 = 1 := Kraus.map_one_of_isUnital A hUnital
    have hFixedSpace : Module.End.eigenspace (Kraus.transferMap A) 1 =
        Submodule.span ℂ {(1 : Matrix (Fin D) (Fin D) ℂ)} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hDim
        (Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using hOne))
        one_ne_zero
    have hXFixed : X ∈ Module.End.eigenspace (Kraus.transferMap A) 1 := by
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [hzOne, one_smul] using hAmbient
    rw [hFixedSpace] at hXFixed
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hXFixed
    have hcZero : c ≠ 0 := by
      intro hcZero
      apply hX.2
      rw [← hc, hcZero, zero_smul]
    have hQOne : Q = 1 := by
      apply (smul_right_injective (Matrix (Fin D) (Fin D) ℂ) hcZero)
      simpa only [← hc, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hQ.2] using hSupport
    apply hPZero
    simpa only [Q, sub_eq_self] using hQOne
  exact hspec z
    (Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hAmbient, hX.2⟩)) hzOne

/-- A complementary diagonal corner with no peripheral transfer eigenvalues
has a periodic MPS norm tending to zero. In combination with the exact
triangular trace split, this permits asymptotic comparison with the recurrent
corner without asserting equality of their finite-ring rays. -/
theorem norm_mpvState_transientCorner_tendsto_zero_of_transfer_spectrum
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : IsOrthogonalProjection P) (hPZero : P ≠ 0)
    (hUpper : ∀ i, P * A i * (1 - P) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    Filter.Tendsto
      (fun N : ℕ => ‖mpvState (fun i => (1 - P) * A i * (1 - P)) N‖)
      Filter.atTop (nhds (0 : ℝ)) := by
  let R : MPSTensor d D := fun i => (1 - P) * A i * (1 - P)
  have hBound : ∀ z ∈ spectrum ℂ (Kraus.transferMap R), ‖z‖ ≤ q :=
    spectrum_transferMap_transientCorner_norm_le A hUnital hDim P hP hPZero
      hUpper q hq hspec
  have hRadius : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap R)) < 1 := by
    apply spectralRadius_lt_of_forall_quasispectrum_lt (r := 1)
    intro z hz
    rw [quasispectrum_eq_spectrum_union_zero] at hz
    rcases hz with hz | hz
    · rw [AlgEquiv.spectrum_eq] at hz
      have hlt : ‖z‖ < 1 := lt_of_le_of_lt (hBound z hz) hqOne
      exact_mod_cast hlt
    · have hzZero : z = 0 := hz
      rw [hzZero]
      norm_num
  have hOverlap : Filter.Tendsto (fun N => mpvOverlap R R N)
      Filter.atTop (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one R R
      (by simpa only [Kraus.mixedMapLM_self] using hRadius)
  have hSquare : Filter.Tendsto (fun N => ‖mpvState R N‖ ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, ← ofReal_norm_mpvState_sq,
      Complex.ofReal_re, Complex.zero_re]
      using (Complex.continuous_re.tendsto (0 : ℂ)).comp hOverlap
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero]
    using hSquare.sqrt

end MPSTensor

end TransientCornerSpectrum

section TransientSupportGaugeIdentification

/-!
## Identification after removal of a transient periodic component

A periodic tensor with a norm-vanishing remainder can be compared asymptotically
with its retained component. A limiting overlap of modulus one identifies the
bond dimensions and gives gauge equivalence up to a scalar between irreducible
retained tensors. Faithful adjoint stationary densities provide trace-preserving
normalizations by pure bond gauges, so all periodic coefficients are unchanged.

These are finite-dimensional auxiliary statements for arXiv:1010.3732,
Appendix C, lines 2653–2717, using arXiv:1606.00608, Lemma equalMPS. They do not
assert exact equality of the full and retained finite-ring rays, or deduce
transfer contraction from a physical Hamiltonian gap.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology
open Filter

namespace MPSTensor

private theorem exists_gaugePhase_of_unit_overlap_of_faithful_adjoint_fixedPoints
    {d D E : ℕ} [NeZero D] [NeZero E]
    (A : MPSTensor d D) (C : MPSTensor d E)
    (hA : Kraus.IsIrreducibleFamily A) (hC : Kraus.IsIrreducibleFamily C)
    (σ : Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin E) (Fin E) ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hσfix : Kraus.adjointMap A σ = σ) (hτfix : Kraus.adjointMap C τ = τ)
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A C N‖) atTop (𝓝 (1 : ℝ))) :
    ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  let A' := Kraus.tpGauge A σ
  let C' := Kraus.tpGauge C τ
  have hATP : ∑ i, (A' i)ᴴ * A' i = 1 :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint A σ hσ (by
      simpa only [Kraus.mapLM_apply, Kraus.map_apply, Kraus.adjointMap_apply,
        Matrix.conjTranspose_conjTranspose] using hσfix)
  have hCTP : ∑ i, (C' i)ᴴ * C' i = 1 :=
    Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint C τ hτ (by
      simpa only [Kraus.mapLM_apply, Kraus.map_apply, Kraus.adjointMap_apply,
        Matrix.conjTranspose_conjTranspose] using hτfix)
  have hAIrr : Kraus.IsIrreducibleFamily A' :=
    (Kraus.isIrreducibleFamily_tpGauge_iff A σ hσ).mpr hA
  have hCIrr : Kraus.IsIrreducibleFamily C' :=
    (Kraus.isIrreducibleFamily_tpGauge_iff C τ hτ).mpr hC
  have hGaugeA := gaugeEquiv_tpGauge A σ hσ
  have hGaugeC := gaugeEquiv_tpGauge C τ hτ
  have hSame : ∀ N, mpvOverlap A' C' N = mpvOverlap A C N := by
    intro N
    unfold mpvOverlap
    apply Finset.sum_congr rfl
    intro x _
    rw [← hGaugeA.sameMPV N x, ← hGaugeC.sameMPV N x]
  have hOverlap' : Tendsto (fun N => ‖mpvOverlap A' C' N‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hSame] using hOverlap
  have hdim := dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
    A' C' hAIrr hCIrr hATP hCTP hOverlap'
  subst E
  have hCore := gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
    A' C' hAIrr hCIrr hATP hCTP hOverlap'
  exact ⟨rfl, gaugePhaseEquiv_trans_same_dim hGaugeA.toGaugePhaseEquiv
    (gaugePhaseEquiv_trans_same_dim hCore hGaugeC.symm.toGaugePhaseEquiv)⟩

/-- A norm-vanishing periodic remainder can be removed before the rectangular
fundamental theorem identifies the actual retained tensors and bond dimensions.
Faithful adjoint stationary matrices give pure trace-preserving gauges. This
conditional auxiliary statement is used in arXiv:1010.3732, Appendix C,
lines 2653–2717; gauge recovery is arXiv:1606.00608, Lemma equalMPS. -/
theorem exists_dim_eq_gaugePhase_of_vanishing_periodic_remainder
    {d D E k l : ℕ} [NeZero D] [NeZero E]
    (A : MPSTensor d D) (B : MPSTensor d k)
    (C : MPSTensor d E) (R : MPSTensor d l)
    (hA : Kraus.IsIrreducibleFamily A) (hC : Kraus.IsIrreducibleFamily C)
    (σ : Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin E) (Fin E) ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hσfix : Kraus.adjointMap A σ = σ) (hτfix : Kraus.adjointMap C τ = τ)
    (M : ℝ) (hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hdecomp : ∀ᶠ N in atTop, ∀ x : Fin N → Fin d,
      mpv B x = mpv C x + mpv R x)
    (hR : Tendsto (fun N => ‖mpvState R N‖) atTop (𝓝 (0 : ℝ)))
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ))) :
    ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  have hRetained := mpvOverlap_norm_tendsto_one_of_eventual_decomposition
    A B C R M hBound hdecomp hR hOverlap
  exact exists_gaugePhase_of_unit_overlap_of_faithful_adjoint_fixedPoints
    A C hA hC σ τ hσ hτ hσfix hτfix hRetained

end MPSTensor

end TransientSupportGaugeIdentification

section StationarySupportLimitIdentification

/-!
## Identification of a stationary support from a limiting overlap

For a unital tensor with a one-dimensional transfer fixed space and a supplied
strict bound on the remaining spectrum, compression to the entire support of
an adjoint stationary density gives a normal tensor. The complementary periodic
component tends to zero. A unit limiting overlap with an irreducible reference
tensor then identifies the supported bond dimension and its bond gauge up to a
nonzero scalar.

This is a conditional finite-dimensional auxiliary for arXiv:1010.3732,
Appendix C, lines 2653–2717. The transfer spectral bound and limiting overlap
are explicit hypotheses. No physical-gap implication or exact equality of
ambient and supported finite-ring rays is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology
open Filter

namespace MPSTensor

/-- A one-dimensional transfer fixed space gives uniqueness of any trace-one
adjoint fixed matrix. No positivity assumption on the comparison matrix is required.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717, stationary support
of a limiting unital tensor; the fixed-space duality is finite-dimensional linear algebra. -/
theorem normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    {d k : ℕ} (B : MPSTensor d k)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) = 1)
    (σ : Matrix (Fin k) (Fin k) ℂ)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (Z : Matrix (Fin k) (Fin k) ℂ)
    (hZfix : Kraus.adjointMap B Z = Z) (hZtrace : Z.trace = 1) : Z = σ := by
  have hσne : σ ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.trace_zero, zero_ne_one] at htrace
  have hσker : σ ∈ (LinearMap.id - Kraus.adjointMapLM B).ker := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      Kraus.adjointMapLM_apply, hfix, sub_self]
  have hZker : Z ∈ (LinearMap.id - Kraus.adjointMapLM B).ker := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      Kraus.adjointMapLM_apply, hZfix, sub_self]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    ((finrank_adjointFixedSpace_eq_transferFixedSpace B).trans hDim) hσker hσne
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hZker)
  have hcOne : c = 1 := by
    simpa only [← hc, Matrix.trace_smul, htrace, smul_eq_mul, mul_one] using hZtrace
  simpa only [hcOne, one_smul] using hc.symm

/-- A full stationary support compression of a unital tensor with simple
fixed space and strictly contracting remaining spectrum is normal. A unit
limiting overlap identifies this compression with an irreducible reference
up to a scalar and a bond gauge, including equality of their bond dimensions.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717, using
arXiv:1606.00608, Lemma equalMPS. The spectral bound and overlap limit are
supplied hypotheses; no physical-gap implication is asserted. -/
theorem exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap
    {d D E k : ℕ} [NeZero D]
    (A : MPSTensor d D) (B : MPSTensor d k) (C : MPSTensor d E)
    (hA : Kraus.IsIrreducibleFamily A)
    (τ : Matrix (Fin D) (Fin D) ℂ) (hτ : τ.PosDef)
    (hτfix : Kraus.adjointMap A τ = τ)
    (hB : Kraus.IsUnital B)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap B) 1) = 1)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hsupport : K * Kᴴ = hσ.supportProj) (hC : ∀ i, C i = Kᴴ * B i * K)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap B), z ≠ 1 → ‖z‖ ≤ q)
    (M : ℝ) (hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ))) :
    IsNormalTensor C ∧
      ∃ h : D = E, GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) A) C := by
  have hk : k ≠ 0 := by
    intro hzero
    subst k
    simp only [Matrix.trace_fin_zero, zero_ne_one] at htrace
  let : NeZero k := ⟨hk⟩
  let : NeZero E := ⟨Nat.ne_of_gt
    (Matrix.supportFrame_dimension_pos_of_trace_one K σ hσ hsupport htrace)⟩
  have huniq := normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    B hDim σ hfix htrace
  obtain ⟨_, hCIrr, hρPD, _, hρfix⟩ := prepare_stationary_support_compression
    B C K hK hC hB σ hσ hsupport hfix htrace huniq
  have hNormal := isNormalTensor_of_unital_stationary_support_compression
    B C K hK hC hB σ hσ hsupport hfix htrace huniq q hqOne hspec
  have hfix' : Kraus.map (fun i => (B i)ᴴ) σ = σ := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using hfix
  have hInv := Kraus.lowerZero_of_posSemidef_fixedPoint
    (fun i => (B i)ᴴ) σ hσ hfix'
  have hP : IsOrthogonalProjection (K * Kᴴ) := by
    simpa only [Kraus.stationaryProj, ← hsupport] using hInv.1
  have hUpper : ∀ i, (K * Kᴴ) * B i * (1 - K * Kᴴ) = 0 := fun i => by
    simpa only [Kraus.stationaryProj, ← hsupport, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, Matrix.mul_assoc]
      using congrArg Matrix.conjTranspose (hInv.2 i)
  have hσne : σ ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.trace_zero, zero_ne_one] at htrace
  have hPne : K * Kᴴ ≠ 0 := by
    rw [hsupport]
    exact hσ.supportProj_ne_zero_of_ne_zero hσne
  have hR := norm_mpvState_transientCorner_tendsto_zero_of_transfer_spectrum
    B hB hDim (K * Kᴴ) hP hPne hUpper q hq hqOne hspec
  have hdecomp : ∀ᶠ N in atTop, ∀ x : Fin N → Fin d,
      mpv B x = mpv C x + mpv (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) x := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact mpv_eq_compression_add_transient_of_upperZero B C K hK hC hUpper hN
  refine ⟨hNormal, ?_⟩
  exact exists_dim_eq_gaugePhase_of_vanishing_periodic_remainder
    A B C (fun i => (1 - K * Kᴴ) * B i * (1 - K * Kᴴ)) hA
    (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM C hCIrr)
    τ (Kᴴ * σ * K) hτ hρPD hτfix hρfix M hBound hdecomp hR hOverlap

end MPSTensor

end StationarySupportLimitIdentification
