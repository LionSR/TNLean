/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EvenFamilyVirtualGauge
import TNLean.MPS.MPU.PhysicalAdjointCanonicalForm
import TNLean.MPS.MPU.TimeReversalTwistedTransfer
import TNLean.Algebra.StabilizedWeightedTrace
import TNLean.Algebra.UnitaryKronecker
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The actual canonical twisted transfer under even-chain adjoint symmetry

The virtual sign gauge is derived from actual even periodic adjoint symmetry.
It expresses the twisted transfer as a signed unitary conjugate of the actual
normalized completely positive transfer. The order of its product bond factors
is checked through the existing double-layer identity; no exchange of those
factors is silently inserted.

**Scope restriction (canonical ambient tensor):** Canonical form II is explicit.
This is an intrinsic trace statement, not a construction of the printed blocked
gates. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

Source: arXiv:1703.09188, `PropChiral`, lines 1209--1252, and
`prop:sigma1-and-sigma2-equal`, lines 1633--1733.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

variable {d D : ℕ}

private theorem normalizedDiagonal_mulTensor_productCoordinates
    (A B : MPOTensor d D) :
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (normalizedDiagonal (mulTensor A B)) =
      (d : ℂ)⁻¹ • ∑ i : Fin d, ∑ j : Fin d, A i j ⊗ₖ B j i := by
  classical
  let R := Matrix.reindexAlgEquiv ℂ ℂ (finProdFinEquiv (m := D) (n := D)).symm
  have hR (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
      R (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = M :=
    (Matrix.reindex finProdFinEquiv finProdFinEquiv).symm_apply_apply M
  have hdiag : contractPhysical (mulTensor A B) 1 = ∑ i : Fin d, mulTensor A B i i := by
    simp only [contractPhysical, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change R ((d : ℂ)⁻¹ • contractPhysical (mulTensor A B) 1) = _
  rw [hdiag]
  simp only [map_smul, map_sum, mulTensor_apply, hR]

/-- Actual even-chain adjoint symmetry gives a signed unitary comparison of
the twisted transfer with the normalized completely positive transfer.
The first bond factor carries the virtual gauge and the second is unchanged;
no bond exchange is needed in this convention.

Source: arXiv:1703.09188, `PropChiral`, lines 1209--1252, and
`prop:sigma1-and-sigma2-equal`, lines 1633--1733. -/
theorem IsMPUCanonicalFormII.exists_twistedTransfer_signed_unitary_comparison
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ) :
    ∃ (η : ℂ) (z : Matrix.unitaryGroup (Fin D) ℂ),
      (η = 1 ∨ η = -1) ∧
      timeReversalTwistedTransfer U = η •
        (((z : Matrix (Fin D) (Fin D) ℂ)ᴴ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
          transferMatrix (Kraus.transferMap U.normalizedFlattening) *
          ((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) := by
  classical
  let : NeZero d := hU.neZero_phys
  have hEq : ∀ N : ℕ, 1 < N → Even N →
      mpo U N = mpo (physicalAdjointTensor U) N := by
    intro N hN heven
    rw [mpo_physicalAdjointTensor_eq_conjTranspose]
    exact hTR N hN heven
  obtain ⟨_, η, z, hη, hrel⟩ :=
    hU.exists_unitary_virtual_sign_gauge_of_mpo_eq_even hU.physicalAdjointTensor hEq
  have hrel' (i j : Fin d) : physicalAdjointTensor U i j =
      η • ((z : Matrix (Fin D) (Fin D) ℂ) * U i j *
        (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    simpa only [cast_eq] using hrel i j
  have hηsq : η * η = 1 := by
    rcases hη with rfl | rfl <;> norm_num
  let Z : Matrix (Fin D) (Fin D) ℂ := z
  have hZ : Zᴴ * Z = 1 :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr z.property).1
  have hrecover (i j : Fin d) :
      U i j = η • (Zᴴ * physicalAdjointTensor U i j * Z) := by
    have h := congrArg (fun M ↦ Zᴴ * M * Z) (hrel' i j)
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h
    change Zᴴ * physicalAdjointTensor U i j * Z = η • (Zᴴ * (Z * U i j * Zᴴ) * Z)
      at h
    simp only [Matrix.mul_assoc, hZ, Matrix.mul_one] at h
    rw [← Matrix.mul_assoc Zᴴ Z, hZ, Matrix.one_mul] at h
    have hh := congrArg (fun M ↦ η • M) h
    rw [smul_smul, hηsq, one_smul] at hh
    simpa only [Matrix.mul_assoc] using hh.symm
  let E := transferMatrix (Kraus.transferMap U.normalizedFlattening)
  let G := Z ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)
  have hE : E = (d : ℂ)⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
      physicalAdjointTensor U i j ⊗ₖ U j i := by
    have h := normalizedDiagonal_mulTensor_productCoordinates (physicalAdjointTensor U) U
    change Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (normalizedDiagonal (doubleLayerTensor U)) = _ at h
    rw [normalizedDiagonal_doubleLayerTensor] at h
    have hcancel : Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (E.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) = E :=
      (Matrix.reindex finProdFinEquiv finProdFinEquiv).symm_apply_apply E
    exact hcancel.symm.trans h
  have hterm (i j : Fin d) : U i j ⊗ₖ U j i =
      η • (Gᴴ * (physicalAdjointTensor U i j ⊗ₖ U j i) * G) := by
    rw [hrecover, Matrix.smul_kronecker]
    congr 1
    simp only [G, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  refine ⟨η, z, hη, ?_⟩
  have hG : Gᴴ = Zᴴ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    simp only [G, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  change timeReversalTwistedTransfer U =
    η • ((Zᴴ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * E * G)
  rw [← hG]
  rw [timeReversalTwistedTransfer, normalizedDiagonal_mulTensor_productCoordinates]
  simp_rw [hterm]
  rw [hE]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.smul_sum, smul_smul, mul_comm]

private theorem intrinsic_trace_eq_trace_twistedTransfer (U : MPOTensor d D) :
    intrinsicTimeReversalSign U =
      Matrix.trace (Matrix.swapMatrix D * timeReversalTwistedTransfer U) := by
  classical
  rw [intrinsicTimeReversalSign, timeReversalPeriodicTrace_eq_sum,
    timeReversalTwistedTransfer, normalizedDiagonal_mulTensor_productCoordinates,
    Matrix.mul_smul, Matrix.trace_smul]
  simp only [Finset.mul_sum, Matrix.trace_sum,
    Matrix.trace_swapMatrix_mul_kronecker, smul_eq_mul]

private theorem trace_signed_unitary_comparison
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T E F : Matrix ι ι ℂ) (G : Matrix.unitaryGroup ι ℂ) (η : ℂ)
    (hη : η = 1 ∨ η = -1)
    (hT : T = η • ((G : Matrix ι ι ℂ)ᴴ * E * (G : Matrix ι ι ℂ)))
    (hFT : Commute F T) {bound : ℕ} (data : Matrix.StabilizedRankOneData E bound) :
    ∃ C : ℂ, ∀ k : ℕ, 0 < k → Matrix.trace (F * T ^ k) = η ^ k * C := by
  let A := (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) G).symm
  let B := A.symm F
  have hTA : T = η • A E := by
    simpa only [A, Unitary.conjStarAlgAut_symm_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using hT
  have hBE : Commute B E := by
    have h := hFT.map A.symm
    rw [hTA, map_smul, StarAlgEquiv.symm_apply_apply] at h
    change B * (η • E) = (η • E) * B at h
    change B * E = E * B
    rcases hη with rfl | rfl <;> simpa using h
  have hG : (G : Matrix ι ι ℂ).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr G.property
  have htrace (M : Matrix ι ι ℂ) : Matrix.trace (A M) = Matrix.trace M := by
    simp only [A, Unitary.conjStarAlgAut_symm_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose]
    rw [Matrix.trace_mul_cycle, hG.2, Matrix.one_mul]
  refine ⟨Matrix.trace (B * E ^ data.exponent), ?_⟩
  intro k hk
  have hpow : T ^ k = η ^ k • A (E ^ k) := by
    rw [hTA, smul_pow, ← map_pow]
  have hmap : A (B * E ^ k) = F * A (E ^ k) := by
    simp only [map_mul, B, StarAlgEquiv.apply_symm_apply]
  calc
    Matrix.trace (F * T ^ k) = η ^ k * Matrix.trace (F * A (E ^ k)) := by
      rw [hpow, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    _ = η ^ k * Matrix.trace (B * E ^ k) := by rw [← hmap, htrace]
    _ = _ := by rw [data.trace_mul_pow_eq_of_commute B hBE k hk]

/-- Actual even-chain adjoint symmetry yields the intrinsic blocked-trace
formula `τₖ = η^k C`, with both constants derived. The constant `C` is retained;
the virtual sign is not identified with the first intrinsic trace.
Stabilization is obtained internally from the actual normalized MPU transfer.

Source: arXiv:1703.09188, `PropChiral`, lines 1209--1252, and
`prop:sigma1-and-sigma2-equal`, lines 1633--1733. -/
theorem IsMPUCanonicalFormII.exists_intrinsic_blocking_phase_formula
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ) :
    ∃ η C : ℂ, (η = 1 ∨ η = -1) ∧
      intrinsicTimeReversalSign U = η * C ∧
      ∀ k : ℕ, 0 < k → intrinsicTimeReversalSign (blockTensor U k) = η ^ k * C := by
  classical
  let : NeZero d := hU.neZero_phys
  let : NeZero D := hU.neZero_bond
  obtain ⟨η, z, hη, hcomp⟩ := hU.exists_twistedTransfer_signed_unitary_comparison hTR
  let E := transferMatrix (Kraus.transferMap U.normalizedFlattening)
  have hz : (z : Matrix (Fin D) (Fin D) ℂ).IsUnitaryBetween :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr z.property
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ).IsUnitaryBetween := by
    constructor <;> simp [Matrix.IsIsometry, Matrix.IsCoisometry]
  let G : Matrix.unitaryGroup (Fin D × Fin D) ℂ :=
    ⟨(z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ),
      (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp (hz.kronecker _ _ hI)⟩
  have hT : timeReversalTwistedTransfer U =
      η • ((G : Matrix _ _ ℂ)ᴴ * E * (G : Matrix _ _ ℂ)) := by
    simpa only [G, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] using hcomp
  have hdata : ∃ bound : ℕ, Nonempty (Matrix.StabilizedRankOneData E bound) := by
    by_cases hD : D = 1
    · subst D
      exact ⟨1, ⟨hU.isMPU.normalizedTransferStabilization_fin_one⟩⟩
    · have hDpos : 0 < D := NeZero.pos D
      exact ⟨D * D - 1, ⟨hU.isMPU.normalizedTransferStabilization (by omega)⟩⟩
  obtain ⟨_, ⟨data⟩⟩ := hdata
  obtain ⟨C, hC⟩ := trace_signed_unitary_comparison (timeReversalTwistedTransfer U) E
    (Matrix.swapMatrix D) G η hη hT (swapMatrix_commute_timeReversalTwistedTransfer U) data
  have hfirst := hC 1 (by omega)
  rw [pow_one, pow_one, ← intrinsic_trace_eq_trace_twistedTransfer] at hfirst
  refine ⟨η, C, hη, hfirst, ?_⟩
  intro k hk
  rw [intrinsicTimeReversalSign_blockTensor_eq_twistedTransfer_trace]
  exact hC k hk

/-- Odd positive blocking preserves the first intrinsic time-reversal trace,
under actual even-chain adjoint symmetry of a canonical MPU. No blocked source
factors, local certificates, similarity or stabilization data are premises.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1643--1733.
This is intrinsic canonical parity, not the printed blocked-gate construction. -/
theorem IsMPUCanonicalFormII.intrinsic_blocking_trace_eq_of_odd
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ)
    (k : ℕ) (hk : 0 < k) (hodd : Odd k) :
    intrinsicTimeReversalSign (blockTensor U k) = intrinsicTimeReversalSign U := by
  obtain ⟨η, C, hη, hfirst, hform⟩ := hU.exists_intrinsic_blocking_phase_formula hTR
  have hηsq : η ^ 2 = 1 := sq_eq_one_iff.mpr hη
  obtain ⟨m, hm⟩ := hodd
  have hkm : k = 2 * m + 1 := by omega
  have hpow : η ^ k = η := by
    rw [hkm, pow_succ, pow_mul, hηsq, one_pow, one_mul]
  rw [hform k hk, hpow, hfirst]

/-- Even positive blocking has the same intrinsic time-reversal trace as
blocking by two, under actual even-chain adjoint symmetry of a canonical MPU.
The two initial intrinsic values are not asserted equal.

Source: arXiv:1703.09188, `prop:sigma1-and-sigma2-equal`, lines 1643--1733.
This is intrinsic canonical parity, not the printed blocked-gate construction. -/
theorem IsMPUCanonicalFormII.intrinsic_blocking_trace_eq_of_even
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo U N = (mpo U N)ᴴ)
    (k : ℕ) (hk : 0 < k) (heven : Even k) :
    intrinsicTimeReversalSign (blockTensor U k) =
      intrinsicTimeReversalSign (blockTensor U 2) := by
  obtain ⟨η, C, hη, _, hform⟩ := hU.exists_intrinsic_blocking_phase_formula hTR
  have hηsq : η ^ 2 = 1 := sq_eq_one_iff.mpr hη
  obtain ⟨m, hm⟩ := heven
  have hkm : k = 2 * m := by omega
  have hpow : η ^ k = 1 := by rw [hkm, pow_mul, hηsq, one_pow]
  rw [hform k hk, hform 2 (by omega), hpow, hηsq]

end MPOTensor
