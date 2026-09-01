/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import QICLean.Analysis.SpectralRadiusPowerDecay
import TNLean.MPS.ParentHamiltonian.FNWLimitMap
import TNLean.MPS.ParentHamiltonian.WeightedVirtualHilbert

/-!
# FNW transfer-remainder decay

Fannes--Nachtergaele--Werner, *Communications in Mathematical Physics* 144
(1992), 443--490, Lemma 5.2 and equations (5.9)--(5.10), bound the positive
powers of the transfer remainder in the Hilbert-space norm weighted by the
faithful stationary density. The source quantity is
\(a(n)=\operatorname{Tr}(\rho^{-1})\lVert E^n-E_\infty\rVert_\rho\).

This module first transfers the complementary eigenvalue gap from TNLean's
Schrödinger map to the FNW observable map through the bilinear trace adjoint.
It then activates the rho-weighted norm from equation (5.6), derives the
corresponding spectral-radius gap, and proves prescribed-rate geometric decay
with an existential rate-dependent prefactor.

No dimension-only value of the prefactor is asserted.
-/

open scoped ENNReal Matrix NNReal

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The FNW transfer remainder has the same eigenvalues as TNLean's
Schrödinger remainder. Hence primitivity bounds every eigenvalue in modulus by
one strictly. This norm-independent bridge is the spectral step in FNW 1992,
Lemma 5.2, before the weighted norm in equations (5.9)--(5.10) is chosen. -/
theorem IsPrimitiveMPS.fnwRemainder_eigenvalue_norm_lt_one [NeZero D]
    {A : MPSTensor d D} {ρ : Mat} (hP : IsPrimitiveMPS A ρ) (ν : ℂ)
    (hν : Module.End.HasEigenvalue
      (fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero) ν) :
    ‖ν‖ < 1 := by
  have hremainder :
      fnwTransferMap A - fnwLimitMap ρ hP.trace_ne_zero =
        Matrix.traceAdjointMap
          (Kraus.transferMap A - fixedPointProj ρ hP.trace_ne_zero) := by
    rw [Matrix.traceAdjointMap_sub, ← fnwTransferMap_eq_traceAdjointMap,
      ← fnwLimitMap_eq_traceAdjointMap_fixedPointProj]
  rw [hremainder, Matrix.traceAdjointMap_hasEigenvalue_iff] at hν
  exact hP.complement_eigenvalue_norm_lt_one ν hν

end

end MPSTensor
