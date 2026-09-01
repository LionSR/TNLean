/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Kraus.Transfer
import TNLean.MPS.Core.CanonicalNormalization

/-!
# FNW transfer-map convention

Fannes--Nachtergaele--Werner, *Communications in Mathematical Physics* 144
(1992), 443--490, equations (5.1)--(5.3), use
\(E(B)=\sum_\mu v_\mu Bv_\mu^*\). TNLean uses the Schrödinger convention
\(\E_A(X)=\sum_\mu A^\mu X (A^\mu)^\dagger\). Under
\(A^\mu=v(\mu)^\dagger\), the FNW map is the bilinear trace-pairing adjoint of
TNLean's transfer map.

The theorem below is phrased using only the bilinear pairing
\(\operatorname{Tr}(XY)\). For the unweighted Frobenius inner product, the
same map also agrees with the Hilbert-space adjoint of TNLean's transfer map.
It is generally different from the Hilbert-space adjoint for the rho-weighted
inner product of FNW equation (5.6).
-/

open scoped Matrix

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The FNW 1992 transfer map from equations (5.1)--(5.3), in TNLean coordinates
\(A^\mu=v(\mu)^\dagger\). -/
def fnwTransferMap (A : MPSTensor d D) : Mat →ₗ[ℂ] Mat :=
  Kraus.transferMap fun μ => (A μ)ᴴ

/-- Under \(A^\mu=v(\mu)^\dagger\), the FNW map in equations (5.1)--(5.3) is the
bilinear trace-pairing adjoint of TNLean's transfer map. It also agrees with
the Hilbert-space adjoint for the unweighted Frobenius inner product, but is
generally different from the rho-weighted adjoint of equation (5.6). -/
theorem fnwTransferMap_eq_traceAdjointMap (A : MPSTensor d D) :
    fnwTransferMap A = Matrix.traceAdjointMap (Kraus.transferMap A) := by
  simpa only [fnwTransferMap] using
    (Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose A).symm

/-- The unitality identity in FNW 1992, equations (5.2)--(5.3), follows exactly
from TNLean's left-canonical, equivalently trace-preserving, normalization. -/
theorem fnwTransferMap_one (A : MPSTensor d D) (hA : IsLeftCanonical A) :
    fnwTransferMap A 1 = 1 := by
  rw [fnwTransferMap_eq_traceAdjointMap]
  exact isTracePreservingMap_iff_traceAdjointMap_one.mp
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hA)

/-- The explicit convention bridge for FNW 1992, equations (5.1)--(5.3):
pairing a density \(\rho\) against the FNW map equals pairing TNLean's transfer
of \(\rho\) against the observable \(X\). The displayed identity uses the
bilinear matrix trace rather than the rho-weighted Hilbert pairing. -/
theorem trace_mul_fnwTransferMap (A : MPSTensor d D) (ρ X : Mat) :
    Matrix.trace (ρ * fnwTransferMap A X) =
      Matrix.trace (Kraus.transferMap A ρ * X) := by
  rw [fnwTransferMap_eq_traceAdjointMap, Matrix.trace_mul_comm]
  calc
    Matrix.trace (Matrix.traceAdjointMap (Kraus.transferMap A) X * ρ) =
        Matrix.trace (X * Kraus.transferMap A ρ) :=
      Matrix.trace_traceAdjointMap_mul (Kraus.transferMap A) X ρ
    _ = Matrix.trace (Kraus.transferMap A ρ * X) := Matrix.trace_mul_comm _ _

end

end MPSTensor
