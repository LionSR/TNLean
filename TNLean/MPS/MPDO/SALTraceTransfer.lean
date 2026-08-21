/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.SectorTrace

/-!
# Trace-transfer consequences of saturation of the area law

The normalization clause in saturation of the area law makes the one-site
physical-trace transfer nonzero. Consequently, literal idempotence of that
matrix implies the scale-invariant source zero-correlation-length relation.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.6 and Appendix C.2, lines 1406--1497
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ} {M : MPOTensor d D}

/-- Saturation of the area law forces the physical-trace transfer to be
nonzero: its vanishing would make the one-site periodic operator have zero
trace, contrary to the normalization clause in SAL.

Source: arXiv:1606.00608, Definition 4.6 (line 811), together with the
one-site vertical-loop trace identity used in Appendix C.2. -/
theorem IsSAL.physTraceTransfer_ne_zero (hSAL : IsSAL M) :
    physTraceTransfer M ≠ 0 := by
  intro hZero
  exact (Classical.choose_spec hSAL).1 1 Nat.zero_lt_one (by
    rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer, hZero]
    simp)

/-- Under saturation of the area law, literal idempotence of the
physical-trace transfer implies source zero correlation length.

Source: arXiv:1606.00608, Definition 4.2 (lines 735--739) and Definition 4.6
(line 811). -/
theorem IsSAL.isSourceZCL_of_physTraceTransfer_sq (hSAL : IsSAL M)
    (hSq : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M) :
    IsSourceZCL M :=
  MPOTensor.isSourceZCL_of_physTraceTransfer_sq M hSAL.physTraceTransfer_ne_zero hSq

end MPOTensor
