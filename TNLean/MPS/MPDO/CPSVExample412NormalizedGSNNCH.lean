/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample412NormalizedRFP
import TNLean.MPS.MPDO.GSNNCHFourCycleMarkov.ExampleFourCycleObstruction

/-!
# The normalized representative of CPSV16 Example 4.12 is not GSNNCH

The GSNNCH condition of CPSV16 Definition 4.8 concerns only the normalized
density-operator family, and that family is unchanged by any nonzero complex
rescaling of the MPO tensor.  The condition is therefore invariant under such
rescaling.  In particular the density-normalized representative
`M̂ = (1 / 2) M` of the tensor printed in Example 4.12 inherits the GSNNCH
obstruction proved for the printed tensor.

## Main results

* `MPOTensor.isGSNNCH_smul_iff`: the GSNNCH condition is invariant under
  nonzero complex rescaling of the tensor.
* `MPOTensor.CPSVExample412NormalizedRFP.Mhat_not_isGSNNCH`: the
  density-normalized representative of Example 4.12 is not GSNNCH.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.8,
  lines 829--850, and Example 4.12, lines 932--938.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The GSNNCH condition is invariant under nonzero complex rescaling of the
MPO tensor, since it constrains only the normalized density-operator family
and that family is unchanged by the rescaling.

Project-derived from the GSNNCH definition in arXiv:1606.00608,
Definition 4.8, lines 829--850, together with the normalization convention of
line 792. -/
theorem isGSNNCH_smul_iff {c : ℂ} (hc : c ≠ 0) (M : MPOTensor d D) :
    IsGSNNCH (c • M) ↔ IsGSNNCH M := by
  unfold IsGSNNCH
  refine forall_congr' fun N => imp_congr_right fun _ => ?_
  rw [normalizedMPO_smul hc M N]

namespace CPSVExample412NormalizedRFP

/-- The density-normalized representative of the tensor printed in CPSV16
Example 4.12 is not GSNNCH.  The GSNNCH condition depends only on the
normalized density-operator family, which the rescaling by `1 / 2` leaves
unchanged, so the obstruction proved for the printed tensor transports to the
normalized representative.

Source conclusion: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--938. -/
theorem Mhat_not_isGSNNCH : ¬ IsGSNNCH Mhat := by
  rw [Mhat, isGSNNCH_smul_iff (by norm_num)]
  exact CPSVExample412Literal.M_not_isGSNNCH

end CPSVExample412NormalizedRFP

end MPOTensor
