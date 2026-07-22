/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorCoordinates

/-!
# Fixed generators of the transported vertical-sector composites

The transported refinement map sends each multiplicity-trace-scaled
one-site vertical BNT bond contraction to its two-site counterpart, and the
transported coarse-graining map sends it back.  Thus these contractions are
fixed by the coarse-graining--refinement composite.  The reverse composite
fixes the two-site contractions in the same way.

These conclusions concern only the two contraction families.  They do not
assert that either composite is the identity on the full sector algebra.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1974--1980.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

/-- Every multiplicity-trace-scaled one-site vertical BNT bond contraction is
fixed by the transported coarse-graining--refinement composite.

This proves only the inclusion of the one-site contraction family in the
fixed-point space.  The conclusion that the composite is the identity uses
the later fixed-point structure argument of Appendix C.4, lines 1980--1993.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem transportedVerticalSectorS_comp_T_fixed_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorFixedGeneratorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    h.SbarTbar (fun α => verticalMultiplicityTrace h.weight₁ α •
      MPSTensor.contractBondMatrix (h.A₁ α) X) =
      fun α => verticalMultiplicityTrace h.weight₁ α •
        MPSTensor.contractBondMatrix (h.A₁ α) X := by
  simp only [VerticalSectorFixedGeneratorHypotheses.SbarTbar,
    VerticalSectorFixedGeneratorHypotheses.Sbar,
    VerticalSectorFixedGeneratorHypotheses.Tbar, LinearMap.comp_apply]
  rw [transportedVerticalSectorT_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₁ h.hWeight₁
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.T h.hReconstruct₁ h.hForward₂ X (h.hTphys X)]
  exact transportedVerticalSectorS_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.S h.hForward₁ h.hReconstruct₂ X (h.hSphys X)

/-- Every multiplicity-trace-scaled two-site vertical BNT bond contraction is
fixed by the transported refinement--coarse-graining composite.

This proves only the inclusion of the two-site contraction family in the
fixed-point space.  The conclusion that the composite is the identity uses
the later fixed-point structure argument of Appendix C.4, lines 1980--1993.

Source: arXiv:1606.00608, Appendix C.4, lines 1974--1980. -/
theorem transportedVerticalSectorT_comp_S_fixed_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorFixedGeneratorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    h.TbarSbar (fun β => verticalMultiplicityTrace h.weight₂ β •
      MPSTensor.contractBondMatrix (h.A₂ β) X) =
      fun β => verticalMultiplicityTrace h.weight₂ β •
        MPSTensor.contractBondMatrix (h.A₂ β) X := by
  simp only [VerticalSectorFixedGeneratorHypotheses.TbarSbar,
    VerticalSectorFixedGeneratorHypotheses.Tbar,
    VerticalSectorFixedGeneratorHypotheses.Sbar, LinearMap.comp_apply]
  rw [transportedVerticalSectorS_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.S h.hForward₁ h.hReconstruct₂ X (h.hSphys X)]
  exact transportedVerticalSectorT_contractBondMatrix_trace_smul
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₁ h.hWeight₁
    h.M h.A₁ h.A₂ h.U₁ h.U₂ h.T h.hReconstruct₁ h.hForward₂ X (h.hTphys X)

end MPOTensor
