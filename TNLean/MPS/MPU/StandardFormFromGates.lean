/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FundamentalTheoremGates

/-!
# Constructing a standard-form MPU from its two gates

Given the ordered gates from the two Margolus layers, a virtual index
records one physical output and one right intermediate coordinate.
The first half factor is the corresponding matrix unit; the second is
an entry of the shifted gate. Their contraction is exactly that gate.
This constructs the open tensor, rather than assuming an auxiliary
factorization. The existing supplied standard-form circuit theorem
then proves its periodic unitarity, including the one-block ring.

The physical alphabet is the ordered pair of original sites. Thus this
constructor implements the second blocking in the QCA-to-MPU direction.
It does not assert equality with an unblocked automorphism.

Source: CPSV17, arXiv:1703.09188, equations uu, vdagger and StandardForm,
lines 532--543 and 603--622; Appendix, line 2308. The gate input comes
from Schumacher--Werner, arXiv:quant-ph/0405174, equations bruleU and bruleV.
-/

open Matrix
open scoped BigOperators Kronecker

namespace MPOTensor

variable {d ℓ r : ℕ}

private def gateHalfRight : Matrix (Fin d × Fin (d * r)) (Fin r) ℂ :=
  fun p s => if p.2 = finProdFinEquiv (p.1, s) then 1 else 0

private def gateHalfLeft
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin (d * r) × Fin d) (Fin ℓ) ℂ :=
  fun p t => v ((finProdFinEquiv.symm p.1).1, p.2)
    ((finProdFinEquiv.symm p.1).2, t)

/-- The explicit two-site tensor obtained from the unshifted gate
\(u:\mathbb C^d\otimes\mathbb C^d\to\mathbb C^\ell\otimes\mathbb C^r\)
and shifted gate
\(v:\mathbb C^r\otimes\mathbb C^\ell\to\mathbb C^d\otimes\mathbb C^d\).
Its constructed virtual space has dimension \(dr\).
Source: CPSV17, StandardForm, lines 603--617; Appendix, line 2308. -/
def standardFormTensorOfGates
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) : MPOTensor (d * d) (d * r) :=
  fun i j α γ => ∑ t : Fin ℓ, ∑ s : Fin r,
    gateHalfLeft v (α, (finProdFinEquiv.symm i).1) t *
      u (t, s) (finProdFinEquiv.symm j) *
        gateHalfRight ((finProdFinEquiv.symm i).2, γ) s

/-- Any two ordered unitary gates supply an actual tensor and the single
public two-site standard-form witness. All half factors are constructed;
no factorization or MPU hypothesis is supplied.
Source: CPSV17, StandardForm and SF, lines 603--622; Appendix, line 2308. -/
def standardFormTensorOfGatesData [NeZero d] [NeZero ℓ] [NeZero r]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) :
    TwoSiteStandardFormData (standardFormTensorOfGates u v) u v where
  phys_pos := NeZero.pos d
  bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos r)
  left_pos := NeZero.pos ℓ
  right_pos := NeZero.pos r
  X₁ := gateHalfRight
  X₂ := gateHalfLeft v
  u_unitary := hu
  v_unitary := hv
  v_apply := by
    intro i₁ i₂ s t
    simp [gateHalfRight, gateHalfLeft]
  W_apply := by
    intro i j α γ
    rfl

/-- The tensor built from two unitary gates generates an MPU. Periodic
unitarity is a conclusion, rather than a constructor hypothesis.
Source: CPSV17, StandardForm, lines 603--622; Appendix, line 2308. -/
theorem isMPU_standardFormTensorOfGates [NeZero d] [NeZero ℓ] [NeZero r]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) :
    (standardFormTensorOfGates u v).IsMPU :=
  TwoSiteStandardFormData.isMPU (standardFormTensorOfGates u v) u v
    (standardFormTensorOfGatesData u v hu hv)

/-- At every positive length, the constructed tensor is exactly the
unshifted \(u\) layer followed by the shifted \(v\) layer, in the original
ordered physical pair coordinates. This reuses the general supplied
standard-form contraction, including its periodic seam.
Source: CPSV17, StandardForm, lines 603--622; Appendix, line 2308. -/
theorem mpo_standardFormTensorOfGates [NeZero d] [NeZero ℓ] [NeZero r]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (N : ℕ) [NeZero N] :
    Matrix.reindex (twoSitePairConfigEquiv d N).symm
        (twoSitePairConfigEquiv d N).symm (mpo (standardFormTensorOfGates u v) N) =
      twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u :=
  TwoSiteStandardFormData.mpo_eq_shifted_mul_unshifted
    (standardFormTensorOfGates u v) u v (standardFormTensorOfGatesData u v hu hv)

/-- Cancelling changes of the intermediate Margolus bases preserve every
positive-length periodic operator of the constructed tensor.
Source: Schumacher--Werner, equations bruleU and bruleV, lines 1003--1041;
CPSV17, FundamentalMPU, lines 624--646. -/
theorem mpo_standardFormTensorOfGates_eq_of_gate_gauges
    [NeZero d] [NeZero ℓ] [NeZero r]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ)
    (N : ℕ) [NeZero N] :
    mpo (standardFormTensorOfGates u v) N =
      mpo (standardFormTensorOfGates
        (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
        (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ
          star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)))) N := by
  let S := standardFormTensorOfGatesData u v hu hv
  have hu' := ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _
    (Matrix.isUnitaryBetween_coe_unitaryGroup y)).mul _ _ hu
  have hv' := hv.mul _ _ ((Matrix.isUnitaryBetween_star_coe_unitaryGroup y).kronecker _ _
    (Matrix.isUnitaryBetween_star_coe_unitaryGroup x))
  exact S.mpo_eq_of_gate_gauges x y (standardFormTensorOfGatesData _ _ hu' hv')

/-- Schumacher--Werner's second gate has intermediate order
\((\ell,r)\). Cirac's shifted gate has order \((r,\ell)\), so its
columns are transported by the explicit product-factor swap.
Source: Schumacher--Werner, bruleV; CPSV17, vdagger, lines 532--543. -/
def margolusShiftedGate
    (V : Matrix (Fin d × Fin d) (Fin ℓ × Fin r) ℂ) :
    Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ :=
  Matrix.reindex (Equiv.refl _) (Equiv.prodComm _ _) V

/-- The generalized Margolus gates construct a positive-bond MPU with a
supplied literal standard form, and its periodic operator is their
alternating circuit. The physical alphabet is the ordered pair of
original sites, so this is the second blocking of the converse theorem.
Equality with a chosen QCA still requires that QCA's actual local action.
Source: CPSV17, Appendix, line 2308; StandardForm and SF, lines 603--622;
Schumacher--Werner, bruleU and bruleV, lines 980--1001. -/
theorem exists_standardFormTensor_of_margolus_gates [NeZero d] [NeZero ℓ] [NeZero r]
    (U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (V : Matrix (Fin d × Fin d) (Fin ℓ × Fin r) ℂ)
    (hU : U.IsUnitaryBetween) (hV : V.IsUnitaryBetween) :
    ∃ (D : ℕ) (_hD : 0 < D) (W : MPOTensor (d * d) D)
      (_S : TwoSiteStandardFormData W U (margolusShiftedGate V)),
      W.IsMPU ∧ ∀ (N : ℕ) (_hN : 0 < N),
        letI : NeZero N := ⟨Nat.ne_of_gt _hN⟩
        Matrix.reindex (twoSitePairConfigEquiv d N).symm
            (twoSitePairConfigEquiv d N).symm (mpo W N) =
          twoSiteShiftedLayer (N := N) (margolusShiftedGate V) *
            twoSiteUnshiftedLayer (N := N) U := by
  have hv : (margolusShiftedGate V).IsUnitaryBetween :=
    hV.reindex V (Equiv.refl _) (Equiv.prodComm _ _)
  refine ⟨d * r, Nat.mul_pos (NeZero.pos d) (NeZero.pos r),
    standardFormTensorOfGates U (margolusShiftedGate V),
    standardFormTensorOfGatesData U _ hU hv,
    isMPU_standardFormTensorOfGates U _ hU hv, ?_⟩
  intro N hN
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact mpo_standardFormTensorOfGates U _ hU hv N

end MPOTensor
