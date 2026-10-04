/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Examples.SpinOne
import TNLean.MPS.Core.PhysicalRotation
import TNLean.MPS.Symmetry.StringOrderDefs
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The physical AKLT string-order parameter

Example 1 of Pérez-García–Wolf–Sanz–Verstraete–Cirac, arXiv:0802.0447,
`Papers/0802.0447/StringOrder-v10.tex` lines 392–400, has physical endpoints
`x = y = S_z`, twist `exp (iπ S_z)`, and string-order value `-4/9`.
The quantity here is the source's stationary infinite-chain transfer
expression, not a finite periodic-chain expectation or arbitrary virtual
boundary nondecay. The calculation is on the unblocked physical tensor.

Two conventions are made explicit. The printed tensor has a positive last
letter, whereas `akltTensor` has a negative one; the source tensor below is
obtained by a diagonal unitary change of the physical basis. Both `S_z` and
the twist are unchanged by that rephasing.

**Local fix (normalized stationary density):** The stationary density is `I/2`,
as required by `tr Λ = 1` in the source's display `fixed` (lines 147–152).
The example's literal `Λ = I` is missing this normalization and would give
`-8/9` in display `SOPMP`; the stated physical value `-4/9` uses `I/2`.
The correction and its literal-boundary countercheck are recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

noncomputable section

namespace MPSTensor

/-- The source's physical pi rotation about the spin-z axis, in the physical
order `(m=0,m=+1,m=-1)`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
def akltSpinRotationZ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, -1, -1]

/-- The normalized AKLT tensor printed in PGWSVC08 Example 1. The sign change
of the last letter is a physical basis rephasing of the existing tensor.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
def akltPGWSVC08Tensor : MPSTensor 3 2 :=
  rotatePhysical (Matrix.diagonal ![1, 1, -1]) akltTensor

/-- The source tensor is exactly `(σ_z, √2 σ_+, √2 σ_-)/√3`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08Tensor_apply (i : Fin 3) :
    akltPGWSVC08Tensor i = match i with
      | 0 => (↑(1 / Real.sqrt 3) : ℂ) • !![1, 0; 0, -1]
      | 1 => (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 1; 0, 0]
      | 2 => (↑(Real.sqrt 2 / Real.sqrt 3) : ℂ) • !![0, 0; 1, 0] := by
  fin_cases i <;>
    simp [akltPGWSVC08Tensor, rotatePhysical, Matrix.diagonal, akltTensor]

/-- The source rephasing is unitary, so it is a genuine physical basis change.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08_rephasing_unitary :
    (Matrix.diagonal ![1, 1, -1] : Matrix (Fin 3) (Fin 3) ℂ) ∈
      Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

/-- The source's virtual gauge `σ_z` implements the physical pi rotation on
the printed tensor.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08_sigmaZ_intertwine (i : Fin 3) :
    (∑ j : Fin 3, akltSpinRotationZ i j • akltPGWSVC08Tensor j) =
      !![(1 : ℂ), 0; 0, -1] * akltPGWSVC08Tensor i * !![1, 0; 0, -1] := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltSpinRotationZ, Matrix.diagonal, akltPGWSVC08Tensor_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem spinOneOperator_z_diagonal :
    spinOneOperator 2 = Matrix.diagonal ![0, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinOneOperator, Matrix.diagonal]

/-- The explicit string twist is the actual matrix exponential `exp(iπ S_z)`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltSpinRotationZ_eq_exp :
    akltSpinRotationZ =
      NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) • spinOneOperator 2) := by
  rw [spinOneOperator_z_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  have hpi : Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I := mul_comm _ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [akltSpinRotationZ, Matrix.diagonal, Pi.coe_exp,
      ← Complex.exp_eq_exp_ℂ, hpi]

/-- The pi rotation is a nontrivial unitary physical operator.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltSpinRotationZ_unitary_ne_one :
    akltSpinRotationZ * akltSpinRotationZᴴ = 1 ∧ akltSpinRotationZ ≠ 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [akltSpinRotationZ, Matrix.mul_apply, Fin.sum_univ_three]
  · intro h
    have := congrFun (congrFun h 1) 1
    norm_num [akltSpinRotationZ] at this

/-- Every diagonal physical insertion is invariant under the source's change of
physical phases. In particular this applies to `S_z` and `exp(iπ S_z)`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem twistedTransferMap_akltPGWSVC08_diagonal (w : Fin 3 → ℂ) :
    twistedTransferMap akltPGWSVC08Tensor (Matrix.diagonal w) =
      twistedTransferMap akltTensor (Matrix.diagonal w) := by
  ext X i j
  simp [twistedTransferMap_apply, akltPGWSVC08Tensor, rotatePhysical,
    Matrix.diagonal, Fin.sum_univ_three]

/-- The transfer matrix with a diagonal physical insertion, in explicit virtual
coordinates. This one calculation supplies both physical endpoints and twist.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem twistedTransferMap_aklt_diagonal (w : Fin 3 → ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    twistedTransferMap akltTensor (Matrix.diagonal w) X =
      !![(w 0 * X 0 0 + 2 * w 1 * X 1 1) / 3, -(w 0 * X 0 1) / 3;
        -(w 0 * X 1 0) / 3, (w 0 * X 1 1 + 2 * w 2 * X 0 0) / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistedTransferMap_apply, Matrix.diagonal, Fin.sum_univ_three,
      akltTensor, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply,
      Complex.ofReal_div] <;>
    field_simp <;> ring_nf <;>
    norm_num [Complex.ofReal_sqrt_sq 3 (by norm_num),
      Complex.ofReal_sqrt_sq 2 (by norm_num)] <;> ring

/-- The printed tensor is unital, with positive trace-one stationary density
`I/2`. This is the canonical normalization required by the source's display
`fixed`, rather than the unnormalized identity printed in the example.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08_canonical :
    Kraus.transferMap akltPGWSVC08Tensor 1 = 1 ∧
      Kraus.transferMap (fun i => (akltPGWSVC08Tensor i)ᴴ) ((1 / 2 : ℂ) • 1) =
        (1 / 2 : ℂ) • 1 ∧
      Matrix.PosDef ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      Matrix.trace ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  have hstar (i : Fin 3) : (akltPGWSVC08Tensor i)ᴴ =
      akltPGWSVC08Tensor (Equiv.swap 1 2 i) := by
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [akltPGWSVC08Tensor_apply, Matrix.conjTranspose_apply, Equiv.swap_apply_def]
  have hone : Kraus.transferMap akltPGWSVC08Tensor 1 = 1 := by
    rw [← twistedTransferMap_one]
    rw [show (1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.diagonal (fun _ => 1) by
      ext i j; simp [Matrix.diagonal, Matrix.one_apply]]
    rw [twistedTransferMap_akltPGWSVC08_diagonal, twistedTransferMap_aklt_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  refine ⟨hone, ?_, Matrix.PosDef.one.smul (by norm_num), ?_⟩
  · have hreindex : Kraus.transferMap (fun i => (akltPGWSVC08Tensor i)ᴴ) =
        Kraus.transferMap akltPGWSVC08Tensor := by
      have hf : (fun i => (akltPGWSVC08Tensor i)ᴴ) =
          fun i => akltPGWSVC08Tensor (Equiv.swap 1 2 i) := funext hstar
      rw [hf]
      ext X : 1
      simp only [Kraus.transferMap_apply]
      exact Equiv.sum_comp (Equiv.swap (1 : Fin 3) 2)
        (fun i : Fin 3 => akltPGWSVC08Tensor i * X * (akltPGWSVC08Tensor i)ᴴ)
    rw [hreindex, map_smul, hone]
  · norm_num [Matrix.trace_smul, Matrix.trace_one]

/-- The physical right endpoint sends the identity to `(2/3) σ_z`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem twistedTransferMap_aklt_spinZ_one :
    twistedTransferMap akltTensor (spinOneOperator 2) 1 =
      (2 / 3 : ℂ) • !![1, 0; 0, -1] := by
  rw [spinOneOperator_z_diagonal, twistedTransferMap_aklt_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The twisted transfer fixes the virtual sigma-z matrix.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem twistedTransferMap_aklt_rotationZ_sigmaZ :
    twistedTransferMap akltTensor akltSpinRotationZ !![1, 0; 0, -1] =
      !![1, 0; 0, -1] := by
  rw [akltSpinRotationZ, twistedTransferMap_aklt_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The physical left endpoint sends sigma-z to `-(2/3) I`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem twistedTransferMap_aklt_spinZ_sigmaZ :
    twistedTransferMap akltTensor (spinOneOperator 2) !![1, 0; 0, -1] =
      (-2 / 3 : ℂ) • 1 := by
  rw [spinOneOperator_z_diagonal, twistedTransferMap_aklt_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The actual physical-endpoint AKLT string correlator is `-4/9` at every
middle-string length, with normalized stationary boundary `I/2`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem physicalStringOrderParam_aklt (N : ℕ) :
    physicalStringOrderParam akltTensor ((1 / 2 : ℂ) • 1)
      (spinOneOperator 2) (spinOneOperator 2) akltSpinRotationZ N = -4 / 9 := by
  have hfix (n : ℕ) : (twistedTransferMap akltTensor akltSpinRotationZ ^ n)
      !![1, 0; 0, -1] = !![1, 0; 0, -1] := by
    simpa only [Module.End.pow_apply] using
      Function.iterate_fixed twistedTransferMap_aklt_rotationZ_sigmaZ n
  rw [physicalStringOrderParam, twistedTransferMap_aklt_spinZ_one]
  simp only [twistedTransferIter, map_smul, hfix, twistedTransferMap_aklt_spinZ_sigmaZ,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.one_mul, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- The printed tensor has the same physical string value: its diagonal
physical rephasing changes neither the endpoints nor the string unitary.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem physicalStringOrderParam_akltPGWSVC08 (N : ℕ) :
    physicalStringOrderParam akltPGWSVC08Tensor ((1 / 2 : ℂ) • 1)
      (spinOneOperator 2) (spinOneOperator 2) akltSpinRotationZ N = -4 / 9 := by
  simpa only [physicalStringOrderParam, spinOneOperator_z_diagonal, akltSpinRotationZ,
    twistedTransferIter, twistedTransferMap_akltPGWSVC08_diagonal] using
    physicalStringOrderParam_aklt N

/-- Without the source's required trace-one normalization, the identity boundary
gives `-8/9`, explaining the correction of Example 1's printed `Λ=I` to `I/2`.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem physicalStringOrderParam_akltPGWSVC08_identity_boundary (N : ℕ) :
    physicalStringOrderParam akltPGWSVC08Tensor 1
      (spinOneOperator 2) (spinOneOperator 2) akltSpinRotationZ N = -8 / 9 := by
  have h := physicalStringOrderParam_akltPGWSVC08 N
  simp only [physicalStringOrderParam, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Matrix.one_mul] at h ⊢
  calc
    _ = (2 : ℂ) * ((1 / 2 : ℂ) * _) := by ring
    _ = 2 * (-4 / 9) := by rw [h]
    _ = _ := by norm_num

/-- The source's explicit physical endpoints witness physical string order for
the unblocked AKLT tensor, rather than only virtual-boundary nondecay.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08_hasPhysicalStringOrderWith :
    HasPhysicalStringOrderWith akltPGWSVC08Tensor ((1 / 2 : ℂ) • 1)
      (spinOneOperator 2) (spinOneOperator 2) akltSpinRotationZ := by
  refine ⟨4 / 9, by norm_num, ?_⟩
  have hfun : (fun N : ℕ => ‖physicalStringOrderParam akltPGWSVC08Tensor
      ((1 / 2 : ℂ) • 1) (spinOneOperator 2) (spinOneOperator 2) akltSpinRotationZ N‖) =
      fun _ => (4 / 9 : ℝ) := by
    funext N
    rw [physicalStringOrderParam_akltPGWSVC08]
    norm_num
  rw [hfun]
  exact tendsto_const_nhds

/-- The printed AKLT tensor has physical string order with a nonidentity physical
unitary, as defined by PGWSVC08's stationary correlator.
Supporting calculation for arXiv:0802.0447, Example 1, lines 392–399. -/
theorem akltPGWSVC08_hasPhysicalStringOrder :
    HasPhysicalStringOrder akltPGWSVC08Tensor ((1 / 2 : ℂ) • 1) :=
  ⟨akltSpinRotationZ, spinOneOperator 2, spinOneOperator 2,
    akltSpinRotationZ_unitary_ne_one.1, akltSpinRotationZ_unitary_ne_one.2,
    akltPGWSVC08_hasPhysicalStringOrderWith⟩

end MPSTensor

end
