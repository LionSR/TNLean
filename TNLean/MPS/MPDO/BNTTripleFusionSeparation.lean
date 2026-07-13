/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTripleFusionComparison
import TNLean.MPS.MPDO.BNTFinalSectorFusion
import TNLean.MPS.MPDO.BiCFDerivation.Core

/-!
# Separation of final sectors in the triple-fusion comparison

The full triple-fusion comparison intertwines direct sums over all final labels.
If a common word polynomial selects one final-label tensor and annihilates all
the others, its off-diagonal final-label corners vanish.  This is the finite
word form of the simultaneous inverse used in the fixed-channel extraction in
arXiv:1511.08090.

The selector hypothesis is stated explicitly.  It is not presently derived
from the assumptions on `BNTFusionIsometryFamily`.  Consequently the result below is
a conditional final-sector decomposition; it does not construct an invertible
fixed-sector comparison, identify its multiplicity factor with the source
$F$-matrix, or prove a pentagon identity.

## References

* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, lines 237--277, especially the simultaneous inverse at
  line 269; see also lines 427--431 for the blocked direct-sum span input
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

@[simp] private theorem leftFinalIndexEquiv_symm_apply
    (α β γ ε δ : Λ) (μ : Fin (Fam.chi.dim α β δ))
    (ν : Fin (Fam.chi.dim δ γ ε)) (b : Fin (Fam.bondDim ε)) :
    (Fam.leftFinalIndexEquiv α β γ ε).symm (⟨⟨δ, μ, ν⟩, b⟩) =
      ⟨δ, μ, ν, b⟩ := by
  rfl

@[simp] private theorem rightFinalIndexEquiv_symm_apply
    (α β γ ε δ : Λ) (μ : Fin (Fam.chi.dim β γ δ))
    (ν : Fin (Fam.chi.dim α δ ε)) (b : Fin (Fam.bondDim ε)) :
    (Fam.rightFinalIndexEquiv α β γ ε).symm (⟨⟨δ, μ, ν⟩, b⟩) =
      ⟨δ, μ, ν, b⟩ := by
  rfl

/-- A common finite family of word polynomials separates every final-label
tensor from all the others.  This is the arbitrary-finite-label form of
`MPSTensor.HasBlockSelectorWords`.

For each `ε`, the same coefficients evaluate to the identity on `tensor ε`
and to zero on every `tensor ε'` with `ε' ≠ ε`.

Source: arXiv:1511.08090, simultaneous inverse relation
`B_d^+ B_{d'} = δ_{d,d'} 1` at line 269, after the common blocking described
at lines 427--431. -/
def HasFinalLabelSelectorWords (S : ℕ) : Prop :=
  ∀ ε : Λ, ∃ c : (Fin S → Fin (p * p)) → ℂ,
    (∑ w : Fin S → Fin (p * p),
      c w • MPSTensor.evalWord (Fam.tensor ε).toMPSTensor (List.ofFn w)) = 1 ∧
    ∀ ε' : Λ, ε' ≠ ε →
      (∑ w : Fin S → Fin (p * p),
        c w • MPSTensor.evalWord (Fam.tensor ε').toMPSTensor (List.ofFn w)) = 0

private theorem rectangularIntertwiner_eq_zero_of_selectorWords
    {d D₁ D₂ S : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (C : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hC : ∀ i : Fin d, A i * C = C * B i)
    (c : (Fin S → Fin d) → ℂ)
    (hA : (∑ w : Fin S → Fin d,
      c w • MPSTensor.evalWord A (List.ofFn w)) = 1)
    (hB : (∑ w : Fin S → Fin d,
      c w • MPSTensor.evalWord B (List.ofFn w)) = 0) :
    C = 0 := by
  have hWord : ∀ w : List (Fin d),
      MPSTensor.evalWord A w * C = C * MPSTensor.evalWord B w := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
        simp only [MPSTensor.evalWord_cons]
        calc
          (A i * MPSTensor.evalWord A w) * C =
              A i * (MPSTensor.evalWord A w * C) := Matrix.mul_assoc _ _ _
          _ =
              A i * (C * MPSTensor.evalWord B w) := by rw [ih]
          _ = (A i * C) * MPSTensor.evalWord B w := by rw [Matrix.mul_assoc]
          _ = (C * B i) * MPSTensor.evalWord B w := by rw [hC i]
          _ = C * (B i * MPSTensor.evalWord B w) := by rw [Matrix.mul_assoc]
  have hSum :
      (∑ w : Fin S → Fin d,
        (c w • MPSTensor.evalWord A (List.ofFn w)) * C) =
      ∑ w : Fin S → Fin d,
        C * (c w • MPSTensor.evalWord B (List.ofFn w)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hWord]
  rw [← Matrix.sum_mul, hA, Matrix.one_mul, ← Matrix.mul_sum, hB,
    Matrix.mul_zero] at hSum
  exact hSum

/-- **Conditional off-diagonal final-sector vanishing.** Suppose the positive
trace-power coefficients are independent of the positive chain length and a
common finite word family separates the final-label tensors.  Then the full
triple-fusion comparison has no corner from a right final sector `ε'` to a
distinct left final sector `ε`.

**Scope restriction (simultaneous final-label separation):** the selector
hypothesis is the finite-word form of the simultaneous inverse at line 269 of
arXiv:1511.08090.  It is not derived from the current assumptions on
`BNTFusionIsometryFamily`; this remaining implication is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

This theorem asserts only off-diagonal vanishing.  It does not assert that a
diagonal corner is invertible, identify such a corner with an $F$-matrix, or
prove a pentagon identity.

Source: arXiv:1511.08090, equations `zippercondition2` and `Fmove`, lines
237--277, especially line 269; arXiv:1606.00608, lines 995--1010. -/
theorem tripleFusionComparison_finalSector_submatrix_eq_zero
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ}
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε ε' : Λ) (hε : ε' ≠ ε) :
    (Fam.tripleFusionComparison α β γ).submatrix
        (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε') = 0 := by
  let C := Fam.tripleFusionComparison α β γ
  ext x y
  rcases x with ⟨δL, μL, νL, bL⟩
  rcases y with ⟨δR, μR, νR, bR⟩
  let Cblock : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε')) ℂ :=
    fun b b' => C (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, b⟩)
      (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, b'⟩)
  have hLetter : ∀ ij : Fin (p * p),
      (Fam.tensor ε).toMPSTensor ij * Cblock =
        Cblock * (Fam.tensor ε').toMPSTensor ij := by
    intro ij
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ij
    have hFull := Fam.tripleFusionComparison_intertwines_of_lengthIndependent
      c hχ hLI α β γ i k
    ext b b'
    have hEntry := congrArg
      (fun X => X (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, b⟩)
        (Fam.rightFinalRow α β γ ε' ⟨δR, μR, νR, b'⟩)) hFull
    simpa [Cblock, C, Matrix.mul_apply, Matrix.blockDiagonal'_apply,
      leftFinalRow, rightFinalRow, Fintype.sum_sigma, Fintype.sum_prod_type,
      Matrix.one_apply, MPOTensor.toMPSTensor]
      using hEntry
  obtain ⟨coeff, hSelf, hOther⟩ := hSel ε
  have hZero := rectangularIntertwiner_eq_zero_of_selectorWords
    (Fam.tensor ε).toMPSTensor (Fam.tensor ε').toMPSTensor Cblock hLetter
    coeff hSelf (hOther ε' hε)
  exact congrArg (fun X => X bL bR) hZero

/-- **Conditional fixed-final Kronecker form.** Suppose the positive
trace-power coefficients are independent of the positive chain length, common
finite word selectors separate the final-label tensors, and the selected final
tensor is injective at the present blocking. Then the diagonal fixed-final corner of the full
triple-fusion comparison has the form \(F_\varepsilon \otimes 1\), while every
corner from a distinct right final sector into the selected left sector
vanishes.

**Scope restriction (injectivity and simultaneous final-label separation):**
neither injectivity at the present blocking nor the selector hypothesis is derived
from the current assumptions on `BNTFusionIsometryFamily`. The missing
implications are documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

The matrix `F` is rectangular in general. This theorem does not assert that it
or the diagonal comparison corner is invertible, identify it with the printed
$F$-matrix, or prove a pentagon identity.

Source: arXiv:1511.08090, equations `Fmove` and `zippercondition2`, lines
237--277, especially the simultaneous inverse at line 269, the injectivity
argument following equation `pentagon3`, and the tensor-product conclusion at
line 277; arXiv:1606.00608, lines 995--1010. -/
theorem exists_tripleFusionComparison_finalSector_eq_kronecker_one_of_separation
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) {S : ℕ}
    (hSel : Fam.HasFinalLabelSelectorWords S)
    (α β γ ε : Λ)
    (hε : MPSTensor.IsInjective (Fam.tensor ε).toMPSTensor) :
    ∃ F : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
        (Fam.RightFinalMultiplicity α β γ ε) ℂ,
      ((Fam.tripleFusionComparison α β γ).submatrix
          (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)).submatrix
            (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
          F ⊗ₖ (1 : Matrix (Fin (Fam.bondDim ε)) (Fin (Fam.bondDim ε)) ℂ) ∧
        ∀ ε' : Λ, ε' ≠ ε →
          (Fam.tripleFusionComparison α β γ).submatrix
            (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε') = 0 := by
  let C := (Fam.tripleFusionComparison α β γ).submatrix
    (Fam.leftFinalRow α β γ ε) (Fam.rightFinalRow α β γ ε)
  have hC : ∀ ij : Fin (p * p),
      ((1 : Matrix (Fam.LeftFinalMultiplicity α β γ ε)
          (Fam.LeftFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
          (Fam.tensor ε).toMPSTensor ij) *
          C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm =
        C.submatrix (Fam.leftFinalIndexEquiv α β γ ε).symm
            (Fam.rightFinalIndexEquiv α β γ ε).symm *
          ((1 : Matrix (Fam.RightFinalMultiplicity α β γ ε)
            (Fam.RightFinalMultiplicity α β γ ε) ℂ) ⊗ₖ
            (Fam.tensor ε).toMPSTensor ij) := by
    intro ij
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ij
    have hFull := Fam.tripleFusionComparison_intertwines_of_lengthIndependent
      c hχ hLI α β γ i k
    ext ⟨⟨δL, μL, νL⟩, bL⟩ ⟨⟨δR, μR, νR⟩, bR⟩
    simp [C, Matrix.mul_apply, MPOTensor.toMPSTensor,
      leftFinalIndexEquiv_symm_apply, rightFinalIndexEquiv_symm_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    have hEntry := congrArg
      (fun X => X (Fam.leftFinalRow α β γ ε ⟨δL, μL, νL, bL⟩)
        (Fam.rightFinalRow α β γ ε ⟨δR, μR, νR, bR⟩)) hFull
    simpa [Matrix.mul_apply, Matrix.blockDiagonal'_apply,
      leftFinalRow, rightFinalRow, Fintype.sum_sigma,
      Fintype.sum_prod_type, Matrix.one_apply] using hEntry
  obtain ⟨F, hF⟩ :=
    Fam.exists_reindexed_intertwiner_eq_kronecker_one_of_isInjective
      α β γ ε hε C hC
  refine ⟨F, ?_, ?_⟩
  · exact hF
  · intro ε' hε'
    exact Fam.tripleFusionComparison_finalSector_submatrix_eq_zero
      c hχ hLI hSel α β γ ε ε' hε'

end MPOTensor.BNTFusionIsometryFamily
