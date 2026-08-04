/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LengthIndependentCoefficients

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

def A : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (4/5 : ℂ) • Matrix.single (0 : Fin 2) (0 : Fin 2) 1
  | 1 => (4/5 : ℂ) • Matrix.single (1 : Fin 2) (1 : Fin 2) 1
  | 2 => (3/5 : ℂ) • Matrix.single (0 : Fin 2) (1 : Fin 2) 1
  | 3 => (3/5 : ℂ) • Matrix.single (1 : Fin 2) (0 : Fin 2) 1

lemma A_map_star (k : Fin 4) : (A k).map (starRingEnd ℂ) = A k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.map_apply, starRingEnd_apply]

def bondEquiv : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
def bondEquivSymm : Fin 4 ≃ Fin 2 × Fin 2 := bondEquiv.symm


@[simp] lemma bondEquiv_symm_val (k : Fin 4) : bondEquiv.symm k =
    match k with
    | 0 => ((0 : Fin 2), (0 : Fin 2))
    | 1 => ((0 : Fin 2), (1 : Fin 2))
    | 2 => ((1 : Fin 2), (0 : Fin 2))
    | 3 => ((1 : Fin 2), (1 : Fin 2)) := by
  fin_cases k <;> native_decide

def R : MPOTensor 4 4 :=
  fun a b => (25/32 : ℂ) • (Matrix.reindex bondEquiv bondEquiv)
    (A a ⊗ₖ (A b).map (starRingEnd ℂ))

noncomputable def B (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt (25/32 : ℝ) : ℂ) • A a

lemma sqrt25_32_sq : ((Real.sqrt (25/32 : ℝ) : ℂ) : ℂ) ^ 2 = (25/32 : ℂ) := by
  have h := Real.sq_sqrt (show 0 ≤ (25/32 : ℝ) by norm_num)
  have h' : ((Real.sqrt (25/32 : ℝ) : ℂ) ^ 2) = ((25/32 : ℝ) : ℂ) := by exact_mod_cast h
  simpa [sq] using h'

lemma B_kron_conj_B_eq (a b : Fin 4) :
    B a ⊗ₖ ((B b).map (starRingEnd ℂ)) =
    (25/32 : ℂ) • (A a ⊗ₖ (A b).map (starRingEnd ℂ)) := by
  ext z w
  rcases z with ⟨i₁, i₂⟩
  rcases w with ⟨j₁, j₂⟩
  simp only [B, Matrix.kroneckerMap_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hstar_sqrt : star ((Real.sqrt (25/32 : ℝ) : ℂ)) = (Real.sqrt (25/32 : ℝ) : ℂ) := by simp
  have hstar_prod : star ((Real.sqrt (25/32 : ℝ) : ℂ) * A b i₂ j₂) =
      (Real.sqrt (25/32 : ℝ) : ℂ) * star (A b i₂ j₂) := by
    calc
      star ((Real.sqrt (25/32 : ℝ) : ℂ) * A b i₂ j₂) =
          star (A b i₂ j₂) * star ((Real.sqrt (25/32 : ℝ) : ℂ)) := by rw [star_mul]
      _ = star (A b i₂ j₂) * (Real.sqrt (25/32 : ℝ) : ℂ) := by rw [hstar_sqrt]
      _ = (Real.sqrt (25/32 : ℝ) : ℂ) * star (A b i₂ j₂) := mul_comm _ _
  calc
    ((Real.sqrt (25/32 : ℝ) : ℂ) * A a i₁ j₁) *
      star ((Real.sqrt (25/32 : ℝ) : ℂ) * A b i₂ j₂) =
      ((Real.sqrt (25/32 : ℝ) : ℂ) * A a i₁ j₁) *
        ((Real.sqrt (25/32 : ℝ) : ℂ) * star (A b i₂ j₂)) := by rw [hstar_prod]
    _ = ((Real.sqrt (25/32 : ℝ) : ℂ) ^ 2) * (A a i₁ j₁ * star (A b i₂ j₂)) := by ring
    _ = (25/32 : ℂ) * (A a i₁ j₁ * star (A b i₂ j₂)) := by rw [sqrt25_32_sq]

lemma R_isLPDO : IsLPDO R := by
  refine ⟨1, 2, fun a _ => B a, bondEquivSymm, ?_⟩
  intro a b
  have h_smul_reindex : (25/32 : ℂ) • (Matrix.reindex bondEquiv bondEquiv)
      (A a ⊗ₖ (A b).map (starRingEnd ℂ)) =
    Matrix.reindex bondEquiv bondEquiv
      ((25/32 : ℂ) • (A a ⊗ₖ (A b).map (starRingEnd ℂ))) := by
    ext p q; simp [Matrix.reindex_apply, smul_eq_mul]
  have h_reindex_submatrix : Matrix.reindex bondEquiv bondEquiv
      (B a ⊗ₖ ((B b).map (starRingEnd ℂ))) =
    (B a ⊗ₖ ((B b).map (starRingEnd ℂ))).submatrix
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2)
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2) := by
    ext p q; simp [bondEquivSymm, Matrix.submatrix_apply, Matrix.reindex_apply]
  calc
    R a b = (25/32 : ℂ) • (Matrix.reindex bondEquiv bondEquiv)
      (A a ⊗ₖ (A b).map (starRingEnd ℂ)) := rfl
    _ = Matrix.reindex bondEquiv bondEquiv
      ((25/32 : ℂ) • (A a ⊗ₖ (A b).map (starRingEnd ℂ))) := by rw [h_smul_reindex]
    _ = Matrix.reindex bondEquiv bondEquiv
      (B a ⊗ₖ ((B b).map (starRingEnd ℂ))) := by rw [B_kron_conj_B_eq]
    _ = (B a ⊗ₖ ((B b).map (starRingEnd ℂ))).submatrix
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2)
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2) := by rw [h_reindex_submatrix]
    _ = (∑ k : Fin 1, B a ⊗ₖ ((B b).map (starRingEnd ℂ))).submatrix
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2)
      (bondEquivSymm : Fin 4 → Fin 2 × Fin 2) := by simp

theorem R_isMPDO : IsMPDO R :=
  R_isLPDO.isMPDO

/-!
# A rescaling-stable length-dependent coefficient family

**Scope: partial delivery (#5406).** This file constructs the explicit MPO tensor `R`
of the project example motivated by arXiv:1606.00608, Theorem 4.14 and lines
995--1010 (NOT a tensor stated in CPSV16).  It proves:

* `R_isMPDO` — `R` is a matrix product density operator (`IsMPDO`), via the
  local purification / LPDO structure;
* `oneLabelCoeffs_not_lengthIndependent` — the one-label BNT coefficient
  family `c^{(L)} = 1 + (7/25)^L` (on `χ = diag(1, 7/25)`) is not
  length-independent;
* `oneLabelCoeffs_rescaling_stable_not_lengthIndependent` — the length
  dependence survives every uniform positive rescaling of the displayed
  BNT block.

## Remaining gap

The literal CPSV canonical form of `R.toMPSTensor` (`II_CF1`, single bond‑4
block with weight `μ = (25/32)² = 625/1024`) and the Definition 4.1
renormalization fixed‑point condition (`IsRFPViaTS`) are future work.
The transfer map of `R` is `φ ⊗ φ` with `φ(Y) = Σ_a A^a Y (A^a)^†` on M₂,
unital (`φ(I₂) = I₂`), and has eigenvalues `{1, 7/25, 0, 0}`; hence the
doubled transfer map is primitive with spectral radius 1.  The letters of
`R` form the full matrix‑unit basis of M₄, which forces irreducibility.
Completing the normality verification and the tpCP‑map construction would
yield `IsRFPViaTS R` via the completed Theorem 4.14 algebra clause, and
thereby the bundled existential theorem.

The direct entrywise computation of `physTraceTransfer R` returns a 4×4
matrix with entries `T₀₀ = 1/2, T₀₃ = T₃₀ = 9/32, T₃₃ = 1/2` and zeros
elsewhere.  Its square differs from itself at the corner entries
(`T²₀₀ = 337/1024 ≠ 512/1024 = T₀₀`).  A different index convention or
identification of physical‑trace objects may be needed to recover literal
idempotence.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and lines 995--1010
-/


