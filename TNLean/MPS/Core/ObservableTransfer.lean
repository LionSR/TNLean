/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import Mathlib.Data.Matrix.Basis

/-!
# Transfer insertions of physical block observables

An observable on a finite physical block induces a linear map on the virtual
matrix algebra. This file contains the common definitions and the elementary
realization of two-sided multiplication by linear combinations of matrix words.

Sources: arXiv:1606.00608, lines 490–496 and 1250–1258;
arXiv:2307.01696, Supplemental Material, proof of Lemma 2.

## References

* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, lines 490–496.
* Malz, Styliaris, Wei, Cirac, arXiv:2307.01696, Supplemental Material, Lemma 2.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The transfer insertion associated with an observable on a block of $L$
physical spins. If $\sigma,\tau:\operatorname{Fin}(L)\to\operatorname{Fin}(d)$
label basis words, then
`physicalObservableTransfer A L O X` equals
$\sum_{\sigma,\tau} O_{\tau,\sigma}\, A^{\sigma} X (A^{\tau})^{\dagger}$.

This is the inserted transfer map $\mathbb{E}_O$ in the two-observable formula
at arXiv:1606.00608, lines 490--496, written as a map on virtual matrices. -/
noncomputable def physicalObservableTransfer (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
    O τ σ • ((LinearMap.mulLeft ℂ (Kraus.evalWord A (List.ofFn σ))).comp
      (LinearMap.mulRight ℂ (Kraus.evalWord A (List.ofFn τ))ᴴ))

/-- The inserted transfer map in coordinates,
`E_O(Z) = ∑_{σ,τ} O_{τσ} A^σ Z (A^τ)†` (arXiv:1606.00608, lines 490--496). -/
theorem physicalObservableTransfer_apply (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L O Z = ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
      O τ σ • (Kraus.evalWord A (List.ofFn σ) * Z * (Kraus.evalWord A (List.ofFn τ))ᴴ) := by
  simp [physicalObservableTransfer, Matrix.mul_assoc]

/-- The inserted transfer map `O ↦ E_O` as a linear map in the observable.

This is the linearity of the observable-to-transfer assignment in the
two-observable formula at arXiv:1606.00608, lines 490--496, and of the map
`E_Q = ∑_{i,j} ⟨i|Q|j⟩ (A^i)^* ⊗ A^j` of arXiv:2307.01696, Supplemental
Material, proof of Lemma 2. -/
noncomputable def physicalObservableTransferₗ (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ →ₗ[ℂ]
      (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) where
  toFun O := physicalObservableTransfer A L O
  map_add' O₁ O₂ := by
    simp only [physicalObservableTransfer, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' c O := by
    simp only [physicalObservableTransfer, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

@[simp] theorem physicalObservableTransferₗ_apply (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    physicalObservableTransferₗ A L O = physicalObservableTransfer A L O := rfl

/-- The inserted transfer map of the product observable built from two
coefficient families `c, e` is the two-sided multiplication
`X ↦ (∑ c_σ A^σ) X (∑ e_τ A^τ)†`, specializing the two-observable formula at
arXiv:1606.00608, lines 490--496. -/
theorem physicalObservableTransfer_coeff_mul (A : MPSTensor d D) (L : ℕ)
    (c e : (Fin L → Fin d) → ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L (fun τ σ ↦ c σ * starRingEnd ℂ (e τ)) X =
      (∑ σ : Fin L → Fin d, c σ • Kraus.evalWord A (List.ofFn σ)) * X *
        (∑ τ : Fin L → Fin d, e τ • Kraus.evalWord A (List.ofFn τ))ᴴ := by
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp only [mul_assoc, Matrix.sum_mul, Algebra.smul_mul_assoc,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
    Matrix.mul_sum, Algebra.mul_smul_comm, Finset.smul_sum, smul_smul, mul_comm]
  rw [Finset.sum_comm]

/-- Matrices in the span of length-`L` words give a physical observable whose
inserted transfer map is their two-sided multiplication. This is the common
observable-realization step in arXiv:1606.00608, lines 1250--1258, and
arXiv:2307.01696, Supplemental Material, proof of Lemma 2. -/
theorem exists_physicalObservableTransfer_mul_of_mem_span (A : MPSTensor d D) (L : ℕ)
    (M N : Matrix (Fin D) (Fin D) ℂ)
    (hM : M ∈ Submodule.span ℂ
      (Set.range fun σ : Fin L → Fin d ↦ Kraus.evalWord A (List.ofFn σ)))
    (hN : N ∈ Submodule.span ℂ
      (Set.range fun σ : Fin L → Fin d ↦ Kraus.evalWord A (List.ofFn σ))) :
    ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ X : Matrix (Fin D) (Fin D) ℂ, physicalObservableTransfer A L O X = M * X * Nᴴ := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hN
  refine ⟨fun τ σ ↦ c σ * starRingEnd ℂ (e τ), fun X ↦ ?_⟩
  rw [physicalObservableTransfer_coeff_mul, hc, he]

end MPSTensor
