/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CoefficientPairing
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Hamiltonians that are a shifted multiple of a parent Hamiltonian

A spin-chain Hamiltonian \(H\) often agrees with a parent Hamiltonian up to a
positive factor and an additive constant: \(H+c=s\,H_{\mathrm{parent}}\) with
\(s>0\). Positivity of the parent Hamiltonian then gives \(H\ge-c\), and the
eigenspace of \(H\) for \(-c\) is the kernel of the parent Hamiltonian.

## Main results
* `MPSTensor.isPositive_conj_of_add_eq_smul_parentHamiltonian` : \(H+c\ge0\)
* `MPSTensor.neg_le_of_hasEigenvalue_of_add_eq_smul_parentHamiltonian` : every
  eigenvalue \(\mu\) of \(H\) satisfies \(-c\le\mu\) in the complex order, so it is
  real and at least \(-c\) when \(c\) is real
* `MPSTensor.eigenspace_neg_eq_ker_of_add_eq_smul_parentHamiltonian` : the eigenspace
  of \(H\) for \(-c\) is the kernel of the parent Hamiltonian
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D} {L N : ℕ} {H : NSiteSpace d N →ₗ[ℂ] NSiteSpace d N}
  {c s : ℂ}

/-- If \(H+c=s\,H_{\mathrm{parent}}\) with \(s\ge0\), then \(H+c\), transported to the
\(\ell^2\) space of coefficient vectors, is positive. -/
theorem isPositive_conj_of_add_eq_smul_parentHamiltonian
    (h : H + c • LinearMap.id = s • parentHamiltonian A L N) (hs : 0 ≤ s) :
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘ₗ (H + c • LinearMap.id) ∘ₗ
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).toLinearMap).IsPositive := by
  have h' : (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘ₗ
      (H + c • LinearMap.id) ∘ₗ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).toLinearMap =
      s • ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘ₗ
        parentHamiltonian A L N ∘ₗ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).toLinearMap) := by
    rw [h]
    ext v
    simp
  rw [h']
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [parentHamiltonian_eq_sum_localTerm, Finset.univ_eq_empty, Finset.sum_empty,
      LinearMap.zero_comp, LinearMap.comp_zero, smul_zero]
    exact LinearMap.isPositive_zero
  · have : NeZero N := ⟨hN.ne'⟩
    have hH : (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap ∘ₗ
        parentHamiltonian A L N ∘ₗ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).toLinearMap =
        Matrix.toEuclideanLin (parentRingInteraction A L N).hamiltonian := by
      rw [parentHamiltonian_eq_toLin'_hamiltonian]
      rfl
    rw [hH]
    exact (Matrix.isPositive_toEuclideanLin_iff.mpr
      (posSemidef_hamiltonian_parentRingInteraction A L N)).smul_of_nonneg hs

/-- If \(H+c=s\,H_{\mathrm{parent}}\) with \(s\ge0\), then every eigenvalue \(\mu\) of
\(H\) satisfies \(-c\le\mu\) in the complex order. -/
theorem neg_le_of_hasEigenvalue_of_add_eq_smul_parentHamiltonian
    (h : H + c • LinearMap.id = s • parentHamiltonian A L N) (hs : 0 ≤ s) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue H μ) : -c ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hshift : Module.End.HasEigenvalue (H + c • LinearMap.id) (μ + c) :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 (by
      simp [Module.End.mem_eigenspace_iff.1 hv.1, add_smul]), hv.2⟩
  have := nonneg_of_hasEigenvalue_of_isPositive_conj
    (isPositive_conj_of_add_eq_smul_parentHamiltonian h hs) hshift
  rw [← sub_nonneg, sub_neg_eq_add]
  exact this

/-- If \(H+c=s\,H_{\mathrm{parent}}\) with \(s\ne0\), then the eigenspace of \(H\) for
\(-c\) is the kernel of the parent Hamiltonian. -/
theorem eigenspace_neg_eq_ker_of_add_eq_smul_parentHamiltonian
    (h : H + c • LinearMap.id = s • parentHamiltonian A L N) (hs : s ≠ 0) :
    Module.End.eigenspace H (-c) = LinearMap.ker (parentHamiltonian A L N) := by
  ext v
  have hv := LinearMap.congr_fun h v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, ← smul_eq_zero_iff_right hs, ← hv,
    neg_smul, ← sub_eq_zero, sub_neg_eq_add]

end MPSTensor
