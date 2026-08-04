/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LengthIndependentCoefficients

/-!
# A rescaling-stable length-dependent coefficient family

**Scope: partial deliverable.** This file constructs the explicit MPO tensor `R`
of the project example motivated by arXiv:1606.00608, Theorem 4.14 and lines
995--1010 (NOT a tensor stated in CPSV16).  It proves:

* `physTraceTransfer_R_idempotent` — the physical-trace transfer of `R` is
  idempotent (rank‑1 projector `(25/32)·|t⟩⟨t|` with `t_a = tr(A^a)`);
* `oneLabelCoeffs_not_lengthIndependent` — the one-label BNT coefficient
  family `c^{(L)} = 1 + (7/25)^L` (on `χ = diag(1, 7/25)`) is not
  length-independent;
* `oneLabelCoeffs_rescaling_stable_not_lengthIndependent` — the length
  dependence survives every uniform positive rescaling of the displayed
  BNT block.

## Tensor definition

The four 2×2 letter matrices are scaled matrix units:
```
A⁰ = (4/5) E₀₀,  A¹ = (4/5) E₁₁,  A² = (3/5) E₀₁,  A³ = (3/5) E₁₀.
```
The vertical letters are `B^{ab} = A^a ⊗ conj(A^b)` (Kronecker on the
bond space `Fin 4 ≃ Fin 2 × Fin 2`).  **Undoing the vertical view**
gives an MPO tensor `R : MPOTensor 4 4`:
```
(R p q) a b = (25/32) · (A^a ⊗ conj(A^b))_{p,q}
```
where `(p,q)` are physical indices and `(a,b)` are bond indices.

## Remaining gap

* `IsMPDO R`: the closed operator factors exactly as
  `mpo R N = (25/32)^N · B · W_N · Bᵀ`, where `B` is the boundary partial
  isometry (`BᵀB = 1`) and `W_N(a,b) = ∏_n W (a n) (b n)` with
  `W = !![16/25, 9/25; 9/25, 16/25]`; `W` has eigenvalues `{1, 7/25}` —
  the `χ = diag(1, 7/25)` of the coefficient family.  Positivity follows
  from `W_N = Σ_s (∏_n λ_{s n}) • vecMulVec (e_s) (star (e_s))`
  (Walsh–Hadamard basis, `λ ∈ {1, 7/25}`) and the `B`-congruence.  The
  local-purification (LPDO) route does NOT apply: the undone-vertical
  letters entangle bra- and ket-side labels, so no purification tensor
  exists.  Verified numerically (N = 1, 2, 3: PSD, trace 1).
* The literal CPSV canonical form of `R.toMPSTensor` (single bond‑4 block
with weight `μ = (25/32)² = 625/1024`, eq. II_CF1) and the Definition 4.1
renormalization fixed‑point condition (`IsRFPViaTS`) are future work.
The letters of `R` form the full matrix‑unit basis of M₄ (irreducibility);
the doubled transfer map is `φ ⊗ φ` with `φ(Y) = Σ_a A^a Y (A^a)^†`
unital and having eigenvalues `{1, 7/25, 0, 0}`, hence primitive with
spectral radius 1.  Completing the normality verification and the
tpCP‑map construction yields `IsRFPViaTS R` via Theorem 4.14.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-! ### The four letter matrices -/

def A : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (4/5 : ℂ) • Matrix.single (0 : Fin 2) (0 : Fin 2) 1
  | 1 => (4/5 : ℂ) • Matrix.single (1 : Fin 2) (1 : Fin 2) 1
  | 2 => (3/5 : ℂ) • Matrix.single (0 : Fin 2) (1 : Fin 2) 1
  | 3 => (3/5 : ℂ) • Matrix.single (1 : Fin 2) (0 : Fin 2) 1

lemma A_map_star (k : Fin 4) : (A k).map (starRingEnd ℂ) = A k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.map_apply, starRingEnd_apply]

lemma A_trace (k : Fin 4) : Matrix.trace (A k) = if k = 0 ∨ k = 1 then (4/5 : ℂ) else 0 := by
  fin_cases k <;> simp [A, Matrix.trace] <;> norm_num

/-! ### The MPO tensor (undone-vertical reading) -/

def bondEquiv : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
def bondEquivSymm : Fin 4 ≃ Fin 2 × Fin 2 := bondEquiv.symm

/-- The rescaling-stable length-dependent example.

The vertical letters are `B^{ab} = A^a ⊗ conj(A^b)`.  Undoing the vertical
view gives the MPO tensor `R^{pq}_{ab} = (25/32)·B^{ab}_{pq}`, i.e.
`(R p q) a b = (25/32)·(A^a ⊗ conj(A^b)) (p₁,p₂) (q₁,q₂)` where
`(p₁,p₂) = bondEquiv⁻¹ p` etc.

Source: arXiv:1606.00608, lines 995--1010 (project example). -/

@[simp] lemma bondEquiv_symm_val (k : Fin 4) : bondEquiv.symm k =
    match k with
    | 0 => ((0 : Fin 2), (0 : Fin 2))
    | 1 => ((0 : Fin 2), (1 : Fin 2))
    | 2 => ((1 : Fin 2), (0 : Fin 2))
    | 3 => ((1 : Fin 2), (1 : Fin 2)) := by
  fin_cases k <;> rfl

def R : MPOTensor 4 4 :=
  fun p q a b => (25/32 : ℂ) * (A a ⊗ₖ (A b).map (starRingEnd ℂ))
    (bondEquiv.symm p) (bondEquiv.symm q)

@[simp]
lemma R_apply (p q a b : Fin 4) : R p q a b =
    (25/32 : ℂ) * (A a ⊗ₖ (A b).map (starRingEnd ℂ)) (bondEquiv.symm p) (bondEquiv.symm q) := rfl

/-! ### Physical-trace transfer idempotence -/

lemma physTraceTransfer_R_entry (a b : Fin 4) : physTraceTransfer R a b =
    (25/32 : ℂ) * (Matrix.trace (A a)) * (Matrix.trace (A b)) := by
  dsimp [physTraceTransfer]
  -- sum over p of (25/32)*(A a ⊗ conj A b)(bondEquiv.symm p, bondEquiv.symm p)
  -- The 4 values of bondEquiv.symm p are (0,0), (0,1), (1,0), (1,1)
  -- Expand the Kronecker product: (A a)(i₁,j₁)*conj(A b)(i₂,j₂)
  fin_cases a <;> fin_cases b <;>
    simp [R_apply, Fin.sum_univ_four, Matrix.kroneckerMap_apply,
      A_map_star, Matrix.map_apply, starRingEnd_apply,
      A, Matrix.trace, bondEquiv_symm_val] <;> norm_num

theorem physTraceTransfer_R_idempotent :
    physTraceTransfer R * physTraceTransfer R = physTraceTransfer R := by
  ext a b
  simp only [Matrix.mul_apply, physTraceTransfer_R_entry]
  -- Goal: sum over c of (m·tr(A a)·tr(A c))·(m·tr(A c)·tr(A b)) = m·tr(A a)·tr(A b)
  -- where m = 25/32
  have hsum : (∑ c : Fin 4, (Matrix.trace (A c)) ^ 2) = (32/25 : ℂ) := by
    simp [A_trace, Fin.sum_univ_four]; ring
  calc
    (∑ c : Fin 4, ((25/32 : ℂ) * Matrix.trace (A a) * Matrix.trace (A c)) *
      ((25/32 : ℂ) * Matrix.trace (A c) * Matrix.trace (A b))) =
      (∑ c : Fin 4, ((25/32 : ℂ) ^ 2) * Matrix.trace (A a) * Matrix.trace (A b) *
        (Matrix.trace (A c)) ^ 2) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    _ = ((25/32 : ℂ) ^ 2) * Matrix.trace (A a) * Matrix.trace (A b) *
      (∑ c : Fin 4, (Matrix.trace (A c)) ^ 2) := by
      simp [Finset.mul_sum]
    _ = ((25/32 : ℂ) ^ 2) * Matrix.trace (A a) * Matrix.trace (A b) * (32/25 : ℂ) := by rw [hsum]
    _ = (25/32 : ℂ) * Matrix.trace (A a) * Matrix.trace (A b) := by ring

/-! ### The tensor and its transfer -/


def lambda : ℝ := 7/25

def oneLabelChi : DiagonalChiFamily (Fin 1) where
  dim _ _ _ := 2
  entry _ _ _ k :=
    if k = (0 : Fin 2) then (1 : ℂ) else (lambda : ℂ)

lemma oneLabelChi_posEntries : oneLabelChi.PosEntries := by
  intro _ _ _ k
  fin_cases k
  · simp [oneLabelChi]
  · simp [oneLabelChi, lambda]

noncomputable def oneLabelCoeffs : BNTLabelCoefficientFamily (Fin 1) :=
  BNTLabelCoefficientFamily.ofChi oneLabelChi

theorem oneLabelCoeffs_coeff (L : ℕ) :
    oneLabelCoeffs.coeff L (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) =
    (1 : ℂ) + ((lambda : ℂ) ^ L) := by
  dsimp [oneLabelCoeffs, BNTLabelCoefficientFamily.ofChi,
    DiagonalChiFamily.tracePowerCoeff, oneLabelChi]
  simp [Fin.sum_univ_two]

theorem oneLabelCoeffs_coeff_one_ne_coeff_two :
    oneLabelCoeffs.coeff 1 0 0 0 ≠ oneLabelCoeffs.coeff 2 0 0 0 := by
  rw [oneLabelCoeffs_coeff 1, oneLabelCoeffs_coeff 2]
  have hlambda : (lambda : ℂ) = (7/25 : ℂ) := by norm_num [lambda]
  rw [hlambda]
  norm_num

theorem oneLabelCoeffs_not_lengthIndependent :
    ¬ oneLabelCoeffs.LengthIndependent := by
  intro h
  exact oneLabelCoeffs_coeff_one_ne_coeff_two
    (h.coeff_eq one_pos (by norm_num) 0 0 0)

theorem oneLabelCoeffs_rescaling_stable_not_lengthIndependent :
    ∀ s : ℝ, 0 < s →
      ¬ (∃ (c : BNTLabelCoefficientFamily (Fin 1)),
        (∀ L : ℕ, 0 < L → c.coeff L 0 0 0 = (s : ℂ) * oneLabelCoeffs.coeff L 0 0 0) ∧
        c.LengthIndependent) := by
  intro s hs
  intro ⟨c, hcoeff, hLI⟩
  have h1 : c.coeff 1 0 0 0 = c.coeff 2 0 0 0 :=
    hLI.coeff_eq one_pos (by norm_num) 0 0 0
  have hcoeff1 : c.coeff 1 0 0 0 = (s : ℂ) * oneLabelCoeffs.coeff 1 0 0 0 := hcoeff 1 one_pos
  have hcoeff2 : c.coeff 2 0 0 0 = (s : ℂ) * oneLabelCoeffs.coeff 2 0 0 0 := hcoeff 2 (by norm_num)
  rw [hcoeff1, hcoeff2] at h1
  rw [oneLabelCoeffs_coeff 1, oneLabelCoeffs_coeff 2] at h1
  have hlambda : (lambda : ℂ) = (7/25 : ℂ) := by norm_num [lambda]
  rw [hlambda] at h1
  have hs_nonzero : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have h_contr : (1 : ℂ) + (7/25 : ℂ) = (1 : ℂ) + ((7/25 : ℂ) ^ 2) := by
    apply mul_right_cancel₀ hs_nonzero
    simpa [pow_one] using h1
  norm_num at h_contr

end MPOTensor.RescalingStableLengthDependentRFP
