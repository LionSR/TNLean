/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LengthIndependentCoefficients
import Mathlib.Analysis.Matrix.Order

/-!
# A rescaling-stable length-dependent coefficient family

**Scope: partial formalization.** This file constructs the explicit MPO tensor `R`
of the project example motivated by arXiv:1606.00608, Theorem 4.14 and lines
995--1010 (NOT a tensor stated in CPSV16).  It proves:

* `physTraceTransfer_R_idempotent` — the physical-trace transfer of `R` is
  idempotent (rank‑1 projector $(25/32)\,|t\rangle\langle t|$ with $t_a = \operatorname{tr}(A^a)$);
* `oneLabelCoeffs_not_lengthIndependent` — the one-label BNT coefficient
  family `c^{(L)} = 1 + (7/25)^L` (on `χ = diag(1, 7/25)`) is not
  length-independent;
* `oneLabelCoeffs_rescaling_stable_not_lengthIndependent` — the length
  dependence survives every uniform positive rescaling `s` of the displayed
  $\chi$ block: the rescaled roots $\{s, 7s/25\}$ give the family
  $c_s^{(L)} = s^L(1 + (7/25)^L)$, which is not length-independent
  for any $s > 0$.

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
with weight `μ = (25/32)² = 625/1024`, eq. II_CF1) and the Definition 4.1
renormalization fixed‑point condition (`IsRFPViaTS`) are future work.
The letters of `R` form the full matrix‑unit basis of M₄ (irreducibility);
the doubled transfer map is `φ ⊗ φ` with `φ(Y) = Σ_a A^a Y (A^a)^†`
unital and having eigenvalues `{1, 7/25, 0, 0}`, hence primitive with
spectral radius 1.  Completing the normality verification and the
tpCP‑map construction yields `IsRFPViaTS R` via Theorem 4.14.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and lines 995--1010
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

open scoped Classical

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

/-- The physical-trace transfer of `R` is idempotent: it is the rank-one
projector $(25/32)\,|t\rangle\langle t|$ with $t_a = \operatorname{tr}(A^a) = (4/5, 4/5, 0, 0)$.  This is
the literal zero-correlation-length identity of arXiv:1606.00608,
Definition 4.2, lines 735--741 (project example). -/
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

/-- The one-label BNT coefficient family `c^{(L)} = 1 + (7/25)^L` is not
independent of the chain length (`c^{(1)} ≠ c^{(2)}`).

Source: arXiv:1606.00608, Theorem 4.14 and lines 995--1010 (the
length-dependence question; project example). -/
theorem oneLabelCoeffs_not_lengthIndependent :
    ¬ oneLabelCoeffs.LengthIndependent := by
  intro h
  exact oneLabelCoeffs_coeff_one_ne_coeff_two
    (h.coeff_eq one_pos (by norm_num) 0 0 0)

/-- The uniform positive rescaling of the displayed one-label $\chi$ block:
the roots $\{1, 7/25\}$ become $\{s, 7s/25\}$.

Source: arXiv:1606.00608, lines 995--1010 (the rescaling question after
Theorem 4.14; the tensor is a project example). -/
def oneLabelChiScaled (s : ℝ) : DiagonalChiFamily (Fin 1) where
  dim _ _ _ := 2
  entry _ _ _ k :=
    if k = (0 : Fin 2) then (s : ℂ) else (s : ℂ) * (lambda : ℂ)

/-- The rescaled $\chi$ block has positive entries for $s > 0$. -/
lemma oneLabelChiScaled_posEntries {s : ℝ} (hs : 0 < s) :
    (oneLabelChiScaled s).PosEntries := by
  intro _ _ _ k
  fin_cases k
  · simp [oneLabelChiScaled, hs]
  · have hlam : (0 : ℝ) < lambda := by norm_num [lambda]
    simp [oneLabelChiScaled]
    rw [show (s : ℂ) * (lambda : ℂ) = ((s * lambda : ℝ) : ℂ) by norm_cast]
    exact_mod_cast mul_pos hs hlam

/-- The coefficient family of the rescaled $\chi$ block. -/
noncomputable def rescaledCoeffs (s : ℝ) : BNTLabelCoefficientFamily (Fin 1) :=
  BNTLabelCoefficientFamily.ofChi (oneLabelChiScaled s)

/-- The one-label coefficient of the rescaled family is
$s^L + (7s/25)^L = s^L(1 + (7/25)^L)$. -/
theorem rescaledCoeffs_coeff (s : ℝ) (L : ℕ) :
    (rescaledCoeffs s).coeff L (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) =
      (s : ℂ) ^ L * ((1 : ℂ) + ((lambda : ℂ) ^ L)) := by
  dsimp [rescaledCoeffs, BNTLabelCoefficientFamily.ofChi,
    DiagonalChiFamily.tracePowerCoeff, oneLabelChiScaled]
  simp [Fin.sum_univ_two, mul_pow]
  ring

/-- The length dependence of the displayed one-label coefficient family
survives every uniform positive rescaling of its $\chi$ block: the
rescaled roots $\{s, 7s/25\}$ cannot both equal one, and the rescaled
family $s^L(1 + (7/25)^L)$ is not length-independent.

Source: arXiv:1606.00608, Theorem 4.14 and lines 995--1010 (the
rescaling-stability question; the tensor is a project example, not a
tensor stated in CPSV16). -/
theorem oneLabelCoeffs_rescaling_stable_not_lengthIndependent (s : ℝ)
    (hs : 0 < s) : ¬ (rescaledCoeffs s).LengthIndependent := by
  intro hLI
  have e12 : (rescaledCoeffs s).coeff 1 (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) =
      (rescaledCoeffs s).coeff 2 (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) :=
    hLI.coeff_eq one_pos (by norm_num) 0 0 0
  have e23 : (rescaledCoeffs s).coeff 2 (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) =
      (rescaledCoeffs s).coeff 3 (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) :=
    hLI.coeff_eq (show (0 : ℕ) < 2 by norm_num) (by norm_num) 0 0 0
  rw [rescaledCoeffs_coeff, rescaledCoeffs_coeff] at e12
  rw [rescaledCoeffs_coeff, rescaledCoeffs_coeff] at e23
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have h1 : (1 : ℂ) + (lambda : ℂ) = (s : ℂ) * ((1 : ℂ) + (lambda : ℂ) ^ 2) :=
    mul_left_cancel₀ hsne (by linear_combination e12)
  have h2 : (1 : ℂ) + (lambda : ℂ) ^ 2 =
      (s : ℂ) * ((1 : ℂ) + (lambda : ℂ) ^ 3) :=
    mul_left_cancel₀ (mul_ne_zero hsne hsne) (by linear_combination e23)
  have key : ((1 : ℂ) + (lambda : ℂ) ^ 2) ^ 2 =
      ((1 : ℂ) + (lambda : ℂ)) * ((1 : ℂ) + (lambda : ℂ) ^ 3) := by
    have m1 := congrArg (fun x => ((1 : ℂ) + (lambda : ℂ) ^ 2) * x) h2
    calc ((1 : ℂ) + (lambda : ℂ) ^ 2) ^ 2
        = ((1 : ℂ) + (lambda : ℂ) ^ 2) * ((1 : ℂ) + (lambda : ℂ) ^ 2) := by ring
      _ = ((1 : ℂ) + (lambda : ℂ) ^ 2) *
            ((s : ℂ) * ((1 : ℂ) + (lambda : ℂ) ^ 3)) := m1
      _ = (s : ℂ) * ((1 : ℂ) + (lambda : ℂ) ^ 2) * ((1 : ℂ) + (lambda : ℂ) ^ 3) := by
          ring
      _ = ((1 : ℂ) + (lambda : ℂ)) * ((1 : ℂ) + (lambda : ℂ) ^ 3) := by
          rw [h1]
  have hlambda : (lambda : ℂ) = (7 / 25 : ℂ) := by norm_num [lambda]
  rw [hlambda] at key
  norm_num at key


/-! ### IsMPDO — positivity of the MPO family

The strategy: factor `mpo R N = (25/32)^N · C ⊙ M` where `C` is the
chain‑OK indicator (rank‑1 PSD) and `M` is the pullback of the Kronecker
power `W_N` of `W` (PSD by congruence).  Their Hadamard product is PSD
by the Schur product theorem [`Matrix.PosSemidef.hadamard`], and scaling
by `(25/32)^N ≥ 0` preserves PSD.

The entrywise formula for `mpo R N` (the only remaining gap) is verified
by direct analysis of the cyclic sum; the bond‑chain constraints collapse
the sum to at most one term.  A fully formal proof of this formula is
in progress. -/

def bit1 : Fin 4 → Fin 2 | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1
def bit2 : Fin 4 → Fin 2 | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1
def coeff' : Fin 2 → Fin 2 → ℂ | 0, 0 => 4/5 | 0, 1 => 3/5 | 1, 0 => 3/5 | 1, 1 => 4/5

def chainOK (N : ℕ) (p : Fin N → Fin 4) : Prop :=
  ∀ n : Fin N, bit2 (p n) = bit1 (p (finRotate N n))

noncomputable def chainIndicator (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  Matrix.of fun p q => by
    classical
    exact if chainOK N p ∧ chainOK N q then (1 : ℂ) else 0

lemma chainIndicator_posSemidef (N : ℕ) : (chainIndicator N).PosSemidef := by
  classical
  let c : (Fin N → Fin 4) → ℂ := fun p => if chainOK N p then (1 : ℂ) else 0
  have h_eq : chainIndicator N = Matrix.vecMulVec c (star c) := by
    ext p q
    dsimp [chainIndicator, c, Matrix.vecMulVec, Matrix.mul_apply, Matrix.of_apply]
    by_cases hp : chainOK N p <;> by_cases hq : chainOK N q
    · simp [hp, hq]
    · simp [hp, hq]
    · simp [hp, hq]
    · simp [hp, hq]
  rw [h_eq]
  exact Matrix.posSemidef_vecMulVec_self_star c

def Wmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(4/5 : ℂ)^2, (3/5 : ℂ)^2; (3/5 : ℂ)^2, (4/5 : ℂ)^2]

def WN (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.of fun a b => ∏ n : Fin N, Wmat (a n) (b n)

open scoped Classical in
lemma wMat_posSemidef : Wmat.PosSemidef := by
  classical
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), (1 : ℂ); (1 : ℂ), (1 : ℂ)]
  have hJ : J.PosSemidef := by
    have hJ_eq : J = Matrix.vecMulVec (fun (_ : Fin 2) => (1 : ℂ)) (star (fun (_ : Fin 2) => (1 : ℂ))) := by
      ext i j; fin_cases i <;> fin_cases j <;> dsimp [J, Matrix.vecMulVec, star] <;> norm_num
    rw [hJ_eq]; exact Matrix.posSemidef_vecMulVec_self_star _
  have hI : ((1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one
  have h_eq : Wmat = ((7 : ℂ)/25) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((9 : ℂ)/25) • J := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Wmat, J]
  rw [h_eq]
  refine Matrix.PosSemidef.add ?_ ?_
  · have h7 : (0 : ℂ) ≤ (7/25 : ℂ) := by positivity
    refine Matrix.PosSemidef.smul hI h7
  · have h9 : (0 : ℂ) ≤ (9/25 : ℂ) := by positivity
    refine Matrix.PosSemidef.smul hJ h9

open scoped Classical in
lemma wN_posSemidef (N : ℕ) : (WN N).PosSemidef := by
  classical
  induction N with
  | zero =>
      classical
      have h_one : WN 0 = (1 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) := by
        ext a b
        have h_eq : a = b := Subsingleton.elim _ _
        subst h_eq; simp [WN, Matrix.of_apply, Matrix.one_apply]
      rw [h_one]
      exact Matrix.PosSemidef.one
  | succ N ih =>
      let e : (Fin (N + 1) → Fin 2) ≃ (Fin N → Fin 2) × Fin 2 :=
      { toFun := fun f => (f ∘ Fin.succ, f 0)
        invFun := fun (g, x) i => Fin.cases x g i
        left_inv := by
          intro f; ext i
          cases i using Fin.cases with
          | zero => rfl
          | succ i => rfl
        right_inv := by intro ⟨g, x⟩; rfl }
      have h_submatrix : (WN (N + 1)) = (Matrix.kroneckerMap (· * ·) (WN N) Wmat).submatrix e e := by
        ext a b
        simp [WN, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          e, Fin.prod_univ_succ, Function.comp, mul_comm]
      rw [h_submatrix]
      exact Matrix.PosSemidef.submatrix (Matrix.PosSemidef.kronecker ih wMat_posSemidef) e

def φ (N : ℕ) (p : Fin N → Fin 4) : Fin N → Fin 2 := fun n => bit1 (p n)

/-
-- Remaining gap: pullbackWN_posSemidef needs the equality pullbackWN N = B * WN N * Bᴴ
def pullbackWN (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  Matrix.of fun p q => (WN N) (φ N p) (φ N q)
-/

-- WORK IN PROGRESS: pullbackWN_posSemidef
-- requires proving pullbackWN N = B * WN N * Bᴴ for B defined as the boundary map.
-- When completed, R_isMPDO follows by the Hadamard product argument.

lemma coeff_sq_eq_Wmat (i j : Fin 2) : (coeff' i j)^2 = Wmat i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff', Wmat]

/-! ### Remaining gap

The entrywise formula `mpo_R_entry_formula` and the pullback equality
`pullbackWN N = B * WN N * Bᴴ` are a work in progress.  When completed,
the main theorem `R_isMPDO` follows by the Hadamard (Schur) product
argument via `Matrix.PosSemidef.hadamard`. -/

end MPOTensor.RescalingStableLengthDependentRFP
