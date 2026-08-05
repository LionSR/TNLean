/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LengthIndependentCoefficients
import TNLean.MPS.MPDO.RFPViaTS
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
  for any $s > 0$;
* `R_isMPDO` — the closed operator family `mpo R N` is positive
  semidefinite for every positive chain length `N` (`R` is an MPDO);
* `wMat_eigenvalue_eq_oneLabelChi_entry` — the two entries of `oneLabelChi`
  are eigenvalues of the local factor `wMat` of the `R_isMPDO`
  factorization, exhibited by explicit eigenvectors (a scope-restricted
  spectral link; see *Remaining gap*);
* `transferMap_A_eigen` — the per-site transfer map `φ(Y) = Σ_a A^a Y (A^a)^†`
  has the explicit eigenvalues `{1, lambda, 0, 0}` claimed in the *Remaining
  gap* section below (identity fixed, `diag(1,-1)` scaled by `lambda`, the
  off-diagonal matrix units annihilated).

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

## Positivity of the closed operator family

`R p q` is the rank-one bond matrix `(25/32) • vecMulVec u_{pq} v_{pq}`
(`R_eq_vecMulVec`), so the closed-chain trace `mpo R N p q` telescopes to a
single cyclic product of consecutive pairings (`mpo_R_entry_formula`):
```
mpo R N p q = (25/32)^N · chainIndicator N p q · wN N (φ N p) (φ N q)
```
where `chainIndicator N` is the rank-one indicator of the cyclic bond-matching
condition `ChainOK`, `φ N` reads a physical-index string through its first
bond bit, and `wN N a b = ∏ n, wMat (a n) (b n)` is the `N`-fold Kronecker
power of `wMat = !![16/25, 9/25; 9/25, 16/25]` (eigenvalues `{1, 7/25}` —
the `χ = diag(1, 7/25)` of the coefficient family).  So `mpo R N` is
`(25/32)^N` times the Hadamard product of `chainIndicator N` (rank-one PSD)
with the pullback of `wN N` along `φ N` (PSD by `Matrix.PosSemidef.submatrix`),
and the Schur product theorem (`Matrix.PosSemidef.hadamard`) gives `R_isMPDO`.
The local-purification (LPDO) route does NOT apply: the undone-vertical
letters entangle bra- and ket-side labels, so no purification tensor exists.

## Remaining gap

* The uniform BNT-label structure-coefficient statement of
  arXiv:1606.00608, Theorem 4.14(ii) for `R` — that `oneLabelCoeffs`
  literally arises from `R`'s same-length product algebra, not only that
  its spectral data matches (`wMat_eigenvalue_eq_oneLabelChi_entry`) —
  requires the `AlgebraStructureData` witness apparatus of
  `TNLean/MPS/MPDO/BNTTheoremWitness.lean`, which in turn needs
  `IsRFPViaTS R` (below).  Documented in
  `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.
* The literal CPSV canonical form of `R.toMPSTensor` (single bond‑4 block
with weight `μ = (25/32)² = 625/1024`, eq. II_CF1) and the Definition 4.1
renormalization fixed‑point condition (`IsRFPViaTS`) are future work.
The letters of `R` form the full matrix‑unit basis of M₄ (irreducibility);
the doubled transfer map is `φ ⊗ φ` with `φ(Y) = Σ_a A^a Y (A^a)^†`
unital and having eigenvalues `{1, 7/25, 0, 0}` (`transferMap_A_eigen`),
hence primitive with spectral radius 1.  Completing the irreducibility
argument (the Kronecker products `A^a ⊗ conj(A^b)` span `M₄(ℂ)`), the
Kronecker-product factorization of `transferMap R.toMPSTensor` in terms of
`φ`, the primitivity and spectral-radius-one lemmas for the doubled map, and
the `tpCP`-map construction yields `IsRFPViaTS R` via Theorem 4.14.

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

lemma bondEquiv_val (x y : Fin 2) : bondEquiv (x, y) =
    match x, y with
    | 0, 0 => (0 : Fin 4)
    | 0, 1 => (1 : Fin 4)
    | 1, 0 => (2 : Fin 4)
    | 1, 1 => (3 : Fin 4) := by
  fin_cases x <;> fin_cases y <;> rfl

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

Source: arXiv:1606.00608, lines 995--1010 pose the length-dependence
question after Theorem 4.14; the rescaling-stability strengthening is a
project-internal follow-up motivated by that question (the tensor is a
project example). -/
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
length-dependence question); the rescaling-stability strengthening is a
project-internal follow-up motivated by that question (the tensor is a
project example, not a tensor stated in CPSV16). -/
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
power `wN N` of `wMat` (PSD by congruence).  Their Hadamard product is PSD
by the Schur product theorem, and scaling by `(25/32)^N ≥ 0` preserves PSD.

The entrywise formula for `mpo R N` is `mpo_R_entry_formula`, proved by
direct analysis of the cyclic sum: the bond‑chain constraints collapse the
sum to at most one term.  Positivity is `R_isMPDO`. -/

/-- The first bit of a bond label `k : Fin 4` under the Kronecker
identification `bondEquiv : Fin 2 × Fin 2 ≃ Fin 4`:
`bit1 k = (bondEquiv.symm k).1` (`bit1_eq_bondEquiv_symm_fst`).
Together with `bit2` it reads a bond
label as the pair of bits indexing the two tensor factors of the vertical
(Kronecker) reading `B^{ab} = A^a ⊗ conj(A^b)`.

Project example; not from CPSV16. -/
def bit1 : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- The second bit of a bond label `k : Fin 4` under `bondEquiv`:
`bit2 k = (bondEquiv.symm k).2` (`bit2_eq_bondEquiv_symm_snd`).
See `bit1`.

Project example; not from CPSV16. -/
def bit2 : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1

/-- The first bit of a bond label is the first component of its preimage
under `bondEquiv`. -/
@[simp] lemma bit1_eq_bondEquiv_symm_fst (k : Fin 4) :
    bit1 k = (bondEquiv.symm k).1 := by
  fin_cases k <;> rfl

/-- The second bit of a bond label is the second component of its preimage
under `bondEquiv`. -/
@[simp] lemma bit2_eq_bondEquiv_symm_snd (k : Fin 4) :
    bit2 k = (bondEquiv.symm k).2 := by
  fin_cases k <;> rfl

/-- The entrywise positive square root of `wMat` (`coeff_sq_eq_wMat`).  The
values `4/5` and `3/5` are the scaling factors already encoded in the
letter matrices `A`: `coeff' i j` is the unique nonzero entry of the
letter supported on the matrix unit `E_{ij}`, namely `4/5` for the
diagonal letters `A 0`, `A 1` and `3/5` for the off-diagonal letters
`A 2`, `A 3`; the consistency check `A_entry_eq_coeff'` ties these values
back to `A`.

Project example; not from CPSV16. -/
def coeff' : Fin 2 → Fin 2 → ℂ
  | 0, 0 => 4/5
  | 0, 1 => 3/5
  | 1, 0 => 3/5
  | 1, 1 => 4/5

/-- Consistency of the explicit values in `coeff'` with the letter
matrices `A`: every nonzero entry of every letter `A a` at position
`(r, c)` equals `coeff' r c`. -/
lemma A_entry_eq_coeff' {a : Fin 4} {r c : Fin 2} (h : A a r c ≠ 0) :
    A a r c = coeff' r c := by
  fin_cases a <;> fin_cases r <;> fin_cases c <;> simp_all [A, coeff']

/-- The cyclic bond-matching condition on a physical-index string
`p : Fin N → Fin 4`: the second bit of each letter equals the first bit of
the next letter around the ring (`bit2 (p n) = bit1 (p (n + 1))`, with the
successor given by `finRotate N`).  This closed-chain constraint
collapses the bond sum in the entrywise formula for `mpo R N` to at most
one term.

Project example; not from CPSV16. -/
def ChainOK (N : ℕ) (p : Fin N → Fin 4) : Prop :=
  ∀ n : Fin N, bit2 (p n) = bit1 (p (finRotate N n))

/-- `ChainOK N p` is decidable: it is a `Fin N`-indexed universal
quantification of equalities between `Fin 2` values. -/
instance decidableChainOK (N : ℕ) (p : Fin N → Fin 4) : Decidable (ChainOK N p) :=
  inferInstanceAs (Decidable (∀ n : Fin N, bit2 (p n) = bit1 (p (finRotate N n))))

/-- The indicator matrix of the cyclic bond-matching condition:
`(chainIndicator N) p q = 1` if both `p` and `q` satisfy `ChainOK N`, and
`0` otherwise.  It is the rank-one matrix `vecMulVec c (star c)` for the
indicator vector `c` of `ChainOK N`, hence positive semidefinite
(`chainIndicator_posSemidef`); in the planned factorization of `mpo R N`
it is the chain-OK factor `C`.

Project example; not from CPSV16. -/
noncomputable def chainIndicator (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  Matrix.of fun p q => if ChainOK N p ∧ ChainOK N q then (1 : ℂ) else 0

/-- The chain-OK indicator matrix is positive semidefinite: it is the
rank-one matrix `vecMulVec c (star c)` for the `ChainOK` indicator vector
`c`. -/
lemma chainIndicator_posSemidef (N : ℕ) : (chainIndicator N).PosSemidef := by
  let c : (Fin N → Fin 4) → ℂ := fun p => if ChainOK N p then (1 : ℂ) else 0
  have h_eq : chainIndicator N = Matrix.vecMulVec c (star c) := by
    ext p q
    dsimp [chainIndicator, c, Matrix.vecMulVec, Matrix.mul_apply, Matrix.of_apply]
    by_cases hp : ChainOK N p <;> by_cases hq : ChainOK N q
    · simp [hp, hq]
    · simp [hp, hq]
    · simp [hp, hq]
    · simp [hp, hq]
  rw [h_eq]
  exact Matrix.posSemidef_vecMulVec_self_star c

/-- The local factor `wMat = !![16/25, 9/25; 9/25, 16/25]` of the
Kronecker-power factorization of the closed operator, entrywise the
square of `coeff'` (`coeff_sq_eq_wMat`).  Its eigenvalues are `1` and
`7/25` — the `χ = diag(1, 7/25)` of the one-label coefficient family
`oneLabelChi`.

Project example; not from CPSV16. -/
def wMat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(4/5 : ℂ)^2, (3/5 : ℂ)^2; (3/5 : ℂ)^2, (4/5 : ℂ)^2]

/-- The `N`-fold Kronecker power of `wMat`, entrywise:
`wN N a b = ∏ n, wMat (a n) (b n)`.  The realized factorization of the
closed operator (`mpo_R_entry_formula`) is `(25/32)^N` times the Hadamard
product of the chain-OK indicator with the pullback of `wN N` along `φ N`
(no boundary map is constructed).

Project example; not from CPSV16. -/
def wN (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.of fun a b => ∏ n : Fin N, wMat (a n) (b n)

/-- `wMat` is positive semidefinite: `wMat = (7/25) • 1 + (9/25) • J` with
`J = !![1, 1; 1, 1]` rank-one PSD — the spectral decomposition with
eigenvalues `1` and `7/25`. -/
lemma wMat_posSemidef : wMat.PosSemidef := by
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), (1 : ℂ); (1 : ℂ), (1 : ℂ)]
  have hJ : J.PosSemidef := by
    have hJ_eq : J = Matrix.vecMulVec (fun (_ : Fin 2) => (1 : ℂ))
        (star (fun (_ : Fin 2) => (1 : ℂ))) := by
      ext i j; fin_cases i <;> fin_cases j <;> dsimp [J, Matrix.vecMulVec, star] <;> norm_num
    rw [hJ_eq]; exact Matrix.posSemidef_vecMulVec_self_star _
  have hI : ((1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one
  have h_eq : wMat = ((7 : ℂ)/25) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((9 : ℂ)/25) • J := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [wMat, J]
  rw [h_eq]
  refine Matrix.PosSemidef.add ?_ ?_
  · have h7 : (0 : ℂ) ≤ (7/25 : ℂ) := by positivity
    refine Matrix.PosSemidef.smul hI h7
  · have h9 : (0 : ℂ) ≤ (9/25 : ℂ) := by positivity
    refine Matrix.PosSemidef.smul hJ h9

/-- The uniform Walsh–Hadamard vector `![1, 1]` is a fixed point of `wMat`
(eigenvalue `1`). -/
lemma wMat_mulVec_ones : wMat.mulVec ![1, 1] = (1 : ℂ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, wMat, Fin.sum_univ_two] <;> norm_num

/-- The alternating Walsh–Hadamard vector `![1, -1]` is an eigenvector of
`wMat` with eigenvalue `lambda = 7/25`. -/
lemma wMat_mulVec_alt : wMat.mulVec ![1, -1] = (lambda : ℂ) • ![1, -1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, wMat, Fin.sum_univ_two, lambda] <;> norm_num

/-- **The two entries of `oneLabelChi` are eigenvalues of `wMat`, exhibited
by explicit eigenvectors.** For each `k : Fin 2`, `oneLabelChi.entry 0 0 0 k`
(`1` at `k = 0`, `lambda` at `k = 1`) is an eigenvalue of `wMat`, witnessed
by the Walsh–Hadamard eigenvectors `![1, 1]` and `![1, -1]`.  This
identifies the local factor of the `R_isMPDO` factorization (`wMat`, via
`coeff_sq_eq_wMat`) with the one-label `χ` block `oneLabelChi` declared
independently in this file.

**Scope restriction (partial BNT-coefficient link):** this identifies the
*spectral data* of `wMat` with `oneLabelChi`'s entries; it is not the
uniform BNT-label structure-coefficient statement of arXiv:1606.00608,
Theorem 4.14(ii) (which requires the `AlgebraStructureData` witness that
`R`'s same-length product algebra realizes `oneLabelCoeffs`).  That
construction needs `IsRFPViaTS R`, itself future work (module docstring,
*Remaining gap*).  Documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`. -/
theorem wMat_eigenvalue_eq_oneLabelChi_entry (k : Fin 2) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      wMat.mulVec v = (oneLabelChi.entry 0 0 0 k) • v := by
  fin_cases k
  · exact ⟨![1, 1], by simp, by simpa [oneLabelChi] using wMat_mulVec_ones⟩
  · refine ⟨![1, -1], by simp, ?_⟩
    simpa [oneLabelChi] using wMat_mulVec_alt

/-- **The per-site transfer map `φ(Y) = Σ_a A^a Y (A^a)^†` is unital.**
`φ` is `MPSTensor.transferMap A`, viewing the letter family `A` as an
`MPSTensor 4 2`. -/
theorem transferMap_A_one : MPSTensor.transferMap A 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPSTensor.transferMap_apply, Fin.sum_univ_four, A] <;> norm_num

/-- `φ` scales the traceless diagonal `diag(1, -1)` by `lambda = 7/25`. -/
theorem transferMap_A_diag_alt :
    MPSTensor.transferMap A !![(1 : ℂ), 0; 0, -1] =
      (lambda : ℂ) • !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPSTensor.transferMap_apply, Fin.sum_univ_four, A, lambda] <;> norm_num

/-- `φ` annihilates the off-diagonal matrix unit `E₀₁`. -/
theorem transferMap_A_single01 :
    MPSTensor.transferMap A (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MPSTensor.transferMap_apply, Fin.sum_univ_four, A]

/-- `φ` annihilates the off-diagonal matrix unit `E₁₀`. -/
theorem transferMap_A_single10 :
    MPSTensor.transferMap A (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MPSTensor.transferMap_apply, Fin.sum_univ_four, A]

/-- **The explicit eigenvalues of `φ` (`MPSTensor.transferMap A`).** The
identity is fixed (eigenvalue `1`), the traceless diagonal `diag(1, -1)` is
scaled by `lambda = 7/25` (eigenvalue `lambda`), and the off-diagonal matrix
units `E₀₁`, `E₁₀` are annihilated (eigenvalue `0`).  Together `{1, lambda,
0, 0}` are exactly the eigenvalues asserted for `φ` in the module docstring
(*Remaining gap*).

**Scope restriction (transfer-map eigenvalue groundwork):** this
characterizes the per-site map `φ`, not the doubled transfer map of
`R.toMPSTensor` itself, nor the primitivity, spectral-radius-one, and
irreducibility lemmas needed for `IsNormalTensor` and the literal CPSV
canonical form (`MPSTensor.IsCPSVCanonicalForm`).  Those require the
Kronecker-product factorization of `transferMap R.toMPSTensor` in terms of
`φ`, which is future work; see the module docstring `Remaining gap`
section and `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`. -/
theorem transferMap_A_eigen :
    MPSTensor.transferMap A 1 = (1 : ℂ) • 1 ∧
      MPSTensor.transferMap A !![(1 : ℂ), 0; 0, -1] =
        (lambda : ℂ) • !![(1 : ℂ), 0; 0, -1] ∧
      MPSTensor.transferMap A (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) =
        (0 : ℂ) • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) ∧
      MPSTensor.transferMap A (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)) =
        (0 : ℂ) • Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) :=
  ⟨by rw [transferMap_A_one, one_smul],
    transferMap_A_diag_alt,
    by rw [transferMap_A_single01, zero_smul],
    by rw [transferMap_A_single10, zero_smul]⟩

/-- The Kronecker power `wN N` is positive semidefinite: by induction on
`N`, `wN (N + 1)` is a submatrix of the Kronecker product `wN N ⊗ wMat`
of positive semidefinite matrices, along the last-coordinate peeling
equivalence `Fin.succFunEquiv`. -/
lemma wN_posSemidef (N : ℕ) : (wN N).PosSemidef := by
  induction N with
  | zero =>
      have h_one : wN 0 = (1 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) := by
        ext a b
        have h_eq : a = b := Subsingleton.elim _ _
        subst h_eq; simp [wN, Matrix.of_apply]
      rw [h_one]
      exact Matrix.PosSemidef.one
  | succ N ih =>
      let e : (Fin (N + 1) → Fin 2) ≃ (Fin N → Fin 2) × Fin 2 :=
        Fin.succFunEquiv (Fin 2) N
      have h_fst : ∀ f : Fin (N + 1) → Fin 2, (e f).1 = f ∘ Fin.castSucc :=
        fun f => funext fun i => rfl
      have h_snd : ∀ f : Fin (N + 1) → Fin 2, (e f).2 = f (Fin.last N) :=
        fun f => rfl
      have h_submatrix : (wN (N + 1)) =
          (Matrix.kroneckerMap (· * ·) (wN N) wMat).submatrix e e := by
        ext a b
        simp [wN, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          h_fst, h_snd, Fin.prod_univ_castSucc, Function.comp_apply]
      rw [h_submatrix]
      exact Matrix.PosSemidef.submatrix (Matrix.PosSemidef.kronecker ih wMat_posSemidef) e

/-- The pullback map extracting the first-bit string of a physical-index
string: `(φ N p) n = bit1 (p n)`.  In the planned factorization it pulls
`wN N` back to the `(Fin N → Fin 4)`-indexed space as
`Matrix.of fun p q => (wN N) (φ N p) (φ N q)`.

Project example; not from CPSV16. -/
def φ (N : ℕ) (p : Fin N → Fin 4) : Fin N → Fin 2 := fun n => bit1 (p n)

/-- `wMat` is the entrywise square of `coeff'`: the local factor's entries
are the squared magnitudes of the letter-matrix entries. -/
lemma coeff_sq_eq_wMat (i j : Fin 2) : (coeff' i j)^2 = wMat i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff', wMat]

/-! ### The entrywise formula for `mpo R N` and `IsMPDO R` -/

/-- Each letter matrix `A b` has real entries, so its entries are unaffected
by complex conjugation. -/
lemma A_star_eq (b : Fin 4) (i j : Fin 2) : star (A b i j) = A b i j := by
  have h := congrFun (congrFun (A_map_star b) i) j
  simpa [Matrix.map_apply] using h

/-- The bond matrix `R p q` is the rank-one outer product of the letter-column
vectors `u_{pq} a = A a (bit1 p) (bit1 q)` and `v_{pq} b = A b (bit2 p) (bit2 q)`,
scaled by `25/32`.  This is the rank-one structure underlying the closed-chain
trace factorization of `mpo R N`.

Project example; not from CPSV16. -/
lemma R_eq_vecMulVec (p q : Fin 4) :
    R p q = (25/32 : ℂ) • Matrix.vecMulVec (fun a => A a (bit1 p) (bit1 q))
      (fun b => A b (bit2 p) (bit2 q)) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, R_apply,
    Matrix.kroneckerMap_apply, Matrix.map_apply, starRingEnd_apply,
    ← bit1_eq_bondEquiv_symm_fst, ← bit2_eq_bondEquiv_symm_snd]
  rw [A_star_eq]

/-- The dot product of two `A`-letter column vectors collapses: it equals
`wMat r1 c1` when the target positions coincide (`r1 = r2` and `c1 = c2`), and
vanishes otherwise.  Each letter `A b` is a scaled matrix unit, nonzero at a
unique position, so the sum over `b` has at most one nonzero term.

Project example; not from CPSV16. -/
lemma dotProduct_A_col (r1 c1 r2 c2 : Fin 2) :
    (fun b : Fin 4 => A b r1 c1) ⬝ᵥ (fun b : Fin 4 => A b r2 c2) =
      if r1 = r2 ∧ c1 = c2 then wMat r1 c1 else 0 := by
  fin_cases r1 <;> fin_cases c1 <;> fin_cases r2 <;> fin_cases c2 <;>
    simp [dotProduct, Fin.sum_univ_four, A, wMat] <;> norm_num

/-- **Open-chain rank-one product formula.** For a length-`(n + 1)` chain of
rank-one matrices `c • vecMulVec (u i) (v i)`, the ordinary (non-cyclic)
matrix product telescopes to `c ^ (n + 1)` times the product of the
intermediate pairings `v i ⬝ᵥ u i.succ`, times the outer rank-one matrix built
from the first and last vectors of the chain.

Project example; not from CPSV16. -/
lemma prod_smul_vecMulVec_ofFn (c : ℂ) :
    ∀ (n : ℕ) (u v : Fin (n + 1) → Fin 4 → ℂ),
      (List.ofFn fun i : Fin (n + 1) => c • Matrix.vecMulVec (u i) (v i)).prod =
        c ^ (n + 1) • ((∏ i : Fin n, v i.castSucc ⬝ᵥ u i.succ) •
          Matrix.vecMulVec (u 0) (v (Fin.last n))) := by
  intro n
  induction n with
  | zero => intro u v; simp
  | succ n ih =>
      intro u v
      rw [List.ofFn_succ, List.prod_cons,
        ih (fun i => u i.succ) (fun i => v i.succ)]
      have e0 : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := Fin.ext (by simp)
      have e1 : (Fin.last n : Fin (n + 1)).succ = Fin.last (n + 1) := Fin.ext (by simp)
      have e2 : ∀ i : Fin n,
          (i.castSucc : Fin (n + 1)).succ = (i.succ : Fin (n + 1)).castSucc :=
        fun i => Fin.ext (by simp)
      simp only [e1]
      simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.vecMulVec_mul_vecMulVec,
        Matrix.vecMulVec_smul]
      rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => v i.castSucc ⬝ᵥ u i.succ), ← e0]
      have hprod :
          (∏ i : Fin n, v (i.castSucc : Fin (n + 1)).succ ⬝ᵥ u (i.succ : Fin (n + 1)).succ) =
          ∏ i : Fin n, v (i.succ : Fin (n + 1)).castSucc ⬝ᵥ u (i.succ : Fin (n + 1)).succ :=
        Finset.prod_congr rfl fun i _ => by rw [e2 i]
      rw [hprod]
      congr 1
      ring

/-- The cyclic-bond pairing across a single step: the dot product of the
second-bit-indexed vector at `p n, q n` with the first-bit-indexed vector at
`p (finRotate N n), q (finRotate N n)` collapses to `wMat` at the second bits
when both steps of the bond chain match, and vanishes otherwise.

Project example; not from CPSV16. -/
lemma dotProduct_A_col_step {N : ℕ} (p q : Fin N → Fin 4) (n : Fin N) :
    (fun b : Fin 4 => A b (bit2 (p n)) (bit2 (q n))) ⬝ᵥ
        (fun b : Fin 4 => A b (bit1 (p (finRotate N n))) (bit1 (q (finRotate N n)))) =
      if bit2 (p n) = bit1 (p (finRotate N n)) ∧ bit2 (q n) = bit1 (q (finRotate N n))
        then wMat (bit2 (p n)) (bit2 (q n)) else 0 :=
  dotProduct_A_col _ _ _ _

/-- The one-step rotation `finRotate (N + 1)` sends the embedding `i.castSucc`
of `i : Fin N` to `i.succ`, matching the ordinary (non-wraparound) successor
step of the bond chain. -/
lemma finRotate_succ_castSucc {N : ℕ} (i : Fin N) :
    finRotate (N + 1) i.castSucc = i.succ := by
  have h := finRotate_of_lt (n := N) i.isLt
  have e1 : (⟨(i : ℕ), i.isLt.trans_le N.le_succ⟩ : Fin (N + 1)) = i.castSucc := Fin.ext rfl
  have e2 : (⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) = i.succ := Fin.ext rfl
  rw [e1, e2] at h
  exact h

/-- **Entrywise formula for the closed MPO operator.** For a positive chain
length `N`, the `(p, q)` matrix element of `mpo R N` is `(25/32)^N` times the
chain-OK indicator times the pullback of the `N`-fold Kronecker power `wN N`
along the first-bit reading `φ N`.

This is the central combinatorial identity behind `R_isMPDO`: the closed
trace of the rank-one bond-matrix chain collapses to a single term exactly
when the bond-matching condition `ChainOK` holds on both the ket and the bra
index strings.

Project example; not from CPSV16. -/
theorem mpo_R_entry_formula {N : ℕ} (hN : 0 < N) (p q : Fin N → Fin 4) :
    mpo R N p q = (25/32 : ℂ) ^ N * chainIndicator N p q * wN N (φ N p) (φ N q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  have hRstep : ∀ i : Fin (n + 1), R (p i) (q i) =
      (25/32 : ℂ) • Matrix.vecMulVec (fun a => A a (bit1 (p i)) (bit1 (q i)))
        (fun b => A b (bit2 (p i)) (bit2 (q i))) := fun i => R_eq_vecMulVec (p i) (q i)
  simp only [hRstep]
  rw [prod_smul_vecMulVec_ofFn (25/32 : ℂ) n
    (fun i => fun a => A a (bit1 (p i)) (bit1 (q i)))
    (fun i => fun b => A b (bit2 (p i)) (bit2 (q i)))]
  rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp only [smul_eq_mul]
  have hlast :
      (fun a : Fin 4 => A a (bit1 (p 0)) (bit1 (q 0))) ⬝ᵥ
          (fun b : Fin 4 => A b (bit2 (p (Fin.last n))) (bit2 (q (Fin.last n)))) =
        (fun b : Fin 4 => A b (bit2 (p (Fin.last n))) (bit2 (q (Fin.last n)))) ⬝ᵥ
          (fun a : Fin 4 => A a (bit1 (p 0)) (bit1 (q 0))) :=
    dotProduct_comm _ _
  rw [hlast]
  -- combine the open-chain pairing product with the wraparound term into a
  -- single cyclic product indexed by `Fin (n + 1)`, driven by `finRotate`.
  set g : Fin (n + 1) → ℂ := fun i =>
      (fun b : Fin 4 => A b (bit2 (p i)) (bit2 (q i))) ⬝ᵥ
        (fun a : Fin 4 => A a (bit1 (p (finRotate (n + 1) i))) (bit1 (q (finRotate (n + 1) i))))
    with hg
  have hgterm : ∀ i : Fin (n + 1), g i =
      if bit2 (p i) = bit1 (p (finRotate (n + 1) i)) ∧ bit2 (q i) = bit1 (q (finRotate (n + 1) i))
        then wMat (bit2 (p i)) (bit2 (q i)) else 0 :=
    fun i => dotProduct_A_col_step p q i
  have hstep : ∀ i : Fin n,
      (fun b : Fin 4 => A b (bit2 (p i.castSucc)) (bit2 (q i.castSucc))) ⬝ᵥ
          (fun a : Fin 4 => A a (bit1 (p i.succ)) (bit1 (q i.succ))) = g i.castSucc := by
    intro i
    simp only [hg, finRotate_succ_castSucc]
  have hlaststep :
      (fun b : Fin 4 => A b (bit2 (p (Fin.last n))) (bit2 (q (Fin.last n)))) ⬝ᵥ
          (fun a : Fin 4 => A a (bit1 (p 0)) (bit1 (q 0))) = g (Fin.last n) := by
    simp only [hg, finRotate_last]
  have hcombine :
      (∏ i : Fin n, (fun b : Fin 4 => A b (bit2 (p i.castSucc)) (bit2 (q i.castSucc))) ⬝ᵥ
          (fun a : Fin 4 => A a (bit1 (p i.succ)) (bit1 (q i.succ)))) *
        ((fun b : Fin 4 => A b (bit2 (p (Fin.last n))) (bit2 (q (Fin.last n)))) ⬝ᵥ
          (fun a : Fin 4 => A a (bit1 (p 0)) (bit1 (q 0)))) = ∏ i : Fin (n + 1), g i := by
    rw [Fin.prod_univ_castSucc]
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => hstep i) hlaststep
  rw [hcombine]
  have hmain : (∏ i : Fin (n + 1), g i) =
      chainIndicator (n + 1) p q * wN (n + 1) (φ (n + 1) p) (φ (n + 1) q) := by
    by_cases hChain : ChainOK (n + 1) p ∧ ChainOK (n + 1) q
    · have hall : ∀ i : Fin (n + 1), g i = wMat (bit2 (p i)) (bit2 (q i)) := fun i => by
        rw [hgterm, if_pos ⟨hChain.1 i, hChain.2 i⟩]
      have hprodeq : (∏ i : Fin (n + 1), g i) =
          ∏ i : Fin (n + 1), wMat (bit2 (p i)) (bit2 (q i)) :=
        Finset.prod_congr rfl fun i _ => hall i
      have hrotate : (∏ i : Fin (n + 1), wMat (bit2 (p i)) (bit2 (q i))) =
          ∏ i : Fin (n + 1),
            wMat (bit1 (p (finRotate (n + 1) i))) (bit1 (q (finRotate (n + 1) i))) :=
        Finset.prod_congr rfl fun i _ => by rw [hChain.1 i, hChain.2 i]
      have hreindex :
          (∏ i : Fin (n + 1),
              wMat (bit1 (p (finRotate (n + 1) i))) (bit1 (q (finRotate (n + 1) i)))) =
            ∏ j : Fin (n + 1), wMat (bit1 (p j)) (bit1 (q j)) :=
        Equiv.prod_comp (finRotate (n + 1)) (fun j => wMat (bit1 (p j)) (bit1 (q j)))
      have hwNeq : wN (n + 1) (φ (n + 1) p) (φ (n + 1) q) =
          ∏ j : Fin (n + 1), wMat (bit1 (p j)) (bit1 (q j)) := by
        simp [wN, φ, Matrix.of_apply]
      have hchainInd : chainIndicator (n + 1) p q = 1 := by
        simp [chainIndicator, hChain.1, hChain.2]
      rw [hprodeq, hrotate, hreindex, ← hwNeq, hchainInd, one_mul]
    · have hchainInd : chainIndicator (n + 1) p q = 0 := by
        simp [chainIndicator, hChain]
      rw [hchainInd, zero_mul]
      rw [not_and_or] at hChain
      rcases hChain with hp | hq
      · unfold ChainOK at hp
        push Not at hp
        obtain ⟨i0, hi0⟩ := hp
        exact Finset.prod_eq_zero (Finset.mem_univ i0)
          (by rw [hgterm, if_neg (fun h => hi0 h.1)])
      · unfold ChainOK at hq
        push Not at hq
        obtain ⟨i0, hi0⟩ := hq
        exact Finset.prod_eq_zero (Finset.mem_univ i0)
          (by rw [hgterm, if_neg (fun h => hi0 h.2)])
  rw [hmain, pow_succ]
  ring

/-- **`R` is an MPDO.** The closed operator `mpo R N` is positive
semidefinite for every positive chain length `N`: it factors as
`(25/32)^N` times the Hadamard product of the chain-OK indicator (rank-one
PSD) with the pullback of the `N`-fold Kronecker power of `wMat` (PSD by
congruence), and the Hadamard product of PSD matrices is PSD by the Schur
product theorem.

Source: arXiv:1606.00608, Theorem 4.14 and lines 995--1010 (project
example; the positivity of this MPO family is a project-internal
verification, not a tensor stated in CPSV16). -/
theorem R_isMPDO : IsMPDO R := by
  intro N hN
  have key : mpo R N =
      (25/32 : ℂ) ^ N • (chainIndicator N ⊙ (wN N).submatrix (φ N) (φ N)) := by
    ext p q
    rw [mpo_R_entry_formula hN p q]
    simp [Matrix.smul_apply, Matrix.hadamard_apply, Matrix.submatrix_apply, mul_assoc]
  rw [key]
  exact ((chainIndicator_posSemidef N).hadamard ((wN_posSemidef N).submatrix (φ N))).smul
    (by positivity)

/-! ### IsRFPViaTS — the tp-CP renormalization maps

The physical index `Fin 4` of `R` factors through the same bit reading used
above: a physical index `p` carries the pair `(bit1 p, bit2 p)`.  `combine p q`
glues the first bit of `p` to the second bit of `q`, and `gate p q` is the
bond-matching condition between two consecutive letters.  The two-site
physical operator `physClose2 R X` is a rescaled, gate-restricted pullback of
the one-site physical operator `physClose1 R X` along `combine`. -/

/-- The physical index gluing the first bit of `p` to the second bit of `q`. -/
def combine (p q : Fin 4) : Fin 4 := bondEquiv (bit1 p, bit2 q)

@[simp] lemma bit1_combine (p q : Fin 4) : bit1 (combine p q) = bit1 p := by
  simp [combine, bit1_eq_bondEquiv_symm_fst]

@[simp] lemma bit2_combine (p q : Fin 4) : bit2 (combine p q) = bit2 q := by
  simp [combine, bit2_eq_bondEquiv_symm_snd]

/-- The bond-matching condition between two consecutive physical letters:
the second bit of `p` equals the first bit of `q`. -/
def gate (p q : Fin 4) : Prop := bit2 p = bit1 q

instance decidableGate (p q : Fin 4) : Decidable (gate p q) :=
  inferInstanceAs (Decidable (bit2 p = bit1 q))

/-- The one-site physical operator of `R`, as a bilinear pairing of the
letter-column vectors through `X`: `physClose1 R X i j = (25/32) *
(u_{ij} ⬝ᵥ (v_{ij} ᵥ* X))`. -/
lemma physClose1_R_entry (X : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    physClose1 R X i j = (25/32 : ℂ) *
      ((fun a => A a (bit1 i) (bit1 j)) ⬝ᵥ
        ((fun b => A b (bit2 i) (bit2 j)) ᵥ* X)) := by
  rw [physClose1_apply, R_eq_vecMulVec, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, smul_eq_mul]

/-- **The two-site physical operator of `R` is a gate-restricted, rescaled
pullback of the one-site physical operator along `combine`.** When both
`(i1, i2)` and `(j1, j2)` satisfy the bond-matching condition `gate`, the
`(i1,i2),(j1,j2)` entry of `physClose2 R X` is `(25/32) · wMat (bit2 i1)
(bit2 j1)` times the `combine i1 i2, combine j1 j2` entry of `physClose1 R X`;
otherwise it vanishes. -/
lemma physClose2_R_entry (X : Matrix (Fin 4) (Fin 4) ℂ) (i1 i2 j1 j2 : Fin 4) :
    physClose2 R X (i1, i2) (j1, j2) =
      (25/32 : ℂ) * (if gate i1 i2 ∧ gate j1 j2 then wMat (bit2 i1) (bit2 j1) else 0) *
        physClose1 R X (combine i1 i2) (combine j1 j2) := by
  rw [physClose2_apply, R_eq_vecMulVec, R_eq_vecMulVec]
  simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul]
  rw [Matrix.trace_smul, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [physClose1_R_entry]
  simp only [bit1_combine, bit2_combine]
  have hdot : (fun b : Fin 4 => A b (bit2 i1) (bit2 j1)) ⬝ᵥ
      (fun a : Fin 4 => A a (bit1 i2) (bit1 j2)) =
      if gate i1 i2 ∧ gate j1 j2 then wMat (bit2 i1) (bit2 j1) else 0 :=
    dotProduct_A_col _ _ _ _
  rw [hdot]
  by_cases h : gate i1 i2 ∧ gate j1 j2
  · simp only [h, if_true]; ring
  · rw [if_neg h]; ring

/-! ### The Walsh–Hadamard eigenbasis of `wMat`, reused as Kraus data -/

/-- The two (unnormalized) Walsh–Hadamard eigenvectors of `wMat`. -/
def eigVecs : Fin 2 → Fin 2 → ℂ
  | 0 => ![1, 1]
  | 1 => ![1, -1]

/-- The eigenvalues of `wMat` matching `eigVecs`. -/
def eigVals : Fin 2 → ℝ
  | 0 => 1
  | 1 => lambda

lemma wMat_mulVec_eigVecs (s : Fin 2) :
    wMat.mulVec (eigVecs s) = (eigVals s : ℂ) • eigVecs s := by
  fin_cases s
  · exact wMat_mulVec_ones
  · exact wMat_mulVec_alt

lemma eigVecs_sq_sum (s : Fin 2) : (eigVecs s 0) ^ 2 + (eigVecs s 1) ^ 2 = 2 := by
  fin_cases s <;> norm_num [eigVecs]

/-- **The gated fiber of `combine` over a physical index `k` has exactly two
elements, indexed by the shared bond bit `b`.** For any function `f` of the
first-site's second bit, the sum over gated pairs `(p, q)` with `combine p q
= k` of `f (bit2 p)` collapses to `f 0 + f 1`. -/
lemma gated_combine_fiber_sum (k : Fin 4) (f : Fin 2 → ℂ) :
    (∑ pq : Fin 4 × Fin 4,
        if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then f (bit2 pq.1) else 0) =
      f 0 + f 1 := by
  rw [Fintype.sum_prod_type]
  fin_cases k <;>
    simp [gate, combine, bit1, bit2, bondEquiv_val, Fin.sum_univ_four]

/-! ### The refinement map `T`: one-site to two-site physical operators -/

lemma eigVals_pos (s : Fin 2) : 0 < eigVals s := by
  fin_cases s <;> norm_num [eigVals, lambda]

/-- The Kraus amplitude of the refinement map's `s`-th component. -/
noncomputable def refineAmp (s : Fin 2) : ℝ := Real.sqrt (25 * eigVals s / 64)

lemma refineAmp_sq (s : Fin 2) : (refineAmp s) ^ 2 = 25 * eigVals s / 64 := by
  rw [refineAmp, Real.sq_sqrt (by have := eigVals_pos s; linarith)]

/-- The `s`-th Kraus operator of the refinement map `T` sending the one-site
physical operator to the two-site physical operator: it places the
amplitude `refineAmp s * eigVecs s (bit2 p)` at the gated pair `(p, q)`
whose `combine` equals `k`, and vanishes elsewhere. -/
noncomputable def refineKraus (s : Fin 2) : Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  Matrix.of fun pq k =>
    if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then
      (refineAmp s : ℂ) * eigVecs s (bit2 pq.1)
    else 0

/-- The refinement map `T` from one-site to two-site physical operators. -/
noncomputable def refineMap :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.rectangularKrausMap refineKraus

lemma refineAmp_star (s : Fin 2) : star ((refineAmp s : ℝ) : ℂ) = (refineAmp s : ℂ) :=
  Complex.conj_ofReal _

lemma eigVecs_star (s b : Fin 2) : star (eigVecs s b) = eigVecs s b := by
  fin_cases s <;> fin_cases b <;> simp [eigVecs]

lemma refineKraus_apply_conj_mul (s : Fin 2) (pq : Fin 4 × Fin 4) (k : Fin 4) :
    star (refineKraus s pq k) * refineKraus s pq k =
      if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then
        (refineAmp s : ℂ) ^ 2 * (eigVecs s (bit2 pq.1)) ^ 2
      else 0 := by
  simp only [refineKraus, Matrix.of_apply]
  by_cases h : gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k
  · simp only [if_pos h, star_mul', refineAmp_star, eigVecs_star]
    ring
  · simp [h]

lemma refineAmp_sq_sum :
    (refineAmp (0 : Fin 2) : ℂ) ^ 2 * 2 + (refineAmp (1 : Fin 2) : ℂ) ^ 2 * 2 = 1 := by
  have h0 := refineAmp_sq (0 : Fin 2)
  have h1 := refineAmp_sq (1 : Fin 2)
  have e0 : ((refineAmp (0 : Fin 2) : ℝ) : ℂ) ^ 2 = ((refineAmp (0 : Fin 2)) ^ 2 : ℝ) := by
    push_cast; ring
  have e1 : ((refineAmp (1 : Fin 2) : ℝ) : ℂ) ^ 2 = ((refineAmp (1 : Fin 2)) ^ 2 : ℝ) := by
    push_cast; ring
  rw [e0, e1, h0, h1]
  norm_num [eigVals, lambda]

/-- **The refinement Kraus family resolves the identity.** -/
lemma refineKraus_resolution :
    ∑ s : Fin 2, (refineKraus s)ᴴ * refineKraus s = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext k k'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hkk' : k = k'
  · subst hkk'
    rw [Matrix.one_apply_eq]
    have hstep : ∀ s : Fin 2,
        (∑ pq : Fin 4 × Fin 4, star (refineKraus s pq k) * refineKraus s pq k) =
          (refineAmp s : ℂ) ^ 2 * 2 := by
      intro s
      simp_rw [refineKraus_apply_conj_mul]
      rw [gated_combine_fiber_sum k (fun b => (refineAmp s : ℂ) ^ 2 * (eigVecs s b) ^ 2)]
      have := eigVecs_sq_sum s
      have heq : (eigVecs s 0) ^ 2 + (eigVecs s 1) ^ 2 = (2 : ℂ) := by exact_mod_cast this
      rw [← mul_add, heq]
    rw [Finset.sum_congr rfl fun s _ => hstep s]
    simpa [Fin.sum_univ_two] using refineAmp_sq_sum
  · rw [Matrix.one_apply_ne hkk']
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro pq _
    simp only [refineKraus, Matrix.of_apply]
    by_cases h1 : gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k
    · have h2 : ¬ (gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k') := by
        rintro ⟨_, hc⟩
        exact hkk' (h1.2.symm.trans hc)
      rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]

end MPOTensor.RescalingStableLengthDependentRFP
