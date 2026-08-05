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

It also provides PSD infrastructure toward the remaining `IsMPDO R` gap
(preliminary framework, not yet connected to `R`; see *Remaining gap* below):
`chainIndicator_posSemidef`, `wMat_posSemidef`, `wN_posSemidef`, and
`coeff_sq_eq_wMat`.

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
  `mpo R N = (25/32)^N · B * wN N * Bᵀ`, where `B` is the boundary partial
  isometry (`BᵀB = 1`) and `wN N a b = ∏ n, wMat (a n) (b n)` with
  `wMat = !![16/25, 9/25; 9/25, 16/25]`; `wMat` has eigenvalues
  `{1, 7/25}` — the `χ = diag(1, 7/25)` of the coefficient family.
  Positivity follows from
  `wN N = Σ_s (∏_n λ_{s n}) • vecMulVec (e_s) (star (e_s))`
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

The entrywise formula for `mpo R N` (the only remaining gap) is verified
by direct analysis of the cyclic sum; the bond‑chain constraints collapse
the sum to at most one term.  A fully formal proof of this formula is
in progress. -/

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
`wN N a b = ∏ n, wMat (a n) (b n)`.  In the planned factorization the
closed operator is `(25/32)^N • (B * wN N * Bᴴ)` for the boundary map `B`.

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

/-! ### Remaining gap

The entrywise formula `mpo_R_entry_formula` and the pullback equality —
the pullback of `wN N` along `φ N`, namely
`Matrix.of fun p q => (wN N) (φ N p) (φ N q)`, equals `B * wN N * Bᴴ` for
`B` the boundary map — are a work in progress.  When completed, the main
theorem `R_isMPDO` follows by the Hadamard (Schur) product argument via
`Matrix.PosSemidef.hadamard`. -/

end MPOTensor.RescalingStableLengthDependentRFP
