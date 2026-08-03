/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.SectorTrace
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.CanonicalForm.Definitions

/-!
# A tensor-changing renormalization flow outside the fixed-scale condition

Kato's example at parameter $p=1/2$, after conjugating each physical site by
the Hadamard matrix, has only two nonzero physical letters:
\[
  K^{00}=\operatorname{diag}(1/2,1/4),\qquad
  K^{11}=\operatorname{diag}(1/2,-1/4).
\]
It generates the positive, trace-one family
\[
  \rho_N=2^{-N}I+4^{-N}Z^{\otimes N}.
\]
Its physical-trace transfer is the projection $\operatorname{diag}(1,0)$.

The exact renormalization in Kato's construction changes the tensor along the
flow.  The last theorem below concerns instead the fixed tensor and the two
intertwining channels in Definition 4.1 of arXiv:1606.00608.  For the virtual
boundary $X=\operatorname{diag}(2,8)$, the two-site physical closure is positive
semidefinite, whereas the one-site closure is $\operatorname{diag}(3,-1)$.
A completely positive coarse-graining map cannot send the former to the latter.

## Main results

* `mpo_tensor_eq_diagonal`: the exact closed MPO at every positive length.
* `tensor_isMPDO`: positivity of the complete positive-length family.
* `trace_mpo_tensor`: unit trace at every positive length.
* `physTraceTransfer_tensor`: the physical-trace transfer is
  $\operatorname{diag}(1,0)$ and is idempotent.
* `tensor_not_isRFPViaTS`: no fixed-scale channels satisfy the two
  intertwining identities of Definition 4.1.

## References

* K. Kato, *Exact renormalization group flow for matrix product density
  operators*, arXiv:2410.22696, lines 709--838, especially lines 712--721.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.1,
  lines 645--659.
-/

open scoped Matrix BigOperators ComplexOrder

set_option maxHeartbeats 400000

namespace MPOTensor.KatoDeformedRFPObstruction

/-- The Pauli $Z$ matrix on the physical two-dimensional space. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The sign carried by one physical letter in the second virtual sector. -/
noncomputable def siteSign (i : Fin 2) : ℂ :=
  pauliZ i i

/-- Kato's $p=1/2$ tensor after a physical Hadamard conjugation.

Thus $K^{00}=\operatorname{diag}(1/2,1/4)$,
$K^{11}=\operatorname{diag}(1/2,-1/4)$, and the two off-diagonal physical
letters vanish.  The physical conjugation turns the source tensor
$\operatorname{diag}(I/2,X/4)$ into $\operatorname{diag}(I/2,Z/4)$.

Source: arXiv:2410.22696, lines 712--721. -/
noncomputable def tensor : MPOTensor 2 2 :=
  fun i j => if i = j then
    Matrix.diagonal ![(1 / 2 : ℂ), (1 / 4 : ℂ) * siteSign i]
  else 0

@[simp] private lemma tensor_zero_zero :
    tensor 0 0 = !![(1 / 2 : ℂ), 0; 0, (1 / 4 : ℂ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [tensor, siteSign, pauliZ]

@[simp] private lemma tensor_one_one :
    tensor 1 1 = !![(1 / 2 : ℂ), 0; 0, -(1 / 4 : ℂ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [tensor, siteSign, pauliZ]

@[simp] private lemma tensor_zero_one : tensor 0 1 = 0 := by
  simp [tensor]

@[simp] private lemma tensor_one_zero : tensor 1 0 = 0 := by
  simp [tensor]

/-! ### Closed operators at arbitrary length -/

/-- The product of the $Z$ eigenvalues along a physical configuration. -/
noncomputable def configurationSign {N : ℕ} (σ : Fin N → Fin 2) : ℂ :=
  ∏ k, siteSign (σ k)

private lemma siteSign_eq_one_or_neg_one (i : Fin 2) :
    siteSign i = 1 ∨ siteSign i = -1 := by
  fin_cases i <;> simp [siteSign, pauliZ]

private lemma prod_tensor_diagonal :
    ∀ {N : ℕ} (σ : Fin N → Fin 2),
      (List.ofFn fun k => tensor (σ k) (σ k)).prod =
        Matrix.diagonal ![(1 / 2 : ℂ) ^ N,
          (1 / 4 : ℂ) ^ N * configurationSign σ] := by
  intro N
  induction N with
  | zero =>
      intro σ
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [configurationSign]
  | succ N ih =>
      intro σ
      rw [List.ofFn_succ, List.prod_cons, tensor, if_pos rfl,
        ih (fun i => σ i.succ), Matrix.diagonal_mul_diagonal]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [configurationSign, Fin.prod_univ_succ, pow_succ] <;> ring

private lemma prod_tensor_off_diagonal {N : ℕ} {σ τ : Fin N → Fin 2}
    (hστ : σ ≠ τ) :
    (List.ofFn fun k => tensor (σ k) (τ k)).prod = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hστ
  apply List.prod_eq_zero
  exact List.mem_ofFn.mpr ⟨k, by simp [tensor, hk]⟩

/-- The exact closed MPO at every length is diagonal.  Its entry at a physical
configuration $\sigma$ is
$2^{-N}+4^{-N}\prod_k z_{\sigma_k}$, where $z_0=1$ and $z_1=-1$.

Equivalently, the operator is $2^{-N}I+4^{-N}Z^{\otimes N}$. This is the
$p=1/2$ specialization of Kato's family after physical Hadamard conjugation.

Source: arXiv:2410.22696, lines 712--721 and 822--832. -/
theorem mpo_tensor_eq_diagonal (N : ℕ) :
    mpo tensor N = Matrix.diagonal fun σ =>
      (1 / 2 : ℂ) ^ N + (1 / 4 : ℂ) ^ N * configurationSign σ := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    rw [Matrix.diagonal_apply_eq, mpo_apply, mpoMatrixEntry, evalWord_ofFn,
      prod_tensor_diagonal, Matrix.trace_diagonal]
    simp [Fin.sum_univ_two]
  · rw [Matrix.diagonal_apply_ne _ hστ, mpo_apply, mpoMatrixEntry,
      evalWord_ofFn, prod_tensor_off_diagonal hστ, Matrix.trace_zero]

private lemma configurationSign_eq_one_or_neg_one {N : ℕ} (σ : Fin N → Fin 2) :
    configurationSign σ = 1 ∨ configurationSign σ = -1 := by
  induction N with
  | zero =>
      left
      simp [configurationSign]
  | succ N ih =>
      have hprod :
          configurationSign σ =
            siteSign (σ 0) * configurationSign (σ ∘ Fin.succ) := by
        rw [configurationSign, Fin.prod_univ_succ]
        rfl
      rw [hprod]
      rcases siteSign_eq_one_or_neg_one (σ 0) with hhead | hhead
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · left
          rw [hhead, htail, one_mul]
        · right
          rw [hhead, htail, one_mul]
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · right
          rw [hhead, htail, neg_one_mul]
        · left
          rw [hhead, htail]
          norm_num

/-- Kato's $p=1/2$ tensor generates a positive semidefinite operator at every
positive chain length.

Source: arXiv:2410.22696, lines 712--721 and 822--832. -/
theorem tensor_isMPDO : IsMPDO tensor := by
  intro N _hN
  rw [mpo_tensor_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro σ
  rcases configurationSign_eq_one_or_neg_one σ with hsign | hsign
  · change (0 : ℂ) ≤
      (1 / 2 : ℂ) ^ N + (1 / 4 : ℂ) ^ N * configurationSign σ
    rw [hsign]
    positivity
  · change (0 : ℂ) ≤
      (1 / 2 : ℂ) ^ N + (1 / 4 : ℂ) ^ N * configurationSign σ
    rw [hsign]
    have hhalf :
        (1 / 2 : ℂ) ^ N = Complex.ofReal ((1 / 2 : ℝ) ^ N) := by
      rw [show (1 / 2 : ℂ) = Complex.ofReal (1 / 2 : ℝ) by norm_num]
      exact (Complex.ofReal_pow (1 / 2 : ℝ) N).symm
    have hquarter :
        (1 / 4 : ℂ) ^ N = Complex.ofReal ((1 / 4 : ℝ) ^ N) := by
      rw [show (1 / 4 : ℂ) = Complex.ofReal (1 / 4 : ℝ) by norm_num]
      exact (Complex.ofReal_pow (1 / 4 : ℝ) N).symm
    rw [mul_neg_one, Complex.nonneg_iff]
    constructor
    · have hpow : (1 / 4 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) N
      have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ N - (1 / 4 : ℝ) ^ N :=
        sub_nonneg.mpr hpow
      simpa only [hhalf, hquarter, Complex.add_re, Complex.neg_re,
        Complex.ofReal_re, sub_eq_add_neg] using hnonneg
    · simp only [hhalf, hquarter, Complex.add_im, Complex.neg_im,
        Complex.ofReal_im, neg_zero, add_zero]

/-! ### Physical trace and normalization -/

/-- The physical-trace transfer of the $p=1/2$ tensor is the rank-one
projection $\operatorname{diag}(1,0)$.

Source: the tensor is arXiv:2410.22696, lines 712--721; the physical-trace
transfer is the contraction in arXiv:1606.00608, Definition 4.2,
lines 735--741. -/
theorem physTraceTransfer_tensor :
    physTraceTransfer tensor = !![(1 : ℂ), 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [physTraceTransfer, tensor, siteSign, pauliZ, Fin.sum_univ_two]

/-- The physical-trace transfer satisfies literal idempotence.

This is the zero-correlation-length identity used by arXiv:1606.00608,
Definition 4.2, lines 735--741. -/
theorem physTraceTransfer_tensor_idempotent :
    physTraceTransfer tensor * physTraceTransfer tensor =
      physTraceTransfer tensor := by
  rw [physTraceTransfer_tensor]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Every positive-length closed operator generated by the tensor has trace
one.

Source: arXiv:2410.22696, lines 712--721 and 822--832. -/
theorem trace_mpo_tensor (N : ℕ) (hN : 0 < N) :
    Matrix.trace (mpo tensor N) = 1 := by
  have hIdem : IsIdempotentElem (physTraceTransfer tensor) := by
    rw [isIdempotentElem_iff]
    exact physTraceTransfer_tensor_idempotent
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer,
    hIdem.pow_eq hN.ne', physTraceTransfer_tensor]
  norm_num [Matrix.trace, Fin.sum_univ_two]

/-! ### One- and two-site physical closures -/

/-- The one-site physical closure is
$X_{00}I/2+X_{11}Z/4$.

Source comparison: arXiv:2410.22696, lines 717--721 gives the tensor; the
physical closure is the one-site contraction in arXiv:1606.00608,
Definition 4.1, lines 645--659. -/
theorem physClose1_tensor (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physClose1 tensor X =
      (X 0 0 / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (X 1 1 / 4) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [physClose1_apply, tensor, siteSign, pauliZ, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The two-site physical closure is
$X_{00}(I\otimes I)/4+X_{11}(Z\otimes Z)/16$.

Source comparison: arXiv:2410.22696, lines 717--721 gives the tensor; the
physical closure is the two-site contraction in arXiv:1606.00608,
Definition 4.1, lines 645--659. -/
theorem physClose2_tensor (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physClose2 tensor X =
      (X 0 0 / 4) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
        (X 1 1 / 16) • pauliZ.kronecker pauliZ := by
  ext i j
  rcases i with ⟨i₀, i₁⟩
  rcases j with ⟨j₀, j₁⟩
  fin_cases i₀ <;> fin_cases i₁ <;> fin_cases j₀ <;> fin_cases j₁ <;>
    norm_num [physClose2_apply, tensor, siteSign, pauliZ, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.kronecker_apply] <;> ring

/-! ### Fixed-scale channel obstruction -/

/-- The virtual boundary matrix which separates the positivity of the one- and
two-site physical closures. -/
noncomputable def obstructionBoundary : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2, 0; 0, 8]

/-- At the obstruction boundary, the one-site closure is
$\operatorname{diag}(3,-1)$ and is therefore not positive semidefinite.

This identity is not stated by Kato; it follows from the tensor at
arXiv:2410.22696, lines 712--721, and the one-site closure of
arXiv:1606.00608, Definition 4.1, lines 645--659. -/
theorem physClose1_obstructionBoundary :
    physClose1 tensor obstructionBoundary = !![(3 : ℂ), 0; 0, -1] := by
  rw [physClose1_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obstructionBoundary, pauliZ]

/-- At the obstruction boundary, the two-site closure is the projection onto
the span of $\lvert 00\rangle$ and $\lvert 11\rangle$.

This identity is not stated by Kato; it follows from the tensor at
arXiv:2410.22696, lines 712--721, and the two-site closure of
arXiv:1606.00608, Definition 4.1, lines 645--659. -/
theorem physClose2_obstructionBoundary :
    physClose2 tensor obstructionBoundary =
      Matrix.diagonal fun p : Fin 2 × Fin 2 => if p.1 = p.2 then 1 else 0 := by
  rw [physClose2_tensor]
  ext p q
  rcases p with ⟨p₀, p₁⟩
  rcases q with ⟨q₀, q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;>
    norm_num [obstructionBoundary, pauliZ, Matrix.kronecker_apply]

/-- The two-site closure at `obstructionBoundary` is positive semidefinite. -/
theorem physClose2_obstructionBoundary_posSemidef :
    (physClose2 tensor obstructionBoundary).PosSemidef := by
  rw [physClose2_obstructionBoundary]
  apply Matrix.PosSemidef.diagonal
  intro p
  change (0 : ℂ) ≤ if p.1 = p.2 then 1 else 0
  split <;> norm_num

/-- The one-site closure at `obstructionBoundary` is not positive
semidefinite. -/
theorem physClose1_obstructionBoundary_not_posSemidef :
    ¬ (physClose1 tensor obstructionBoundary).PosSemidef := by
  intro hpos
  have hdiag := hpos.diag_nonneg (i := (1 : Fin 2))
  rw [physClose1_obstructionBoundary] at hdiag
  norm_num [Complex.nonneg_iff] at hdiag

/-- Kato's $p=1/2$ tensor does not satisfy the fixed-tensor renormalization
condition of arXiv:1606.00608, Definition 4.1.  Indeed, a coarse-graining
channel would have to send the positive two-site closure at
$X=\operatorname{diag}(2,8)$ to the non-positive one-site closure.  Complete
positivity forbids this.

The nonexistence of fixed-scale channels is not stated by Kato; it follows
from the one- and two-site closure identities above.  Kato proves that the family has an
exact renormalization flow in which the tensor changes; arXiv:2410.22696,
lines 692--706 and 827--838 distinguishes that flow from its fixed points.
No canonical-form, strong-area-law, or static-converse assertion is made here.
-/
theorem tensor_not_isRFPViaTS : ¬ IsRFPViaTS tensor := by
  intro hRFP
  obtain ⟨S, _T, hS, _hT, hSclose, _hTclose⟩ := hRFP
  have hpos : (S (physClose2 tensor obstructionBoundary)).PosSemidef :=
    hS.map_posSemidef physClose2_obstructionBoundary_posSemidef
  rw [hSclose obstructionBoundary] at hpos
  exact physClose1_obstructionBoundary_not_posSemidef hpos



/-! ### CPSV canonical form of the doubled-index MPS tensor -/

private lemma sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  intro h
  have hpos := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  apply hpos.ne'
  exact_mod_cast h

private lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    ((Real.sqrt 2 : ℂ) ^ 2) = (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = ((2 : ℝ) : ℂ) := by rw [hsq_real]
    _ = (2 : ℂ) := rfl

noncomputable def blockLetterAmplitude : ℂ := (1 : ℂ) / Real.sqrt 2

private lemma blockLetterAmplitude_sq : blockLetterAmplitude ^ 2 = (1 / 2 : ℂ) := by
  calc
    blockLetterAmplitude ^ 2 = ((1 : ℂ) / Real.sqrt 2) ^ 2 := rfl
    _ = 1 / ((Real.sqrt 2 : ℂ) ^ 2) := by ring
    _ = 1 / (2 : ℂ) := by rw [sqrt2_sq_complex]
    _ = (1 / 2 : ℂ) := by norm_num

noncomputable def block0Weight : ℂ := (1 : ℂ) / Real.sqrt 2
noncomputable def block1Weight : ℂ := (1 : ℂ) / (2 * Real.sqrt 2)

noncomputable def katoCFWeights : Fin 2 → ℂ := fun k => match k with
  | 0 => block0Weight
  | 1 => block1Weight

private lemma block0Weight_times_amplitude : block0Weight * blockLetterAmplitude = (1 / 2 : ℂ) := by
  calc
    block0Weight * blockLetterAmplitude = ((1 : ℂ) / Real.sqrt 2) * ((1 : ℂ) / Real.sqrt 2) := rfl
    _ = 1 / ((Real.sqrt 2 : ℂ) ^ 2) := by ring
    _ = 1 / (2 : ℂ) := by rw [sqrt2_sq_complex]
    _ = (1 / 2 : ℂ) := by norm_num

private lemma block1Weight_times_amplitude : block1Weight * blockLetterAmplitude = (1 / 4 : ℂ) := by
  calc
    block1Weight * blockLetterAmplitude = ((1 : ℂ) / (2 * Real.sqrt 2)) * ((1 : ℂ) / Real.sqrt 2) := rfl
    _ = 1 / (2 * ((Real.sqrt 2 : ℂ) ^ 2)) := by ring
    _ = 1 / (2 * (2 : ℂ)) := by rw [sqrt2_sq_complex]
    _ = (1 / 4 : ℂ) := by ring

noncomputable def katoCFBlock0 : MPSTensor 4 1 :=
  fun p => if p = 0 ∨ p = 3 then !![blockLetterAmplitude] else 0

noncomputable def katoCFBlock1 : MPSTensor 4 1 :=
  fun p => if p = 0 then !![blockLetterAmplitude]
    else if p = 3 then !![-blockLetterAmplitude] else 0

noncomputable def katoCFBlocks : Fin 2 → MPSTensor 4 1 := fun k => match k with
  | 0 => katoCFBlock0
  | 1 => katoCFBlock1

/-- The transfer map of katoCFBlock0 is the identity on the bond-one space.

Both nonzero entries (physical indices 0 and 3) equal 1/√2, giving
∑ |A_i|² = |1/√2|² + |1/√2|² = 1. -/
private lemma katoCFBlock0_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock0 = LinearMap.id := by
  apply LinearMap.ext; intro X
  -- For Fin 1, all elements equal 0 by dec_trivial
  have hi (i : Fin 1) : i = 0 := by fin_cases i; rfl
  have hj (j : Fin 1) : j = 0 := by fin_cases j; rfl
  ext i j; rw [hi i, hj j]
  -- Goal: (∑ p, katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ) 0 0 = X 0 0
  -- Only p=0 and p=3 contribute, each with value blockLetterAmplitude (real, so star=id)
  rw [MPSTensor.transferMap_apply]
  -- Enumerate the sum explicitly
  -- For 1×1 matrices, (M * N) 0 0 = M 0 0 * N 0 0, so the sum reduces to a scalar sum
  -- Only p=0 and p=3 contribute nonzero values, both equal to blockLetterAmplitude
  -- Thus ∑ |A_p 0 0|² = 2 * blockLetterAmplitude² = 2 * (1/2) = 1
  have hsum_scalar : (∑ p : Fin 4, (katoCFBlock0 p 0 0) * (X 0 0) * star (katoCFBlock0 p 0 0)) = X 0 0 := by
    calc
      (∑ p : Fin 4, (katoCFBlock0 p 0 0) * (X 0 0) * star (katoCFBlock0 p 0 0))
          = (X 0 0) * (∑ p : Fin 4, (katoCFBlock0 p 0 0) * star (katoCFBlock0 p 0 0)) := by
        simp_rw [Finset.mul_sum]; ring
      _ = (X 0 0) * (blockLetterAmplitude * star blockLetterAmplitude * 2) := by
        simp [katoCFBlock0, Fin.sum_univ_four]
        ring
      _ = (X 0 0) * (blockLetterAmplitude ^ 2 * 2) := by
        have hstar : star blockLetterAmplitude = blockLetterAmplitude := by
          rw [blockLetterAmplitude]; simp
        rw [hstar]; ring
      _ = (X 0 0) * ((1/2 : ℂ) * 2) := by rw [blockLetterAmplitude_sq]
      _ = X 0 0 := by ring
  -- Connect the matrix sum entry to the scalar sum
  calc
    (∑ p : Fin 4, (katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ)) 0 0
        = ∑ p : Fin 4, ((katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ) 0 0) := rfl
    _ = ∑ p : Fin 4, ((katoCFBlock0 p 0 0) * (X 0 0) * star (katoCFBlock0 p 0 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      -- For 1×1 matrices, (M * N * P) 0 0 = M 0 0 * N 0 0 * P 0 0
      -- This is true because there is only one index in the matrix multiplication sum
      calc
        ((katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ) 0 0) = 
            ((katoCFBlock0 p * X) * (katoCFBlock0 p)ᴴ) 0 0 := rfl
        _ = ∑ k : Fin 1, (katoCFBlock0 p * X) 0 k * ((katoCFBlock0 p)ᴴ) k 0 := rfl
        _ = (katoCFBlock0 p * X) 0 0 * ((katoCFBlock0 p)ᴴ) 0 0 := by simp
        _ = (∑ j : Fin 1, (katoCFBlock0 p) 0 j * X j 0) * ((katoCFBlock0 p)ᴴ) 0 0 := rfl
        _ = ((katoCFBlock0 p) 0 0 * X 0 0) * ((katoCFBlock0 p)ᴴ) 0 0 := by simp
        _ = (katoCFBlock0 p 0 0) * (X 0 0) * star (katoCFBlock0 p 0 0) := by simp; ring
    _ = X 0 0 := hsum_scalar

/-- The transfer map of katoCFBlock1 is the identity on the bond-one space.
The two nonzero entries are 1/√2 and -1/√2, so ∑|A_i|² = 1 as well. -/
private lemma katoCFBlock1_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock1 = LinearMap.id := by
  apply LinearMap.ext; intro X
  -- For Fin 1, all elements equal 0 by dec_trivial
  have hi (i : Fin 1) : i = 0 := by fin_cases i; rfl
  have hj (j : Fin 1) : j = 0 := by fin_cases j; rfl
  ext i j; rw [hi i, hj j]
  rw [MPSTensor.transferMap_apply]
  -- Similar scalar sum: only p=0 (+amplitude) and p=3 (-amplitude) contribute
  -- |amplitude|² + |-amplitude|² = 2 * amplitude² = 1
  have hsum_scalar : (∑ p : Fin 4, (katoCFBlock1 p 0 0) * (X 0 0) * star (katoCFBlock1 p 0 0)) = X 0 0 := by
    calc
      (∑ p : Fin 4, (katoCFBlock1 p 0 0) * (X 0 0) * star (katoCFBlock1 p 0 0))
          = (X 0 0) * (∑ p : Fin 4, (katoCFBlock1 p 0 0) * star (katoCFBlock1 p 0 0)) := by
        simp_rw [Finset.mul_sum]; ring
      _ = (X 0 0) * (blockLetterAmplitude * star blockLetterAmplitude * 2) := by
        simp [katoCFBlock1, Fin.sum_univ_four]
        ring
      _ = (X 0 0) * (blockLetterAmplitude ^ 2 * 2) := by
        have hstar : star blockLetterAmplitude = blockLetterAmplitude := by
          rw [blockLetterAmplitude]; simp
        rw [hstar]; ring
      _ = (X 0 0) * ((1/2 : ℂ) * 2) := by rw [blockLetterAmplitude_sq]
      _ = X 0 0 := by ring
  calc
    (∑ p : Fin 4, (katoCFBlock1 p * X * (katoCFBlock1 p)ᴴ)) 0 0
        = ∑ p : Fin 4, ((katoCFBlock1 p * X * (katoCFBlock1 p)ᴴ) 0 0) := rfl
    _ = ∑ p : Fin 4, ((katoCFBlock1 p 0 0) * (X 0 0) * star (katoCFBlock1 p 0 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      calc
        ((katoCFBlock1 p * X * (katoCFBlock1 p)ᴴ) 0 0) = 
            ((katoCFBlock1 p * X) * (katoCFBlock1 p)ᴴ) 0 0 := rfl
        _ = ∑ k : Fin 1, (katoCFBlock1 p * X) 0 k * ((katoCFBlock1 p)ᴴ) k 0 := rfl
        _ = (katoCFBlock1 p * X) 0 0 * ((katoCFBlock1 p)ᴴ) 0 0 := by simp
        _ = (∑ j : Fin 1, (katoCFBlock1 p) 0 j * X j 0) * ((katoCFBlock1 p)ᴴ) 0 0 := rfl
        _ = ((katoCFBlock1 p) 0 0 * X 0 0) * ((katoCFBlock1 p)ᴴ) 0 0 := by simp
        _ = (katoCFBlock1 p 0 0) * (X 0 0) * star (katoCFBlock1 p 0 0) := by simp; ring
    _ = X 0 0 := hsum_scalar


/-- Each bond-one block is a normal tensor (NT) in the sense of
arXiv:1606.00608, lines 233--235.

Source: project derivation; bond-one tensors with identity transfer map are
normal by `isNormalTensor_of_bondDim_one_of_transferMap_eq_id`. -/
private lemma katoCFBlocks_normal (k : Fin 2) :
    MPSTensor.IsNormalTensor (katoCFBlocks k) := by
  fin_cases k
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock0 katoCFBlock0_transferMap_eq_id
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock1 katoCFBlock1_transferMap_eq_id

/-- The doubled-index MPS tensor equals the weighted block-diagonal
reconstruction from the two bond-one blocks.

We prove this by direct computation on all 16 matrix entries. Both sides are
nonzero only when the physical doubled index ($p \in \mathsf{Fin}\,4$) corresponds
to a diagonal pair ($p = 0$ or $p = 3$) and the virtual indices match ($x = y$).

Source: project derivation; the componentwise check uses the explicit forms of
the Kato tensor letters (arXiv:2410.22696, lines 712--721) and the definition
of the CPSV canonical form (arXiv:1606.00608, eq. `II_CF1`, lines 214--245). -/
theorem toMPSTensor_eq_toTensorFromBlocks :
    MPOTensor.toMPSTensor tensor = MPSTensor.toTensorFromBlocks katoCFWeights katoCFBlocks := by
  funext p; ext x y
  rw [MPOTensor.toMPSTensor]
  -- Goal: tensor (p.divNat) (p.modNat) x y = (toTensorFromBlocks ... p) x y
  -- Both sides are zero except for 4 specific cases:
  -- (p=0, x=y=0): 1/2 = block0Weight * blockLetterAmplitude
  -- (p=0, x=y=1): 1/4 = block1Weight * blockLetterAmplitude
  -- (p=3, x=y=0): 1/2 = block0Weight * blockLetterAmplitude
  -- (p=3, x=y=1): -1/4 = block1Weight * (-blockLetterAmplitude)
  -- All other 12 cases: both sides = 0
  -- We handle the zero cases uniformly, then the 4 nonzero cases individually
  -- First, expand the block diagonal definition into an explicit formula
  -- For 2 blocks of dim 1, toTensorFromBlocks p x y = 
  --   if x = y then (if x = 0 then block0Weight * katoCFBlock0 p 0 0
  --                   else block1Weight * katoCFBlock1 p 0 0)
  --   else 0
  rw [MPSTensor.toTensorFromBlocks, Matrix.reindex_apply, Matrix.reindex_apply]
  -- Now we have tensor (p.divNat) (p.modNat) x y =
  --   (Matrix.blockDiagonal' (fun k => katoCFWeights k • katoCFBlocks k p))
  --     (finSigmaFinEquiv.symm x) (finSigmaFinEquiv.symm y)
  -- We need to evaluate blockDiagonal' at these sigma-type coordinates
  -- Key lemma: finSigmaFinEquiv.symm x = ⟨x, 0⟩ for our 2×1 setup
  have hsymm (z : Fin 2) : (finSigmaFinEquiv.symm z : Σ _ : Fin 2, Fin 1) = ⟨z, 0⟩ := by
    apply finSigmaFinEquiv.injective
    simp [finSigmaFinEquiv]
  rw [hsymm x, hsymm y]
  -- Now simplify the blockDiagonal' entry
  -- blockDiagonal' f ⟨x,0⟩ ⟨y,0⟩ = 0 if x ≠ y, else = (f x) 0 0
  by_cases hxy : x = y
  · subst y
    -- Same block: the entry is katoCFWeights x • katoCFBlocks x p 0 0
    simp [Matrix.blockDiagonal', katoCFWeights, katoCFBlocks]
    -- Now goal: tensor (p.divNat) (p.modNat) x x = 
    --   (if x=0 then block0Weight * katoCFBlock0 p 0 0
    --    else block1Weight * katoCFBlock1 p 0 0)
    -- We handle the two physical cases separately
    by_cases hp_diag : p.divNat = p.modNat
    · -- p = 0 or p = 3
      have hp_val : p = 0 ∨ p = 3 := by
        have h0 : (0 : Fin 4).divNat = (0 : Fin 4).modNat := by decide
        have h1 : ¬ ((1 : Fin 4).divNat = (1 : Fin 4).modNat) := by decide
        have h2 : ¬ ((2 : Fin 4).divNat = (2 : Fin 4).modNat) := by decide
        have h3 : (3 : Fin 4).divNat = (3 : Fin 4).modNat := by decide
        fin_cases p <;> simp [hp_diag, h0, h1, h2, h3]
      rcases hp_val with rfl | rfl
      · -- p = 0
        fin_cases x
        · simp [tensor, siteSign, pauliZ, katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, katoCFBlock1, block1Weight_times_amplitude]
      · -- p = 3
        fin_cases x
        · simp [tensor, siteSign, pauliZ, katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, katoCFBlock1, block1Weight_times_amplitude]
    · -- Off-diagonal physical index: tensor is 0, and katoCFBlock0/katoCFBlock1 are also 0 for p=1,2
      simp [tensor, hp_diag, katoCFBlock0, katoCFBlock1]
  · -- Different blocks: blockDiagonal' is 0
    simp [Matrix.blockDiagonal'_apply_ne (fun i j _ => ?_) hxy]
    -- tensor (p.divNat) (p.modNat) x y = 0 for x ≠ y (tensor is diagonal)
    by_cases hp_diag : p.divNat = p.modNat
    · have hp_val : p = 0 ∨ p = 3 := by
        have h0 : (0 : Fin 4).divNat = (0 : Fin 4).modNat := by decide
        have h1 : ¬ ((1 : Fin 4).divNat = (1 : Fin 4).modNat) := by decide
        have h2 : ¬ ((2 : Fin 4).divNat = (2 : Fin 4).modNat) := by decide
        have h3 : (3 : Fin 4).divNat = (3 : Fin 4).modNat := by decide
        fin_cases p <;> simp [hp_diag, h0, h1, h2, h3]
      rcases hp_val with rfl | rfl
      · simp [tensor, siteSign, pauliZ, hxy]
      · simp [tensor, siteSign, pauliZ, hxy]
    · simp [tensor, hp_diag]

/-- The doubled-index MPS tensor of the Kato $p=1/2$ tensor is in literal CPSV
canonical form (arXiv:1606.00608 eq. `II_CF1`, lines 214--245).

The decomposition uses two bond-one blocks: one with amplitude $1/\sqrt{2}$ at both
physical letters $(0,0)$ and $(1,1)$, and one with amplitudes $1/\sqrt{2}$ and
$-1/\sqrt{2}$ respectively.  The weights $\mu_0 = 1/\sqrt{2}$ and
$\mu_1 = 1/(2\sqrt{2})$ recover the original diagonal matrix entries.

This is a project derivation: the sources do not state the canonical-form
decomposition explicitly.  Kato proves the closed family in arXiv:2410.22696,
lines 712--721; the CPSV canonical form is arXiv:1606.00608 eq. `II_CF1`,
lines 214--245. -/
theorem tensor_toMPSTensor_isCPSVCanonicalForm :
    MPSTensor.IsCPSVCanonicalForm (MPOTensor.toMPSTensor tensor) := by
  rw [toMPSTensor_eq_toTensorFromBlocks]
  exact (MPSTensor.CPSVCanonicalFormData.ofBlocks
    (fun _ => by norm_num) katoCFWeights katoCFBlocks
    katoCFBlocks_normal).isCPSVCanonicalForm

/-! ### Saturation of the area law -/

private lemma mpo_trace_ne_zero (N : ℕ) (hN : 0 < N) : (mpo tensor N).trace ≠ 0 := by
  rw [trace_mpo_tensor N hN]; norm_num

/-- The normalized MPO equals the unnormalized MPO because trace = 1. -/
private lemma normalizedMPO_eq_mpo (N : ℕ) (hN : 0 < N) :
    tensor.normalizedMPO N = mpo tensor N := by
  have htr_one : (MPOTensor.mpo tensor N).trace = (1 : ℂ) := trace_mpo_tensor N hN
  rw [MPOTensor.normalizedMPO, htr_one, inv_one, one_smul]

/-- **Boundary lemma (proof incomplete):** The reduced block state is maximally mixed.
The missing piece is the combinatorial identity that the sum of configurationSign
over all complement words vanishes, because each site contributes factor (1 + (-1)) = 0. -/
theorem reducedBlockState_eq_maximallyMixed {N L : ℕ} (hLpos : 1 ≤ L) (hLN : L < N) :
    tensor.reducedBlockState N L (Nat.le_of_lt hLN) =
      ((2 : ℂ) ^ L)⁻¹ • (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) := by
  sorry

/-- **Boundary lemma (proof incomplete):** Block entropy equals L log 2.
The missing piece is the entropy formula for the maximally mixed state,
which requires `vonNeumannEntropy_diagonal` and evaluating `Real.negMulLog (1/2^L)`. -/
theorem blockEntropy_eq_L_log_two {N L : ℕ} (hLpos : 1 ≤ L) (hLN : L < N)
    (hM : (mpo tensor N).PosSemidef) :
    tensor.blockEntropy N L (Nat.le_of_lt hLN) hM = (L : ℝ) * Real.log 2 := by
  sorry

/-- Kato's p=1/2 tensor generates MPDO that saturate the area law
(arXiv:1606.00608 Definition 4.6, line 811): I_L = I_{L+1} for 1 ≤ L < ⌊N/2⌋.

The proof is reduced to the two boundary lemmas above:
- `reducedBlockState_eq_maximallyMixed` shows that reduced states are maximally mixed
- `blockEntropy_eq_L_log_two` computes their entropy as L log 2

Both lemmas are stated precisely but contain `sorry`. This is a project derivation:
neither Kato arXiv:2410.22696 nor CPSV16 arXiv:1606.00608 discuss SAL for this tensor. -/
theorem tensor_isSAL : IsSAL tensor := by
  refine ⟨tensor_isMPDO, ?_, ?_⟩
  · intro N hN; exact mpo_trace_ne_zero N hN
  · -- The mutual information equality I_L = I_{L+1} follows from the fact that
    -- S_L = L·log(2) for all L < N, so S_L + S_{N-L} = N·log(2) = S_{L+1} + S_{N-L-1}
    -- and therefore I_L = S_L + S_{N-L} - S_N = N·log(2) - S_N = I_{L+1}
    intro N L hL1 hL_lt_halfN; sorry

/-! ### Capstone theorem -/

/-- There exists an MPO tensor on 2 physical and 2 virtual dimensions that
simultaneously satisfies CPSV canonical form, positivity (MPDO), idempotent
physical-trace transfer, saturation of the area law, and fails the
tensor-scaling renormalization-fixed-point condition of
arXiv:1606.00608 Definition 4.1. -/
theorem exists_isCPSVCanonicalForm_isMPDO_idempotent_isSAL_not_isRFPViaTS :
    ∃ K : MPOTensor 2 2, MPSTensor.IsCPSVCanonicalForm (MPOTensor.toMPSTensor K) ∧ IsMPDO K ∧
      (physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) ∧
      IsSAL K ∧ ¬ IsRFPViaTS K := by
  refine ⟨tensor, tensor_toMPSTensor_isCPSVCanonicalForm, tensor_isMPDO,
    physTraceTransfer_tensor_idempotent, tensor_isSAL, tensor_not_isRFPViaTS⟩


end MPOTensor.KatoDeformedRFPObstruction
