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
* `tensor_toMPSTensor_isCPSVCanonicalForm`: the doubled-index MPS tensor
  is in literal CPSV canonical form (arXiv:1606.00608, eq. `II_CF1`).
* `tensor_isSAL`: the tensor saturates the area law (Definition 4.6).
* `exists_isCPSVCanonicalForm_isMPDO_idempotent_isSAL_not_isRFPViaTS`:
  the tensor simultaneously exhibits CPSV canonical form, MPDO positivity,
  idempotent physical-trace transfer, strong area law, and absence of
  fixed-scale renormalization.

## References

* K. Kato, *Exact renormalization group flow for matrix product density
  operators*, arXiv:2410.22696, lines 709--838, especially lines 712--721.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.1,
  lines 645--659.
-/

open scoped Matrix BigOperators ComplexOrder

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

private lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    ((Real.sqrt 2 : ℂ) ^ 2) = (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = ((2 : ℝ) : ℂ) := by rw [hsq_real]
    _ = (2 : ℂ) := rfl

private noncomputable def blockLetterAmplitude : ℂ := (1 : ℂ) / Real.sqrt 2

private lemma blockLetterAmplitude_sq : blockLetterAmplitude ^ 2 = (1 / 2 : ℂ) := by
  calc
    blockLetterAmplitude ^ 2 = ((1 : ℂ) / Real.sqrt 2) ^ 2 := rfl
    _ = 1 / ((Real.sqrt 2 : ℂ) ^ 2) := by ring
    _ = 1 / (2 : ℂ) := by rw [sqrt2_sq_complex]
    _ = (1 / 2 : ℂ) := by norm_num

private noncomputable def block0Weight : ℂ := (1 : ℂ) / Real.sqrt 2
private noncomputable def block1Weight : ℂ := (1 : ℂ) / (2 * Real.sqrt 2)
private noncomputable def katoCFWeights : Fin 2 → ℂ :=
  fun k => match k with | 0 => block0Weight | 1 => block1Weight

private lemma block0Weight_times_amplitude :
    block0Weight * blockLetterAmplitude = (1 / 2 : ℂ) := by
  calc
    block0Weight * blockLetterAmplitude =
        ((1 : ℂ) / Real.sqrt 2) * ((1 : ℂ) / Real.sqrt 2) := rfl
    _ = 1 / ((Real.sqrt 2 : ℂ) ^ 2) := by ring
    _ = 1 / (2 : ℂ) := by rw [sqrt2_sq_complex]
    _ = (1 / 2 : ℂ) := by norm_num

private lemma block1Weight_times_amplitude :
    block1Weight * blockLetterAmplitude = (1 / 4 : ℂ) := by
  calc
    block1Weight * blockLetterAmplitude =
        ((1 : ℂ) / (2 * Real.sqrt 2)) * ((1 : ℂ) / Real.sqrt 2) := rfl
    _ = 1 / (2 * ((Real.sqrt 2 : ℂ) ^ 2)) := by ring
    _ = 1 / (2 * (2 : ℂ)) := by rw [sqrt2_sq_complex]
    _ = (1 / 4 : ℂ) := by ring

private noncomputable def katoCFBlock0 : MPSTensor 4 1 :=
  fun p => if p = 0 ∨ p = 3 then !![blockLetterAmplitude] else 0

private noncomputable def katoCFBlock1 : MPSTensor 4 1 :=
  fun p =>
    if p = 0 then !![blockLetterAmplitude]
    else if p = 3 then !![-blockLetterAmplitude]
    else 0

private noncomputable def katoCFBlocks : Fin 2 → MPSTensor 4 1 :=
  fun k => match k with | 0 => katoCFBlock0 | 1 => katoCFBlock1

private lemma one_by_one_mul_apply (A B : Matrix (Fin 1) (Fin 1) ℂ) :
    (A * B) 0 0 = (A 0 0) * (B 0 0) := by
  rw [Matrix.mul_apply]
  have huniv : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by decide
  rw [huniv, Finset.sum_singleton]

private lemma one_by_one_mul_conj_apply (A X : Matrix (Fin 1) (Fin 1) ℂ) :
    (A * X * Aᴴ) 0 0 = (A 0 0) * (X 0 0) * star (A 0 0) := by
  calc
    (A * X * Aᴴ) 0 0 = ((A * X) * Aᴴ) 0 0 := rfl
    _ = (A * X) 0 0 * (Aᴴ) 0 0 := by rw [one_by_one_mul_apply]
    _ = ((A 0 0) * (X 0 0)) * (Aᴴ) 0 0 := by rw [one_by_one_mul_apply]
    _ = (A 0 0) * (X 0 0) * star (A 0 0) := by rw [Matrix.conjTranspose_apply]

/-- Both Kato CF blocks have transfer map equal to the identity.
The common computation is factored through this helper, parameterized
by the two nonzero entries of the block (entries 1 and 2 are zero). -/
private lemma katoCFBlock_transferMap_eq_id_aux (s : ℂ) (B : MPSTensor 4 1)
    (hB0 : (B 0) 0 0 = blockLetterAmplitude) (hB1 : (B 1) 0 0 = 0)
    (hB2 : (B 2) 0 0 = 0) (hB3 : (B 3) 0 0 = s)
    (hs_sum : blockLetterAmplitude * star blockLetterAmplitude +
              s * star s = 1) :
    MPSTensor.transferMap B = LinearMap.id := by
  apply LinearMap.ext; intro X
  ext i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi, hj]
  rw [MPSTensor.transferMap_apply]
  calc
    (∑ p : Fin 4, (B p * X * (B p)ᴴ)) 0 0
        = ∑ p : Fin 4, ((B p * X * (B p)ᴴ) 0 0) := rfl
    _ = ∑ p : Fin 4, ((B p 0 0) * (X 0 0) * star (B p 0 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [one_by_one_mul_conj_apply (B p) X]
    _ = (X 0 0) * (∑ p : Fin 4, (B p 0 0) * star (B p 0 0)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => ?_); ring
    _ = (X 0 0) * (1 : ℂ) := by
      have hsum : (∑ p : Fin 4, (B p 0 0) * star (B p 0 0)) = (1 : ℂ) := by
        rw [Fin.sum_univ_four, hB0, hB1, hB2, hB3]
        simp
        simpa using hs_sum
      rw [hsum]
    _ = X 0 0 := by simp

private lemma katoCFBlock0_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock0 = LinearMap.id :=
  katoCFBlock_transferMap_eq_id_aux blockLetterAmplitude katoCFBlock0
    (by simp [katoCFBlock0]) (by simp [katoCFBlock0])
    (by simp [katoCFBlock0]) (by simp [katoCFBlock0])
    (by
      have hstar : star blockLetterAmplitude = blockLetterAmplitude := by
        rw [blockLetterAmplitude]; simp
      rw [hstar, ← pow_two, blockLetterAmplitude_sq]
      norm_num)

private lemma katoCFBlock1_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock1 = LinearMap.id :=
  katoCFBlock_transferMap_eq_id_aux (-blockLetterAmplitude) katoCFBlock1
    (by simp [katoCFBlock1]) (by simp [katoCFBlock1])
    (by simp [katoCFBlock1]) (by simp [katoCFBlock1])
    (by
      have hstar_amp : star blockLetterAmplitude = blockLetterAmplitude := by
        rw [blockLetterAmplitude]; simp
      have hstar_neg : star (-blockLetterAmplitude) = -blockLetterAmplitude := by
        simp [hstar_amp]
      rw [hstar_amp, hstar_neg]
      ring_nf
      rw [blockLetterAmplitude_sq]
      norm_num)

private lemma katoCFBlocks_normal (k : Fin 2) : MPSTensor.IsNormalTensor (katoCFBlocks k) := by
  fin_cases k
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock0 katoCFBlock0_transferMap_eq_id
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock1 katoCFBlock1_transferMap_eq_id

private theorem toMPSTensor_eq_toTensorFromBlocks :
    MPOTensor.toMPSTensor tensor = MPSTensor.toTensorFromBlocks katoCFWeights katoCFBlocks := by
  let e : (Σ _k : Fin 2, Fin 1) ≃ Fin 2 := finSigmaFinEquiv
  have hflat (k : Fin 2) : e ⟨k, (0 : Fin 1)⟩ = k := by fin_cases k <;> rfl
  have hflat_symm (k : Fin 2) : e.symm k = ⟨k, (0 : Fin 1)⟩ := by
    apply e.injective; rw [e.apply_symm_apply, hflat]
  funext p; ext x y
  simp only [MPOTensor.toMPSTensor, MPSTensor.toTensorFromBlocks,
    Matrix.reindex_apply, katoCFWeights, katoCFBlocks]
  change tensor (p.divNat) (p.modNat) x y =
    (Matrix.blockDiagonal' (fun k : Fin 2 => (katoCFWeights k) • (katoCFBlocks k p)))
      (e.symm x) (e.symm y)
  rw [hflat_symm x, hflat_symm y]
  by_cases h : x = y
  · subst y
    simp [Matrix.blockDiagonal', katoCFWeights, katoCFBlocks, katoCFBlock0, katoCFBlock1]
    by_cases hp_diag : p.divNat = p.modNat
    · have hp_val : p = 0 ∨ p = 3 := by
        fin_cases p
        · left; rfl
        · exfalso
          apply (by decide : ¬ ((1 : Fin (2*2)).divNat = (1 : Fin (2*2)).modNat))
          exact hp_diag
        · exfalso
          apply (by decide : ¬ ((2 : Fin (2*2)).divNat = (2 : Fin (2*2)).modNat))
          exact hp_diag
        · right; rfl
      rcases hp_val with rfl | rfl
      · fin_cases x
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat,
            katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat,
            katoCFBlock1, block1Weight_times_amplitude]
      · fin_cases x
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat,
            katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat,
            katoCFBlock1, block1Weight_times_amplitude]
    · -- p.divNat ≠ p.modNat means p is 1 or 2; tensor = 0 and blocks = 0
      have hp12 : p = (1 : Fin (2*2)) ∨ p = (2 : Fin (2*2)) := by
        fin_cases p
        · exfalso; exact hp_diag (by decide : ((0 : Fin (2*2)).divNat = (0 : Fin (2*2)).modNat))
        · left; rfl
        · right; rfl
        · exfalso; exact hp_diag (by decide : ((3 : Fin (2*2)).divNat = (3 : Fin (2*2)).modNat))
      rcases hp12 with rfl | rfl
      · -- p = (1 : Fin (2*2)); divNat ≠ modNat, so tensor=0 and blocks=0
        have h1 : ¬ ((1 : Fin (2*2)).divNat = (1 : Fin (2*2)).modNat) := by decide
        rw [tensor, if_neg h1]
        fin_cases x <;> simp [katoCFBlock0, katoCFBlock1]
      · -- p = (2 : Fin (2*2)); divNat ≠ modNat, so tensor=0 and blocks=0
        have h2 : ¬ ((2 : Fin (2*2)).divNat = (2 : Fin (2*2)).modNat) := by decide
        rw [tensor, if_neg h2]
        fin_cases x <;> simp [katoCFBlock0, katoCFBlock1]
  · rw [Matrix.blockDiagonal'_apply_ne (fun k : Fin 2 => (katoCFWeights k) • (katoCFBlocks k p))
      (0 : Fin 1) (0 : Fin 1) h]
    by_cases hp_diag : p.divNat = p.modNat
    · have hp_val : p = 0 ∨ p = 3 := by
        fin_cases p
        · left; rfl
        · exfalso
          apply (by decide : ¬ ((1 : Fin (2*2)).divNat = (1 : Fin (2*2)).modNat))
          exact hp_diag
        · exfalso
          apply (by decide : ¬ ((2 : Fin (2*2)).divNat = (2 : Fin (2*2)).modNat))
          exact hp_diag
        · right; rfl
      rcases hp_val with rfl | rfl
      · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, h]
      · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, h]
    · -- p.divNat ≠ p.modNat: tensor evaluates to 0 because off-diagonal physical letter
      rw [tensor, if_neg hp_diag]
      simp

/-- The doubled-index MPS tensor of Kato's $p=1/2$ tensor is in literal CPSV
canonical form (arXiv:1606.00608, Section 2.3, eq. `II_CF1`, lines 214–245):
a weighted direct sum of two normal bond-one tensors.

Source: the tensor is arXiv:2410.22696 lines 712–721; the canonical form
verification follows the construction in arXiv:1606.00608 Section 2.3. -/
theorem tensor_toMPSTensor_isCPSVCanonicalForm :
    MPSTensor.IsCPSVCanonicalForm (MPOTensor.toMPSTensor tensor) := by
  rw [toMPSTensor_eq_toTensorFromBlocks]
  exact (MPSTensor.CPSVCanonicalFormData.ofBlocks
    (fun _ => by norm_num) katoCFWeights katoCFBlocks
    katoCFBlocks_normal).isCPSVCanonicalForm

/-! ### Strong Area Law (SAL)

The saturation of the area law (arXiv:1606.00608, Definition 4.6, line 811)
requires the mutual information chain $I_1 = I_2 = \dots$ with
$I_L = S_L + S_{N-L} - S_N$ (line 797).  For Kato's $p=1/2$ tensor
the block reduced states are maximally mixed for non-full blocks,
which forces $S_L = L \log 2$ and cancels the $N$-dependence.
**All entropy computations in this section are project derivations,
not stated by Kato or CPSV16.** -/

/-- When the unnormalized MPO has unit trace the normalized MPO collapses
to the bare MPO.  This relies on `trace_mpo_tensor` giving trace 1. -/
private lemma normalizedMPO_tensor_eq_mpo (N : ℕ) (hN : 0 < N) :
    normalizedMPO tensor N = mpo tensor N := by
  rw [normalizedMPO, trace_mpo_tensor N hN, inv_one, one_smul]

/-- The site-sum vanishes: $\sum_{a=0,1} \operatorname{siteSign} a = 1+(-1)=0$. -/
private lemma sum_siteSign_eq_zero : (∑ a : Fin 2, siteSign a) = (0 : ℂ) := by
  calc
    (∑ a : Fin 2, siteSign a) = siteSign 0 + siteSign 1 := Fin.sum_univ_two _
    _ = (1 : ℂ) + (-1 : ℂ) := by simp [siteSign, pauliZ]
    _ = 0 := by ring

/-- Sum of `configurationSign` over all binary words of length $n$
vanishes when $n > 0$.  This is the distributive-law identity
$\sum_{w} \prod_k \operatorname{siteSign}(w_k)
  = \prod_k \sum_{a} \operatorname{siteSign}(a) = 0^n$.
(project derivation) -/
private lemma sum_configurationSign_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ w : Fin n → Fin 2, configurationSign w = 0 := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  calc
    ∑ w : Fin n → Fin 2, configurationSign w
        = ∑ w : Fin n → Fin 2, (∏ k : Fin n, siteSign (w k)) := rfl
    _ = ∑ w ∈ (Fintype.piFinset fun (_ : Fin n) => (Finset.univ : Finset (Fin 2))),
        (∏ k : Fin n, siteSign (w k)) := by simp [Fintype.piFinset_univ]
    _ = ∏ k : Fin n, (∑ a ∈ (Finset.univ : Finset (Fin 2)), siteSign a) := by
      rw [← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
        (fun (_ : Fin n) a => siteSign a)]
    _ = ∏ k : Fin n, (∑ a : Fin 2, siteSign a) := by simp
    _ = ∏ k : Fin n, (0 : ℂ) := by rw [sum_siteSign_eq_zero]
    _ = 0 := by
      rw [Finset.prod_const, Finset.card_univ, hcard]
      exact zero_pow hn.ne'

/-- `configurationSign` factorises through `Fin.append`.
For $u : \operatorname{Fin} L \to \operatorname{Fin} 2$ and
$w : \operatorname{Fin} M \to \operatorname{Fin} 2$,
$\operatorname{configurationSign}(u \mathbin{+\!\!+} w)
  = \operatorname{configurationSign}(u) \cdot \operatorname{configurationSign}(w)$.
(project derivation) -/
private lemma configurationSign_append {L M : ℕ}
    (u : Fin L → Fin 2) (w : Fin M → Fin 2) :
    configurationSign (Fin.append u w) = configurationSign u * configurationSign w := by
  rw [configurationSign, configurationSign, configurationSign]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- `configurationSign` is invariant under the canonical bijection
$\operatorname{Fin} N \simeq \operatorname{Fin}(L+M)$ given by $h_N : N = L + M$:
for $u : \operatorname{Fin} L \to \operatorname{Fin} 2$ and
$w : \operatorname{Fin} M \to \operatorname{Fin} 2$,
$\operatorname{configurationSign}(u \mathbin{+\!\!+} w \circ e_{h_N})
  = \operatorname{configurationSign}(u) \cdot \operatorname{configurationSign}(w)$.
(project derivation) -/
private lemma configurationSign_append_cast {L M N : ℕ} (hN : N = L + M)
    (u : Fin L → Fin 2) (w : Fin M → Fin 2) :
    configurationSign (Fin.append u w ∘ Fin.cast hN) =
      configurationSign u * configurationSign w := by
  subst hN
  simp [configurationSign_append]

/-- The $(u,v)$ entry of the reduced block state of the Kato tensor.

When $u = v$ the entry is the constant $(1/2)^L$ plus the sign term
(which vanishes when the complement is nonempty, i.e. $L < N$).
When $u \neq v$ the entry is zero because the MPO is diagonal.

(project derivation) -/
private lemma reducedBlockState_tensor_apply_eq {N L : ℕ} (hL : L ≤ N) (hNpos : 0 < N)
    (u v : Fin L → Fin 2) :
    reducedBlockState tensor N L hL u v =
      if u = v then ((1 / 2 : ℂ) ^ L)
                   + ((1 / 4 : ℂ) ^ N) * (configurationSign u) *
                       (∑ w : Fin (N - L) → Fin 2, configurationSign w)
      else 0 := by
  set M := N - L with hM
  have hNM : N = L + M := by omega
  have hcard_fun : Fintype.card (Fin M → Fin 2) = 2 ^ M := by
    simp
  rw [reducedBlockState_eq_sum tensor hL u v,
    normalizedMPO_tensor_eq_mpo N hNpos,
    mpo_tensor_eq_diagonal N]
  by_cases huv : u = v
  · subst huv
    simp only [Matrix.diagonal_apply_eq]
    -- ∑ w, ((1/2)^N + (1/4)^N * configurationSign (Fin.append u w ∘ Fin.cast hNM))
    rw [Finset.sum_add_distrib]
    congr 1
    · -- ∑ w, (1/2)^N = (1/2)^L
      rw [Finset.sum_const, Finset.card_univ, hcard_fun, hNM]
      -- Goal: (2 ^ M : ℕ) • ((1 / 2 : ℂ) ^ (L + M)) = (1 / 2 : ℂ) ^ L
      -- Convert ℕ-scalar multiplication to ℂ multiplication
      simpa [nsmul_eq_mul] using calc
        ((2 : ℂ) ^ M) * (((1 : ℂ) / 2) ^ (L + M))
            = ((2 : ℂ) ^ M) * (((1 : ℂ) / 2) ^ L * ((1 : ℂ) / 2) ^ M) := by rw [pow_add]
        _ = (((2 : ℂ) ^ M) * ((1 / 2 : ℂ) ^ M)) * ((1 / 2 : ℂ) ^ L) := by ring
        _ = (((2 : ℂ) * (1 / 2 : ℂ)) ^ M) * ((1 / 2 : ℂ) ^ L) := by rw [mul_pow]
        _ = (1 ^ M) * ((1 / 2 : ℂ) ^ L) := by ring
        _ = (1 : ℂ) * ((1 / 2 : ℂ) ^ L) := by simp
        _ = (1 / 2 : ℂ) ^ L := by simp
    · -- ∑ w, (1/4)^N * configurationSign (Fin.append u w ∘ Fin.cast hNM)
      -- = (1/4)^N * configurationSign u * (∑ w, configurationSign w)
      calc
        (∑ w : Fin M → Fin 2,
            ((1 / 4 : ℂ) ^ N *
              configurationSign (Fin.append u w ∘ Fin.cast hNM)))
            = (∑ w : Fin M → Fin 2,
                ((1 / 4 : ℂ) ^ N *
                  (configurationSign u * configurationSign w))) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [configurationSign_append_cast hNM u w]
        _ = ((1 / 4 : ℂ) ^ N) * (configurationSign u) *
            (∑ w : Fin M → Fin 2, configurationSign w) := by
          simp [Finset.mul_sum, mul_assoc]
  · -- u ≠ v: each term in the sum is zero because the MPO is diagonal
    have hterm_zero : ∀ w : Fin M → Fin 2,
        (Matrix.diagonal fun σ : Fin N → Fin 2 =>
          (1 / 2 : ℂ) ^ N + (1 / 4 : ℂ) ^ N * configurationSign σ)
        (Fin.append u w ∘ Fin.cast hNM) (Fin.append v w ∘ Fin.cast hNM) = 0 := by
      intro w
      have hne : Fin.append u w ∘ Fin.cast hNM ≠ Fin.append v w ∘ Fin.cast hNM := by
        intro heq
        apply huv
        -- Cancelling Fin.cast hNM (which is an Equiv, hence surjective)
        have hcast_eq_fun : (Fin.cast hNM : Fin N → Fin (L + M)) = (finCongr hNM) := by
          ext i; simp
        have heq' : Fin.append u w = Fin.append v w := by
          ext i
          have h_eq_val : Fin.append u w i = Fin.append v w i := by
            obtain ⟨j, hj⟩ := (finCongr hNM).surjective i
            calc
              Fin.append u w i = Fin.append u w ((finCongr hNM) j) := by rw [hj]
              _ = Fin.append u w ((Fin.cast hNM) j) := by rw [hcast_eq_fun]
              _ = (Fin.append u w ∘ Fin.cast hNM) j := rfl
              _ = (Fin.append v w ∘ Fin.cast hNM) j := by rw [heq]
              _ = Fin.append v w ((Fin.cast hNM) j) := rfl
              _ = Fin.append v w ((finCongr hNM) j) := by rw [hcast_eq_fun]
              _ = Fin.append v w i := by rw [hj]
          exact congrArg Fin.val h_eq_val
        funext i
        have hi := congrArg (fun f : Fin (L + M) → Fin 2 => f (Fin.castAdd M i)) heq'
        simpa [Fin.append_left] using hi
      rw [Matrix.diagonal_apply_ne _ hne]
    have hsum : (∑ w : Fin M → Fin 2,
        (Matrix.diagonal fun σ : Fin N → Fin 2 =>
          (1 / 2 : ℂ) ^ N + (1 / 4 : ℂ) ^ N * configurationSign σ)
        (Fin.append u w ∘ Fin.cast hNM) (Fin.append v w ∘ Fin.cast hNM)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [hterm_zero w]
    rw [hsum]
    simp [huv]

/-- When $1 \le L < N$ the reduced block state of the Kato tensor on
$L$ spins is maximally mixed:
$\rho_L = 2^{-L} \cdot \mathbf{1}$.
(project derivation) -/
private lemma reducedBlockState_tensor_eq_scaled_one {N L : ℕ}
    (hLpos : 1 ≤ L) (hLN : L < N) (hL : L ≤ N := Nat.le_of_lt hLN) :
    reducedBlockState tensor N L hL =
      ((2 : ℂ)⁻¹ ^ L : ℂ) •
      (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) := by
  ext u v
  rw [reducedBlockState_tensor_apply_eq hL (by omega) u v]
  by_cases huv : u = v
  · subst huv
    have hsum_zero : (∑ w : Fin (N - L) → Fin 2, configurationSign w) = 0 :=
      sum_configurationSign_eq_zero (Nat.sub_pos_of_lt hLN)
    simp [hsum_zero, Matrix.one_apply_eq,
      show ((1 : ℂ) / 2) = (2 : ℂ)⁻¹ by norm_num]
  · simp [huv, Matrix.one_apply_ne huv, smul_apply]

/-- For $d \neq 0$, $d \cdot \operatorname{negMulLog}(d^{-1}) = \log d$
(project derivation). -/
private lemma negMulLog_pow_inv_mul (d : ℝ) (hd : d ≠ 0) :
    d * Real.negMulLog (d⁻¹) = Real.log d := by
  rw [Real.negMulLog]
  calc
    d * (-(d⁻¹) * Real.log (d⁻¹)) = -(d * d⁻¹ * Real.log (d⁻¹)) := by ring
    _ = -(1 * Real.log (d⁻¹)) := by
      field_simp [hd]
    _ = -Real.log (d⁻¹) := by simp
    _ = Real.log d := by rw [Real.log_inv, neg_neg]

/-- The block entropy $S_L$ for the Kato tensor equals $L \log 2$
whenever $1 \le L < N$ (so the block is a proper subsystem).
(project derivation; the maximally-mixed computation above
and the entropy of a scalar matrix are not in Kato or CPSV16.) -/
private lemma blockEntropy_tensor_eq {N L : ℕ} (hLpos : 1 ≤ L) (hLN : L < N)
    (hL : L ≤ N) (hM : (mpo tensor N).PosSemidef) :
    blockEntropy tensor N L hL hM = L * Real.log 2 := by
  rw [blockEntropy]
  have hrho_herm : (reducedBlockState tensor N L hL).IsHermitian :=
    reducedBlockState_isHermitian tensor N L hL hM
  have hrho_eq : reducedBlockState tensor N L hL =
      ((2 : ℂ)⁻¹ ^ L : ℂ) • (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) :=
    reducedBlockState_tensor_eq_scaled_one hLpos hLN
  -- Hermitian proof for the scaled identity
  have hc_selfadj : IsSelfAdjoint ((2 : ℂ)⁻¹ ^ L : ℂ) := by
    simp [IsSelfAdjoint]
  have h_scaled_herm : (((2 : ℂ)⁻¹ ^ L : ℂ) •
      (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ)).IsHermitian :=
    (Matrix.isHermitian_one (n := Fin L → Fin 2) (α := ℂ)).smul hc_selfadj
  rw [vonNeumannEntropy_congr hrho_eq hrho_herm h_scaled_herm]
  -- Now compute von Neumann entropy of c • 1 via charpoly
  rw [vonNeumannEntropy_eq_charpoly_roots _ h_scaled_herm]
  have h_card : Fintype.card (Fin L → Fin 2) = 2 ^ L := by
    simp [Fintype.card_fun, Fintype.card_fin]
  have h_charpoly : (((2 : ℂ)⁻¹ ^ L : ℂ) •
      (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ)).charpoly =
      (Polynomial.X - Polynomial.C ((2 : ℂ)⁻¹ ^ L : ℂ)) ^
        (Fintype.card (Fin L → Fin 2)) := by
    calc
      _ = (Matrix.diagonal fun _ : Fin L → Fin 2 => ((2 : ℂ)⁻¹ ^ L : ℂ)).charpoly := by
        rw [Matrix.smul_one_eq_diagonal]
      _ = ∏ _i : Fin L → Fin 2,
          (Polynomial.X - Polynomial.C ((2 : ℂ)⁻¹ ^ L : ℂ)) :=
        Matrix.charpoly_diagonal
          (fun _ : Fin L → Fin 2 => ((2 : ℂ)⁻¹ ^ L : ℂ))
      _ = (Polynomial.X - Polynomial.C ((2 : ℂ)⁻¹ ^ L : ℂ)) ^
          (Fintype.card (Fin L → Fin 2)) := by
        simp
  rw [h_charpoly, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  simp only [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton,
    Multiset.sum_singleton]
  -- Now we have: (Fintype.card ... : ℝ) • Real.negMulLog (...) = ...
  -- where • is nsmul; convert to multiplication
  rw [nsmul_eq_mul]
  rw [h_card]
  have h_re : (((2 : ℂ)⁻¹ ^ L : ℂ).re : ℝ) = ((2⁻¹ : ℝ) ^ L) := by
    calc
      (((2 : ℂ)⁻¹ ^ L : ℂ).re : ℝ) =
          ((((2⁻¹ : ℝ) : ℂ) ^ L : ℂ).re : ℝ) := by norm_num
      _ = ((((2⁻¹ : ℝ) ^ L : ℝ) : ℂ).re : ℝ) := by rw [Complex.ofReal_pow]
      _ = ((2⁻¹ : ℝ) ^ L : ℝ) := by rw [Complex.ofReal_re]
  rw [h_re]
  -- Now: (2^L : ℝ) * Real.negMulLog (((2⁻¹ : ℝ) ^ L)) = L * Real.log 2
  have h_inv : ((2⁻¹ : ℝ) ^ L) = ((2 ^ L : ℝ)⁻¹) := by
    simp [inv_pow]
  rw [h_inv]
  -- Goal: ↑(2 ^ L) * Real.negMulLog ((2 ^ L : ℝ)⁻¹) = ↑L * Real.log 2
  -- Push the Nat.cast through
  push_cast
  -- Goal: (2 ^ L : ℝ) * Real.negMulLog ((2 ^ L : ℝ)⁻¹) = (L : ℝ) * Real.log 2
  rw [negMulLog_pow_inv_mul ((2 : ℝ) ^ L) (pow_ne_zero L (by norm_num : (2 : ℝ) ≠ 0))]
  rw [Real.log_pow]

/-- Kato's $p=1/2$ tensor saturates the area law (arXiv:1606.00608,
Definition 4.6, line 811): the mutual information $I_L$ is constant
in the block size $L$ for $1 \le L < \lfloor N/2\rfloor$.

The proof: for a proper subsystem, the reduced state is maximally mixed,
so $S_L = L \log 2$ (project derivation).  Therefore
$I_L = L\log 2 + (N-L)\log 2 - c_N = N\log 2 - c_N$
which is independent of $L$. -/
theorem tensor_isSAL : IsSAL tensor := by
  refine ⟨tensor_isMPDO, ?_, ?_⟩
  · -- ∀ N, 0 < N → (mpo tensor N).trace ≠ 0
    intro N hN
    rw [trace_mpo_tensor N hN]
    norm_num
  · -- ∀ N L, 1 ≤ L → (hL : L < N / 2) →
    --   mutualInfoChain ... L ... = mutualInfoChain ... (L+1) ...
    intro N L hLpos hL_lt_half
    have hM : (mpo tensor N).PosSemidef :=
      tensor_isMPDO N (by omega)
    -- mutualInfoChain expands to blockEntropy with specific hL proofs.
    -- We use `apply` with blockEntropy_tensor_eq so Lean unifies the proof terms.
    simp only [mutualInfoChain]
    have hL_val : blockEntropy tensor N L
        (Nat.le_of_lt (hL_lt_half.trans_le (Nat.div_le_self N 2))) hM =
        (L : ℝ) * Real.log 2 := by
      apply blockEntropy_tensor_eq hLpos (by omega) _ hM
    have hNL_val : blockEntropy tensor N (N - L) (Nat.sub_le N L) hM =
        ((N - L : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_tensor_eq (by omega) (by omega) _ hM
    have hLp1_val : blockEntropy tensor N (L + 1)
        (hL_lt_half.trans_le (Nat.div_le_self N 2)) hM =
        ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_tensor_eq (by omega) (by omega) _ hM
    have hNLp1_val : blockEntropy tensor N (N - (L + 1))
        (Nat.sub_le N (L + 1)) hM =
        ((N - (L + 1) : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_tensor_eq (by omega) (by omega) _ hM
    rw [hL_val, hNL_val, hLp1_val, hNLp1_val]
    -- Cancel the S_N term (blockEntropy N N) from both sides
    -- Then simplify L*log2 + (N-L)*log2 = (L+1)*log2 + (N-(L+1))*log2
    -- Both sides equal N*log2
    have hcast1 : ((N - L : ℕ) : ℝ) = (N : ℝ) - (L : ℝ) := Nat.cast_sub (by omega)
    have hcast2 : ((N - (L + 1) : ℕ) : ℝ) = (N : ℝ) - ((L + 1 : ℕ) : ℝ) :=
      Nat.cast_sub (by omega)
    have hcast3 : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by simp
    rw [hcast1, hcast2, hcast3]
    ring

/-- Kato's $p=1/2$ tensor is in CPSV canonical form, generates MPDO,
has idempotent physical-trace transfer, saturates the area law, but
admits no fixed-scale renormalization a la arXiv:1606.00608
Definition 4.1. -/
theorem exists_isCPSVCanonicalForm_isMPDO_idempotent_isSAL_not_isRFPViaTS :
    ∃ K : MPOTensor 2 2,
      MPSTensor.IsCPSVCanonicalForm K.toMPSTensor ∧
      IsMPDO K ∧
      (physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) ∧
      IsSAL K ∧
      ¬ IsRFPViaTS K := by
  refine ⟨tensor, ?_, tensor_isMPDO, physTraceTransfer_tensor_idempotent, tensor_isSAL,
    tensor_not_isRFPViaTS⟩
  -- The canonical form is stated for the MPSTensor, not MPOTensor.toMPSTensor
  -- But the theorem `tensor_toMPSTensor_isCPSVCanonicalForm` gives exactly this
  exact tensor_toMPSTensor_isCPSVCanonicalForm

end MPOTensor.KatoDeformedRFPObstruction
