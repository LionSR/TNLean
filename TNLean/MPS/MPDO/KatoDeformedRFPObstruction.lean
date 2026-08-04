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
  intro h; have hpos := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2); apply hpos.ne'; exact_mod_cast h

private lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hsq_real : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
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
noncomputable def katoCFWeights : Fin 2 → ℂ := fun k => match k with | 0 => block0Weight | 1 => block1Weight

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
  fun p => if p = 0 then !![blockLetterAmplitude] else if p = 3 then !![-blockLetterAmplitude] else 0

noncomputable def katoCFBlocks : Fin 2 → MPSTensor 4 1 := fun k => match k with | 0 => katoCFBlock0 | 1 => katoCFBlock1

private lemma oneByOne_mul_apply (A B : Matrix (Fin 1) (Fin 1) ℂ) : (A * B) 0 0 = (A 0 0) * (B 0 0) := by
  rw [Matrix.mul_apply]
  have huniv : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by decide
  rw [huniv, Finset.sum_singleton]

private lemma oneByOne_mul_conj_apply (A X : Matrix (Fin 1) (Fin 1) ℂ) :
    (A * X * Aᴴ) 0 0 = (A 0 0) * (X 0 0) * star (A 0 0) := by
  calc
    (A * X * Aᴴ) 0 0 = ((A * X) * Aᴴ) 0 0 := rfl
    _ = (A * X) 0 0 * (Aᴴ) 0 0 := by rw [oneByOne_mul_apply]
    _ = ((A 0 0) * (X 0 0)) * (Aᴴ) 0 0 := by rw [oneByOne_mul_apply]
    _ = (A 0 0) * (X 0 0) * star (A 0 0) := by rw [Matrix.conjTranspose_apply]

private lemma katoCFBlock0_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock0 = LinearMap.id := by
  apply LinearMap.ext; intro X
  ext i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi, hj]
  rw [MPSTensor.transferMap_apply]
  calc
    (∑ p : Fin 4, (katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ)) 0 0
        = ∑ p : Fin 4, ((katoCFBlock0 p * X * (katoCFBlock0 p)ᴴ) 0 0) := rfl
    _ = ∑ p : Fin 4, ((katoCFBlock0 p 0 0) * (X 0 0) * star (katoCFBlock0 p 0 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [oneByOne_mul_conj_apply (katoCFBlock0 p) X]
    _ = (X 0 0) * (∑ p : Fin 4, (katoCFBlock0 p 0 0) * star (katoCFBlock0 p 0 0)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => ?_); ring
    _ = (X 0 0) * (1 : ℂ) := by
      have hsum : (∑ p : Fin 4, (katoCFBlock0 p 0 0) * star (katoCFBlock0 p 0 0)) = (1 : ℂ) := by
        have h0 : (katoCFBlock0 0) 0 0 = blockLetterAmplitude := by simp [katoCFBlock0]
        have h1 : (katoCFBlock0 1) 0 0 = (0 : ℂ) := by simp [katoCFBlock0]
        have h2 : (katoCFBlock0 2) 0 0 = (0 : ℂ) := by simp [katoCFBlock0]
        have h3 : (katoCFBlock0 3) 0 0 = blockLetterAmplitude := by simp [katoCFBlock0]
        rw [Fin.sum_univ_four, h0, h1, h2, h3]
        have hstar : star blockLetterAmplitude = blockLetterAmplitude := by
          rw [blockLetterAmplitude]; simp
        rw [hstar]
        simp [hstar]
        rw [← pow_two, blockLetterAmplitude_sq]
        norm_num
      rw [hsum]
    _ = X 0 0 := by simp

private lemma katoCFBlock1_transferMap_eq_id :
    MPSTensor.transferMap katoCFBlock1 = LinearMap.id := by
  apply LinearMap.ext; intro X
  ext i j
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi, hj]
  rw [MPSTensor.transferMap_apply]
  calc
    (∑ p : Fin 4, (katoCFBlock1 p * X * (katoCFBlock1 p)ᴴ)) 0 0
        = ∑ p : Fin 4, ((katoCFBlock1 p * X * (katoCFBlock1 p)ᴴ) 0 0) := rfl
    _ = ∑ p : Fin 4, ((katoCFBlock1 p 0 0) * (X 0 0) * star (katoCFBlock1 p 0 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [oneByOne_mul_conj_apply (katoCFBlock1 p) X]
    _ = (X 0 0) * (∑ p : Fin 4, (katoCFBlock1 p 0 0) * star (katoCFBlock1 p 0 0)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => ?_); ring
    _ = (X 0 0) * (1 : ℂ) := by
      have hsum : (∑ p : Fin 4, (katoCFBlock1 p 0 0) * star (katoCFBlock1 p 0 0)) = (1 : ℂ) := by
        have h0 : (katoCFBlock1 0) 0 0 = blockLetterAmplitude := by simp [katoCFBlock1]
        have h1 : (katoCFBlock1 1) 0 0 = (0 : ℂ) := by simp [katoCFBlock1]
        have h2 : (katoCFBlock1 2) 0 0 = (0 : ℂ) := by simp [katoCFBlock1]
        have h3 : (katoCFBlock1 3) 0 0 = -blockLetterAmplitude := by simp [katoCFBlock1]
        rw [Fin.sum_univ_four, h0, h1, h2, h3]
        have hstar : star blockLetterAmplitude = blockLetterAmplitude := by
          rw [blockLetterAmplitude]; simp
        rw [hstar]
        simp [hstar]
        rw [← pow_two, blockLetterAmplitude_sq]
        norm_num
      rw [hsum]
    _ = X 0 0 := by simp

private lemma katoCFBlocks_normal (k : Fin 2) : MPSTensor.IsNormalTensor (katoCFBlocks k) := by
  fin_cases k
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock0 katoCFBlock0_transferMap_eq_id
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      katoCFBlock1 katoCFBlock1_transferMap_eq_id

theorem toMPSTensor_eq_toTensorFromBlocks :
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
        · exfalso; apply (by decide : ¬ ((1 : Fin (2*2)).divNat = (1 : Fin (2*2)).modNat)); exact hp_diag
        · exfalso; apply (by decide : ¬ ((2 : Fin (2*2)).divNat = (2 : Fin (2*2)).modNat)); exact hp_diag
        · right; rfl
      rcases hp_val with rfl | rfl
      · fin_cases x
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, katoCFBlock1, block1Weight_times_amplitude]
      · fin_cases x
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, katoCFBlock0, block0Weight_times_amplitude]
        · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, katoCFBlock1, block1Weight_times_amplitude]
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
        · exfalso; apply (by decide : ¬ ((1 : Fin (2*2)).divNat = (1 : Fin (2*2)).modNat)); exact hp_diag
        · exfalso; apply (by decide : ¬ ((2 : Fin (2*2)).divNat = (2 : Fin (2*2)).modNat)); exact hp_diag
        · right; rfl
      rcases hp_val with rfl | rfl
      · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, h]
      · simp [tensor, siteSign, pauliZ, Fin.divNat, Fin.modNat, h]
    · -- p.divNat ≠ p.modNat: tensor evaluates to 0 because off-diagonal physical letter
      rw [tensor, if_neg hp_diag]
      simp

theorem tensor_toMPSTensor_isCPSVCanonicalForm :
    MPSTensor.IsCPSVCanonicalForm (MPOTensor.toMPSTensor tensor) := by
  rw [toMPSTensor_eq_toTensorFromBlocks]
  exact (MPSTensor.CPSVCanonicalFormData.ofBlocks
    (fun _ => by norm_num) katoCFWeights katoCFBlocks
    katoCFBlocks_normal).isCPSVCanonicalForm


end MPOTensor.KatoDeformedRFPObstruction
