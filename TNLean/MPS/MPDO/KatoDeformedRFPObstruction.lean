/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.SectorTrace

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

end MPOTensor.KatoDeformedRFPObstruction
