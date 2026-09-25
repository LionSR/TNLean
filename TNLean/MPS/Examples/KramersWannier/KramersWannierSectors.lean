/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.KramersWannier.KramersWannierSource
import QICLean.Algebra.PosSemidefSupport

/-!
# Kramers–Wannier duality: sectors, partial isometry, and coupling exchange

**Source.** Aasen, Mong, Fendley 2016 (arXiv:1601.07185), subsection "The duality defect",
`References/1601.07185/source/Ising-Defects.tex` lines 1026–1042: the duality defect is not
invertible, has a zero eigenvalue, and `D_σ²/2` is the projection onto the sector where the
spin-flip defect has eigenvalue `1`; lines 1008–1017: commuting the duality defect through the
lattice interchanges the two couplings. Seiberg, Shao 2023 (arXiv:2307.02534),
`References/2307.02534/source/Majoranadraft.tex` line 2423: the non-invertible translation has
kernel the states with `η = -1` and acts unitarily on the states with `η = +1`, a partial
isometry; line 2475: `𝖣 𝖣† = 𝖣† 𝖣 = ½(1 + η)`. Their operator and `η = ∏_j Z_j` act in the
basis exchanged by the Hadamard gate; the statements here are about `K` and the spin flip
`∏_j X_j`, and the corresponding statements for their circuit are in
`TNLean.MPS.Examples.KramersWannier.KramersWannierCircuit`.

**Formalized here.** For the raw periodic duality operator `K = kwTensor.mpo N` on a ring of
`N ≥ 1` sites: its kernel is exactly the spin-flip-odd sector, its range is exactly the
spin-flip-even sector, and its rank is `2^{N-1}`. The normalized operators `D_σ = 2^{-N/2} K`
and `U = 2^{-(N+1)/2} K` satisfy `D_σ† D_σ = D_σ D_σ† = 1 + η` and
`U† U = U U† = ½(1 + η)`. For the periodic transverse-field Ising Hamiltonian
`H(J, h) = -J ∑_j Z_j Z_{j+1} - h ∑_j X_j`, the coupling exchange `K H(J, h) = H(h, J) K`.

The rank formula and the Hamiltonian form of the coupling exchange are not printed in either
source: Aasen–Mong–Fendley state the exchange for transfer matrices, and Seiberg–Shao only the
commutation at their self-dual point. They are project results derived here from the relations
the sources do print.

## Main definitions

* `KWExample.isingHamiltonian`: the periodic transverse-field Ising Hamiltonian `H(J, h)`.

## Main results

* `KWExample.kwTensor_mpo_mulVec_eq_zero_iff`: `K v = 0 ↔ η v = -v`.
* `KWExample.exists_kwTensor_mpo_mulVec_eq_iff`: `y ∈ range K ↔ η y = y`.
* `KWExample.kwTensor_mpo_rank`: `rank K = 2^{N-1}`.
* `KWExample.kwDefect_conjTranspose_mul`, `KWExample.kwDefect_mul_conjTranspose`,
  `KWExample.kwTensor_mpo_normalized_conjTranspose_mul`,
  `KWExample.kwTensor_mpo_normalized_mul_conjTranspose`: the partial-isometry identities.
* `KWExample.kwTensor_mpo_mul_isingHamiltonian`: `K H(J, h) = H(h, J) K`.

## References

- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong,
  P. Fendley, *Topological defects on the lattice I: The Ising model*
- [arXiv:2307.02534](https://arxiv.org/abs/2307.02534) -- N. Seiberg, S.-H. Shao,
  *Majorana chain and Ising model -- (non-invertible) translations, anomalies, and emanant
  symmetries*
-/

noncomputable section

open scoped Matrix BigOperators ComplexOrder

namespace KWExample

open Complex (invSqrtTwo invSqrtTwo_pow_mul_self star_invSqrtTwo)

variable {N : ℕ}

/-! ### Kernel, range, and rank -/

/-- **The kernel of the duality is the spin-flip-odd sector**, `ker K = {v | η v = -v}`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1032 and 1042
(a zero eigenvalue, and `D_σ²/2` projects onto the sector where `D_ψ = 1`). This is also the
statement of arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` line 2423, read
in the Hadamard frame, where `η = ∏_j Z_j` becomes the spin flip `∏_j X_j`; the statement for the
circuit itself is `ssCircuit_mulVec_eq_zero_iff`. -/
theorem kwTensor_mpo_mulVec_eq_zero_iff [NeZero N] (v : (Fin N → Fin 2) → ℂ) :
    kwTensor.mpo N *ᵥ v = 0 ↔ spinFlip N *ᵥ v = -v := by
  refine ⟨fun h => ?_, kwTensor_mpo_mulVec_eq_zero_of_odd v⟩
  have h2 : ((kwTensor.mpo N)ᵀ * kwTensor.mpo N) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  rw [kwTensor_mpo_transpose_mul, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec] at h2
  have h3 := (smul_eq_zero.mp h2).resolve_left (pow_ne_zero _ two_ne_zero)
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h3

/-- **The range of the duality is the spin-flip-even sector**: `y` is in the range of `K`
exactly when `η y = y`.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` line 1042. This is
also the statement of arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex`
line 2423, read in the Hadamard frame; the statement for the circuit itself is
`exists_ssCircuit_mulVec_eq_iff`. -/
theorem exists_kwTensor_mpo_mulVec_eq_iff [NeZero N] (y : (Fin N → Fin 2) → ℂ) :
    (∃ v, kwTensor.mpo N *ᵥ v = y) ↔ spinFlip N *ᵥ y = y := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [Matrix.mulVec_mulVec, spinFlip_mul_kwTensor_mpo]
  · intro hy
    refine ⟨((2 : ℂ) ^ (N + 1))⁻¹ • ((kwTensor.mpo N)ᵀ *ᵥ y), ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, kwTensor_mpo_mul_transpose,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hy, ← two_smul ℂ y,
      smul_smul, smul_smul]
    rw [show ((2 : ℂ) ^ (N + 1))⁻¹ * (2 : ℂ) ^ N * 2 = 1 by
      rw [mul_assoc, ← pow_succ, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)], one_smul]

/-- The global spin flip is real symmetric. -/
theorem spinFlip_conjTranspose : (spinFlip N)ᴴ = spinFlip N := by
  ext c b
  rw [Matrix.conjTranspose_apply, ← Matrix.transpose_apply (M := spinFlip N), spinFlip_transpose]
  simp only [spinFlip]
  split_ifs <;> simp

/-- The spin flip fixes no configuration, so its trace vanishes at positive length. -/
theorem trace_spinFlip [NeZero N] : (spinFlip N).trace = 0 := by
  classical
  refine Finset.sum_eq_zero fun b _ => ?_
  simp only [Matrix.diag_apply, spinFlip]
  exact ite_eq_right (ne_flipConfig b)

/-- Project result: **the duality has rank `2^{N-1}`** at every positive length. The rank is
the trace of the projection `½(1 + η)`, since `rank K = rank (K† K)` and
`K† K = 2^N (1 + η)`. The sources state the kernel and the sectors but print no dimension. -/
theorem kwTensor_mpo_rank [NeZero N] : (kwTensor.mpo N).rank = 2 ^ (N - 1) := by
  classical
  set P : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ := (2 : ℂ)⁻¹ • (1 + spinFlip N) with hP
  have hK : (kwTensor.mpo N)ᴴ * kwTensor.mpo N = (2 : ℂ) ^ (N + 1) • P := by
    rw [kwTensor_mpo_conjTranspose_mul, hP, smul_smul, pow_succ,
      mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]
  have hherm : P.IsHermitian := by
    rw [Matrix.IsHermitian, hP, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, spinFlip_conjTranspose]
    simp
  have hidem : P * P = P := half_one_add_spinFlip_isIdempotentElem
  have hrank : (P.rank : ℝ) = (P.trace).re := hherm.rank_eq_trace_re_of_idem hidem
  have htr : P.trace = (2 : ℂ)⁻¹ * (2 : ℂ) ^ N := by
    rw [hP, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, trace_spinFlip, add_zero,
      smul_eq_mul]
    simp
  rw [← Matrix.rank_conjTranspose_mul_self, hK,
    Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ two_ne_zero))]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have hre : (P.trace).re = (2 : ℝ) ^ n := by
    rw [htr, pow_succ]
    have : (2 : ℂ)⁻¹ * ((2 : ℂ) ^ n * 2) = ((2 : ℝ) ^ n : ℝ) := by
      push_cast; field_simp
    rw [this, Complex.ofReal_re]
  rw [Nat.add_sub_cancel]
  exact_mod_cast hrank.trans hre

/-! ### The partial-isometry identities -/

/-- **`D_σ† D_σ = 1 + η`**, twice the projection `P_+ = ½(1 + η)` onto the spin-flip-even
sector.

Source: arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex` lines 1033–1041
(`D_σ² = 1 + D_ψ`, read with the return map `D_σᵀ = D_σ†`). -/
theorem kwDefect_conjTranspose_mul [NeZero N] :
    (kwDefect N)ᴴ * kwDefect N = 1 + spinFlip N := by
  rw [kwDefect, Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo, kwTensor_mpo_conjTranspose]
  exact kwDefect_transpose_mul

/-- **`D_σ D_σ† = 1 + η`**, the companion on the dual lattice. -/
theorem kwDefect_mul_conjTranspose [NeZero N] :
    kwDefect N * (kwDefect N)ᴴ = 1 + spinFlip N := by
  rw [kwDefect, Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo, kwTensor_mpo_conjTranspose]
  exact kwDefect_mul_transpose

/-- **`U† U = ½(1 + η)`** for `U = 2^{-(N+1)/2} K`: the partial-isometry normalization of
Seiberg–Shao, with initial projection onto the spin-flip-even sector.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2423 and 2475,
read in the Hadamard frame with `η` the spin flip; for the circuit itself this is
`ssCircuit_conjTranspose_mul`. -/
theorem kwTensor_mpo_normalized_conjTranspose_mul [NeZero N] :
    (invSqrtTwo ^ (N + 1) • kwTensor.mpo N)ᴴ * (invSqrtTwo ^ (N + 1) • kwTensor.mpo N) =
      (2 : ℂ)⁻¹ • (1 + spinFlip N) := by
  rw [Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_conjTranspose_mul, smul_smul, smul_smul, invSqrtTwo_pow_succ_mul_self]

/-- **`U U† = ½(1 + η)`**: the final projection of the partial isometry `U`.

Source: arXiv:2307.02534, `References/2307.02534/source/Majoranadraft.tex` lines 2423 and 2475,
read in the Hadamard frame with `η` the spin flip; for the circuit itself this is
`ssCircuit_mul_conjTranspose`. -/
theorem kwTensor_mpo_normalized_mul_conjTranspose [NeZero N] :
    (invSqrtTwo ^ (N + 1) • kwTensor.mpo N) * (invSqrtTwo ^ (N + 1) • kwTensor.mpo N)ᴴ =
      (2 : ℂ)⁻¹ • (1 + spinFlip N) := by
  rw [Matrix.conjTranspose_smul, star_pow, star_invSqrtTwo, Matrix.smul_mul, Matrix.mul_smul,
    kwTensor_mpo_mul_conjTranspose, smul_smul, smul_smul, invSqrtTwo_pow_succ_mul_self]

/-! ### Coupling exchange for the transverse-field Ising Hamiltonian -/

/-- The periodic transverse-field Ising Hamiltonian
`H(J, h) = -J ∑_j Z_j Z_{j+1} - h ∑_j X_j` with real couplings, one bond per site. -/
def isingHamiltonian (N : ℕ) [NeZero N] (J h : ℝ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  -((J : ℂ) • ∑ j : Fin N, siteZZ j) - (h : ℂ) • ∑ j : Fin N, siteX j

/-- Project result: **the duality exchanges the couplings**, `K H(J, h) = H(h, J) K`. Summing
`K Z_j Z_{j+1} = X_j K` and `K X_j = Z_{j-1} Z_j K` over the ring and reindexing the bonds by
`j ↦ j - 1` gives the identity. Aasen–Mong–Fendley state the interchange of the couplings for
the transfer matrices (arXiv:1601.07185, `References/1601.07185/source/Ising-Defects.tex`
lines 1008–1017). -/
theorem kwTensor_mpo_mul_isingHamiltonian [NeZero N] (J h : ℝ) :
    kwTensor.mpo N * isingHamiltonian N J h = isingHamiltonian N h J * kwTensor.mpo N := by
  have hZZ : kwTensor.mpo N * ∑ j : Fin N, siteZZ j = (∑ j : Fin N, siteX j) * kwTensor.mpo N := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j _ => kwTensor_mpo_mul_siteZZ j
  have hX : kwTensor.mpo N * ∑ j : Fin N, siteX j = (∑ j : Fin N, siteZZ j) * kwTensor.mpo N := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [kwTensor_mpo_mul_siteX]
    exact Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)
  simp only [isingHamiltonian, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, hZZ, hX]
  abel

/-- At the self-dual point the duality commutes with the Hamiltonian, `K H(J, J) = H(J, J) K`. -/
theorem kwTensor_mpo_mul_isingHamiltonian_self [NeZero N] (J : ℝ) :
    kwTensor.mpo N * isingHamiltonian N J J = isingHamiltonian N J J * kwTensor.mpo N :=
  kwTensor_mpo_mul_isingHamiltonian J J

end KWExample
