/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BinaryConfigurationSign
import TNLean.MPS.MPDO.TwistedDimerMPDO
import TNLean.MPS.Symmetry.MPDO.Defs

/-!
# The twisted quantum dimer: strong and weak Pauli symmetries

**Source.** The project example `T` of `TNLean/MPS/MPDO/TwistedDimer.lean`, motivated by
Cirac, Pérez-García, Schuch, Verstraete 2017 (arXiv:1606.00608), Theorem 4.14 and
`Papers/1606.00608/MPDO-22-12-17-2.tex` lines 995–1010; it is not a tensor printed in the
source. Each site carries qubits `L`, `R` and a flag qubit `F`, and on the support of
`ρ^{(N)}(T)` the `R` qubit of site `n` equals the `L` qubit of site `n + 1`
(`mpo_T_entry_formula`). The strong and weak symmetries are those of Sun 2025
(arXiv:2504.16985), `References/2504.16985/main.tex` line 182.

**Formalized here.** Project result: at every positive length `ρ^{(N)}(T)` is strongly
symmetric with eigenvalue `1` under `(Z_L Z_R)^{⊗N}` and under `(X_L X_R Z_F)^{⊗N}`, and weakly
but not strongly symmetric under `(X_L X_R)^{⊗N}` and under `Z_F^{⊗N}`. The second strong
symmetry holds because flipping the `L` bit exchanges the two bond matrices `C_0`, `C_1`, and
multiplying by the flag sign exchanges the two flag signs `τ_0 = 1`, `τ_1 = Z`.

## Main definitions

* `sigmaZZ`, `flipXX`, `sigmaZF`, `flipXXZF`: the on-site operators `Z_L Z_R`, `X_L X_R`,
  `Z_F`, and `X_L X_R Z_F` in the encoding `physIdx l r f = 4 l + 2 r + f`.

## Main results

* `isStrongMPOSymmetry_sigmaZZ`, `isStrongMPOSymmetry_flipXXZF`: strong symmetries.
* `isWeakMPOSymmetry_flipXX`, `isWeakMPOSymmetry_sigmaZF`: weak symmetries.
* `not_isStrongMPOSymmetry_flipXX`, `not_isStrongMPOSymmetry_sigmaZF`: neither weak symmetry
  is strong.

## References
- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product density operators: Renormalization fixed points
  and boundary theories*
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### The on-site operators -/

/-- The operator `Z_L Z_R ⊗ 1_F` on one site. -/
def sigmaZZ : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal fun i => siteSign (bitL i) * siteSign (bitR i)

/-- The operator `1 ⊗ 1 ⊗ Z_F` on one site. -/
def sigmaZF : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal fun i => siteSign (bitF i)

/-- Flipping the `L` and `R` bits of a physical index. -/
def flipLR (i : Fin 8) : Fin 8 :=
  physIdx (bitL i).rev (bitR i).rev (bitF i)

@[simp] private lemma bitL_flipLR (i : Fin 8) : bitL (flipLR i) = (bitL i).rev := by
  simp [flipLR]

@[simp] private lemma bitR_flipLR (i : Fin 8) : bitR (flipLR i) = (bitR i).rev := by
  simp [flipLR]

@[simp] private lemma bitF_flipLR (i : Fin 8) : bitF (flipLR i) = bitF i := by
  simp [flipLR]

private lemma flipLR_flipLR (i : Fin 8) : flipLR (flipLR i) = i := by
  simp only [flipLR, bitL_physIdx, bitR_physIdx, bitF_physIdx, Fin.rev_rev, physIdx_bits]

/-- The operator `X_L X_R ⊗ 1_F` on one site. -/
def flipXX : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if j = flipLR i then 1 else 0

/-- The operator `X_L X_R ⊗ Z_F` on one site. -/
def flipXXZF : Matrix (Fin 8) (Fin 8) ℂ :=
  sigmaZF * flipXX

private lemma flipXX_apply (i j : Fin 8) : flipXX i j = if j = flipLR i then 1 else 0 := rfl

private lemma flipXX_apply' (i j : Fin 8) : flipXX i j = if i = flipLR j then 1 else 0 := by
  simp only [flipXX, Matrix.of_apply]
  exact if_congr ⟨fun h => by rw [h, flipLR_flipLR], fun h => by rw [h, flipLR_flipLR]⟩ rfl rfl

/-! ### Local identities -/

private lemma Cmat_rev_left (k p p' : Fin 2) : Cmat k p.rev p' = Cmat k p p'.rev := by
  fin_cases k <;> fin_cases p <;> fin_cases p' <;> rfl

private lemma Cmat_rev_left' (k p p' : Fin 2) : Cmat k p.rev p' = Cmat k.rev p p' := by
  fin_cases k <;> fin_cases p <;> fin_cases p' <;> rfl

private lemma siteSign_mul_tau (k f : Fin 2) :
    siteSign f * ((tau k f : ℝ) : ℂ) = ((tau k.rev f : ℝ) : ℂ) := by
  fin_cases k <;> fin_cases f <;> simp [siteSign, SpinCover.pauli, tau]

private lemma coef_flipLR_left (k : Fin 2) (i j : Fin 8) :
    coef k (flipLR i) j = coef k i (flipLR j) := by
  simp only [coef, bitF_flipLR, bitL_flipLR, Cmat_rev_left]

private lemma siteSign_mul_coef_flipLR (k : Fin 2) (i j : Fin 8) :
    siteSign (bitF i) * coef k (flipLR i) j = coef k.rev i j := by
  simp only [coef, bitF_flipLR, bitL_flipLR, Cmat_rev_left']
  split_ifs
  · push_cast
    rw [← siteSign_mul_tau]
    ring
  · simp

private lemma coef_eq_zero_of_bitF_ne {k : Fin 2} {i j : Fin 8} (h : bitF i ≠ bitF j) :
    coef k i j = 0 := by
  simp [coef, h]

/-! ### Configurations -/

private lemma isCyclicBondMatched_flipLR_iff {N : ℕ} (σ : Fin N → Fin 8) :
    IsCyclicBondMatched N (fun n => flipLR (σ n)) ↔ IsCyclicBondMatched N σ := by
  simp only [IsCyclicBondMatched, IsBondMatchedPair, bitR_flipLR, bitL_flipLR, Fin.rev_inj]

private lemma chainIndicator_flipLR_left {N : ℕ} (σ τ : Fin N → Fin 8) :
    chainIndicator N (fun n => flipLR (σ n)) τ = chainIndicator N σ τ := by
  simp only [chainIndicator, Matrix.of_apply, isCyclicBondMatched_flipLR_iff]

private lemma chainIndicator_flipLR_right {N : ℕ} (σ τ : Fin N → Fin 8) :
    chainIndicator N σ (fun n => flipLR (τ n)) = chainIndicator N σ τ := by
  simp only [chainIndicator, Matrix.of_apply, isCyclicBondMatched_flipLR_iff]

/-- On a configuration satisfying the cyclic matching condition, the `Z_L Z_R` signs multiply
to `1`. -/
private lemma prod_sigmaZZ_of_isCyclicBondMatched {N : ℕ} {σ : Fin N → Fin 8}
    (hσ : IsCyclicBondMatched N σ) :
    ∏ n, siteSign (bitL (σ n)) * siteSign (bitR (σ n)) = 1 := by
  rw [Finset.prod_mul_distrib]
  have h2 : ∏ n, siteSign (bitR (σ n)) = ∏ n, siteSign (bitL (σ n)) := by
    rw [← Equiv.prod_comp (finRotate N) (fun n => siteSign (bitL (σ n)))]
    exact Finset.prod_congr rfl fun n _ => by rw [hσ n]
  rw [h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun n _ => siteSign_mul_self _

private lemma chainIndicator_eq_zero_of_not {N : ℕ} {σ : Fin N → Fin 8}
    (hσ : ¬ IsCyclicBondMatched N σ) (τ : Fin N → Fin 8) : chainIndicator N σ τ = 0 := by
  simp [chainIndicator, hσ]

/-! ### Strong symmetries -/

/-- **Strong `Z_L Z_R` symmetry with eigenvalue `1`.**

Project result: at every positive length, `(Z_L Z_R)^{⊗N} ρ^{(N)}(T) = ρ^{(N)}(T)` (strong
symmetry, arXiv:2504.16985, line 182), because on the support the `R` bit of each site is the
`L` bit of the next, so the product of the signs is a square. -/
theorem isStrongMPOSymmetry_sigmaZZ :
    IsStrongMPOSymmetry (fun _ : Unit => onSite sigmaZZ) T fun _ _ => 1 := by
  intro _ L hL
  rw [mpo_onSite, sigmaZZ, Matrix.finKronecker_diagonal, one_smul]
  ext σ τ
  rw [Matrix.diagonal_mul]
  by_cases hσ : IsCyclicBondMatched L σ
  · rw [prod_sigmaZZ_of_isCyclicBondMatched hσ, one_mul]
  · rw [mpo_T_entry_formula hL, chainIndicator_eq_zero_of_not hσ]
    simp

/-- **Strong `X_L X_R Z_F` symmetry with eigenvalue `1`.**

Project result: at every positive length, `(X_L X_R Z_F)^{⊗N} ρ^{(N)}(T) = ρ^{(N)}(T)` (strong
symmetry, arXiv:2504.16985, line 182). Flipping the `L` and `R` bits preserves the matching
condition and, together with the flag sign, exchanges the two block labels of the one-site
coefficient: `Z_F · coef_k(X_L X_R i, j) = coef_{1-k}(i, j)`. -/
theorem isStrongMPOSymmetry_flipXXZF :
    IsStrongMPOSymmetry (fun _ : Unit => onSite flipXXZF) T fun _ _ => 1 := by
  intro _ L hL
  rw [mpo_onSite, flipXXZF, ← Matrix.finKronecker_mul, sigmaZF, Matrix.finKronecker_diagonal,
    one_smul, Matrix.mul_assoc]
  ext σ τ
  rw [Matrix.diagonal_mul, Matrix.finKronecker_mul_apply_of_eq_ite flipXX_apply,
    mpo_T_entry_formula hL, mpo_T_entry_formula hL, chainIndicator_flipLR_left, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  simp_rw [← Finset.prod_mul_distrib, siteSign_mul_coef_flipLR]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, add_comm]
  rfl

/-! ### Weak symmetries -/

/-- **Weak `X_L X_R` symmetry.**

Project result: at every positive length, `(X_L X_R)^{⊗N}` commutes with `ρ^{(N)}(T)` (weak
symmetry, arXiv:2504.16985, line 182): flipping the `L` and `R` bits preserves the matching
condition, and `C_k(1 - l, l') = C_k(l, 1 - l')`. -/
theorem isWeakMPOSymmetry_flipXX : IsWeakMPOSymmetry (fun _ : Unit => onSite flipXX) T := by
  intro _ L hL
  rw [mpo_onSite]
  change _ * _ = _ * _
  ext σ τ
  rw [Matrix.finKronecker_mul_apply_of_eq_ite flipXX_apply,
    Matrix.mul_finKronecker_apply_of_eq_ite flipXX_apply', mpo_T_entry_formula hL,
    mpo_T_entry_formula hL, chainIndicator_flipLR_left, chainIndicator_flipLR_right]
  simp only [coef_flipLR_left]

/-- **Weak `Z_F` symmetry.**

Project result: at every positive length, `Z_F^{⊗N}` commutes with `ρ^{(N)}(T)` (weak symmetry,
arXiv:2504.16985, line 182), because every one-site coefficient is diagonal in the flag bit. -/
theorem isWeakMPOSymmetry_sigmaZF : IsWeakMPOSymmetry (fun _ : Unit => onSite sigmaZF) T := by
  intro _ L hL
  rw [mpo_onSite, sigmaZF, Matrix.finKronecker_diagonal]
  change _ * _ = _ * _
  ext σ τ
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hf : ∀ n, bitF (σ n) = bitF (τ n)
  · simp only [hf]
    ring
  · push Not at hf
    obtain ⟨n, hn⟩ := hf
    have h0 : mpo T L σ τ = 0 := by
      rw [mpo_T_entry_formula hL]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
      exact Finset.prod_eq_zero (Finset.mem_univ n) (coef_eq_zero_of_bitF_ne hn)
    rw [h0, mul_zero, zero_mul]

/-! ### The weak symmetries are not strong -/

private lemma mpo_T_one_diag (i j : Fin 8) (hi : bitR i = bitL i) (hj : bitR j = bitL j) :
    mpo T 1 (fun _ => i) (fun _ => j) = ∑ k : Fin 2, coef k i j := by
  have hci : IsCyclicBondMatched 1 fun _ => i := fun _ => hi
  have hcj : IsCyclicBondMatched 1 fun _ => j := fun _ => hj
  rw [mpo_T_entry_formula one_pos]
  simp [chainIndicator, hci, hcj]

private lemma entry_00 : mpo T 1 (fun _ => 0) (fun _ => 0) = 7 / 16 := by
  rw [mpo_T_one_diag 0 0 (by decide) (by decide)]
  simp [Fin.sum_univ_two, coef, Cmat, tau, cDiag_eq, cOff_eq, bitL, bitF]
  norm_num

private lemma entry_60 : mpo T 1 (fun _ => 6) (fun _ => 0) = 7 / 16 := by
  rw [mpo_T_one_diag 6 0 (by decide) (by decide)]
  simp [Fin.sum_univ_two, coef, Cmat, tau, cDiag_eq, cOff_eq, bitL, bitF]
  norm_num

private lemma entry_11 : mpo T 1 (fun _ => 1) (fun _ => 1) = 1 / 16 := by
  rw [mpo_T_one_diag 1 1 (by decide) (by decide)]
  simp [Fin.sum_univ_two, coef, Cmat, tau, cDiag_eq, cOff_eq, bitL, bitF]
  norm_num

private lemma entry_71 : mpo T 1 (fun _ => 7) (fun _ => 1) = -1 / 16 := by
  rw [mpo_T_one_diag 7 1 (by decide) (by decide)]
  simp [Fin.sum_univ_two, coef, Cmat, tau, cDiag_eq, cOff_eq, bitL, bitF]
  norm_num

/-- **No strong `X_L X_R` symmetry at one site.**

Project result: at `N = 1`, `(X_L X_R) ρ^{(1)}(T)` is not a multiple of `ρ^{(1)}(T)`
(arXiv:2504.16985, line 182): in the flag sector `f = 0` the flip preserves the entries and in
the sector `f = 1` it reverses their sign. -/
theorem not_isStrongSymmetry_flipXX_one :
    ¬ Matrix.IsStrongSymmetry (Matrix.finKronecker fun _ : Fin 1 => flipXX) (mpo T 1) := by
  rintro ⟨c, hc⟩
  have e1 := congrFun (congrFun hc (fun _ => 0)) (fun _ => 0)
  have e2 := congrFun (congrFun hc (fun _ => 1)) (fun _ => 1)
  rw [Matrix.finKronecker_mul_apply_of_eq_ite flipXX_apply, Matrix.smul_apply] at e1 e2
  have h0 : (fun _ : Fin 1 => flipLR ((fun _ : Fin 1 => (0 : Fin 8)) 0)) = fun _ => 6 := by
    funext _; decide
  have h1 : (fun _ : Fin 1 => flipLR ((fun _ : Fin 1 => (1 : Fin 8)) 0)) = fun _ => 7 := by
    funext _; decide
  simp only [h0, h1, entry_00, entry_60, entry_11, entry_71, smul_eq_mul] at e1 e2
  have hc1 : c = 1 := by linear_combination -(16 / 7 : ℂ) * e1
  rw [hc1] at e2
  norm_num at e2

/-- **The family is not strongly `X_L X_R`-symmetric**, for any eigenvalues. -/
theorem not_isStrongMPOSymmetry_flipXX (c : Unit → ℕ → ℂ) :
    ¬ IsStrongMPOSymmetry (fun _ : Unit => onSite flipXX) T c := by
  intro h
  have h1 := h () 1 one_pos
  rw [mpo_onSite] at h1
  exact not_isStrongSymmetry_flipXX_one ⟨c () 1, h1⟩

/-- **No strong `Z_F` symmetry at one site.**

Project result: at `N = 1`, `Z_F ρ^{(1)}(T)` is not a multiple of `ρ^{(1)}(T)`
(arXiv:2504.16985, line 182): both flag sectors carry nonzero entries, with opposite signs
of `Z_F`. -/
theorem not_isStrongSymmetry_sigmaZF_one :
    ¬ Matrix.IsStrongSymmetry (Matrix.finKronecker fun _ : Fin 1 => sigmaZF) (mpo T 1) := by
  rintro ⟨c, hc⟩
  have e1 := congrFun (congrFun hc (fun _ => 0)) (fun _ => 0)
  have e2 := congrFun (congrFun hc (fun _ => 1)) (fun _ => 1)
  rw [sigmaZF, Matrix.finKronecker_diagonal, Matrix.diagonal_mul, Matrix.smul_apply] at e1 e2
  simp only [entry_00, entry_11, smul_eq_mul, Fin.prod_univ_one] at e1 e2
  norm_num [siteSign, SpinCover.pauli, bitF] at e1 e2
  rw [e1] at e2
  norm_num at e2

/-- **The family is not strongly `Z_F`-symmetric**, for any eigenvalues. -/
theorem not_isStrongMPOSymmetry_sigmaZF (c : Unit → ℕ → ℂ) :
    ¬ IsStrongMPOSymmetry (fun _ : Unit => onSite sigmaZF) T c := by
  intro h
  have h1 := h () 1 one_pos
  rw [mpo_onSite] at h1
  exact not_isStrongSymmetry_sigmaZF_one ⟨c () 1, h1⟩

end MPOTensor.TwistedDimer
