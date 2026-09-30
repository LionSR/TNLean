/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample412Literal
import TNLean.MPS.Symmetry.MPDO.Defs

/-!
# CPSV16 Example 4.12: strong and weak Pauli symmetries of `I^{⊗N} + σ_z^{⊗N}`

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2017 (arXiv:1606.00608), Example 4.12,
`Papers/1606.00608/MPDO-22-12-17-2.tex` lines 932–939: the tensor with
`1 = M_{00}^{00} = M_{00}^{11} = M_{11}^{00} = -M_{11}^{11}` generates
`ρ^{(N)} = I^{⊗N} + σ_z^{⊗N}`. The strong and weak symmetries are those of Sun 2025
(arXiv:2504.16985), `References/2504.16985/main.tex` line 182; the source example does not
discuss symmetries.

**Formalized here.** Project result: the density operators are strongly symmetric under
`σ_z^{⊗N}` with eigenvalue `1` at every length. Under `σ_x^{⊗N}` they are never strongly
symmetric, and weakly symmetric exactly at even length, because
`σ_x^{⊗N} ρ^{(N)} σ_x^{⊗N} = I^{⊗N} + (-1)^N σ_z^{⊗N}`. So the family is not weakly
`σ_x`-symmetric in the all-lengths sense of the definition, while its restriction to even
lengths is.

## Main definitions

* `sigmaX`: the Pauli matrix `σ_x`.

## Main results

* `isStrongMPOSymmetry_sigmaZ`: strong `σ_z` symmetry with eigenvalue `1`.
* `isWeakSymmetry_sigmaX_iff_even`, `not_isStrongSymmetry_sigmaX`,
  `not_isWeakMPOSymmetry_sigmaX`: the `σ_x` behaviour.

## References
- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product density operators: Renormalization fixed points
  and boundary theories*
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
-/

open scoped Matrix BigOperators

namespace MPOTensor.CPSVExample412Literal

/-- The Pauli matrix `σ_x = |0⟩⟨1| + |1⟩⟨0|`. -/
noncomputable def sigmaX : Matrix (Fin 2) (Fin 2) ℂ :=
  SpinCover.pauli 0

private lemma sigmaX_apply (i j : Fin 2) : sigmaX i j = if j = i.rev then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [sigmaX, SpinCover.pauli]

private lemma sigmaX_apply' (i j : Fin 2) : sigmaX i j = if i = j.rev then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [sigmaX, SpinCover.pauli]

private lemma sigmaZ_eq_diagonal : sigmaZ = Matrix.diagonal siteSign := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, siteSign, SpinCover.pauli]

private lemma finKronecker_sigmaX_mul {N : ℕ}
    (B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (σ τ : Fin N → Fin 2) :
    ((Matrix.finKronecker fun _ : Fin N => sigmaX) * B) σ τ = B (fun n => (σ n).rev) τ :=
  Matrix.finKronecker_mul_apply_of_eq_ite sigmaX_apply B σ τ

private lemma mul_finKronecker_sigmaX {N : ℕ}
    (B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (σ τ : Fin N → Fin 2) :
    (B * Matrix.finKronecker fun _ : Fin N => sigmaX) σ τ = B σ (fun n => (τ n).rev) :=
  Matrix.mul_finKronecker_apply_of_eq_ite sigmaX_apply' B σ τ

private lemma configurationSign_rev {N : ℕ} (σ : Fin N → Fin 2) :
    configurationSign (fun n => (σ n).rev) = (-1) ^ N * configurationSign σ := by
  have h : ∀ i : Fin 2, siteSign i.rev = -siteSign i := by
    intro i
    fin_cases i <;> simp [siteSign, SpinCover.pauli]
  simp only [configurationSign, h, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

private lemma configurationSign_mul_self {N : ℕ} (σ : Fin N → Fin 2) :
    configurationSign σ * configurationSign σ = 1 := by
  rcases configurationSign_eq_one_or_neg_one σ with h | h <;> rw [h] <;> norm_num

/-- **Strong `σ_z` symmetry with eigenvalue `1`.**

Project result: `σ_z^{⊗N} (I^{⊗N} + σ_z^{⊗N}) = σ_z^{⊗N} + I^{⊗N}`, so the density operators
of the Example 4.12 tensor (arXiv:1606.00608, lines 932–939) are strongly symmetric in the
sense of arXiv:2504.16985, line 182, with eigenvalue `1` at every positive length. -/
theorem isStrongMPOSymmetry_sigmaZ :
    IsStrongMPOSymmetry (fun _ : Unit => onSite sigmaZ) M fun _ _ => 1 := by
  intro _ L _
  rw [mpo_onSite, sigmaZ_eq_diagonal, Matrix.finKronecker_diagonal, rho_eq_diagonal,
    Matrix.diagonal_mul_diagonal, one_smul]
  congr 1
  funext σ
  change configurationSign σ * (1 + configurationSign σ) = 1 + configurationSign σ
  rw [mul_add, mul_one, configurationSign_mul_self, add_comm]

/-- **Weak `σ_x` symmetry holds exactly at even length.**

Project result: for the Example 4.12 tensor (arXiv:1606.00608, lines 932–939),
`σ_x^{⊗N}` commutes with `ρ^{(N)} = I^{⊗N} + σ_z^{⊗N}` (weak symmetry at one length,
arXiv:2504.16985, line 182) exactly when `N` is even, since conjugation flips every spin and
multiplies `σ_z^{⊗N}` by `(-1)^N`. -/
theorem isWeakSymmetry_sigmaX_iff_even (N : ℕ) :
    Matrix.IsWeakSymmetry (Matrix.finKronecker fun _ : Fin N => sigmaX) (mpo M N) ↔
      Even N := by
  rw [← neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)]
  constructor
  · intro h
    have h1 := congrFun (congrFun h (fun _ => 0)) (fun _ => 1)
    rw [finKronecker_sigmaX_mul, mul_finKronecker_sigmaX, rho_eq_diagonal] at h1
    have hrev1 : (fun n : Fin N => ((fun _ => (1 : Fin 2)) n).rev) = fun _ => 0 := by
      funext _; rfl
    have hrev0 : (fun n : Fin N => ((fun _ => (0 : Fin 2)) n).rev) = fun _ => 1 := by
      funext _; rfl
    rw [hrev1, hrev0, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
    have h0 : configurationSign (fun _ : Fin N => (0 : Fin 2)) = 1 := by
      simp [configurationSign, siteSign, SpinCover.pauli]
    have h1' : configurationSign (fun _ : Fin N => (1 : Fin 2)) = (-1) ^ N := by
      rw [← hrev0, configurationSign_rev, h0, mul_one]
    rw [h0, h1'] at h1
    linear_combination h1
  · intro hN
    change _ * _ = _ * _
    ext σ τ
    rw [finKronecker_sigmaX_mul, mul_finKronecker_sigmaX, rho_eq_diagonal]
    by_cases h : τ = fun n => (σ n).rev
    · subst h
      have hσ : (fun n => ((σ n).rev).rev) = σ := by funext n; exact Fin.rev_rev _
      rw [hσ, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, configurationSign_rev, hN,
        one_mul]
    · have h' : σ ≠ fun n => (τ n).rev := by
        rintro rfl
        exact h (by funext n; exact (Fin.rev_rev _).symm)
      rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h']

/-- **No strong `σ_x` symmetry.**

Project result: for the Example 4.12 tensor (arXiv:1606.00608, lines 932–939) and `N ≥ 1`,
`σ_x^{⊗N} ρ^{(N)}` has the entry `2` between the all-ones and all-zeros configurations, where
`ρ^{(N)}` is zero, so it is not a multiple of `ρ^{(N)}` (arXiv:2504.16985, line 182). -/
theorem not_isStrongSymmetry_sigmaX {N : ℕ} (hN : 0 < N) :
    ¬ Matrix.IsStrongSymmetry (Matrix.finKronecker fun _ : Fin N => sigmaX) (mpo M N) := by
  rintro ⟨c, hc⟩
  have h1 := congrFun (congrFun hc (fun _ => 1)) (fun _ => 0)
  rw [finKronecker_sigmaX_mul, rho_eq_diagonal] at h1
  have hrev1 : (fun n : Fin N => ((fun _ => (1 : Fin 2)) n).rev) = fun _ => 0 := by
    funext _; rfl
  have hne : (fun _ : Fin N => (1 : Fin 2)) ≠ fun _ => 0 := by
    intro h
    exact absurd (congrFun h ⟨0, hN⟩) (by decide)
  rw [hrev1, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hne,
    smul_zero] at h1
  have h0 : configurationSign (fun _ : Fin N => (0 : Fin 2)) = 1 := by
    simp [configurationSign, siteSign, SpinCover.pauli]
  rw [h0] at h1
  norm_num at h1

/-- **The family is not weakly `σ_x`-symmetric.**

Project result: weak symmetry of the family (arXiv:2504.16985, line 182) quantifies over every
positive length, and fails at `N = 1` (`isWeakSymmetry_sigmaX_iff_even`). -/
theorem not_isWeakMPOSymmetry_sigmaX :
    ¬ IsWeakMPOSymmetry (fun _ : Unit => onSite sigmaX) M := by
  intro h
  have h1 := h () 1 one_pos
  simp only [mpo_onSite] at h1
  exact Nat.not_even_one ((isWeakSymmetry_sigmaX_iff_even 1).mp h1)

/-- **Weak `σ_x` symmetry at every even length.**

Project result: the restriction of `isWeakSymmetry_sigmaX_iff_even` to even lengths. -/
theorem isWeakSymmetry_sigmaX_of_even {N : ℕ} (hN : Even N) :
    Matrix.IsWeakSymmetry (Matrix.finKronecker fun _ : Fin N => sigmaX) (mpo M N) :=
  (isWeakSymmetry_sigmaX_iff_even N).mpr hN

end MPOTensor.CPSVExample412Literal
