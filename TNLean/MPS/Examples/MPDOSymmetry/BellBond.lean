/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BinaryConfigurationSign
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFP
import TNLean.MPS.Symmetry.MPDO.Defs

/-!
# The rescaling-stable example `R`: strong `ZZ` and weak `XX` symmetry

**Source.** The project example `R` of `TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean`,
motivated by Cirac, Pérez-García, Schuch, Verstraete 2017 (arXiv:1606.00608), Theorem 4.14 and
`Papers/1606.00608/MPDO-22-12-17-2.tex` lines 995–1010; it is not a tensor printed in the
source. Each site carries two qubits, and on the support of `ρ^{(N)}(R)` the second qubit of
site `n` equals the first qubit of site `n + 1` (`mpo_R_entry_formula`). The strong and weak
symmetries are those of Sun 2025 (arXiv:2504.16985), `References/2504.16985/main.tex` line 182.

**Formalized here.** Project result: `ρ^{(N)}(R)` is strongly symmetric under
`(σ_z ⊗ σ_z)^{⊗N}` with eigenvalue `1` at every positive length, because on the support the
product of the qubit signs is a square. It is weakly symmetric under `(σ_x ⊗ σ_x)^{⊗N}`,
because flipping both qubits preserves the support and the weight matrix
`w = !![16/25, 9/25; 9/25, 16/25]`. It is not strongly `σ_x ⊗ σ_x`-symmetric: at `N = 1`
the flipped operator has entries in the ratio `9 : 16` where `ρ^{(1)}` has `16 : 9`.

## Main definitions

* `sigmaZZ`, `sigmaXX`: the on-site operators `σ_z ⊗ σ_z` and `σ_x ⊗ σ_x` in the encoding
  `bondEquiv : Fin 2 × Fin 2 ≃ Fin 4`.

## Main results

* `isStrongMPOSymmetry_sigmaZZ`, `isWeakMPOSymmetry_sigmaXX`,
  `not_isStrongMPOSymmetry_sigmaXX`.

## References
- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product density operators: Renormalization fixed points
  and boundary theories*
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
-/

open scoped Matrix BigOperators

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The operator `σ_z ⊗ σ_z` on one site, diagonal in the encoding `bondEquiv`. -/
def sigmaZZ : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, 1]

private lemma sigmaZZ_entry (p : Fin 4) :
    (![1, -1, -1, 1] : Fin 4 → ℂ) p = siteSign (bondBit1 p) * siteSign (bondBit2 p) := by
  fin_cases p <;> simp [siteSign, SpinCover.pauli, bondBit1, bondBit2]

/-- The operator `σ_x ⊗ σ_x` on one site: flipping both qubits of `bondEquiv (a, b)` is the
reversal `Fin.rev` of `Fin 4`. -/
def sigmaXX : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun p q => if q = p.rev then 1 else 0

private lemma sigmaXX_apply (p q : Fin 4) : sigmaXX p q = if q = p.rev then 1 else 0 := rfl

private lemma sigmaXX_apply' (p q : Fin 4) : sigmaXX p q = if p = q.rev then 1 else 0 := by
  simp only [sigmaXX, Matrix.of_apply]
  exact if_congr ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩ rfl rfl

private lemma bondBit1_rev (p : Fin 4) : bondBit1 p.rev = (bondBit1 p).rev := by
  fin_cases p <;> rfl

private lemma bondBit2_rev (p : Fin 4) : bondBit2 p.rev = (bondBit2 p).rev := by
  fin_cases p <;> rfl

private lemma wMat_rev_left (a b : Fin 2) : wMat a.rev b = wMat a b.rev := by
  fin_cases a <;> fin_cases b <;> rfl

/-- On a configuration satisfying the cyclic matching condition, the `σ_z ⊗ σ_z` signs
multiply to `1`. -/
private lemma prod_sigmaZZ_of_chainOK {N : ℕ} {p : Fin N → Fin 4} (hp : ChainOK N p) :
    ∏ n, (![1, -1, -1, 1] : Fin 4 → ℂ) (p n) = 1 := by
  simp only [sigmaZZ_entry, Finset.prod_mul_distrib]
  have h2 : ∏ n, siteSign (bondBit2 (p n)) = ∏ n, siteSign (bondBit1 (p n)) := by
    rw [← Equiv.prod_comp (finRotate N) (fun n => siteSign (bondBit1 (p n)))]
    exact Finset.prod_congr rfl fun n _ => by rw [hp n]
  rw [h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun n _ => siteSign_mul_self _

private lemma chainOK_rev_iff {N : ℕ} (p : Fin N → Fin 4) :
    ChainOK N (fun n => (p n).rev) ↔ ChainOK N p := by
  simp only [ChainOK, bondBit1_rev, bondBit2_rev, Fin.rev_inj]

/-- **Strong `σ_z ⊗ σ_z` symmetry with eigenvalue `1`.**

Project result: at every positive length, `(σ_z ⊗ σ_z)^{⊗N} ρ^{(N)}(R) = ρ^{(N)}(R)`
(strong symmetry, arXiv:2504.16985, line 182). On the support of `ρ^{(N)}(R)` the sign
`∏_n z(l_n) z(r_n)` equals `(∏_n z(l_n))²`, because `r_n = l_{n+1}`. -/
theorem isStrongMPOSymmetry_sigmaZZ :
    IsStrongMPOSymmetry (fun _ : Unit => onSite sigmaZZ) R fun _ _ => 1 := by
  intro _ L hL
  rw [mpo_onSite, sigmaZZ, Matrix.finKronecker_diagonal, one_smul]
  ext p q
  rw [Matrix.diagonal_mul]
  by_cases hp : ChainOK L p
  · rw [prod_sigmaZZ_of_chainOK hp, one_mul]
  · rw [mpo_R_entry_formula hL, chainIndicator, Matrix.of_apply,
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hp h.1)]
    simp

/-- **Weak `σ_x ⊗ σ_x` symmetry.**

Project result: at every positive length, `(σ_x ⊗ σ_x)^{⊗N}` commutes with `ρ^{(N)}(R)` (weak
symmetry, arXiv:2504.16985, line 182): flipping every qubit preserves the matching condition,
and the weight matrix satisfies `w_{1-a, b} = w_{a, 1-b}`. -/
theorem isWeakMPOSymmetry_sigmaXX : IsWeakMPOSymmetry (fun _ : Unit => onSite sigmaXX) R := by
  intro _ L hL
  rw [mpo_onSite]
  change _ * _ = _ * _
  ext p q
  rw [Matrix.finKronecker_mul_apply_of_eq_ite sigmaXX_apply,
    Matrix.mul_finKronecker_apply_of_eq_ite sigmaXX_apply', mpo_R_entry_formula hL,
    mpo_R_entry_formula hL]
  congr 1
  · simp only [chainIndicator, Matrix.of_apply, chainOK_rev_iff]
  · simp only [wN, φ, Matrix.of_apply, bondBit1_rev, wMat_rev_left]

/-- **No strong `σ_x ⊗ σ_x` symmetry at one site.**

Project result: at `N = 1`, `(σ_x ⊗ σ_x) ρ^{(1)}(R)` is not a multiple of `ρ^{(1)}(R)`
(arXiv:2504.16985, line 182): on the two supported configurations the entries of `ρ^{(1)}`
are in the ratio `16 : 9`, and those of the flipped operator in the ratio `9 : 16`. -/
theorem not_isStrongSymmetry_sigmaXX_one :
    ¬ Matrix.IsStrongSymmetry (Matrix.finKronecker fun _ : Fin 1 => sigmaXX) (mpo R 1) := by
  rintro ⟨c, hc⟩
  have hok0 : ChainOK 1 (fun _ => (0 : Fin 4)) := by decide
  have hok3 : ChainOK 1 (fun _ => (3 : Fin 4)) := by decide
  have hrev0 : (fun _ : Fin 1 => ((0 : Fin 4)).rev) = fun _ => (3 : Fin 4) := rfl
  have e1 := congrFun (congrFun hc (fun _ => 0)) (fun _ => 0)
  have e2 := congrFun (congrFun hc (fun _ => 0)) (fun _ => 3)
  rw [Matrix.finKronecker_mul_apply_of_eq_ite sigmaXX_apply, hrev0, Matrix.smul_apply,
    mpo_R_entry_formula one_pos, mpo_R_entry_formula one_pos] at e1 e2
  simp only [chainIndicator, Matrix.of_apply, hok0, hok3, and_self, ite_true, wN, φ,
    Fin.prod_univ_one, smul_eq_mul] at e1 e2
  norm_num [wMat, bondBit1] at e1 e2
  have hc916 : c = 9 / 16 := by linear_combination -2 * e1
  rw [hc916] at e2
  norm_num at e2

/-- **The family is not strongly `σ_x ⊗ σ_x`-symmetric**, for any eigenvalues.

Project result: strong symmetry of the family (arXiv:2504.16985, line 182) fails at `N = 1`
(`not_isStrongSymmetry_sigmaXX_one`). -/
theorem not_isStrongMPOSymmetry_sigmaXX (c : Unit → ℕ → ℂ) :
    ¬ IsStrongMPOSymmetry (fun _ : Unit => onSite sigmaXX) R c := by
  intro h
  have h1 := h () 1 one_pos
  rw [mpo_onSite] at h1
  exact not_isStrongSymmetry_sigmaXX_one ⟨c () 1, h1⟩

end MPOTensor.RescalingStableLengthDependentRFP
