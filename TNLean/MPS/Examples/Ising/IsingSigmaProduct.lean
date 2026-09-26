/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingFusionAlgebra
import TNLean.MPS.MPDO.SimpleScaling

/-!
# Ising anyon chain: the sigma operator on the constant closed path

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the Ising F-symbols from which the
letters of the `σ` tensor are built, as for the Fibonacci model (lines 1257–1268). The source
does not evaluate the `σ` operator on any state.

**Formalized here.** At every positive length `N`, the periodic operator of `Â_σ = √2 A_σ`
sends the product state `|6⟩^{⊗N}`, where `6 = (σ, 1, σ)`, to
`(√2)^N (|0⟩^{⊗N} + |3⟩^{⊗N})`, and the periodic operator of the unscaled tensor `A_σ` sends it
to `|0⟩^{⊗N} + |3⟩^{⊗N}`. At the input label `6` the only nonzero letters are
`Â_σ^{0,6} = √2 E_{22}` and `Â_σ^{3,6} = √2 E_{33}`, and these matrix units chain around the
ring only along a constant output path.

**Local fix (sigma scaling):** the tensors omit the factors `v_e v_f` of the `G`-symbols
(lines 1257–1260) and store the `σ` tensor multiplied by `√2`; the identities are proved for
these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

## Main results

* `IsingTwist.isingSigma_eq_smul_single`: every complex letter of `Â_σ` is a scaled matrix unit.
* `IsingTwist.mpo_isingSigma_apply_const_six`: the column of the periodic operator of `Â_σ` at
  the constant input path `6`.
* `IsingTwist.mpo_isingSigma_mulVec_const_six`: the scaled product-state identity.
* `IsingTwist.mpo_isingSigma_normalized_mulVec_const_six`: the unscaled product-state identity.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-- Every complex letter of `Â_σ = √2 A_σ` is a scaled matrix unit. -/
theorem isingSigma_eq_smul_single (h h' : Fin 10) :
    isingSigma h h' = zsqrt2ToComplex (isingSigmaCoefZ h h') •
      Matrix.single (isingSigmaRow h h') (isingSigmaCol h h') 1 := by
  ext a b
  simp only [isingSigma, isingSigmaZ_eq_smul_single h h', complexOfZsqrt2_apply,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- At the input label `6 = (σ,1,σ)` a letter of `Â_σ` is nonzero only at the outputs `0`
and `3`, and there it is `√2` times a diagonal matrix unit. -/
private theorem isingSigmaCoefZ_six (a : Fin 10) :
    isingSigmaCoefZ a 6 = if a = 0 ∨ a = 3 then sqrtd else 0 := by
  revert a
  decide

/-- Two nonzero letters at the input label `6` chain only when their outputs agree. -/
private theorem isingSigma_chain_six :
    ∀ a b : Fin 10, (a = 0 ∨ a = 3) → (b = 0 ∨ b = 3) →
      (isingSigmaCol a 6 = isingSigmaRow b 6 ↔ a = b) := by
  decide

/-- **The column of the sigma operator at the constant path `6`.** Project result: the source
(arXiv:1511.08090, lines 1257–1268 and 1305–1323) builds the operator but does not print its
kernel. At every positive length, the entry of the periodic operator of `Â_σ` at the output
path `s` and the constant input path `6` is `(√2)^N` when `s` is the constant path `0` or the
constant path `3`, and zero otherwise. -/
theorem mpo_isingSigma_apply_const_six {N : ℕ} (hN : 0 < N) (s : Fin N → Fin 10) :
    MPOTensor.mpo isingSigma N s (fun _ => 6) =
      if s = (fun _ => 0) ∨ s = (fun _ => 3) then (Real.sqrt 2 : ℂ) ^ N else 0 := by
  have : NeZero N := ⟨hN.ne'⟩
  rw [MPOTensor.mpo_apply_of_eq_smul_single isingSigma
    (fun h h' => zsqrt2ToComplex (isingSigmaCoefZ h h')) isingSigmaRow isingSigmaCol
    isingSigma_eq_smul_single hN]
  simp only [isingSigmaCoefZ_six]
  by_cases hin : ∀ k, s k = 0 ∨ s k = 3
  · simp only [hin, ite_true, zsqrt2ToComplex_sqrtd, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    simp only [finRotate_apply, isingSigma_chain_six _ _ (hin _) (hin _)]
    by_cases hconst : ∀ k, s k = s (k + 1)
    · have hs : s = fun _ => s 0 := funext fun k =>
        (Fin.cyclic_induction (P := fun k => s k = s 0) rfl
          (fun i hi => (hconst i).symm.trans hi) k)
      have h0 : s = (fun _ => 0) ∨ s = (fun _ => 3) := by
        rcases hin 0 with h | h
        · exact Or.inl (hs.trans (by rw [h]))
        · exact Or.inr (hs.trans (by rw [h]))
      rw [ite_eq_left hconst, ite_eq_left h0]
    · have h0 : ¬ (s = (fun _ => 0) ∨ s = (fun _ => 3)) := by
        rintro (rfl | rfl) <;> exact hconst fun _ => rfl
      rw [ite_eq_right hconst, ite_eq_right h0]
  · obtain ⟨k, hk⟩ := not_forall.mp hin
    have hprod : ∏ k, zsqrt2ToComplex (if s k = 0 ∨ s k = 3 then sqrtd else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
    have h0 : ¬ (s = (fun _ => 0) ∨ s = (fun _ => 3)) := by
      rintro (rfl | rfl) <;> simp at hk
    simp only [hprod, ite_self, h0, ite_false]

/-- **The sigma operator on the constant closed path, scaled form.** Source:
`thm:asymex_ising_sigma_product` of the Ising examples chapter, built from arXiv:1511.08090,
lines 1257–1268 and 1305–1323: for `N ≥ 1`,
`O_N(Â_σ) |6⟩^{⊗N} = (√2)^N (|0⟩^{⊗N} + |3⟩^{⊗N})`, where `6 = (σ,1,σ)`, `0 = (1,1,1)` and
`3 = (ψ,1,ψ)`. -/
theorem mpo_isingSigma_mulVec_const_six {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingSigma N *ᵥ Pi.single (fun _ => 6) 1 =
      (Real.sqrt 2 : ℂ) ^ N •
        (Pi.single (fun _ => 0) 1 + Pi.single (fun _ => 3) 1 : (Fin N → Fin 10) → ℂ) := by
  have h03 : (fun _ : Fin N => (0 : Fin 10)) ≠ fun _ => 3 := fun h => by
    simpa using congrFun h ⟨0, hN⟩
  ext s
  rw [Matrix.mulVec_single_one, Matrix.col_apply, mpo_isingSigma_apply_const_six hN]
  by_cases h0 : s = fun _ => 0
  · subst h0
    simp [h03]
  · by_cases h3 : s = fun _ => 3
    · subst h3
      simp [h03.symm]
    · simp [h0, h3]

/-- **The sigma operator on the constant closed path, unscaled form.** Source:
`thm:asymex_ising_sigma_product` of the Ising examples chapter, built from arXiv:1511.08090,
lines 1257–1268 and 1305–1323: for `N ≥ 1` and the unscaled tensor
`A_σ = (√2)⁻¹ • Â_σ`, `O_N(A_σ) |6⟩^{⊗N} = |0⟩^{⊗N} + |3⟩^{⊗N}`. -/
theorem mpo_isingSigma_normalized_mulVec_const_six {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo (Complex.invSqrtTwo • isingSigma) N *ᵥ Pi.single (fun _ => 6) 1 =
      (Pi.single (fun _ => 0) 1 + Pi.single (fun _ => 3) 1 : (Fin N → Fin 10) → ℂ) := by
  rw [MPOTensor.mpo_smul, Matrix.smul_mulVec, mpo_isingSigma_mulVec_const_six hN, smul_smul,
    ← mul_pow, Complex.invSqrtTwo_mul_sqrtTwo, one_pow, one_smul]

end IsingTwist
