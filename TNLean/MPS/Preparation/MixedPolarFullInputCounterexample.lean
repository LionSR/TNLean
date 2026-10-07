/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SupportedPolar
import TNLean.Algebra.ComplexSqrt

/-!
# A normal tensor whose pseudoinverse polar map is not a full-input isometry

The four physical matrices are `I / √2`, `E₀₁ / √2`, `E₁₀ / √2`, and zero.
They form a nonzero unital and trace-preserving tensor, injective after two
sites. At one site the physical and virtual-pair dimensions are both four,
but the polar map has a zero physical row and cannot be an isometry.

**Local fix (full-input pseudoinverse claim):** footnote 3 of
arXiv:2307.01696 extends the inverse construction to non-injective blocks.
The pseudoinverse gives a partial isometry on the full input. The valid
mixed construction uses orthonormal coordinates on its actual support;
see `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`.

## References

Malz, Styliaris, Wei and Cirac, arXiv:2307.01696, the blocked-polar
paragraph and footnote 1, and equations (13)–(15), footnotes 3–4.
-/

open scoped Matrix BigOperators

namespace MPSPreparation

/-- A dimension-compatible normal witness for the failure of the full-input
pseudoinverse assertion in arXiv:2307.01696, footnote 3 to equations (13)–(15). -/
noncomputable def mixedPolarFullInputCounterexample : MPSTensor 4 2 :=
  ![Complex.invSqrtTwo • 1,
    Complex.invSqrtTwo • Matrix.single 0 1 1,
    Complex.invSqrtTwo • Matrix.single 1 0 1, 0]

private theorem counterexample_basis_product (i j : Fin 2) :
    ∃ u v : Fin 4,
      mixedPolarFullInputCounterexample u * mixedPolarFullInputCounterexample v =
        (2 : ℂ)⁻¹ • Matrix.single i j 1 := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, 2, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [mixedPolarFullInputCounterexample, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single, Complex.invSqrtTwo_mul_self]
  · refine ⟨0, 1, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [mixedPolarFullInputCounterexample, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single, Complex.invSqrtTwo_mul_self]
  · refine ⟨0, 2, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [mixedPolarFullInputCounterexample, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single, Complex.invSqrtTwo_mul_self]
  · refine ⟨2, 1, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [mixedPolarFullInputCounterexample, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single, Complex.invSqrtTwo_mul_self]

/-- The witness is nonzero, unital, trace preserving and normal, yet its actual
polar partial isometry fails the full-input isometry equation. The dimensions
satisfy the source's capacity condition `4 = 2²` at one physical site.

Source: counterexample to the non-injective pseudoinverse extension in
arXiv:2307.01696, footnote 3 to equations (13)–(15). -/
theorem mixedPolarFullInputCounterexample_spec :
    let B := mixedPolarFullInputCounterexample
    B ≠ 0 ∧ (∑ i, B i * (B i)ᴴ = 1) ∧ (∑ i, (B i)ᴴ * B i = 1) ∧
      Kraus.IsNormal B ∧ ¬ (MPSTensor.polarIsoMatrix B).IsIsometry := by
  dsimp only
  let B := mixedPolarFullInputCounterexample
  have hU : ∑ i, B i * (B i)ᴴ = 1 := by
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [B, mixedPolarFullInputCounterexample, Fin.sum_univ_succ,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.conjTranspose_apply,
        Complex.invSqrtTwo_mul_self]
  have hTP : ∑ i, (B i)ᴴ * B i = 1 := by
    ext a b; fin_cases a <;> fin_cases b <;>
      norm_num [B, mixedPolarFullInputCounterexample, Fin.sum_univ_succ,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.conjTranspose_apply,
        Complex.invSqrtTwo_mul_self]
  have hNormal : Kraus.IsNormal B := by
    refine ⟨2, by omega, ?_⟩
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Matrix.stdBasis ℂ (Fin 2) (Fin 2))).2
    rintro ⟨i, j⟩
    rw [Matrix.stdBasis_eq_single]
    obtain ⟨u, v, huv⟩ := counterexample_basis_product i j
    have hmem : B u * B v ∈ Kraus.wordSpan B 2 := by
      simpa [Kraus.evalWord] using Kraus.evalWord_mem_wordSpan B [u, v]
    have h := Submodule.smul_mem (Kraus.wordSpan B 2) (2 : ℂ) hmem
    simpa only [B, huv, smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h
  have hNot : ¬ (MPSTensor.polarIsoMatrix B).IsIsometry := by
    obtain ⟨G, hG⟩ := MPSTensor.exists_polarIsoMatrix_eq_sum B
    have hrow : ∀ x, MPSTensor.polarIsoMatrix B 3 x = 0 := by
      intro x
      rw [hG]
      simp [B, mixedPolarFullInputCounterexample]
    intro hIso
    change (MPSTensor.polarIsoMatrix B)ᴴ * MPSTensor.polarIsoMatrix B = 1 at hIso
    have hCo := mul_eq_one_comm.mp hIso
    have hEntry := congrFun (congrFun hCo (3 : Fin 4)) (3 : Fin 4)
    simp [Matrix.mul_apply, hrow] at hEntry
  refine ⟨?_, hU, hTP, hNormal, hNot⟩
  intro hB
  have h := congrFun (congrFun (congrFun hB 0) 0) 0
  exact Complex.invSqrtTwo_ne_zero (by simpa [mixedPolarFullInputCounterexample] using h)

end MPSPreparation
