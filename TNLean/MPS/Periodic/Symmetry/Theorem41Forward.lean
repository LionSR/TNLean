/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ListProduct
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.Periodic.Symmetry.Theorem41Defs

/-!
# Theorem 4.1, forward direction

This module contains the forward half of arXiv:1708.00029, Theorem 4.1,
together with the tensor \(C\) defined from the refinement isometry \(W\) in
lines 735--743 of the paper.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Theorem 4.1 — forward direction (`p`-refinability ⇒ `p`-divisibility) -/

section Theorem41Forward

variable {d D : ℕ}

/-- Evaluation of the tensor \(C\) defined from \(W\) on a blocked word is a \(W\)-weighted sum
of evaluations of the original tensor.

If `C τ = ∑_σ W(τ, σ) • B σ` is the isometric mixing of an MPS tensor
`B : MPSTensor d D` by `W : Matrix (Fin m) (Fin d) ℂ`, then for every `N` and
every `τ : Fin N → Fin m`,
`Kraus.evalWord C (List.ofFn τ) = ∑_σ (∏_k W (τ k) (σ k)) • Kraus.evalWord B (List.ofFn σ)`.

This is the coefficient-expansion identity used in both directions of Theorem 4.1:
in the forward direction it rewrites a refinement witness as `SameMPV` for the
tensor \(C\), and in the reverse direction it expands the blocked witness
produced by Wolf Theorem 2.1(4). -/
theorem evalWord_sum_smul_ofFn
    {m : ℕ} (B : MPSTensor d D) (W : Matrix (Fin m) (Fin d) ℂ) :
    ∀ (N : ℕ) (τ : Fin N → Fin m),
      Kraus.evalWord (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') (List.ofFn τ) =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) • Kraus.evalWord B (List.ofFn σ) := by
  classical
  intro N τ
  rw [evalWord_ofFn_eq_prod, List.prod_ofFn_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [List.prod_ofFn_smul, evalWord_ofFn_eq_prod]

private theorem mpv_sum_smul_ofFn
    {m : ℕ} (B : MPSTensor d D) (W : Matrix (Fin m) (Fin d) ℂ)
    (N : ℕ) (τ : Fin N → Fin m) :
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') τ =
      ∑ σ : Fin N → Fin d,
        (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
  simp [mpv_eq, coeff_eq, evalWord_sum_smul_ofFn, Matrix.trace_sum, Matrix.trace_smul]

/-- Physical-index mixing by a fixed matrix preserves `SameMPV₂`. -/
theorem sameMPV₂_sum_smul_ofFn
    {m D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (W : Matrix (Fin m) (Fin d) ℂ)
    (hAB : SameMPV₂ A B) :
    SameMPV₂
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ • A σ)
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  intro N τ
  calc
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • A σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff A (List.ofFn σ) := by
          exact mpv_sum_smul_ofFn A W N τ
    _ = ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simpa [mpv_eq, coeff_eq] using
            congrArg
              (fun z : ℂ => (∏ k : Fin N, W (τ k) (σ k)) * z)
              (hAB N σ)
    _ = mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • B σ') τ := by
          symm
          exact mpv_sum_smul_ofFn B W N τ

/-- A physical-index isometry preserves periodicity and its period. -/
theorem isPeriodic_kraus_isometry
    {m p : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsPeriodic p B) :
    IsPeriodic p (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  let C : MPSTensor m D := fun τ => ∑ σ : Fin d, W τ σ • B σ
  have hEq : Kraus.transferMap C = Kraus.transferMap B := by
    simpa [C] using transferMap_kraus_isometry B W hW
  have hIrrMapB : IsIrreducibleMap (Kraus.transferMap B) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily B hB.irreducible
  have hIrrMapC : IsIrreducibleMap (Kraus.transferMap C) := by
    simpa [hEq] using hIrrMapB
  refine ⟨Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM C hIrrMapC,
    isLeftCanonical_kraus_isometry B W hW hB.leftCanonical,
    hB.period_pos, ?_⟩
  simpa [C, hEq] using hB.peripheral_eq

private theorem sameMPV₂_toTensorFromBlocks_sum_smul_ofFn
    {m r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (W : Matrix (Fin m) (Fin d) ℂ) :
    SameMPV₂
      (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
        toTensorFromBlocks (d := d) (μ := μ) blocks σ)
      (toTensorFromBlocks (d := m) (μ := μ)
        (fun k : Fin r => fun τ : Fin m => ∑ σ : Fin d, W τ σ • blocks k σ)) := by
  intro N τ
  calc
    mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' •
        toTensorFromBlocks (d := d) (μ := μ) blocks σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) *
            mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
          simpa [mpv_eq, coeff_eq] using
            mpv_sum_smul_ofFn (B := toTensorFromBlocks (d := d) (μ := μ) blocks) W N τ
    _ = ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) *
            ∑ j : Fin r, (μ j) ^ N * mpv (blocks j) σ := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          rw [mpv_toTensorFromBlocks_eq_sum]
          simp only [smul_eq_mul]
    _ = ∑ σ : Fin N → Fin d,
          ∑ j : Fin r,
            (∏ k : Fin N, W (τ k) (σ k)) *
              ((μ j) ^ N * mpv (blocks j) σ) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ j : Fin r,
          ∑ σ : Fin N → Fin d,
            (∏ k : Fin N, W (τ k) (σ k)) *
              ((μ j) ^ N * mpv (blocks j) σ) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin r,
          (μ j) ^ N *
            ∑ σ : Fin N → Fin d,
              (∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ := by
          refine Finset.sum_congr rfl ?_
          intro j _
          calc
            ∑ σ : Fin N → Fin d,
                (∏ k : Fin N, W (τ k) (σ k)) *
                  ((μ j) ^ N * mpv (blocks j) σ)
                = ∑ σ : Fin N → Fin d,
                    (μ j) ^ N *
                      ((∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ) := by
                    refine Finset.sum_congr rfl ?_
                    intro σ _
                    simp [mul_assoc, mul_comm]
            _ = (μ j) ^ N *
                  ∑ σ : Fin N → Fin d,
                    (∏ k : Fin N, W (τ k) (σ k)) * mpv (blocks j) σ := by
                    rw [← Finset.mul_sum]
    _ = ∑ j : Fin r,
          (μ j) ^ N *
            mpv (fun τ' : Fin m => ∑ σ' : Fin d, W τ' σ' • blocks j σ') τ := by
          refine Finset.sum_congr rfl ?_
          intro j _
          congr 1
          symm
          simpa [mpv_eq, coeff_eq] using mpv_sum_smul_ofFn (B := blocks j) W N τ
    _ = mpv (toTensorFromBlocks (d := m) (μ := μ)
          (fun k : Fin r => fun τ' : Fin m => ∑ σ : Fin d, W τ' σ • blocks k σ)) τ := by
          symm
          rw [mpv_toTensorFromBlocks_eq_sum]
          simp only [smul_eq_mul]

/-- A physical-index isometry preserves irreducible form II. -/
noncomputable def isIrreducibleForm_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsIrreducibleForm B) :
    IsIrreducibleForm (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ) := by
  refine
    { r := hB.r
      dim := hB.dim
      blocks := fun k : Fin hB.r =>
        fun τ : Fin m => ∑ σ : Fin d, W τ σ • hB.blocks k σ
      μ := hB.μ
      period := hB.period
      periodic := ?_
      weight_pos := hB.weight_pos
      sameMPV := ?_ }
  · intro k
    exact isPeriodic_kraus_isometry (B := hB.blocks k) W hW (hB.periodic k)
  · have hPullbackSame :
        SameMPV₂
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ • B σ)
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
            toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks σ) :=
        sameMPV₂_sum_smul_ofFn B
          (toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks) W hB.sameMPV
    have hBlocksSame :
        SameMPV₂
          (fun τ : Fin m => ∑ σ : Fin d, W τ σ •
            toTensorFromBlocks (d := d) (μ := hB.μ) hB.blocks σ)
          (toTensorFromBlocks (d := m) (μ := hB.μ)
            (fun k : Fin hB.r => fun τ : Fin m => ∑ σ : Fin d, W τ σ • hB.blocks k σ)) :=
        sameMPV₂_toTensorFromBlocks_sum_smul_ofFn hB.μ hB.blocks W
    intro N τ
    exact (hPullbackSame N τ).trans (hBlocksSame N τ)

/-- **The tensor \(C\) in the forward proof of Theorem 4.1.**

From a `p`-refinement witness `(A, W)` for `B`, the tensor
`C τ := ∑_σ W(τ, σ) • B σ` has the same transfer map as `B` and the same MPV
family as `blockTensor A p`.

This is the tensor \(C\) of arXiv:1708.00029, lines 735--743:
\[
  C^{i_1,\ldots,i_p}=\sum_i W^{(i_1,\ldots,i_p),i}B^i .
\]
The theorem records the formal consequences of this definition before the
paper applies the equal-case periodic Fundamental Theorem. -/
theorem pRefinementCanonicalization_pullback
    (B : MPSTensor d D) (p : ℕ)
    (hRefine : IsPRefinable B p) :
    ∃ (A : MPSTensor d D)
      (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ),
      Wᴴ * W = 1 ∧
      Kraus.transferMap (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) =
        Kraus.transferMap B ∧
      SameMPV (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)
        (blockTensor A p) := by
  rcases hRefine with ⟨A, W, hW, hCoeff⟩
  refine ⟨A, W, hW, transferMap_kraus_isometry B W hW, ?_⟩
  intro N τ
  calc
    mpv (fun τ' : Fin (blockPhysDim d p) => ∑ σ' : Fin d, W τ' σ' • B σ') τ =
        ∑ σ : Fin N → Fin d,
          (∏ k : Fin N, W (τ k) (σ k)) * coeff B (List.ofFn σ) := by
          simp [mpv_eq, coeff_eq, evalWord_sum_smul_ofFn, Matrix.trace_sum, Matrix.trace_smul]
    _ = mpv (blockTensor A p) τ := by
          simpa [mpv_eq] using (hCoeff N τ).symm

/-- **The tensor \(C\) is still in irreducible form II.**

If the refined tensor `B` is already in irreducible form II, then the tensor
`C τ := ∑_σ W(τ, σ) • B σ` coming from a `p`-refinement witness is again in
irreducible form II, has the same transfer map as `B`, and has the same MPV
family as `blockTensor A p`. This formalizes the sentence in arXiv:1708.00029,
lines 744--745, that \(C\), viewed with \((i_1,\ldots,i_p)\) as one physical
index, is again in irreducible form II. -/
theorem pRefinementCanonicalization_pullback_of_irreducibleForm
    (B : MPSTensor d D) (hB : IsIrreducibleForm B) (p : ℕ)
    (hRefine : IsPRefinable B p) :
    ∃ (A : MPSTensor d D)
      (W : Matrix (Fin (blockPhysDim d p)) (Fin d) ℂ)
      (_ : IsIrreducibleForm
        (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)),
      Wᴴ * W = 1 ∧
      Kraus.transferMap (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ) =
        Kraus.transferMap B ∧
      SameMPV (fun τ : Fin (blockPhysDim d p) => ∑ σ : Fin d, W τ σ • B σ)
        (blockTensor A p) := by
  obtain ⟨A, W, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback B p hRefine
  exact ⟨A, W, isIrreducibleForm_kraus_isometry B W hW hB, hW, hTransfer, hSame⟩

/-- **Theorem 4.1, forward direction (witness-based form).**

If we can produce a witness `A : MPSTensor d D` for the `p`-refinement of `B`
satisfying *both* left-canonical normalization (`∑ᵢ Aᵢᴴ · Aᵢ = 1`, so that the
transfer map `E_A` is a CPTP channel) *and* the channel-level matching
`E_B = E_{A^{[p]}}`, then `E_B` is `p`-divisible: concretely, it equals
`(E_A)^p`.

The proof combines the channel-level blocking identity `E_{A^{[p]}} = (E_A)^p`
(`MPSTensor.transferMap_blockTensor`) with the left-canonical channel property
`Kraus.isChannel_mapLM`. The construction from a refinement witness for normalized literal periodic
block forms is proved in `LiteralRefinementForward.lean`. -/
theorem thm_4_1_p_refinement_forward_witness
    (B : MPSTensor d D) (p : ℕ)
    (A : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hTransferEq : Kraus.transferMap B = Kraus.transferMap (blockTensor A p)) :
    IsPDivisibleChannel (Kraus.transferMap B) p :=
  ⟨Kraus.transferMap A, Kraus.isChannel_mapLM A hA_norm, by
    rw [hTransferEq, transferMap_blockTensor]⟩

end Theorem41Forward

end MPSTensor
