/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTCharacterization

/-!
# Uniqueness boundary for bases of normal tensors

This module examines the uniqueness sentence following the characterization of
a basis of normal tensors in arXiv:1606.00608, Appendix A, line 1148.

It also proves the uniqueness statement after adding converse coverage of every
candidate by an active canonical-form block.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The bond-dimension-one tensor supported on one physical symbol. -/
private def symbolTensor (a : Fin 2) : MPSTensor 2 1 :=
  fun i => if i = a then 1 else 0

private lemma symbolTensor_transferMap (a : Fin 2) :
    transferMap (symbolTensor a) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext x y
  fin_cases x
  fin_cases y
  simp [transferMap_apply, symbolTensor]

private theorem symbolTensor_isNormalTensor (a : Fin 2) :
    IsNormalTensor (symbolTensor a) :=
  isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    (symbolTensor a) (symbolTensor_transferMap a)

private lemma symbolTensor_mpv_self (a : Fin 2) (N : ℕ) :
    mpv (symbolTensor a) (fun _ : Fin N => a) = 1 := by
  rw [mpv_const_eq_trace_pow]
  simp [symbolTensor, Matrix.trace]

private lemma symbolTensor_mpv_other {a b : Fin 2} (hab : a ≠ b)
    (N : ℕ) (hN : 0 < N) :
    mpv (symbolTensor a) (fun _ : Fin N => b) = 0 := by
  rw [mpv_const_eq_trace_pow]
  simp [symbolTensor, Ne.symm hab, Matrix.trace, Nat.ne_of_gt hN]

private lemma symbolTensor_pair_linearIndependent (N : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ (fun j : Fin 2 => mpvState (symbolTensor j) N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum j
  fin_cases j
  · have hzero := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (0 : Fin 2))) hsum
    have h00 : mpv (symbolTensor 0) (fun _ : Fin N => (0 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 0 N
    have h10 : mpv (symbolTensor 1) (fun _ : Fin N => (0 : Fin 2)) = 0 :=
      symbolTensor_mpv_other (by decide) N hN
    have hc0 : c (0 : Fin 2) = 0 := by
      simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
        mpvState_apply, smul_eq_mul, h00, h10, mul_one, mul_zero, add_zero,
        PiLp.zero_apply] using hzero
    simpa using hc0
  · have hone := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (1 : Fin 2))) hsum
    have h01 : mpv (symbolTensor 0) (fun _ : Fin N => (1 : Fin 2)) = 0 :=
      symbolTensor_mpv_other (by decide) N hN
    have h11 : mpv (symbolTensor 1) (fun _ : Fin N => (1 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 1 N
    have hc1 : c (1 : Fin 2) = 0 := by
      simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply,
        mpvState_apply, smul_eq_mul, h01, h11, mul_zero, mul_one, zero_add,
        PiLp.zero_apply] using hone
    simpa using hc1

private def singletonSymbolFamily : Fin 1 → Σ D : ℕ, MPSTensor 2 D :=
  fun _ => ⟨1, symbolTensor 0⟩

private def pairSymbolFamily : Fin 2 → Σ D : ℕ, MPSTensor 2 D :=
  fun j => ⟨1, symbolTensor j⟩

private theorem singletonSymbolFamily_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors (symbolTensor 0) singletonSymbolFamily := by
  refine {
    blocks_normal := fun _ => symbolTensor_isNormalTensor 0
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N _hN
    refine ⟨fun _ => 1, ?_⟩
    intro σ
    simp [singletonSymbolFamily]
  · refine ⟨0, ?_⟩
    intro N hN
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hzero
    have hcomponent := congrArg
      (fun v : MPVSpace 2 N => v (fun _ : Fin N => (0 : Fin 2))) hzero
    have hself : mpv (symbolTensor 0) (fun _ : Fin N => (0 : Fin 2)) = 1 :=
      symbolTensor_mpv_self 0 N
    have hone : (1 : ℂ) = 0 := by
      simpa only [singletonSymbolFamily, mpvState_apply, hself, PiLp.zero_apply]
        using hcomponent
    exact one_ne_zero hone

private theorem pairSymbolFamily_isCPSVBasisOfNormalTensors :
    IsCPSVBasisOfNormalTensors (symbolTensor 0) pairSymbolFamily := by
  refine {
    blocks_normal := fun j => symbolTensor_isNormalTensor j
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N _hN
    refine ⟨fun j => if j = 0 then 1 else 0, ?_⟩
    intro σ
    simp [pairSymbolFamily]
  · refine ⟨0, ?_⟩
    intro N hN
    exact symbolTensor_pair_linearIndependent N (by omega)

/-- Two bases of normal tensors for one fixed canonical-form family need not
have equivalent index types under the literal definition of arXiv:1606.00608.

This is a counterexample to the unrestricted uniqueness sentence in
arXiv:1606.00608, Appendix A, line 1148. Take the bond-dimension-one tensor
supported on physical symbol zero. Its singleton family is a basis of normal
tensors. Adjoining the tensor supported on physical symbol one gives a second
basis: its coefficient is identically zero, while the two matrix product
vectors are orthogonal and hence linearly independent at every positive
length. The two index types have cardinalities one and two.

See `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`. -/
theorem exists_isCPSVBasisOfNormalTensors_unequal_card :
    ∃ (A : MPSTensor 2 1)
      (basis₁ : Fin 1 → Σ D : ℕ, MPSTensor 2 D)
      (basis₂ : Fin 2 → Σ D : ℕ, MPSTensor 2 D),
      IsNormalTensor A ∧
      SameMPV₂Pos A
        (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) ∧
      IsCPSVBasisOfNormalTensors A basis₁ ∧
      IsCPSVBasisOfNormalTensors A basis₂ ∧
      Fintype.card (Fin 1) ≠ Fintype.card (Fin 2) ∧
      ¬ Nonempty (Fin 1 ≃ Fin 2) := by
  refine ⟨symbolTensor 0, singletonSymbolFamily, pairSymbolFamily,
    symbolTensor_isNormalTensor 0, ?_,
    singletonSymbolFamily_isCPSVBasisOfNormalTensors,
    pairSymbolFamily_isCPSVBasisOfNormalTensors, ?_, ?_⟩
  · intro N _hN σ
    rw [mpv_toTensorFromBlocks_eq_sum]
    simp
  · norm_num
  · rintro ⟨e⟩
    have hcard := Fintype.card_congr e
    norm_num at hcard

/-- Two bases of normal tensors are equivalent when every member of each basis
is represented by an active block of the same canonical-form expansion.

This is the restricted uniqueness statement described after the counterexample
to arXiv:1606.00608, Appendix A, line 1148. Proposition 2.7 (`prop:char-BNT`,
lines 1135--1146) supplies coverage of every active block by each basis. The
additional converse hypotheses supply coverage in the other direction.

**Scope restriction (converse coverage):** unlike the literal uniqueness
sentence at line 1148, this theorem assumes that every candidate tensor in
both bases is gauge-phase equivalent to a nonzero-weight canonical-form block.
See `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`. -/
theorem IsCPSVBasisOfNormalTensors.equiv_of_converse_coverage
    {r g₁ g₂ : ℕ}
    {dimCF : Fin r → ℕ} {dim₁ : Fin g₁ → ℕ} {dim₂ : Fin g₂ → ℕ}
    [∀ k, NeZero (dimCF k)] [∀ j, NeZero (dim₁ j)] [∀ j, NeZero (dim₂ j)]
    {A : MPSTensor d D} {μ : Fin r → ℂ}
    {blocks : (k : Fin r) → MPSTensor d (dimCF k)}
    {basis₁ : (j : Fin g₁) → MPSTensor d (dim₁ j)}
    {basis₂ : (j : Fin g₂) → MPSTensor d (dim₂ j)}
    (hBlocksNormal : ∀ k, IsNormalTensor (blocks k))
    (hCF : SameMPV₂Pos A (toTensorFromBlocks (d := d) μ blocks))
    (hBNT₁ : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim₁ j, basis₁ j⟩))
    (hBNT₂ : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim₂ j, basis₂ j⟩))
    (hConverse₁ : ∀ j : Fin g₁,
      ∃ k : Fin r, μ k ≠ 0 ∧
        ∃ hdim : dim₁ j = dimCF k,
        ∃ X : GL (Fin (dimCF k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, blocks k i = ζ •
            ((X : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis₁ j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ)))
    (hConverse₂ : ∀ j : Fin g₂,
      ∃ k : Fin r, μ k ≠ 0 ∧
        ∃ hdim : dim₂ j = dimCF k,
        ∃ X : GL (Fin (dimCF k)) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          ∀ i, blocks k i = ζ •
            ((X : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ) *
              (cast (congr_arg (MPSTensor d) hdim) (basis₂ j)) i *
              (↑(X⁻¹) : Matrix (Fin (dimCF k)) (Fin (dimCF k)) ℂ))) :
    ∃ e : Fin g₁ ≃ Fin g₂, ∀ j : Fin g₁,
      ∃ hdim : dim₁ j = dim₂ (e j),
      ∃ X : GL (Fin (dim₂ (e j))) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
        ∀ i, basis₂ (e j) i = ζ •
          ((X : Matrix (Fin (dim₂ (e j))) (Fin (dim₂ (e j))) ℂ) *
            (cast (congr_arg (MPSTensor d) hdim) (basis₁ j)) i *
            (↑(X⁻¹) : Matrix (Fin (dim₂ (e j))) (Fin (dim₂ (e j))) ℂ)) := by
  classical
  have hCover₁ :=
    (isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
      A μ blocks basis₁ hBlocksNormal hCF).mp hBNT₁ |>.2.1
  have hCover₂ :=
    (isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal
      A μ blocks basis₂ hBlocksNormal hCF).mp hBNT₂ |>.2.1
  have hMatch₁ : ∀ j : Fin g₁,
      ∃ k : Fin g₂, ∃ hdim : dim₁ j = dim₂ k,
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) (basis₁ j)) (basis₂ k) := by
    intro j
    obtain ⟨l, hl, hdim₁, X₁, ζ₁, hζ₁, hrel₁⟩ := hConverse₁ j
    obtain ⟨k, hdim₂, X₂, ζ₂, hζ₂, hrel₂⟩ := hCover₂ l hl
    have hGE₁ : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim₁) (basis₁ j)) (blocks l) :=
      ⟨X₁, ζ₁, Complex.ne_zero_of_norm_eq_one hζ₁, hrel₁⟩
    have hGE₂ : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim₂) (basis₂ k)) (blocks l) :=
      ⟨X₂, ζ₂, Complex.ne_zero_of_norm_eq_one hζ₂, hrel₂⟩
    refine ⟨k, hdim₁.trans hdim₂.symm, ?_⟩
    simpa using gaugePhaseEquiv_cast_compose_via_centre
      hdim₁.symm hdim₂.symm
      (gaugePhaseEquiv_swap_cast hdim₁.symm hGE₁)
      (gaugePhaseEquiv_swap_cast hdim₂.symm hGE₂)
  choose f hdimF hGEF using hMatch₁
  have rebase₂ :
      ∀ (l l' : Fin g₂) (_hll : l = l') {j : Fin g₁}
        (hdim : dim₁ j = dim₂ l')
        (hGE : GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) (basis₁ j)) (basis₂ l')),
        ∃ hdim' : dim₁ j = dim₂ l,
          GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hdim') (basis₁ j)) (basis₂ l) := by
    rintro _ _ rfl _ hdim hGE
    exact ⟨hdim, hGE⟩
  have hf : Function.Injective f := by
    intro j k hjk
    by_contra hne
    obtain ⟨hdimK, hGEK⟩ :=
      rebase₂ (f j) (f k) hjk (hdimF k) (hGEF k)
    apply hBNT₁.blocks_not_gaugePhaseEquiv j k hne
      ((hdimF j).trans hdimK.symm)
    simpa using gaugePhaseEquiv_cast_compose_via_centre
      (hdimF j).symm hdimK.symm
      (gaugePhaseEquiv_swap_cast (hdimF j).symm (hGEF j))
      (gaugePhaseEquiv_swap_cast hdimK.symm hGEK)
  have hMatch₂ : ∀ j : Fin g₂,
      ∃ k : Fin g₁, ∃ hdim : dim₂ j = dim₁ k,
        GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) (basis₂ j)) (basis₁ k) := by
    intro j
    obtain ⟨l, hl, hdim₂, X₂, ζ₂, hζ₂, hrel₂⟩ := hConverse₂ j
    obtain ⟨k, hdim₁, X₁, ζ₁, hζ₁, hrel₁⟩ := hCover₁ l hl
    have hGE₂ : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim₂) (basis₂ j)) (blocks l) :=
      ⟨X₂, ζ₂, Complex.ne_zero_of_norm_eq_one hζ₂, hrel₂⟩
    have hGE₁ : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim₁) (basis₁ k)) (blocks l) :=
      ⟨X₁, ζ₁, Complex.ne_zero_of_norm_eq_one hζ₁, hrel₁⟩
    refine ⟨k, hdim₂.trans hdim₁.symm, ?_⟩
    simpa using gaugePhaseEquiv_cast_compose_via_centre
      hdim₂.symm hdim₁.symm
      (gaugePhaseEquiv_swap_cast hdim₂.symm hGE₂)
      (gaugePhaseEquiv_swap_cast hdim₁.symm hGE₁)
  choose q hdimQ hGEQ using hMatch₂
  have rebase₁ :
      ∀ (l l' : Fin g₁) (_hll : l = l') {j : Fin g₂}
        (hdim : dim₂ j = dim₁ l')
        (hGE : GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) (basis₂ j)) (basis₁ l')),
        ∃ hdim' : dim₂ j = dim₁ l,
          GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) hdim') (basis₂ j)) (basis₁ l) := by
    rintro _ _ rfl _ hdim hGE
    exact ⟨hdim, hGE⟩
  have hq : Function.Injective q := by
    intro j k hjk
    by_contra hne
    obtain ⟨hdimK, hGEK⟩ :=
      rebase₁ (q j) (q k) hjk (hdimQ k) (hGEQ k)
    apply hBNT₂.blocks_not_gaugePhaseEquiv j k hne
      ((hdimQ j).trans hdimK.symm)
    simpa using gaugePhaseEquiv_cast_compose_via_centre
      (hdimQ j).symm hdimK.symm
      (gaugePhaseEquiv_swap_cast (hdimQ j).symm (hGEQ j))
      (gaugePhaseEquiv_swap_cast hdimK.symm hGEK)
  have hcard : Fintype.card (Fin g₁) = Fintype.card (Fin g₂) :=
    Nat.le_antisymm (Fintype.card_le_of_injective f hf)
      (Fintype.card_le_of_injective q hq)
  have hfBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
  let e : Fin g₁ ≃ Fin g₂ := Equiv.ofBijective f hfBij
  refine ⟨e, fun j => ?_⟩
  obtain ⟨X, ζ, hζ, hrel⟩ := hGEF j
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
      (hBNT₁.blocks_normal j) (hBNT₂.blocks_normal (f j)) (hdimF j) hrel
  exact ⟨hdimF j, X, ζ, hζnorm, hrel⟩

end MPSTensor
