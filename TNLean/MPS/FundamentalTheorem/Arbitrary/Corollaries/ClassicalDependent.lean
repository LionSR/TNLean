/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.Corollaries.WeightedStates
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.PeriodExistence

/-!
# The classical proportional theorems from dependent states

The fundamental theorems of Cirac, Pérez-García, Schuch and Verstraete (arXiv:1606.00608,
Theorem 2.10) and of De las Cuevas, Cirac, Schuch and Pérez-García (arXiv:1708.00029, theorem
`thm:bd`) match the bases of two tensors whose states are proportional for all `N`. The theorem of
this file contains both: normal tensors are the irreducible tensors of period one. It follows
from the statement on classes of factors for dependent states, which
needs only linear dependence of the states at all large lengths: constants `γ_N = 0` are allowed.
Thus `C ⊕ (-C)` and `C`, whose states are related by `γ_N = 1 + (-1) ^ N`, are covered.

## Main results

* `MPSTensor.fundamentalTheorem_irreducibleForm_of_statesDependent`

## References

* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Theorem 2.10.
* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, theorem `thm:bd`, lines 613--623.
-/

open Filter
open scoped Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- A block whose transfer map has spectral radius one has a nonzero letter. -/
private theorem exists_ne_zero_of_spectralRadius_eq_one {n : ℕ} {C : MPSTensor d n}
    (hC : spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin n) (Fin n) ℂ))
      (Kraus.transferMap (d := d) (D := n) C)) = 1) : ∃ i, C i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : Kraus.transferMap (d := d) (D := n) C = 0 := by
    refine LinearMap.ext fun Z => ?_
    rw [Kraus.transferMap_apply]
    simp [hcon]
  rw [h0, map_zero, spectrum.spectralRadius_zero] at hC
  exact zero_ne_one hC

/-- A sector decomposition with nonzero irreducible basis blocks reduces onto its weighted
blocks. -/
private theorem nonempty_multiBlockCompression_toTensor (P : SectorDecomposition d)
    (hirr : ∀ j, Matrix.IsIrreducibleAction (P.basis j)) (hlet : ∀ j, ∃ i, P.basis j i ≠ 0) :
    Nonempty (MultiBlockCompression (D := fun x : (Σ j, Fin (P.copies j)) => P.basisDim x.1)
      P.toTensor Finset.univ (fun x => P.weight x.1 x.2 • P.basis x.1)) := by
  classical
  obtain ⟨Q, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ
    (D := fun x : (Σ j, Fin (P.copies j)) => P.basisDim x.1)
    (fun x => P.weight x.1 x.2 • P.basis x.1)
    (fun x _ => isIrreducibleAction_smul (hirr x.1) (P.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hlet x.1) (P.weight_ne_zero _ _)) P.toTensor
    (fun w _ => by
      have h := P.mpv_toTensor_eq_sum_sectors w.get
      simp only [mpv_eq, coeff_eq, List.ofFn_get] at h
      rw [h, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
      rw [trace_evalWord_smul])
  exact ⟨Q⟩

/-- A gauge relation with a phase is a repeated-block relation. -/
private theorem hetRepeatedBlocks_of_isGaugeRelated_smul {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {B : MPSTensor d D₂} {c : ℂ} (hc : ‖c‖ = 1) (h : IsGaugeRelated A (c • B)) :
    HetRepeatedBlocks A B := by
  have hdim : D₁ = D₂ := h.dim_eq
  subst hdim
  obtain ⟨G, hG⟩ := isGaugeRelated_iff_gaugeEquiv.1 h
  refine ⟨rfl, c, G⁻¹, hc, fun i => ?_⟩
  simp only [cast_eq, inv_inv]
  have hgi : ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
      (G : Matrix (Fin D₁) (Fin D₁) ℂ) = 1 := Units.inv_mul G
  have hi : (c • B) i = (G : Matrix (Fin D₁) (Fin D₁) ℂ) * A i *
      ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) := hG i
  calc A i = (((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
        (G : Matrix (Fin D₁) (Fin D₁) ℂ)) * A i *
        (((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) *
          (G : Matrix (Fin D₁) (Fin D₁) ℂ)) := by
        rw [hgi, Matrix.one_mul, Matrix.mul_one]
    _ = ((G⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) * ((c • B) i) *
        (G : Matrix (Fin D₁) (Fin D₁) ℂ) := by
        rw [hi]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- Under dependent states, every basis block of one decomposition is a repeated block of a basis
block of the other, when all gauge scalars between basis blocks have modulus one. -/
private theorem forall_exists_hetRepeatedBlocks_of_statesDependent (P Q : SectorDecomposition d)
    (hirrP : ∀ j, Matrix.IsIrreducibleAction (P.basis j)) (hletP : ∀ j, ∃ i, P.basis j i ≠ 0)
    (hirrQ : ∀ k, Matrix.IsIrreducibleAction (Q.basis k)) (hletQ : ∀ k, ∃ i, Q.basis k i ≠ 0)
    (hP0 : 0 < P.basisCount) (hQ0 : 0 < Q.basisCount)
    (hnorm : ∀ j k (c : ℂ), IsGaugeRelated (P.basis j) (c • Q.basis k) → ‖c‖ = 1)
    (hdep : ∀ᶠ N in atTop, StatesDependentAt P.toTensor Q.toTensor N) :
    (∀ j, ∃ k, HetRepeatedBlocks (P.basis j) (Q.basis k)) ∧
      ∀ k, ∃ j, HetRepeatedBlocks (P.basis j) (Q.basis k) := by
  classical
  have hS : (Finset.univ : Finset (Σ j, Fin (P.copies j))).Nonempty :=
    ⟨⟨⟨0, hP0⟩, ⟨0, P.copies_pos _⟩⟩, Finset.mem_univ _⟩
  have hT : (Finset.univ : Finset (Σ k, Fin (Q.copies k))).Nonempty :=
    ⟨⟨⟨0, hQ0⟩, ⟨0, Q.copies_pos _⟩⟩, Finset.mem_univ _⟩
  obtain ⟨h1, h2⟩ := forall_exists_isGaugeRelated_smul_of_eventually_statesDependentAt
    (nonempty_multiBlockCompression_toTensor P hirrP hletP)
    (nonempty_multiBlockCompression_toTensor Q hirrQ hletQ)
    (fun x _ => isIrreducibleAction_smul (hirrP x.1) (P.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hletP x.1) (P.weight_ne_zero _ _))
    (fun x _ => isIrreducibleAction_smul (hirrQ x.1) (Q.weight_ne_zero _ _))
    (fun x _ => exists_smul_apply_ne_zero (hletQ x.1) (Q.weight_ne_zero _ _)) hS hT hdep
  constructor
  · intro j
    obtain ⟨t, -, c, -, hg⟩ := h1 ⟨j, ⟨0, P.copies_pos j⟩⟩ (Finset.mem_univ _)
    set μ := P.weight j ⟨0, P.copies_pos j⟩ with hμ
    have hμ0 : μ ≠ 0 := P.weight_ne_zero _ _
    have hg' : IsGaugeRelated (P.basis j) ((μ⁻¹ * (c * Q.weight t.1 t.2)) • Q.basis t.1) := by
      have := hg.smul μ⁻¹
      simpa [smul_smul, inv_mul_cancel₀ hμ0] using this
    exact ⟨t.1, hetRepeatedBlocks_of_isGaugeRelated_smul (hnorm _ _ _ hg') hg'⟩
  · intro k
    obtain ⟨s, -, c, hc, hg⟩ := h2 ⟨k, ⟨0, Q.copies_pos k⟩⟩ (Finset.mem_univ _)
    set ν := Q.weight k ⟨0, Q.copies_pos k⟩ with hν
    have hμ0 : c * P.weight s.1 s.2 ≠ 0 := mul_ne_zero hc (P.weight_ne_zero _ _)
    have hg' : IsGaugeRelated (P.basis s.1)
        (((c * P.weight s.1 s.2)⁻¹ * ν) • Q.basis k) := by
      have := hg.symm.smul (c * P.weight s.1 s.2)⁻¹
      rw [smul_smul c (P.weight s.1 s.2) (P.basis s.1), smul_smul (c * P.weight s.1 s.2)⁻¹,
        inv_mul_cancel₀ hμ0, one_smul, smul_smul] at this
      exact this
    exact ⟨s.1, hetRepeatedBlocks_of_isGaugeRelated_smul (hnorm _ _ _ hg') hg'⟩

/-- **De las Cuevas et al., proportional case, with dependent states.** Two tensors in irreducible
form with bases of periodic tensors, both nonempty, whose states are linearly dependent at all
large lengths have bases matched up to a phase and a gauge, with equal periods.

Source: arXiv:1708.00029, theorem `thm:bd`, lines 613--623; the source assumes proportional states
for all `N`. The hypotheses `0 < P.basisCount`, `0 < Q.basisCount` exclude the empty form, whose
state vanishes and is dependent on every state. -/
theorem fundamentalTheorem_irreducibleForm_of_statesDependent
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (d := d) (D := P.basisDim j) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (d := d) (D := Q.basisDim k) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hP0 : 0 < P.basisCount) (hQ0 : 0 < Q.basisCount)
    (hdep : ∀ᶠ N in atTop, StatesDependentAt P.toTensor Q.toTensor N) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
      PeriodicBasisMatchingWitness P.basis Q.basis periodP periodQ := by
  classical
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrrQ k) (hRadQ k)
  obtain ⟨hf, hg⟩ := forall_exists_hetRepeatedBlocks_of_statesDependent P Q
    (fun j => Kraus.isIrreducibleAction_of_isIrreducibleFamily _ (hIrrP j))
    (fun j => exists_ne_zero_of_spectralRadius_eq_one (hRadP j))
    (fun k => Kraus.isIrreducibleAction_of_isIrreducibleFamily _ (hIrrQ k))
    (fun k => exists_ne_zero_of_spectralRadius_eq_one (hRadQ k)) hP0 hQ0
    (fun j k _ h => norm_eq_one_of_isGaugeRelated_smul (hRadP j) (hRadQ k) h) hdep
  choose f hf using hf
  choose g hg using hg
  have hfinj : Function.Injective f := fun j₁ j₂ hj => by
    by_contra hne
    have h₂ : HetRepeatedBlocks (Q.basis (f j₁)) (P.basis j₂) := hj ▸ (hf j₂).symm
    exact hNonRepP j₁ j₂ hne ((hf j₁).trans h₂)
  have hginj : Function.Injective g := fun k₁ k₂ hk => by
    by_contra hne
    have h₂ : HetRepeatedBlocks (P.basis (g k₁)) (Q.basis k₂) := hk ▸ hg k₂
    exact hNonRepQ k₁ k₂ hne ((hg k₁).symm.trans h₂)
  have hcard : P.basisCount = Q.basisCount := by
    have h1 := Fintype.card_le_of_injective f hfinj
    have h2 := Fintype.card_le_of_injective g hginj
    simp only [Fintype.card_fin] at h1 h2
    omega
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, by simp [hcard]⟩
  refine ⟨periodP, periodQ, hPerP, hPerQ, hcard, Equiv.ofBijective f hfbij, fun j => ?_⟩
  exact ⟨IsSpectrallyPeriodic.period_eq_of_hetRepeatedBlocks (hPerP j) (hPerQ _) (hf j), hf j⟩

end MPSTensor
