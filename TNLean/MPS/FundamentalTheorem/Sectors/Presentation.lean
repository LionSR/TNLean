/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Sectors.FundamentalCoord
import TNLean.MPS.Tensor.DirectSum.GaugeEquiv

/-!
# The Fundamental Theorem on presentations by bases of normal tensors

The Fundamental Theorem of matrix product vectors (arXiv:1606.00608, Theorem 2.10 and
Corollary 2.11, lines 349--361) is stated for tensors in canonical form with no gauge
condition on their normal blocks.  The comparison theorems of `FundamentalCoord` assume that
the basis tensors are left-canonical.  This module removes that gauge choice: every
presentation by a basis of normal tensors is brought into left-canonical gauge by a
blockwise similarity that leaves the presented vectors unchanged
(`IsBNTSectorPresentation.exists_leftCanonical_withBasis`), the left-canonical theorems are
applied, and the gauges are composed back.

## Main results

* `fundamentalTheorem_proportional_of_isBNTSectorPresentation`: the proportional case,
  arXiv:1606.00608, Theorem 2.10.
* `fundamentalTheorem_equal_of_isBNTSectorPresentation`: the equal case,
  arXiv:1606.00608, Corollary 2.11.
* `ft_sector_data_of_isBNTSectorPresentation`: the equal case with matched copies and
  weights, arXiv:1606.00608, Appendix A, lines 1182--1192.
-/

open MPTensor

open scoped Matrix

namespace MPSTensor

variable {d : ℕ}

/-- A gauge-phase relation `B = ζ Y A Y⁻¹` transports along gauges of `A` and of `B`. -/
private lemma exists_conj_of_conj_of_gaugeEquiv {D : ℕ} {A A' B B' : MPSTensor d D} {ζ : ℂ}
    {Y : GL (Fin D) ℂ}
    (hAB : ∀ i, B i = ζ • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (hA : GaugeEquiv A' A) (hB : GaugeEquiv B B') :
    ∃ Z : GL (Fin D) ℂ, ∀ i, B' i = ζ • ((Z : Matrix (Fin D) (Fin D) ℂ) * A' i *
      ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  obtain ⟨W, hW⟩ := hA
  obtain ⟨V, hV⟩ := hB
  refine ⟨V * Y * W, fun i => ?_⟩
  rw [hV i, hAB i, hW i]
  simp only [mul_inv_rev, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Identifying equal bond dimensions preserves gauge equivalence. -/
private lemma gaugeEquiv_cast {D₁ D₂ : ℕ} (h : D₁ = D₂) {A B : MPSTensor d D₁}
    (hAB : GaugeEquiv A B) :
    GaugeEquiv (cast (congr_arg (MPSTensor d) h) A) (cast (congr_arg (MPSTensor d) h) B) := by
  subst h
  exact hAB

/-- A global conjugation `E = Y C Y⁻¹` across an identification of equal bond dimensions
transports along gauges of `C` and of `E`. -/
private lemma exists_conj_cast_of_conj_cast_of_gaugeEquiv {n m : ℕ} (h : n = m)
    (e : Matrix (Fin n) (Fin n) ℂ = Matrix (Fin m) (Fin m) ℂ)
    {C C' : MPSTensor d n} {E E' : MPSTensor d m} {Y : GL (Fin m) ℂ}
    (hCE : ∀ i, E i = (Y : Matrix (Fin m) (Fin m) ℂ) * cast e (C i) *
      ((Y⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ))
    (hC : GaugeEquiv C' C) (hE : GaugeEquiv E E') :
    ∃ Z : GL (Fin m) ℂ, ∀ i, E' i = (Z : Matrix (Fin m) (Fin m) ℂ) * cast e (C' i) *
      ((Z⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
  subst h
  simp only [cast_eq] at hCE ⊢
  obtain ⟨Z, hZ⟩ := hC.trans (GaugeEquiv.trans ⟨Y, hCE⟩ hE)
  exact ⟨Z, hZ⟩

/-- Gauging every basis tensor of a sector decomposition gauges its assembled tensor by a
block-diagonal similarity (arXiv:1606.00608, lines 281--301). -/
private lemma gaugeEquiv_toTensor_withBasis (P : SectorDecomposition d)
    {B : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j)}
    (hB : ∀ j, GaugeEquiv (P.basis j) (B j)) :
    GaugeEquiv P.toTensor (P.withBasis B).toTensor := by
  change GaugeEquiv (toTensorFromBlocks (α := Fin d) (μ := P.flatWeight) P.flatBasis)
    (toTensorFromBlocks (α := Fin d) (μ := P.flatWeight) (P.withBasis B).flatBasis)
  exact gaugeEquiv_toTensorFromBlocks_of_blockGauge _ _ _ fun s => hB (P.flatIndexEquiv.symm s).1

/-- **Fundamental Theorem of matrix product vectors, proportional case**
(arXiv:1606.00608, Theorem 2.10, lines 349--352; arXiv:2011.12127, Theorem 4.4).

Let `A` and `B` be presented by bases of normal tensors `P` and `Q`, with no gauge condition
on the basis tensors and no normalization of the copy weights.  If `A` and `B` generate
eventually proportional nonzero matrix product vectors, the two bases have the same number of
elements, and after a bijection `β` every basis tensor of `Q` is a phase of unit modulus times
a gauge transform of the matched basis tensor of `P`. -/
theorem fundamentalTheorem_proportional_of_isBNTSectorPresentation
    {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {P Q : SectorDecomposition d}
    (hP : IsBNTSectorPresentation A P) (hQ : IsBNTSectorPresentation B Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ A B) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (Y : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Y k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Y k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) := by
  obtain ⟨BP, hGP, hCFP, hPresP⟩ := hP.exists_leftCanonical_withBasis
  obtain ⟨BQ, hGQ, hCFQ, hPresQ⟩ := hQ.exists_leftCanonical_withBasis
  have hProp' : EventuallyNonzeroProportionalMPV₂ (P.withBasis BP).toTensor
      (Q.withBasis BQ).toTensor := by
    filter_upwards [hProp, Filter.eventually_gt_atTop 0] with N hN hNpos
    obtain ⟨c, hc, hEq⟩ := hN
    refine ⟨c, hc, fun σ => ?_⟩
    rw [← hPresP.sameMPV₂Pos N hNpos σ, ← hPresQ.sameMPV₂Pos N hNpos σ]
    exact hEq σ
  obtain ⟨β, hDim, ζ, Y, hζ, hConj⟩ :=
    fundamentalTheorem_proportional_canonicalForm hCFP hCFQ hProp'
  choose Z hZ using fun k => exists_conj_of_conj_of_gaugeEquiv (hConj k)
    (gaugeEquiv_cast (hDim k) (hGP (β k))) (hGQ k).symm
  exact ⟨β, hDim, ζ, Z, hζ, hZ⟩

/-- **Fundamental Theorem of matrix product vectors, equal case**
(arXiv:1606.00608, Corollary 2.11, lines 354--361).

Let `P` and `Q` be presentations by bases of normal tensors of their assembled tensors, with
no gauge condition on the basis tensors and no normalization of the copy weights.  If the
assembled tensors generate the same matrix product vectors at every positive length, they have
the same bond dimension and are related by one global similarity. -/
theorem fundamentalTheorem_equal_of_isBNTSectorPresentation
    {P Q : SectorDecomposition d}
    (hP : IsBNTSectorPresentation P.toTensor P) (hQ : IsBNTSectorPresentation Q.toTensor Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (hTotal : P.totalDim = Q.totalDim) (Y : GL (Fin Q.totalDim) ℂ),
      ∀ i : Fin d,
        Q.toTensor i =
          (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
            cast (by rw [hTotal] :
                Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
              (P.toTensor i) *
            (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
              Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) := by
  obtain ⟨BP, hGP, hCFP, hPresP⟩ := hP.exists_leftCanonical_withBasis
  obtain ⟨BQ, hGQ, hCFQ, hPresQ⟩ := hQ.exists_leftCanonical_withBasis
  obtain ⟨hTotal, Y, hConj⟩ := fundamentalTheorem_equal_canonicalForm hCFP hCFQ
    (hPresP.sameMPV₂Pos.symm.trans (hEqual.trans hPresQ.sameMPV₂Pos))
  obtain ⟨Z, hZ⟩ := exists_conj_cast_of_conj_cast_of_gaugeEquiv hTotal _ hConj
    (gaugeEquiv_toTensor_withBasis P hGP) (gaugeEquiv_toTensor_withBasis Q hGQ).symm
  exact ⟨hTotal, Z, hZ⟩

/-- **Equal case with matched copies and weights** (arXiv:1606.00608, Corollary 2.11 and
Appendix A, lines 1182--1192), with no gauge condition on the basis tensors.

If `A` and `B` are presented by bases of normal tensors `P` and `Q` and generate the same
matrix product vectors at every positive length, then after a bijection `β` the matched basis
tensors are gauge-phase equivalent, the matched sectors have the same number of copies, and
there are unit-modulus phases `ζ_k` and copy bijections `τ_k` with
`ν_{k,q} = ζ_k⁻¹ μ_{β(k),τ_k(q)}`. -/
theorem ft_sector_data_of_isBNTSectorPresentation
    {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {P Q : SectorDecomposition d}
    (hP : IsBNTSectorPresentation A P) (hQ : IsBNTSectorPresentation B Q)
    (hEqual : SameMPV₂Pos A B) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount),
      (∀ k, ∃ h : P.basisDim (β k) = Q.basisDim k,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) ∧
      (∀ k, P.copies (β k) = Q.copies k) ∧
      ∃ ζ : Fin Q.basisCount → ℂ, (∀ k, ‖ζ k‖ = 1) ∧
        ∀ k, ∃ τ : Fin (Q.copies k) ≃ Fin (P.copies (β k)),
          ∀ q : Fin (Q.copies k), Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ q) := by
  obtain ⟨BP, hGP, hCFP, hPresP⟩ := hP.exists_leftCanonical_withBasis
  obtain ⟨BQ, hGQ, hCFQ, hPresQ⟩ := hQ.exists_leftCanonical_withBasis
  obtain ⟨β, hMatch, hCopies, ζ, hζ, hWeight⟩ := ft_sector_bnt_equal_sector_data hCFP hCFQ
    (hPresP.sameMPV₂Pos.symm.trans (hEqual.trans hPresQ.sameMPV₂Pos))
  refine ⟨β, fun k => ?_, hCopies, ζ, hζ, hWeight⟩
  obtain ⟨h, X, c, hc, hX⟩ := hMatch k
  obtain ⟨Z, hZ⟩ := exists_conj_of_conj_of_gaugeEquiv hX
    (gaugeEquiv_cast h (hGP (β k))) (hGQ k).symm
  exact ⟨h, Z, c, hc, hZ⟩

end MPSTensor
