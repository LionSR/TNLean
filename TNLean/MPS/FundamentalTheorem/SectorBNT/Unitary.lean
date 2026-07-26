/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexPhasePositivity
import TNLean.MPS.FundamentalTheorem.SectorBNT.Fundamental
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.SharedInfra.BlockGauge

/-!
# Unitary refinement of proportional BNT sector matching

The proportional Fundamental Theorem matches the basis normal tensors of two
canonical forms by gauge-phase equivalences. When the basis tensors satisfy the
BNT canonical form hypotheses of left-canonicity and irreducibility, the
matched gauges may be chosen unitary.

This is the proportional part of Canonical Form II in Cirac et al.,
arXiv:1606.00608, Corollary A.6, lines 1197–1199.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Canonical Form II unitary refinement of proportional BNT matching.**

Let two BNT canonical forms generate eventually nonzero proportional MPV
families.  Their basis normal tensors can be matched bijectively so that each
matched pair has the same bond dimension and differs by a unit phase and a
unitary conjugation.

The BNT hypotheses already include left canonicity and irreducibility for each
basis tensor.  Thus no hypothesis beyond those of the proportional BNT theorem
is needed for this refinement.

Source: Cirac et al., arXiv:1606.00608, Corollary A.6, lines 1197–1199. -/
theorem ft_sector_bnt_proportional_unitary_sector_match_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      ∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
  classical
  obtain ⟨β, hDim, ζ₀, X, hζ₀, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses hP hQ hProp
  have hGPE : ∀ k : Fin Q.basisCount,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) (Q.basis k) :=
    fun k => ⟨X k, ζ₀ k, by
      intro hzero
      simpa [hzero] using hζ₀ k, hConj k⟩
  have hUnitary : ∀ k : Fin Q.basisCount,
      ∃ (U : Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧
        ∀ i, Q.basis k i = ζ •
          ((U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
    intro k
    letI : NeZero (Q.basisDim k) := ⟨ne_of_gt (hQ.basis_dim_pos k)⟩
    apply exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible (hGPE k)
    · exact (leftCanonical_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_left_canonical (β k))
    · exact hQ.basis_left_canonical k
    · exact (isIrreducibleTensor_cast_dim (hDim k) (P.basis (β k))).2
        (hP.basis_irreducible (β k))
    · exact hQ.basis_irreducible k
  let U : (k : Fin Q.basisCount) →
      Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ :=
    fun k => (hUnitary k).choose
  let ζ : Fin Q.basisCount → ℂ :=
    fun k => (hUnitary k).choose_spec.choose
  refine ⟨β, hDim, ζ, U, ?_, ?_⟩
  · intro k
    exact (hUnitary k).choose_spec.choose_spec.1
  · intro k i
    exact (hUnitary k).choose_spec.choose_spec.2 i

/-- **Equal-MPV global gauge assembled from the unitary sector gauges.**

For equal BNT canonical forms, the sector phase used by the unitary conjugation
is the same phase that occurs in the copy-weight identity. Repeating each
sector unitary over its matched copies therefore gives a unitary block-diagonal
global gauge in matched flattened coordinates.

Source: arXiv:1606.00608, Corollary A.6 and Appendix MPV proof,
lines 1182--1199. -/
theorem ft_sector_bnt_equal_unitary_global_gauge_witnesses
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ)
      (X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ)) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
        (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) ∈
        Matrix.unitaryGroup (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ ∧
      ∀ i : Fin d,
        toTensorFromBlocks (d := d) (μ := Q.flatWeight) Q.flatBasis i =
          (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
            (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
            toTensorFromBlocks (d := d)
              (μ := matched_p_weight (P := P) (Q := Q) β τ)
              (matched_p_basis (P := P) (Q := Q) β hDim) i *
            (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
              Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) := by
  classical
  obtain ⟨β, hDim, ζ, Xblock, hζ, hConj, ⟨W⟩⟩ :=
    ft_sector_bnt_equal_matched_copy_weight_witnesses hP hQ hEqual
  have hζ_ne : ∀ k : Fin Q.basisCount, ζ k ≠ 0 := fun k =>
    Complex.ne_zero_of_norm_eq_one (hζ k)
  have hUnitary : ∀ k : Fin Q.basisCount,
      ∃ U : Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ,
        ∀ i, Q.basis k i = ζ k •
          ((U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (U : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) := by
    intro k
    letI : NeZero (Q.basisDim k) := ⟨ne_of_gt (hQ.basis_dim_pos k)⟩
    obtain ⟨U, _, hU⟩ :=
      exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
        (Xblock k) (ζ k) (hζ_ne k) (hConj k)
        ((leftCanonical_cast_dim (hDim k) (P.basis (β k))).2
          (hP.basis_left_canonical (β k)))
        (hQ.basis_left_canonical k)
        ((isIrreducibleTensor_cast_dim (hDim k) (P.basis (β k))).2
          (hP.basis_irreducible (β k)))
        (hQ.basis_irreducible k)
    exact ⟨U, hU⟩
  let U : (k : Fin Q.basisCount) → Matrix.unitaryGroup (Fin (Q.basisDim k)) ℂ :=
    fun k => (hUnitary k).choose
  have hConjU : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i = ζ k •
        ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ) :=
    fun k => (hUnitary k).choose_spec
  let Ugl : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ :=
    fun k => unitaryGL (U k)
  have hConjGL : ∀ (k : Fin Q.basisCount) (i : Fin d),
      Q.basis k i = ζ k •
        ((Ugl k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
          (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
          (((Ugl k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
            Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)) := by
    intro k i
    change Q.basis k i = ζ k •
      ((U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
        (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
        (U k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ)ᴴ)
    exact hConjU k i
  obtain ⟨X, hX, hGauge⟩ :=
    sector_bnt_global_gauge_of_copy_weight_matching
      β hDim ζ Ugl hζ_ne hConjGL W
  have hXunitary :
      (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
        (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) ∈
        Matrix.unitaryGroup (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ := by
    rw [hX]
    let Ucopy : (s : Fin Q.totalCopies) →
        Matrix.unitaryGroup (Fin (Q.flatDim s)) ℂ :=
      fun s => U (Q.flatIndexEquiv.symm s).1
    exact globalGaugeOfBlocks_unitaryGL_mem Ucopy
  have hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k := by
    intro k
    have hcard := Fintype.card_congr (W.copy_equiv k)
    simpa using hcard.symm
  exact ⟨β, hDim, hCopies, W.copy_equiv, ζ, U, X, hζ, hConjU,
    W.weight_eq, hXunitary, hGauge⟩

end MPSTensor
