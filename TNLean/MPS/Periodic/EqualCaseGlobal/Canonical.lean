/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseGlobal.Basic

/-!
# Equal-case fundamental theorem for left-canonical periodic blocks

The blockwise matching and multiplicity gauge give a unitary global similarity
between equal positive-length matrix product vector families.
Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643–693.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Similarity carrying a prescribed scalar -/

/-- The two tensors have equal bond dimension and, after that identification,
the matrices of the first are the prescribed scalar `ζ` times a fixed conjugate
of those of the second.

This is the repeated-block relation of arXiv:1708.00029, definition
`def:repeated` and equation `eq:rep`, lines 276--284, with the scalar named
instead of bound existentially. Naming it is what lets one statement use the
same scalar in the similarity and in the multiplicity relation, as the equal
case does at lines 667--671 and 681--688. -/
def ScalarGaugeEquiv {D₁ D₂ : ℕ} (ζ : ℂ) (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    Prop :=
  ∃ (h : D₁ = D₂) (Y : GL (Fin D₂) ℂ),
    ∀ i, (cast (congr_arg (MPSTensor d) h) A) i =
      ζ • ((Y : Matrix (Fin D₂) (Fin D₂) ℂ) * B i *
        ((Y⁻¹ : GL (Fin D₂) ℂ) : Matrix (Fin D₂) (Fin D₂) ℂ))

/-- Forgetting the name of the scalar recovers the repeated-block relation. -/
theorem ScalarGaugeEquiv.toHetRepeatedBlocks {D₁ D₂ : ℕ} {ζ : ℂ}
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} (hζ : ‖ζ‖ = 1)
    (h : ScalarGaugeEquiv ζ A B) : HetRepeatedBlocks A B := by
  obtain ⟨hd, Y, hY⟩ := h
  exact ⟨hd, ζ, Y, hζ, hY⟩

/-- Replacing the first tensor by a purely similar one keeps the scalar. -/
theorem ScalarGaugeEquiv.of_gaugeEquiv_left {D₁ D₂ : ℕ} {ζ : ℂ}
    {A A' : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hAA' : GaugeEquiv A A') (h : ScalarGaugeEquiv ζ A' B) :
    ScalarGaugeEquiv ζ A B := by
  obtain ⟨hd, Y, hY⟩ := h
  subst hd
  obtain ⟨X, hX⟩ := hAA'
  refine ⟨rfl, X⁻¹ * Y, fun i => ?_⟩
  have hA : A i =
      ((X⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ) * A' i *
        (X : Matrix (Fin D₁) (Fin D₁) ℂ) := by
    rw [hX i]
    simp [Matrix.mul_assoc]
  have hA' : A' i =
      ζ • ((Y : Matrix (Fin D₁) (Fin D₁) ℂ) * B i *
        ((Y⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ)) := hY i
  change A i = _
  rw [hA, hA']
  simp [Matrix.mul_assoc, mul_inv_rev]

/-- Replacing the second tensor by a purely similar one keeps the scalar. -/
theorem ScalarGaugeEquiv.of_gaugeEquiv_right {D₁ D₂ : ℕ} {ζ : ℂ}
    {A : MPSTensor d D₁} {B B' : MPSTensor d D₂}
    (h : ScalarGaugeEquiv ζ A B') (hBB' : GaugeEquiv B B') :
    ScalarGaugeEquiv ζ A B := by
  obtain ⟨hd, Y, hY⟩ := h
  obtain ⟨W, hW⟩ := hBB'
  refine ⟨hd, Y * W, fun i => ?_⟩
  rw [hY i, hW i]
  simp [Matrix.mul_assoc, mul_inv_rev]

/-! ## The equal-case fundamental theorem over multiplicity-bearing decompositions -/

/-- Repeated periodic blocks in left-canonical form have equal periods.

This is the last clause of arXiv:1708.00029, proposition
`equal-or-orthogonal-generalized`, lines 602--604: the repeated-block relation
`A^i = e^{iφ} Y B^i Y^{-1}` can hold only between blocks of equal period. The
repeated-block relation preserves the peripheral transfer spectrum, which for a
periodic block is the set of `m`-th roots of unity. -/
theorem IsPeriodic.period_eq_of_hetRepeatedBlocks
    {D₁ D₂ m n : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (h : HetRepeatedBlocks A B) : m = n := by
  obtain ⟨hDim, hRep⟩ := h
  subst hDim
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRep
    hRep.peripheralEigenvalues_transferMap_eq

/-- For repeated periodic blocks with trace-preserving maps, the gauge of
`def:repeated` can be taken unitary while keeping its scalar.
Source: arXiv:1708.00029, line 332 ("if two blocks with associated trace-preserving
CP maps are repeated, then the invertible matrix `Y` in `def:repeated` must be
unitary"). -/
private theorem exists_unitary_of_periodic_gaugePhase
    {d D₁ D₂ m n : ℕ} (hD : D₁ = D₂)
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (X : GL (Fin D₂) ℂ) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hrel : ∀ i, (cast (congrArg (MPSTensor d) hD) A) i =
      ζ • ((X : Matrix (Fin D₂) (Fin D₂) ℂ) * B i *
        ((X⁻¹ : GL (Fin D₂) ℂ) : Matrix (Fin D₂) (Fin D₂) ℂ))) :
    ∃ U : Matrix.unitaryGroup (Fin D₂) ℂ,
      ∀ i, (cast (congrArg (MPSTensor d) hD) A) i =
        ζ • ((U : Matrix (Fin D₂) (Fin D₂) ℂ) * B i *
          (U : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ) := by
  subst D₂
  let : NeZero D₁ := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨U, _, hU⟩ := exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
    X ζ hζ hrel hB.leftCanonical hA.leftCanonical hB.irreducible hA.irreducible
  exact ⟨U, hU⟩

/-- **Fundamental theorem for matrix product states, equal case.**

Let two tensors carry the multiplicity-bearing irreducible forms
`A^i = ⊕_{j ∈ J} (R_j ⊗ A_j^i)` and `B^i = ⊕_{k ∈ K} (S_k ⊗ B_k^i)`, with
`R_j` and `S_k` diagonal with nonzero entries and with pairwise non-repeated
bases of periodic tensors. If the two tensors generate the same matrix-product
vector at every positive length, then the two bases have the same size and
there is a bijection `π : J → K` matching each `A_j` with the single `B_{π(j)}`
of the same period, with `A_j` and `B_{π(j)}` repeated blocks.

Moreover, for every `j` of period `m_j` the multiplicity matrices `R_j` and
`S_{π(j)}` have the same size, and after a reordering of the diagonal entries
of `S_{π(j)}` there is a diagonal matrix `Z_j` whose entries are `m_j`-th roots
of unity with `Z_j (ξ_j R_j) = S_{π(j)}`, where `ξ_j` is the unit-modulus scalar
of the repeated-block relation. Collecting the `Z_j` gives a matrix `Z` on the
bond space of the first tensor that commutes with every one of its matrices,
whose order divides the least common multiple of the periods, that satisfies
`Z A^i = Y B^i Yᴴ` for a unitary `Y`, and that leaves the generated
matrix-product vectors unchanged.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582.

The unit-modulus scalar of each matched pair is displayed rather than
suppressed: the entries of `Z_j` are roots of unity against the *rescaled*
multiplicity matrix `ξ_j R_j`, which is what the source means at lines
667--671 by absorbing the phase into `S_j`. The scalar is genuinely present:
for period one and `B_j = e^{iθ} A_j` it is not a root of unity.

The blocks are assumed left-canonical, that is, their maps are trace
preserving. This is the normalization of `eq:unital` at line 316, and it is
weaker than the source's irreducible form II, which additionally requires the
unique fixed point to be diagonal. The source theorem assumes only irreducible
form and asserts at lines 330--332 that one passes between the forms by a
block-diagonal similarity; that passage is carried out in
`fundamentalTheorem_periodic_equalCase_irreducibleForm`, which receives the
periods of the blocks as input, and of which the present statement is the
normalized half. The blockwise gauges are made unitary without changing their
phases, so the global inverse is the conjugate transpose, as required by the
application at lines 747--756. The source statement itself, with the periods derived, is
`fundamentalTheorem_periodic_equalCase_derivedPeriods`. The normalized half is
isolated because the periodic overlap dichotomy and the vanishing of an
off-period block are available in the normalized orientation. -/
theorem fundamentalTheorem_periodic_equalCase_sectorDecomposition
    (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (perm : Fin P.basisCount ≃ Fin Q.basisCount) (ξ : Fin P.basisCount → ℂ)
      (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ),
      (∀ j, ‖ξ j‖ = 1) ∧
      (∀ j, periodP j = periodQ (perm j)) ∧
      (∀ j, ScalarGaugeEquiv (ξ j) (P.basis j) (Q.basis (perm j))) ∧
      (∀ j, HetRepeatedBlocks (P.basis j) (Q.basis (perm j))) ∧
      (∀ j, Matrix.diagonal (z j) ^ periodP j = 1) ∧
      (∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
              (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j))),
            Matrix.diagonal (z j) * Matrix.diagonal (fun q => ξ j * P.weight j q) =
              Matrix.diagonal (fun q => Q.weight (perm j) (τ q))) ∧
      ∃ (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
        (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
        Y * Y' = 1 ∧ Y' * Y = 1 ∧ Y' = Yᴴ ∧
        blockScalarMatrix P.flatDim (P.flatCopyScalar z) ^
          (Finset.univ.lcm periodP) = 1 ∧
        (∀ i : Fin d,
          blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
            P.toTensor i * blockScalarMatrix P.flatDim (P.flatCopyScalar z)) ∧
        (∀ i : Fin d,
          blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i =
            Y * Q.toTensor i * Y') ∧
        SameMPV₂Pos P.toTensor
          (fun i =>
            blockScalarMatrix P.flatDim (P.flatCopyScalar z) * P.toTensor i) := by
  classical
  -- Theorem 3.4 supplies the matching of the two bases of periodic tensors.
  obtain ⟨_hCount, perm, hMatch⟩ :=
    fundamentalTheorem_periodic_proportional P.basis Q.basis hNonRepP hNonRepQ
      (PeriodicOverlapHypothesis.ofSectorDecompositions P Q periodP periodQ
        hPerP hPerQ hNonRepP hNonRepQ hSame.toNonzeroProportionalMPV₂)
  choose hDimJ ξ Xb hξ hConjRaw using hMatch
  have hξ0 : ∀ j, ξ j ≠ 0 := fun j => Complex.ne_zero_of_norm_eq_one (hξ j)
  have hUnitaryMatch : ∀ j, ∃ U : Matrix.unitaryGroup (Fin (Q.basisDim (perm j))) ℂ,
      ∀ i, (cast (congrArg (MPSTensor d) (hDimJ j)) (P.basis j)) i =
        ξ j • ((U : Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ) *
          Q.basis (perm j) i *
          (U : Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ)ᴴ) :=
    fun j => exists_unitary_of_periodic_gaugePhase (hDimJ j)
      (hPerP j) (hPerQ (perm j)) (Xb j) (hξ0 j) (hConjRaw j)
  choose U hU using hUnitaryMatch
  let Yb' := fun j => unitaryGL (U j)
  have hConj' (j) (i) : (cast (congrArg (MPSTensor d) (hDimJ j)) (P.basis j)) i =
      ξ j • ((Yb' j : Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ) *
        Q.basis (perm j) i *
        ((Yb' j)⁻¹ : GL (Fin (Q.basisDim (perm j))) ℂ)) := hU j i
  have hMatch' : ∀ j, HetRepeatedBlocks (P.basis j) (Q.basis (perm j)) :=
    fun j => ⟨hDimJ j, ξ j, Yb' j, hξ j, hConj' j⟩
  have hPeriodEq : ∀ j, periodP j = periodQ (perm j) := fun j =>
    IsPeriodic.period_eq_of_hetRepeatedBlocks (hPerP j) (hPerQ (perm j)) (hMatch' j)
  -- the matched matrix-product vectors differ by a power of the matched scalar
  have hBasis : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (P.basis j) σ = ξ j ^ N * mpv (Q.basis (perm j)) σ := by
    intro j N σ
    rw [← mpv_cast_dim (hDimJ j) (P.basis j) N σ]
    exact mpv_eq_pow_mul_of_gaugePhase (Q.basis (perm j))
      (cast (congr_arg (MPSTensor d) (hDimJ j)) (P.basis j)) (Yb' j) (ξ j)
      (hConj' j) N σ
  -- coefficient extraction along the period progression
  obtain ⟨N₀, hN₀⟩ :=
    SectorDecomposition.coeff_eq_of_sameMPV_of_matched_basis
      periodP hPerP hNonRepP perm ξ hξ0 hBasis hSame
  have hpowdata : ∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
      (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j))),
      ∀ q, Q.weight (perm j) (τ q) ^ periodP j =
        (ξ j * P.weight j q) ^ periodP j := by
    intro j
    have hm : 0 < periodP j := (hPerP j).period_pos
    have hCoeff : ∀ n > N₀,
        P.coeff (periodP j * n) j =
          (ξ j)⁻¹ ^ (periodP j * n) * Q.coeff (periodP j * n) (perm j) := by
      intro n hn
      exact hN₀ (periodP j * n)
        (le_trans (le_of_lt hn) (Nat.le_mul_of_pos_left n hm)) j ⟨n, rfl⟩
    obtain ⟨hc, τ, hτ⟩ :=
      matched_sector_weight_pow_equiv_of_period_multiple j (perm j) (periodP j)
        (ξ j)⁻¹ (inv_ne_zero (hξ0 j)) hCoeff
    exact ⟨hc, τ, fun q => by simpa [inv_inv] using hτ q⟩
  choose hCopies τ hτpow using hpowdata
  -- the multiplicity ratios are roots of unity of the block period
  have hden : ∀ j q, ξ j * P.weight j q ≠ 0 := fun j q =>
    mul_ne_zero (hξ0 j) (P.weight_ne_zero j q)
  set z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ := fun j q =>
    Q.weight (perm j) (τ j q) / (ξ j * P.weight j q) with hzdef
  have hz : ∀ j q, z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ j q) :=
    fun j q => div_mul_cancel₀ _ (hden j q)
  have hzm : ∀ j q, z j q ^ periodP j = 1 := by
    intro j q
    rw [hzdef, div_pow, hτpow j q, div_self (pow_ne_zero _ (hden j q))]
  refine ⟨perm, ξ, z, hξ, hPeriodEq,
    fun j => ⟨hDimJ j, Yb' j, hConj' j⟩, hMatch', ?_, ?_, ?_⟩
  · -- each blockwise multiplicity gauge has order the block period
    intro j
    simp only [Matrix.diagonal_pow, Pi.pow_def]
    rw [show (fun q => z j q ^ periodP j) = (1 : Fin (P.copies j) → ℂ) from
      funext (hzm j)]
    exact Matrix.diagonal_one
  · -- the blockwise multiplicity gauge relates the two multiplicity matrices
    intro j
    refine ⟨hCopies j, τ j, ?_⟩
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun q => hz j q)
  · -- global multiplicity gauge and similarity
    obtain ⟨Y, Y', h1, h2, hUnitary, hrest⟩ :=
      equalCase_global_zgauge_of_blockwise perm hDimJ τ ξ
      (Equiv.piCongrLeft (fun k => GL (Fin (Q.basisDim k)) ℂ) perm Yb')
      (by
        intro j i
        rw [Equiv.piCongrLeft_apply_apply]
        exact hConj' j i)
      z hz periodP hPerP hzm (Finset.univ.lcm periodP)
      (fun j => Finset.dvd_lcm (Finset.mem_univ j))
    refine ⟨Y, Y', h1, h2, hUnitary ?_, hrest⟩
    intro k
    obtain ⟨j, rfl⟩ := perm.surjective k
    rw [Equiv.piCongrLeft_apply_apply]
    exact (U j).prop

/-- Multiplicities matched to unit-modulus multiplicities also have modulus one.
This is the normalization step in the corrected forward implication of
arXiv:1708.00029, Theorem 4.1, lines 743–756, allowing the phases introduced when
grouping repeated blocks. -/
theorem weight_norm_eq_one_of_sameMPV₂Pos
    (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) :
    ∀ j q, ‖P.weight j q‖ = 1 := by
  obtain ⟨perm, ξ, z, hξ, _, _, _, hz, hw, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition
      P Q periodP periodQ hPerP hPerQ hNonRepP hNonRepQ hSame
  intro j q
  obtain ⟨_, τ, hτ⟩ := hw j
  have hzm := congrArg (fun M : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ => M q q)
    (hz j)
  simp only [Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply,
    Matrix.one_apply_eq] at hzm
  have hznorm := Complex.norm_eq_one_of_pow_eq_one hzm
    (Nat.ne_of_gt (hPerP j).period_pos)
  have hrel := congrArg (fun M : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ => M q q) hτ
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at hrel
  have hnorm := congrArg norm hrel
  simpa only [norm_mul, hznorm, hξ, hQweight, one_mul] using hnorm

end MPSTensor
