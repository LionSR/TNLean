/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Periodic.EqualCaseGlobal
import TNLean.MPS.CanonicalForm.Periodic.SectorNormalization

/-!
# Equal-case fundamental theorem for left-canonical periodic blocks

The blockwise matching and multiplicity gauge give a unitary global similarity
between equal positive-length matrix product vector families.
Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643–693.

It also contains the following results.

* `MPSTensor.fundamentalTheorem_periodic_equalCase_irreducibleForm`: equal-case fundamental theorem
  without trace-preserving normalization.
* `MPSTensor.fundamentalTheorem_periodic_proportional_irreducibleForm`,
  `MPSTensor.fundamentalTheorem_periodic_equalCase_derivedPeriods`: the periodic fundamental
  theorems over the source's irreducible form.
-/

section EqualCaseCanonical

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

end EqualCaseCanonical

section EqualCaseIrreducibleForm

/-!
## Equal-case fundamental theorem without trace-preserving normalization

Blockwise Perron similarities transfer the canonical equal-case theorem to
irreducible form while preserving the multiplicity gauge.
Source: arXiv:1708.00029, `eq:unital` and `thm:bdequal`, lines 313–332 and 643–693.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Removing the trace-preserving restriction -/

/-- **Fundamental theorem for matrix product states, equal case, irreducible
form.**

This is the preceding theorem without the left-canonical normalization of the
blocks, that is, over the source's irreducible form rather than over the
trace-preserving normalization of `eq:unital`. The similarity produced here is
invertible; unitarity is a feature of the normalized form and is not asserted.

The proof normalizes each representative by its positive-definite adjoint
Perron fixed point, which is the source construction at
arXiv:1708.00029, lines 313--332 (equation `eq:unital`, line 316). That
similarity is blockwise, so it leaves every multiplicity entry, every
multiplicity power sum, and the multiplicity gauge itself unchanged; the
multiplicity gauge is scalar on each block and therefore commutes with the
block-diagonal normalizing similarity. Only the global similarity between the
two tensors is conjugated.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582.

The periods are received as input here, together with witnesses that each block
is spectrally periodic of the given period, whereas the source derives the
period of a block from irreducibility and spectral radius one at lines
257--258, citing Wolf. This is the working form; the source statement, with the
periods produced from the source's two conditions on the blocks, is
`fundamentalTheorem_periodic_equalCase_derivedPeriods`. See
`docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`, section "The
periods of an irreducible-form block: restriction eliminated". -/
theorem fundamentalTheorem_periodic_equalCase_irreducibleForm
    (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k))
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
        Y * Y' = 1 ∧ Y' * Y = 1 ∧
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
  -- normalize both bases by the blockwise Perron similarity
  obtain ⟨basisP, hGaugeP, hPeriodicP, -⟩ :=
    P.exists_isPeriodic_replaceBasis periodP hPerP
  obtain ⟨basisQ, hGaugeQ, hPeriodicQ, -⟩ :=
    Q.exists_isPeriodic_replaceBasis periodQ hPerQ
  have hRepP : ∀ j, HetRepeatedBlocks (P.basis j) (basisP j) := fun j =>
    (hGaugeP j).toHetRepeatedBlocks
  have hRepQ : ∀ k, HetRepeatedBlocks (Q.basis k) (basisQ k) := fun k =>
    (hGaugeQ k).toHetRepeatedBlocks
  choose XPb hXPb using hGaugeP
  choose XQb hXQb using hGaugeQ
  set GP : GL (Fin P.totalDim) ℂ :=
    globalGaugeOfBlocks (matched_block_gauge (Q := P) XPb) with hGPdef
  set GQ : GL (Fin Q.totalDim) ℂ :=
    globalGaugeOfBlocks (matched_block_gauge (Q := Q) XQb) with hGQdef
  set XP : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    (GP : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) with hXPdef
  set XP' : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    ((GP⁻¹ : GL (Fin P.totalDim) ℂ) :
      Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) with hXP'def
  set XQ : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ :=
    (GQ : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) with hXQdef
  set XQ' : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ :=
    ((GQ⁻¹ : GL (Fin Q.totalDim) ℂ) :
      Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) with hXQ'def
  have hXPmul : XP * XP' = 1 := by rw [hXPdef, hXP'def]; simp
  have hXPmul' : XP' * XP = 1 := by rw [hXPdef, hXP'def]; simp
  have hXQmul : XQ * XQ' = 1 := by rw [hXQdef, hXQ'def]; simp
  have hXQmul' : XQ' * XQ = 1 := by rw [hXQdef, hXQ'def]; simp
  have hPconj : ∀ i : Fin d,
      (P.replaceBasis basisP).toTensor i = XP * P.toTensor i * XP' :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj (d := d) P.flatWeight
      P.flatBasis (P.replaceBasis basisP).flatBasis
      (matched_block_gauge (Q := P) XPb)
      (fun s i => hXPb (P.flatIndexEquiv.symm s).1 i)
  have hQconj : ∀ i : Fin d,
      (Q.replaceBasis basisQ).toTensor i = XQ * Q.toTensor i * XQ' :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj (d := d) Q.flatWeight
      Q.flatBasis (Q.replaceBasis basisQ).flatBasis
      (matched_block_gauge (Q := Q) XQb)
      (fun s i => hXQb (Q.flatIndexEquiv.symm s).1 i)
  have hGP : GaugeEquiv P.toTensor (P.replaceBasis basisP).toTensor :=
    ⟨GP, hPconj⟩
  have hGQ : GaugeEquiv Q.toTensor (Q.replaceBasis basisQ).toTensor :=
    ⟨GQ, hQconj⟩
  -- transport the hypotheses to the normalized decompositions
  have hNonRepP' : ∀ i j, i ≠ j →
      ¬ HetRepeatedBlocks ((P.replaceBasis basisP).basis i)
        ((P.replaceBasis basisP).basis j) := by
    intro i j hij hRep
    exact hNonRepP i j hij ((hRepP i).trans (hRep.trans (hRepP j).symm))
  have hNonRepQ' : ∀ i j, i ≠ j →
      ¬ HetRepeatedBlocks ((Q.replaceBasis basisQ).basis i)
        ((Q.replaceBasis basisQ).basis j) := by
    intro i j hij hRep
    exact hNonRepQ i j hij ((hRepQ i).trans (hRep.trans (hRepQ j).symm))
  have hSame' : SameMPV₂Pos (P.replaceBasis basisP).toTensor
      (Q.replaceBasis basisQ).toTensor := by
    intro N hN σ
    calc mpv (P.replaceBasis basisP).toTensor σ = mpv P.toTensor σ :=
          (GaugeEquiv.sameMPV hGP N σ).symm
      _ = mpv Q.toTensor σ := hSame N hN σ
      _ = mpv (Q.replaceBasis basisQ).toTensor σ := GaugeEquiv.sameMPV hGQ N σ
  obtain ⟨perm, ξ, z, hξ, hPeriodEq, hScalar, hMatch', hZdiag, hBlock, hEqual⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition
      (P.replaceBasis basisP) (Q.replaceBasis basisQ) periodP periodQ
      hPeriodicP hPeriodicQ hNonRepP' hNonRepQ' hSame'
  have hzm : ∀ j q, z j q ^ periodP j = 1 := by
    intro j q
    have hd := hZdiag j
    rw [Matrix.diagonal_pow] at hd
    have := congrArg (fun M : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ =>
      M q q) hd
    simpa [Matrix.diagonal_apply_eq, Pi.pow_apply] using this
  -- the multiplicity gauge is unchanged: it is scalar on each block
  set Z : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    blockScalarMatrix P.flatDim (P.flatCopyScalar z) with hZdef
  have hZcomm : Z * XP = XP * Z := by
    rw [hZdef, hXPdef, hGPdef]
    exact blockScalarMatrix_globalGaugeOfBlocks_comm _ _
  have hZP : ∀ i : Fin d, Z * P.toTensor i = P.toTensor i * Z := by
    intro i
    rw [hZdef]
    exact (blockScalarMatrix_mul_toTensorFromBlocks _ P.flatWeight P.flatBasis i).trans
      (toTensorFromBlocks_mul_blockScalarMatrix _ P.flatWeight P.flatBasis i).symm
  have hglobal : ∃ (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
      (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
      Y * Y' = 1 ∧ Y' * Y = 1 ∧ Z ^ (Finset.univ.lcm periodP) = 1 ∧
      (∀ i : Fin d, Z * (XP * P.toTensor i * XP') =
        Y * (XQ * Q.toTensor i * XQ') * Y') := by
    obtain ⟨Y, Y', h1, h2, -, h3, -, h5, -⟩ := hEqual
    refine ⟨Y, Y', h1, h2, h3, fun i => ?_⟩
    rw [← hPconj i, ← hQconj i]
    exact h5 i
  obtain ⟨Y, Y', hYY', hY'Y, hZLpow, hgauge⟩ := hglobal
  have hmove : ∀ K : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ,
      Z * (XP * K) = XP * (Z * K) := by
    intro K
    rw [← Matrix.mul_assoc, hZcomm, Matrix.mul_assoc]
  have hcancel : ∀ M : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ,
      XP' * (XP * M * XP') * XP = M := by
    intro M
    simp only [Matrix.mul_assoc]
    rw [hXPmul', mul_one, ← Matrix.mul_assoc, hXPmul', one_mul]
  refine ⟨perm, ξ, z, hξ, hPeriodEq, ?_, ?_, hZdiag, hBlock,
    XP' * Y * XQ, XQ' * Y' * XP, ?_, ?_, hZLpow, hZP, ?_, ?_⟩
  · exact fun j =>
      ((hScalar j).of_gaugeEquiv_left ⟨XPb j, hXPb j⟩).of_gaugeEquiv_right
        ⟨XQb (perm j), hXQb (perm j)⟩
  · exact fun j => (hRepP j).trans ((hMatch' j).trans (hRepQ (perm j)).symm)
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc XQ XQ', hXQmul, Matrix.one_mul,
      ← Matrix.mul_assoc Y Y', hYY', Matrix.one_mul]
    exact hXPmul'
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc XP XP', hXPmul, Matrix.one_mul,
      ← Matrix.mul_assoc Y' Y, hY'Y, Matrix.one_mul]
    exact hXQmul'
  · intro i
    have h : XP * (Z * P.toTensor i) * XP' =
        Y * (XQ * Q.toTensor i * XQ') * Y' := by
      rw [← hgauge i]
      simp only [Matrix.mul_assoc]
      exact (hmove (P.toTensor i * XP')).symm
    calc Z * P.toTensor i
        = XP' * (XP * (Z * P.toTensor i) * XP') * XP := (hcancel _).symm
      _ = XP' * (Y * (XQ * Q.toTensor i * XQ') * Y') * XP := by rw [h]
      _ = XP' * Y * XQ * Q.toTensor i * (XQ' * Y' * XP) := by
          simp only [Matrix.mul_assoc]
  · exact sameMPV₂Pos_blockScalarMatrix_mul_toTensor P z periodP hzm
      (fun j N σ hnd => by
        rw [GaugeEquiv.sameMPV ⟨XPb j, hXPb j⟩ N σ]
        exact pgvwc07_stateVector_eq_zero_of_not_dvd (basisP j) (hPeriodicP j) hnd σ)

end MPSTensor

end EqualCaseIrreducibleForm

section IrreducibleFormPeriods

/-!
## The periodic fundamental theorems over the source's irreducible form

The source states its two fundamental theorems for tensors in irreducible form,
where a block is required only to have an irreducible transfer map of spectral
radius one (arXiv:1708.00029, lines 248--261).  The period of a block is
derived from those two conditions at lines 257--258 and appears in the
conclusion of the theorems, not among their hypotheses.

This file restates the proportional case (arXiv:1708.00029, Theorem 3.4, lines
613--623) and the equal case (Theorem 3.8, lines 643--693) over exactly those
two conditions, producing the periods rather than receiving them.  The periods
come from
`MPSTensor.exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one`.

### Main results

* `MPSTensor.fundamentalTheorem_periodic_proportional_irreducibleForm`
* `MPSTensor.fundamentalTheorem_periodic_equalCase_derivedPeriods`

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Theorems 3.4
  and 3.8.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

variable {d : ℕ}

/-- **Fundamental theorem for matrix product states, proportional case, over
the source's irreducible form.**

The two block families are required only to be irreducible with transfer maps
of spectral radius one, which is the source's irreducible form at
arXiv:1708.00029, lines 248--261.  The periods are produced by the theorem,
as at lines 257--258, together with the witnesses that each block is spectrally
periodic of the produced period; the matching bijection then equates the
periods of matched blocks.

Source: arXiv:1708.00029, theorem `thm:bd`, lines 613--623, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582. -/
theorem fundamentalTheorem_periodic_proportional_irreducibleForm
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (P.basisDim j)) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (Q.basisDim k)) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hProp : NonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
      PeriodicBasisMatchingWitness P.basis Q.basis periodP periodQ := by
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrQ k) (hRadQ k)
  exact ⟨periodP, periodQ, hPerP, hPerQ,
    fundamentalTheorem_periodic_proportional_sectorDecomposition P Q periodP periodQ
      hPerP hPerQ hNonRepP hNonRepQ hProp⟩

/-- **Fundamental theorem for matrix product states, equal case, over the
source's irreducible form.**

The two block families are required only to be irreducible with transfer maps
of spectral radius one, which is the source's irreducible form at
arXiv:1708.00029, lines 248--261.  The periods are produced by the theorem, as
at lines 257--258, together with the witnesses that each block is spectrally
periodic of the produced period; every later clause speaks about those same
periods.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582. -/
theorem fundamentalTheorem_periodic_equalCase_derivedPeriods
    (P Q : SectorDecomposition d)
    (hIrrP : ∀ j, Kraus.IsIrreducibleFamily (P.basis j))
    (hRadP : ∀ j,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (P.basisDim j)) (P.basis j))) = 1)
    (hIrrQ : ∀ k, Kraus.IsIrreducibleFamily (Q.basis k))
    (hRadQ : ∀ k,
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap
            (Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))
          (Kraus.transferMap (ι := Fin d) (n := Fin (Q.basisDim k)) (Q.basis k))) = 1)
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ),
      (∀ j, IsSpectrallyPeriodic (periodP j) (P.basis j)) ∧
      (∀ k, IsSpectrallyPeriodic (periodQ k) (Q.basis k)) ∧
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
          Y * Y' = 1 ∧ Y' * Y = 1 ∧
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
  choose periodP hPerP using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrP j) (hRadP j)
  choose periodQ hPerQ using fun k =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one
      (hIrrQ k) (hRadQ k)
  exact ⟨periodP, periodQ, hPerP, hPerQ,
    fundamentalTheorem_periodic_equalCase_irreducibleForm P Q periodP periodQ
      hPerP hPerQ hNonRepP hNonRepQ hSame⟩

end MPSTensor

end IrreducibleFormPeriods
