/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.WeightEquiv
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.Overlap.NonzeroSubfamily
import TNLean.MPS.Periodic.StateVectorDecomposition
import TNLean.MPS.SharedInfra.SectorDecomposition

/-!
# Coefficient extraction in the equal case

The equal-case fundamental theorem for matrix product states starts from two
tensors in irreducible form whose matrix-product vectors agree at every length,
and from the matching of their bases of periodic tensors supplied by the
proportional case. Expanding both matrix-product vectors along the common basis
and using that a basis member generates the zero vector unless its period
divides the chain length, the independence of the surviving basis vectors turns
the equality of the two states into an equality of the multiplicity power sums
at every large chain length that the corresponding period divides.

## Main declarations

* `MPSTensor.SectorDecomposition.coeff_eq_of_sameMPV_of_matched_basis`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693.
-/

open scoped BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- **Coefficient extraction in the equal case.**

Two multiplicity-bearing decompositions whose bases of periodic tensors are
matched by a bijection up to nonzero scalars, and whose assembled tensors
generate the same matrix-product vector at every positive length, have
multiplicity power sums that agree at every sufficiently large length divisible
by the corresponding period, once the phase carried by the matching is undone.

This is the step
`tr(R_j^N) = tr(S_j^N)` of arXiv:1708.00029, theorem `thm:bdequal`,
lines 672--680. The matched-basis phase is kept explicit: the identity relates
the multiplicity power sum of one decomposition to the *rescaled* power sum of
the other, which is what the source means by absorbing the phase into `S_j` at
lines 667--671. The lengths that the period does not divide drop out because
the corresponding basis vector vanishes there (lines 660--661), and the
surviving vectors are independent by the consequence of proposition
`equal-or-orthogonal-generalized` recorded at lines 677--679.

The matching scalars are only assumed nonzero, which is all the argument uses.
In the intended application they are the unit-modulus scalars of the
repeated-block relation, supplied by
`HetRepeatedBlocks.exists_unit_phase_power_mpv`. -/
theorem SectorDecomposition.coeff_eq_of_sameMPV_of_matched_basis
    {P Q : SectorDecomposition d}
    (periodP : Fin P.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (ζ : Fin P.basisCount → ℂ) (hζ : ∀ j, ζ j ≠ 0)
    (hBasis : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (P.basis j) σ = ζ j ^ N * mpv (Q.basis (perm j)) σ)
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ j : Fin P.basisCount, periodP j ∣ N →
      P.coeff N j = (ζ j)⁻¹ ^ N * Q.coeff N (perm j) := by
  obtain ⟨N₁, hN₁⟩ :=
    periodicBasis_nonzero_subfamily_eventuallyLinearlyIndependent
      P.basis periodP hPerP
      (fun i j hij hdim hrep => hNonRepP i j hij ⟨hdim, hrep⟩)
  refine ⟨max N₁ 1, fun N hN j hj => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hN)
  -- The matched basis vectors differ by the reciprocal phase power.
  have hState : ∀ j : Fin P.basisCount,
      mpvState (d := d) (Q.basis (perm j)) N
        = ((ζ j)⁻¹ ^ N) • mpvState (d := d) (P.basis j) N := by
    intro j
    ext σ
    simp only [mpvState_apply, PiLp.smul_apply, smul_eq_mul, hBasis j N σ]
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (hζ j), one_pow, one_mul]
  -- Both expansions run over the same basis, so their difference vanishes.
  have hSum : ∑ j : Fin P.basisCount,
      (P.coeff N j - (ζ j)⁻¹ ^ N * Q.coeff N (perm j)) •
        mpvState (d := d) (P.basis j) N = 0 := by
    have hP : mpvState (d := d) P.toTensor N
        = ∑ j : Fin P.basisCount, P.coeff N j • mpvState (d := d) (P.basis j) N :=
      P.mpvState_toTensor_eq_sum_coeff N
    have hQ : mpvState (d := d) Q.toTensor N
        = ∑ j : Fin P.basisCount,
            ((ζ j)⁻¹ ^ N * Q.coeff N (perm j)) • mpvState (d := d) (P.basis j) N := by
      rw [Q.mpvState_toTensor_eq_sum_coeff N,
        ← Equiv.sum_comp perm
          (fun k => Q.coeff N k • mpvState (d := d) (Q.basis k) N)]
      exact Finset.sum_congr rfl fun j _ => by
        rw [hState j, smul_smul, mul_comm]
    have hEq : mpvState (d := d) P.toTensor N = mpvState (d := d) Q.toTensor N := by
      ext σ
      simpa using hSame N hNpos σ
    rw [hP, hQ] at hEq
    have hSplit : ∑ j : Fin P.basisCount,
        (P.coeff N j • mpvState (d := d) (P.basis j) N
          - ((ζ j)⁻¹ ^ N * Q.coeff N (perm j)) •
            mpvState (d := d) (P.basis j) N) = 0 := by
      rw [Finset.sum_sub_distrib, hEq, sub_self]
    simpa [sub_smul] using hSplit
  -- Off-period basis vectors vanish, so only the divisible indices survive.
  have hFilter : ∀ x : Fin P.basisCount,
      x ∈ Finset.univ.filter (fun x => periodP x ∣ N) ↔ periodP x ∣ N := by
    intro x; simp
  have hDrop : ∑ x ∈ Finset.univ.filter (fun x => periodP x ∣ N),
      (P.coeff N x - (ζ x)⁻¹ ^ N * Q.coeff N (perm x)) •
        mpvState (d := d) (P.basis x) N = 0 := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · exact hSum
    · intro x _ hx
      have hnd : ¬ periodP x ∣ N := by simpa using hx
      have hzero : mpvState (d := d) (P.basis x) N = 0 := by
        ext σ
        simpa using
          pgvwc07_stateVector_eq_zero_of_not_dvd (P.basis x) (hPerP x) hnd σ
      rw [hzero, smul_zero]
  have hSubtype : ∑ k : {x : Fin P.basisCount // periodP x ∣ N},
      (P.coeff N ↑k - (ζ ↑k)⁻¹ ^ N * Q.coeff N (perm ↑k)) •
        mpvState (d := d) (P.basis ↑k) N = 0 :=
    (Finset.sum_subtype (Finset.univ.filter (fun x => periodP x ∣ N)) hFilter
      (fun x => (P.coeff N x - (ζ x)⁻¹ ^ N * Q.coeff N (perm x)) •
        mpvState (d := d) (P.basis x) N)).symm.trans hDrop
  exact sub_eq_zero.mp
    (Fintype.linearIndependent_iff.mp (hN₁ N hN₁')
      (fun k => P.coeff N ↑k - (ζ ↑k)⁻¹ ^ N * Q.coeff N (perm ↑k)) hSubtype ⟨j, hj⟩)

/-- **Blockwise multiplicity gauge in the equal case.**

Under the hypotheses of the coefficient extraction, each block of the first
decomposition has the same multiplicity as its matched block in the second, and
the two multiplicity families agree after a reordering and after multiplication
by a diagonal matrix whose entries are roots of unity of order the block's
period.

This is the conclusion of arXiv:1708.00029, theorem `thm:bdequal`, lines
681--688: the equality of multiplicity power sums along the multiples of the
period recovers the multiplicity entries up to a permutation and up to a
period-th root of unity, and collecting those roots of unity into a diagonal
matrix gives the relation `Z_j R_j = T_j S_j T_j^†`.

The phase carried by the matched bases is kept explicit as the factor `ζ j`
multiplying the multiplicity entries of the first decomposition. This is the
source's "the phase can be absorbed in `S_j`" of lines 667--671, written here on
the other side of the relation: the roots-of-unity property of the diagonal
matrix holds against the *rescaled* multiplicities, and the rescaling factor is
in general different from one even when the period is one, as the block pair
`B = e^{iθ} A` with period one shows. -/
theorem equalCase_blockwise_zgauge
    {P Q : SectorDecomposition d}
    (periodP : Fin P.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (ζ : Fin P.basisCount → ℂ) (hζ : ∀ j, ζ j ≠ 0)
    (hBasis : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (P.basis j) σ = ζ j ^ N * mpv (Q.basis (perm j)) σ)
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∀ j : Fin P.basisCount,
      ∃ (_hCopies : P.copies j = Q.copies (perm j))
        (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j)))
        (Z : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ),
        Z ^ periodP j = 1 ∧
        Z * Matrix.diagonal (fun q => ζ j * P.weight j q)
          = Matrix.diagonal (fun q => Q.weight (perm j) (τ q)) := by
  obtain ⟨N₀, hN₀⟩ :=
    SectorDecomposition.coeff_eq_of_sameMPV_of_matched_basis
      periodP hPerP hNonRepP perm ζ hζ hBasis hSame
  intro j
  have hm : 0 < periodP j := (hPerP j).period_pos
  have hCoeff : ∀ n > N₀,
      P.coeff (periodP j * n) j
        = (ζ j)⁻¹ ^ (periodP j * n) * Q.coeff (periodP j * n) (perm j) := by
    intro n hn
    exact hN₀ (periodP j * n)
      (le_trans (le_of_lt hn) (Nat.le_mul_of_pos_left n hm)) j ⟨n, rfl⟩
  obtain ⟨hCopies, τ, hτ⟩ :=
    matched_sector_weight_pow_equiv_of_period_multiple j (perm j) (periodP j)
      (ζ j)⁻¹ (inv_ne_zero (hζ j)) hCoeff
  have hpow : ∀ q, Q.weight (perm j) (τ q) ^ periodP j
      = (ζ j * P.weight j q) ^ periodP j := fun q => by
    simpa [inv_inv] using hτ q
  obtain ⟨Z, hZpow, hZmul⟩ :=
    zgauge_construction (periodP j)
      (fun q => Q.weight (perm j) (τ q)) (fun q => ζ j * P.weight j q)
      hpow (fun q => mul_ne_zero (hζ j) (P.weight_ne_zero j q))
  exact ⟨hCopies, τ, Z, hZpow, hZmul⟩

end MPSTensor
