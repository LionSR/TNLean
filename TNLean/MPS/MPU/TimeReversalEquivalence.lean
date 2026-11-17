/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalStrictEquivalence
import TNLean.MPS.MPU.TimeReversalSignTensorProduct

/-!
# The second time-reversal sign is an invariant of equivalence

Two time-reversal-invariant MPUs in standard form that are equivalent under time reversal, after
blocking and adjoining identity ancillas, have the same sign `σ⁽²⁾`. This is the second sentence
of the corollary following Proposition `prop:sigma1-and-sigma2-equal` of arXiv:1703.09188
(lines 1735--1743).

Time reversal is the family `timeReversalSymmetryFamily`: the adjoint, on rings whose length is a
positive multiple of four, at every physical dimension. These are the rings of an even number of
standard-form sites, as in `PropChiral` (`docs/paper-gaps/mpu_standard_form_parity_gap.tex`). The
adjoint is defined on the whole operator algebra at every physical dimension, and it commutes with
adjoining an identity ancilla, `(X ⊗ I)† = X† ⊗ I`. So the coherence law that
`EquivalentUnderSymmetry` requires of a symmetry family is a theorem here, not a hypothesis, and
the scope restriction of `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex` is discharged for this
family: equivalence under it is Definition `def:equivalent-symmetry` (lines 1356--1366) for time
reversal.

The proof compares intrinsic traces. Strict equivalence of the blocked ancilla tensors fixes the
second sign of the `k`-site blocking. An identity ancilla does not change any sign
(`intrinsicTimeReversalSign_blockTensor_tensorPhysicalId`), and by the blocking parity of the sign
the second sign of the `k`-site blocking is that of the original MPU.

## Main results

* `MPOTensor.timeReversalSymmetryFamily`: time reversal as a coherent symmetry family.
* `MPOTensor.timeReversalSign_eq_of_blocked_ancilla_strictlyEquivalent`: the corollary for
  equivalence, with the ancilla dimensions of the source definition, not necessarily coprime.
* `MPOTensor.EquivalentUnderSymmetry.timeReversalSign_eq`: the coprime special case.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- Adjoining an identity ancilla commutes with the adjoint, `(X ⊗ I)† = X† ⊗ I`.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366, for time
reversal, lines 965--973. -/
theorem conjTranspose_tensorPhysicalIdOperator {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    (tensorPhysicalIdOperator X x)ᴴ = tensorPhysicalIdOperator Xᴴ x := by
  rw [tensorPhysicalIdOperator, tensorPhysicalIdOperator, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- **Time reversal as a coherent symmetry family.** At every physical dimension the action is the
adjoint of the operator, on rings whose length is a positive multiple of four: the rings of an
even number of standard-form sites, on which `PropChiral` imposes time reversal. The adjoint
commutes with adjoining an identity ancilla, so the coherence law holds as a theorem, and
equivalence under this family is Definition `def:equivalent-symmetry` for time reversal.

Source: arXiv:1703.09188, time reversal, lines 965--973, with `PropChiral`, lines 1201--1252, and
Definition `def:equivalent-symmetry`, lines 1356--1366. -/
def timeReversalSymmetryFamily : FiniteChainOperatorSymmetryFamily where
  applicable := {N | 0 < N ∧ 4 ∣ N}
  action := fun X ↦ Xᴴ
  tensorPhysicalId_semiconj _ x _ := fun X ↦ (conjTranspose_tensorPhysicalIdOperator X x).symm

/-- The blocked components of the time-reversal family impose self-adjointness on every ring whose
length is a positive multiple of four.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem timeReversalSymmetryFamily_block_selfAdjoint (m k : ℕ) (hk : 0 < k) (N : ℕ) (hN : 0 < N)
    (h4 : 4 ∣ N) :
    N ∈ ((timeReversalSymmetryFamily.at m).block k).applicable ∧
      ∀ X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim m k))
        (Fin N → Fin (MPSTensor.blockPhysDim m k)) ℂ,
        ((timeReversalSymmetryFamily.at m).block k).action X = X → X = Xᴴ := by
  refine ⟨⟨Nat.mul_pos hN hk, Dvd.dvd.mul_right h4 k⟩, fun X hX ↦ ?_⟩
  rw [FiniteChainOperatorSymmetry.block_action] at hX
  change Matrix.reindex _ _ (Matrix.reindex _ _ X)ᴴ = X at hX
  rw [Matrix.conjTranspose_reindex] at hX
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Equiv.self_comp_symm, Matrix.submatrix_id_id] at hX
  exact hX.symm

/-- Under time reversal, the intrinsic sign of the blocking by `4 k` sites is that of the blocking
by four sites: the even case of the blocking parity, for the two-site block.

Source: arXiv:1703.09188, Proposition `prop:sigma1-and-sigma2-equal`, lines 1643--1655. -/
theorem IsMPU.intrinsicTimeReversalSign_blockTensor_four_mul [NeZero d] [NeZero D]
    {V : MPOTensor d D} (hV : IsMPU V)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ)
    (k : ℕ) (hk : 0 < k) :
    intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * (2 * k))) =
      intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * 2)) := by
  have : NeZero (MPSTensor.blockPhysDim d 2) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (NeZero.ne d)⟩
  have hU : MPOTensor.blockTensor V 2 =
      MPOTensor.reindexPhysical (twoSiteBlockEquiv d).symm (MPOTensor.blockTwo V) := by
    rw [blockTwo_eq_blockTensor_reindex]
    funext i j
    simp [MPOTensor.reindexPhysical]
  have hTR₂ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTensor V 2) N = (mpo (MPOTensor.blockTensor V 2) N)ᴴ := by
    intro N hN heven
    rw [hU, mpo_reindexPhysical, Matrix.conjTranspose_reindex, ← hTR N hN heven]
  have hblock : ∀ n : ℕ, intrinsicTimeReversalSign
      (MPOTensor.blockTensor (MPOTensor.blockTensor V 2) n) =
        intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * n)) := fun n ↦ by
    rw [← reindexPhysical_blockTensor_blockTensor V 2 n, intrinsicTimeReversalSign_reindexPhysical]
  have heven := ((hV.blockTensor 2 (by norm_num)).intrinsic_blocking_trace_parity hTR₂ (2 * k)
    (by omega)).2 (even_two_mul k)
  rw [← hblock, ← hblock, heven]

/-- The second sign of the `k`-site blocking of `V` with an identity ancilla is the intrinsic sign
of the blocking of `V` by `4 k` sites.

Source: arXiv:1703.09188, Definition `def:equivalent-symmetry`, lines 1356--1366. -/
private theorem intrinsicTimeReversalSign_blockTwo_blockTensor_ancilla {D : ℕ}
    (V : MPOTensor d D) {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
        (MPOTensor.blockTensor (MPOTensor.blockTensor (tensorPhysicalId V p) k) 2)) =
      intrinsicTimeReversalSign (MPOTensor.blockTensor V (2 * (2 * k))) := by
  rw [← intrinsicTimeReversalSign_reindexPhysical (twoSiteDirectBlockEquiv _ 2),
    reindexPhysical_blockTwo_blockTensor_two_mul,
    ← intrinsicTimeReversalSign_reindexPhysical (MPSTensor.directIteratedBlockEquiv _ k (2 * 2)),
    reindexPhysical_blockTensor_blockTensor,
    intrinsicTimeReversalSign_blockTensor_tensorPhysicalId V hp (by positivity),
    show k * (2 * 2) = 2 * (2 * k) by ring]

/-- **The second time-reversal sign is an invariant of equivalence.** Let `𝒰₁ = V₁` and
`𝒰₂ = V₂` be time-reversal-invariant MPUs, with standard-form gates `a₁, b₁` and `a₂, b₂` of the
two-site blocks of their blockings by two sites, so that `σ⁽²⁾(𝒰ᵢ) = s(aᵢ, bᵢ)`. Suppose that
for some `k > 0` and ancilla dimensions `pa, pb > 0` the tensors `(𝒰₁^{(pa)})_k` and
`(𝒰₂^{(pb)})_k`, obtained by adjoining identity ancillas and blocking `k` sites, are strictly
equivalent under time reversal. Then `σ⁽²⁾(𝒰₁) = σ⁽²⁾(𝒰₂)`. The physical dimensions of `𝒰₁` and
`𝒰₂` need not agree.

The hypothesis is the condition of Definition `def:equivalent-symmetry` for time reversal, with
the action `timeReversalSymmetryFamily` at the enlarged dimension. As in the source, no
coprimality of `pa` and `pb` is assumed. The hypotheses `hTR₁`, `hTR₂` are the time-reversal
invariance of `PropChiral`.

Source: arXiv:1703.09188, corollary after Proposition `prop:sigma1-and-sigma2-equal`, lines
1740--1743 (second sentence), with Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem timeReversalSign_eq_of_blocked_ancilla_strictlyEquivalent {da db Da Db : ℕ}
    {V₁ : MPOTensor da Da} {V₂ : MPOTensor db Db}
    (hV₁ : IsMPU V₁) (hV₂ : IsMPU V₂) {k pa pb : ℕ} (hk : 0 < k) (hpa : 0 < pa) (hpb : 0 < pb)
    {hdim : MPSTensor.blockPhysDim (da * pa) k = MPSTensor.blockPhysDim (db * pb) k}
    (hstrict : StrictlyEquivalentUnderSymmetry ((timeReversalSymmetryFamily.at (db * pb)).block k)
      (MPOTensor.blockTensor (tensorPhysicalId V₁ pa) k)
      (MPOTensor.blockTensor (tensorPhysicalId V₂ pb) k) hdim)
    (hTR₁ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V₁) N = (mpo (MPOTensor.blockTwo V₁) N)ᴴ)
    (hTR₂ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V₂) N = (mpo (MPOTensor.blockTwo V₂) N)ᴴ)
    {a₁ b₁ : Matrix (Fin (MPSTensor.blockPhysDim da 2) × Fin (MPSTensor.blockPhysDim da 2))
      (Fin (MPSTensor.blockPhysDim da 2) × Fin (MPSTensor.blockPhysDim da 2)) ℂ}
    {a₂ b₂ : Matrix (Fin (MPSTensor.blockPhysDim db 2) × Fin (MPSTensor.blockPhysDim db 2))
      (Fin (MPSTensor.blockPhysDim db 2) × Fin (MPSTensor.blockPhysDim db 2)) ℂ}
    (T₁ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₁ 2)) a₁ b₁)
    (T₂ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₂ 2)) a₂ b₂) :
    timeReversalSign a₁ b₁ = timeReversalSign a₂ b₂ := by
  have hd : ∀ {m : ℕ}, 0 < MPSTensor.blockPhysDim m 2 → NeZero m := fun hm ↦ ⟨by
    rintro rfl
    simp [MPSTensor.blockPhysDim_eq_pow] at hm⟩
  have : NeZero da := hd T₁.phys_pos
  have : NeZero db := hd T₂.phys_pos
  have : NeZero Da := ⟨T₁.bond_pos.ne'⟩
  have : NeZero Db := ⟨T₂.bond_pos.ne'⟩
  have : NeZero (MPSTensor.blockPhysDim (db * pb) k) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (mul_ne_zero (NeZero.ne db) hpb.ne')⟩
  have hcore := (StrictlyEquivalentUnderSymmetry.intrinsicTimeReversalSign_eq
    (timeReversalSymmetryFamily_block_selfAdjoint (db * pb) k hk) hstrict).2
  rw [intrinsicTimeReversalSign_blockTwo_blockTensor_ancilla V₁ hpa hk,
    intrinsicTimeReversalSign_blockTwo_blockTensor_ancilla V₂ hpb hk,
    hV₁.intrinsicTimeReversalSign_blockTensor_four_mul hTR₁ k hk,
    hV₂.intrinsicTimeReversalSign_blockTensor_four_mul hTR₂ k hk] at hcore
  rw [T₁.timeReversalSign_eq_intrinsic, T₂.timeReversalSign_eq_intrinsic,
    ← intrinsicTimeReversalSign_reindexPhysical (twoSiteDirectBlockEquiv da 2),
    reindexPhysical_blockTwo_blockTensor_two_mul,
    ← intrinsicTimeReversalSign_reindexPhysical (twoSiteDirectBlockEquiv db 2),
    reindexPhysical_blockTwo_blockTensor_two_mul]
  exact hcore

/-- The second time-reversal sign is an invariant of coherent-family equivalence under time
reversal, the special case of `timeReversalSign_eq_of_blocked_ancilla_strictlyEquivalent` with
coprime ancilla dimensions.

Source: arXiv:1703.09188, corollary after Proposition `prop:sigma1-and-sigma2-equal`, lines
1740--1743, with Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem EquivalentUnderSymmetry.timeReversalSign_eq {da db Da Db : ℕ}
    {V₁ : MPOTensor da Da} {V₂ : MPOTensor db Db}
    (h : EquivalentUnderSymmetry timeReversalSymmetryFamily V₁ V₂)
    (hTR₁ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V₁) N = (mpo (MPOTensor.blockTwo V₁) N)ᴴ)
    (hTR₂ : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V₂) N = (mpo (MPOTensor.blockTwo V₂) N)ᴴ)
    {a₁ b₁ : Matrix (Fin (MPSTensor.blockPhysDim da 2) × Fin (MPSTensor.blockPhysDim da 2))
      (Fin (MPSTensor.blockPhysDim da 2) × Fin (MPSTensor.blockPhysDim da 2)) ℂ}
    {a₂ b₂ : Matrix (Fin (MPSTensor.blockPhysDim db 2) × Fin (MPSTensor.blockPhysDim db 2))
      (Fin (MPSTensor.blockPhysDim db 2) × Fin (MPSTensor.blockPhysDim db 2)) ℂ}
    (T₁ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₁ 2)) a₁ b₁)
    (T₂ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₂ 2)) a₂ b₂) :
    timeReversalSign a₁ b₁ = timeReversalSign a₂ b₂ := by
  obtain ⟨hV₁, hV₂, k, pa, pb, hk, hpa, hpb, -, _hphys, hstrict⟩ := h
  exact timeReversalSign_eq_of_blocked_ancilla_strictlyEquivalent hV₁ hV₂ hk hpa hpb hstrict
    hTR₁ hTR₂ T₁ T₂

end MPOTensor
