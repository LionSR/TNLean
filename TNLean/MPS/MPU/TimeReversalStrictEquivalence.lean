/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TimeReversalBlockingParity
import TNLean.MPS.MPU.TimeReversalSignInvariance
import TNLean.MPS.MPU.SymmetryPathCriterion

/-!
# The time-reversal signs are invariants of strict equivalence

Two time-reversal-invariant MPUs in standard form that are strictly equivalent under time
reversal have the same signs `σ⁽¹⁾` and `σ⁽²⁾`. This is the first sentence of the corollary
following Proposition `prop:sigma1-and-sigma2-equal` of arXiv:1703.09188 (lines 1735--1743).

The tensors are read as in `PropChiral` and in `TimeReversalBlockingParity.lean`: `σ⁽¹⁾` is the
sign of a standard form of the two-site block `𝒰₂`, and `σ⁽²⁾` that of a standard form of the
two-site block of `𝒰₂`'s blocking by two sites of the original chain, i.e. of the blocking of
`𝒰` by two. Time reversal is self-adjointness of the operators of `𝒰` on rings whose length is
a multiple of four, which are the rings of an even number of standard-form sites
(`docs/paper-gaps/mpu_standard_form_parity_gap.tex`). The symmetry of strict equivalence is
any finite-chain symmetry that imposes this, such as `daggerSymmetry`.

The second sentence of the corollary, for equivalence after blocking and identity ancillas, is
`EquivalentUnderSymmetry.timeReversalSign_eq` in `TimeReversalEquivalence.lean`.

## Main results

* `MPOTensor.IsMPU.intrinsicTimeReversalSign_eq_one_or_neg_one`: for every MPU whose operators
  are self-adjoint on rings of even length, the intrinsic trace sign is `±1`. No simplicity or
  canonical form is assumed.
* `MPOTensor.intrinsicTimeReversalSign_eq_of_joinedIn`: the intrinsic sign is constant along a
  path of such MPUs.
* `MPOTensor.StrictlyEquivalentUnderSymmetry.intrinsicTimeReversalSign_eq`: strict equivalence
  fixes both intrinsic signs, between tensors of equal physical dimension.
* `MPOTensor.StrictlyEquivalentUnderSymmetry.timeReversalSign_eq`: the corollary for strict
  equivalence, for the gates of supplied standard forms.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- Self-adjointness of the periodic operators at every positive length divisible by `k`
passes to the blocking by `k` sites.

Source: arXiv:1703.09188, physical blocking, lines 297--304. -/
theorem mpo_blockTensor_selfAdjoint {X : MPOTensor d D} {k N : ℕ}
    (h : mpo X (N * k) = (mpo X (N * k))ᴴ) :
    mpo (MPOTensor.blockTensor X k) N = (mpo (MPOTensor.blockTensor X k) N)ᴴ := by
  rw [mpo_blockTensor_eq_reindex, Matrix.conjTranspose_reindex, ← h]

/-- Self-adjointness at length `2 N` passes to the two-site block at length `N`.

Source: arXiv:1703.09188, physical blocking, lines 297--304. -/
theorem mpo_blockTwo_selfAdjoint {X : MPOTensor d D} {N : ℕ}
    (h : mpo X (N * 2) = (mpo X (N * 2))ᴴ) :
    mpo (blockTwo X) N = (mpo (blockTwo X) N)ᴴ := by
  rw [mpo_blockTwo_eq_reindex_blockTensor, Matrix.conjTranspose_reindex]
  exact congrArg _ (mpo_blockTensor_selfAdjoint h)

/-- **The intrinsic time-reversal sign is `±1`.** For every MPU of positive dimensions whose
periodic operators are self-adjoint on every ring of even length, the normalized trace of the
exchange of two sites against the operator on a ring of two sites is `1` or `-1`. No
simplicity, canonical form or standard form is assumed.

The proof writes the blocked traces of a canonical representative as `η^k C` with `η = ±1`;
at the even blocking length `2 D⁴` the tensor is simple and its trace is a standard-form sign,
hence `C = ±1`.

Source: arXiv:1703.09188, `UUdaggertrick-2` and Proposition `prop:sigma-well-defined`,
lines 1585--1631, with `prop:sigma1-and-sigma2-equal`, lines 1643--1733. -/
theorem IsMPU.intrinsicTimeReversalSign_eq_one_or_neg_one [NeZero d] [NeZero D]
    {X : MPOTensor d D} (hX : IsMPU X)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo X N = (mpo X N)ᴴ) :
    intrinsicTimeReversalSign X = 1 ∨ intrinsicTimeReversalSign X = -1 := by
  obtain ⟨E, _, R, hR, _, hMpo⟩ := hX.exists_reduced_cfii_representative
  have hEq : ∀ N : ℕ, 0 < N → mpo X N = mpo R N := fun N hN ↦ (hMpo N hN).symm
  have hTRR : ∀ N : ℕ, 1 < N → Even N → mpo R N = (mpo R N)ᴴ := by
    intro N hN heven
    rw [← hEq N (by omega)]
    exact hTR N hN heven
  obtain ⟨η, C, hη, hfirst, hblock⟩ := hR.exists_intrinsic_blocking_phase_formula hTRR
  -- The blocking by `D⁴` sites is simple, so the trace at blocking `2 D⁴` is a sign.
  have hk : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
  have hS := hX.blockTensor_pow_four_isMPUSimple
  have hTRb : ∀ N : ℕ, 1 < N → Even N →
      mpo (blockTwo (MPOTensor.blockTensor X (D ^ 4))) N =
        (mpo (blockTwo (MPOTensor.blockTensor X (D ^ 4))) N)ᴴ := by
    intro N hN _
    refine mpo_blockTwo_selfAdjoint (mpo_blockTensor_selfAdjoint (hTR _ ?_ ?_))
    · nlinarith
    · exact ⟨N * D ^ 4, by ring⟩
  have : NeZero (MPSTensor.blockPhysDim d (D ^ 4)) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (NeZero.ne d)⟩
  have hsign := hS.intrinsicTimeReversalSign_blockTwo_eq_one_or_neg_one hTRb
  rw [← intrinsicTimeReversalSign_reindexPhysical (twoSiteDirectBlockEquiv d (D ^ 4)),
    reindexPhysical_blockTwo_blockTensor_two_mul,
    intrinsicTimeReversalSign_blockTensor_eq_of_mpo_eq hEq _ (by omega),
    hblock _ (by omega), pow_mul] at hsign
  have hη2 : η ^ 2 = 1 := by rcases hη with h | h <;> simp [h]
  rw [hη2, one_pow, one_mul] at hsign
  rw [intrinsicTimeReversalSign_eq_of_mpo_two_eq (hEq 2 (by omega)), hfirst]
  rcases hη with h | h <;> rcases hsign with h' | h' <;> simp [h, h']

/-- **Constancy of the intrinsic sign along a path.** Along a path of MPUs whose periodic
operators are self-adjoint on every ring of even length, the intrinsic time-reversal sign is
constant. The path tensors need not be simple or canonical.

Source: arXiv:1703.09188, Proposition `prop:sigma-well-defined`, lines 1616--1631. -/
theorem intrinsicTimeReversalSign_eq_of_joinedIn [NeZero d] [NeZero D]
    {s : Set (MPOTensor d D)}
    (hs : ∀ W ∈ s, IsMPU W ∧ ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ)
    {X Y : MPOTensor d D} (h : JoinedIn s X Y) :
    intrinsicTimeReversalSign X = intrinsicTimeReversalSign Y := by
  have hmem := h.somePath_mem
  have hcont : Continuous fun t ↦ intrinsicTimeReversalSign (h.somePath t) :=
    continuous_intrinsicTimeReversalSign.comp h.somePath.continuous
  have hsq : Set.EqOn ((fun t ↦ intrinsicTimeReversalSign (h.somePath t)) ^ 2) 1
      Set.univ := by
    intro t _
    obtain ⟨hW, hTR⟩ := hs _ (hmem t)
    rcases hW.intrinsicTimeReversalSign_eq_one_or_neg_one hTR with h' | h' <;>
      simp [h']
  rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hcont.continuousOn hsq with h' | h'
  · simpa using (h' (Set.mem_univ 0)).trans (h' (Set.mem_univ 1)).symm
  · simpa using (h' (Set.mem_univ 0)).trans (h' (Set.mem_univ 1)).symm

/-- The two-site block of an MPU generates matrix product unitaries.

Source: arXiv:1703.09188, physical blocking, lines 297--304. -/
theorem IsMPU.blockTwo {X : MPOTensor d D} (hX : IsMPU X) : IsMPU (blockTwo X) := by
  rw [blockTwo_eq_blockTensor_reindex]
  exact (hX.blockTensor 2 (by norm_num)).reindexPhysical (twoSiteBlockEquiv d)

/-- **Strict equivalence under time reversal fixes both intrinsic signs.** If `U` and `V` are
strictly equivalent under a symmetry that imposes self-adjointness on every ring whose length is a
positive multiple of four, the intrinsic signs of their two-site blocks agree, and so do those of
the two-site blocks of their blockings by two. The physical dimensions are equal but need not be
equal by definition.

Source: arXiv:1703.09188, corollary after Proposition `prop:sigma1-and-sigma2-equal`, lines
1735--1740, with Definition `def:strictly-equivalent-symmetry`, lines 1345--1354. -/
theorem StrictlyEquivalentUnderSymmetry.intrinsicTimeReversalSign_eq {da db Da Db : ℕ}
    [NeZero db] [NeZero Da] {S : FiniteChainOperatorSymmetry db}
    (hS : ∀ N : ℕ, 0 < N → 4 ∣ N → N ∈ S.applicable ∧
      ∀ X : Matrix (Fin N → Fin db) (Fin N → Fin db) ℂ, S.action X = X → X = Xᴴ)
    {U : MPOTensor da Da} {V : MPOTensor db Db} {hphys : da = db}
    (h : StrictlyEquivalentUnderSymmetry S U V hphys) :
    intrinsicTimeReversalSign (MPOTensor.blockTwo U) =
        intrinsicTimeReversalSign (MPOTensor.blockTwo V) ∧
      intrinsicTimeReversalSign (MPOTensor.blockTwo (MPOTensor.blockTensor U 2)) =
        intrinsicTimeReversalSign (MPOTensor.blockTwo (MPOTensor.blockTensor V 2)) := by
  subst hphys
  obtain ⟨-, -, D', ha, hb, hpath⟩ := h
  have : NeZero D' := ⟨by have := NeZero.pos Da; omega⟩
  have : NeZero (da * da) := ⟨mul_ne_zero (NeZero.ne da) (NeZero.ne da)⟩
  have : NeZero (MPSTensor.blockPhysDim da 2 * MPSTensor.blockPhysDim da 2) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne da)) (pow_ne_zero _ (NeZero.ne da))⟩
  set s := {W : MPOTensor da D' | IsMPU W ∧ IsInvariantUnderSymmetry S W}
  have hTRs : ∀ W ∈ s, ∀ N : ℕ, 0 < N → 4 ∣ N → mpo W N = (mpo W N)ᴴ := by
    intro W hW N hN h4
    obtain ⟨happ, hsa⟩ := hS N hN h4
    exact hsa _ (hW.2 happ)
  have hX : reindexPhysical (finCongr (rfl : da = da)).symm (padBond U D' ha) =
      padBond U D' ha := rfl
  rw [hX] at hpath
  have hpad : ∀ {E : ℕ} (W : MPOTensor da E) (hE : E ≤ D') (N : ℕ), 0 < N →
      mpo (padBond W D' hE) N = mpo W N := by
    intro E W hE N hN
    have : NeZero N := ⟨hN.ne'⟩
    exact mpo_padBond W hE N
  have hpad₂ : ∀ {E : ℕ} (W : MPOTensor da E) (hE : E ≤ D') (N : ℕ), 0 < N →
      mpo (MPOTensor.blockTensor (padBond W D' hE) 2) N =
        mpo (MPOTensor.blockTensor W 2) N := by
    intro E W hE N hN
    rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex, hpad W hE _ (by omega)]
  constructor
  · have hj := hpath.map (continuous_blockTwo (d := da) (D := D')).continuousOn
    have hconst := intrinsicTimeReversalSign_eq_of_joinedIn ?_ hj
    · rw [← intrinsicTimeReversalSign_eq_of_mpo_two_eq
          (mpo_blockTwo_eq_of_mpo_eq (hpad U ha) 2 (by norm_num)), hconst,
        intrinsicTimeReversalSign_eq_of_mpo_two_eq
          (mpo_blockTwo_eq_of_mpo_eq (hpad V hb) 2 (by norm_num))]
    · rintro _ ⟨W, hW, rfl⟩
      refine ⟨hW.1.blockTwo, fun N hN heven ↦ mpo_blockTwo_selfAdjoint (hTRs W hW _ ?_ ?_)⟩
      · omega
      · obtain ⟨m, rfl⟩ := heven
        exact ⟨m, by ring⟩
  · have hj := hpath.map ((continuous_blockTwo (d := MPSTensor.blockPhysDim da 2)
      (D := D')).comp (continuous_blockTensor (d := da) (D := D') 2)).continuousOn
    have hconst := intrinsicTimeReversalSign_eq_of_joinedIn ?_ hj
    · rw [← intrinsicTimeReversalSign_eq_of_mpo_two_eq
          (mpo_blockTwo_eq_of_mpo_eq (hpad₂ U ha) 2 (by norm_num))]
      exact hconst.trans (intrinsicTimeReversalSign_eq_of_mpo_two_eq
        (mpo_blockTwo_eq_of_mpo_eq (hpad₂ V hb) 2 (by norm_num)))
    · rintro _ ⟨W, hW, rfl⟩
      refine ⟨(hW.1.blockTensor 2 (by norm_num)).blockTwo, fun N hN heven ↦
        mpo_blockTwo_selfAdjoint (mpo_blockTensor_selfAdjoint (hTRs W hW _ ?_ ?_))⟩
      · omega
      · exact ⟨N, by ring⟩

/-- **The time-reversal signs are invariants of strict equivalence.** Let `𝒰₁ = V₁` and
`𝒰₂ = V₂` be MPUs in standard form, with standard-form gates `u₁, v₁` and `u₂, v₂` of their
two-site blocks and `a₁, b₁` and `a₂, b₂` of the two-site blocks of their blockings by two
sites, so that `σ⁽¹⁾(𝒰ᵢ) = s(uᵢ, vᵢ)` and `σ⁽²⁾(𝒰ᵢ) = s(aᵢ, bᵢ)`. If `𝒰₁` and `𝒰₂` are
strictly equivalent under a symmetry `S` that imposes time reversal, then
`σ⁽¹⁾(𝒰₁) = σ⁽¹⁾(𝒰₂)` and `σ⁽²⁾(𝒰₁) = σ⁽²⁾(𝒰₂)`.

The hypothesis `hS` says that `S` acts on rings whose length is a positive multiple of four and
that its invariant operators there are self-adjoint: the time reversal of `PropChiral` on rings of
an even number of standard-form sites (`docs/paper-gaps/mpu_standard_form_parity_gap.tex`).
`daggerSymmetry` satisfies it. The connecting path consists of MPUs that need not be simple or
canonical, as in Definition `def:strictly-equivalent-symmetry`.

Source: arXiv:1703.09188, corollary after Proposition `prop:sigma1-and-sigma2-equal`,
lines 1735--1740 (first sentence), with Definition `def:strictly-equivalent-symmetry`,
lines 1345--1354. -/
theorem StrictlyEquivalentUnderSymmetry.timeReversalSign_eq {D₁ D₂ : ℕ}
    {S : FiniteChainOperatorSymmetry d}
    (hS : ∀ N : ℕ, 0 < N → 4 ∣ N → N ∈ S.applicable ∧
      ∀ X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ, S.action X = X → X = Xᴴ)
    {V₁ : MPOTensor d D₁} {V₂ : MPOTensor d D₂}
    (h : StrictlyEquivalentUnderSymmetry S V₁ V₂ rfl)
    {u₁ v₁ u₂ v₂ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S₁ : TwoSiteStandardFormData (MPOTensor.blockTwo V₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (MPOTensor.blockTwo V₂) u₂ v₂)
    {a₁ b₁ a₂ b₂ : Matrix (Fin (MPSTensor.blockPhysDim d 2) × Fin (MPSTensor.blockPhysDim d 2))
      (Fin (MPSTensor.blockPhysDim d 2) × Fin (MPSTensor.blockPhysDim d 2)) ℂ}
    (T₁ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₁ 2)) a₁ b₁)
    (T₂ : TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V₂ 2)) a₂ b₂) :
    timeReversalSign u₁ v₁ = timeReversalSign u₂ v₂ ∧
      timeReversalSign a₁ b₁ = timeReversalSign a₂ b₂ := by
  have : NeZero d := ⟨S₁.phys_pos.ne'⟩
  have : NeZero D₁ := ⟨S₁.bond_pos.ne'⟩
  obtain ⟨h₁, h₂⟩ := h.intrinsicTimeReversalSign_eq hS
  exact ⟨by rw [S₁.timeReversalSign_eq_intrinsic, S₂.timeReversalSign_eq_intrinsic, h₁],
    by rw [T₁.timeReversalSign_eq_intrinsic, T₂.timeReversalSign_eq_intrinsic, h₂]⟩

end MPOTensor
