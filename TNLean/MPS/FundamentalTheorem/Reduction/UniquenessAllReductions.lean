/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis

/-!
# Unipotent changes of two reductions, and the set of all reductions

Let `P = (σ, g)` and `Q = (σ_tilde, g_tilde)` be two reductions of the same tensor `B` onto two
families of normal blocks of positive bond dimension, with the factorization
`g_tilde g⁻¹ = 𝔄_tilde P_X 𝔄⁻¹` of *A basis adapted to both flags*
(`MPSTensor.MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq`). Replacing them by unipotent
changes `(σ, u g)` and `(σ_tilde, u_tilde g_tilde)`, with `u` and `u_tilde` block upper triangular
with identity diagonal blocks in the two orders, keeps the flags, the complements `L_k`, the
coordinates `Γ` and the factor `P_X`, and multiplies the unipotent factors, `𝔄 ↦ u 𝔄` and
`𝔄_tilde ↦ u_tilde 𝔄_tilde`; every pair of unipotent factors occurs in this way.

The set of all compressions (blueprint `thm:asym_uniq_all`, *The set of all compressions*) is
indexed by the labelled flags, and over the flag of `P` lies the orbit of `P` under the group `T_σ`
of block upper triangular matrices with nonzero scalar diagonal blocks. A tensor has a reduction
onto a family with `z` zero slots exactly when its word module has a labelled invariant flag with
`z` zero steps, and the reductions are the disjoint union over labelled flags of these orbits.

## Main results

* `MPSTensor.MultiBlockCompression.flag_conjTriangular_and_unipotentFactor_conjTriangular`,
  `MPSTensor.MultiBlockCompression.exists_conjTriangular_unipotentFactor_eq`: unipotent changes
  `(σ, u g)`, `(σ_tilde, u_tilde g_tilde)` keep the complements, `Γ` and `P_X` and multiply the
  factors, and every pair of unipotent factors occurs (*The asymmetric fundamental theorem of matrix
  product states*, Theorem 6.5, last sentence).
* `MPSTensor.MultiBlockCompression.flag_withGauge_eq_iff_exists_eq_conjTriangularGauge`,
  `MPSTensor.FlagData.exists_multiBlockCompression_flag_eq`: the set of all compressions (blueprint
  `thm:asym_uniq_all`, *The set of all compressions*).
* `MPSTensor.MultiBlockCompression.exists_z_eq_iff_exists_flagData`,
  `MPSTensor.MultiBlockCompression.existsUnique_conjTriangular`: which families admit a reduction,
  and the set of all reductions as the union over labelled flags of the `T_σ`-orbits (*The
  asymmetric fundamental theorem of matrix product states*, Theorem 6.6).
* `MPSTensor.FlagData.toMultiBlockCompression_toFlagData`,
  `MPSTensor.FlagData.exists_rightInverse_toFlagData`: the compression of a labelled flag has that
  labelled flag, so a choice of one reduction for each labelled flag, as
  `existsUnique_conjTriangular` assumes, exists.

## References

Blueprint `thm:asym_uniq_unipotent_change`, *Unipotent changes of two compressions*,
`thm:asym_uniq_all`, *The set of all compressions*, and `thm:asym_uniq_all_reductions`, *The set of
all reductions*; *The asymmetric fundamental theorem of matrix product states*, Theorem 6.5 (last
sentence) and Theorem 6.6.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}

namespace MultiBlockCompression

variable {d DB : ℕ} {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-! ### Unipotent changes of the two reductions -/

section UnipotentChange

/-! `(σ, h g)` has the number of zero slots and the order of `(σ, g)` only after unfolding
`conjTriangular`, so the proofs below compare the two reductions through statements typed with
`P.z`, glued by `exact` rather than by rewriting. -/

/-- **The reading maps of `(σ, h g)`** (*The asymmetric fundamental theorem of matrix product
states*, proof of the last sentence of Theorem 6.5): the row of `h g` at the slot `b` is
`∑_c h_{bc} W_c`. -/
theorem leftRow_conjTriangular (P : MultiBlockCompression B S C)
    {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1) (b : BlockIndex S P.z) :
    (P.conjTriangular ht hμ hdiag).leftRow b =
      ∑ c, h.submatrix (Sigma.mk b) (Sigma.mk c) * P.leftRow c := by
  change Matrix.blockProj (slotSize D) b * gaugeMatrix (P.conjTriangularGauge ht hμ hdiag) = _
  rw [gaugeMatrix_conjTriangularGauge, ← Matrix.mul_assoc,
    Matrix.blockProj_mul_eq_sum_submatrix_mul_blockProj, Matrix.sum_mul]
  simp only [Matrix.mul_assoc]
  rfl

/-- **On the step of its slot the reading map of `(σ, h g)` is `μ_b W_b`** (*The asymmetric
fundamental theorem of matrix product states*, proof of the last sentence of Theorem 6.5): the added
rows `h_{bc} W_c`, `c` after `b`, vanish on `M_k`, `k` the position of `b`. -/
theorem leftRow_conjTriangular_mulVec_of_mem (P : MultiBlockCompression B S C)
    {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1) {b : BlockIndex S P.z} {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).succ) :
    (P.conjTriangular ht hμ hdiag).leftRow b *ᵥ WordModule.toVec B x =
      μ b • (P.leftRow b *ᵥ WordModule.toVec B x) := by
  have key : (∑ c, h.submatrix (Sigma.mk b) (Sigma.mk c) * P.leftRow c) *ᵥ
      WordModule.toVec B x = μ b • (P.leftRow b *ᵥ WordModule.toVec B x) := by
    rw [Matrix.sum_mulVec, Finset.sum_eq_single b]
    · rw [show h.submatrix (Sigma.mk b) (Sigma.mk b) = h.blockDiag' b from rfl, hdiag,
        Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]
    · intro c _ hcb
      rcases lt_or_gt_of_ne (fun e => hcb (P.ord.injective e)) with hlt | hlt
      · have h0 : h.submatrix (Sigma.mk b) (Sigma.mk c) = 0 := by
          ext j j'
          exact ht (i := ⟨b, j⟩) (j := ⟨c, j'⟩) hlt
        rw [h0, Matrix.zero_mul, Matrix.zero_mulVec]
      · rw [← Matrix.mulVec_mulVec, P.leftRow_mulVec_eq_zero_of_mem
          (P.flag_mono (Fin.succ_le_castSucc_iff.2 hlt) hx), Matrix.mulVec_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  exact (congrArg (· *ᵥ WordModule.toVec B x) (P.leftRow_conjTriangular ht hμ hdiag b)).trans key

/-- The flag of `(σ, h g)` is the flag of `(σ, g)` read as a covering chain. -/
theorem coveringChain_conjTriangular (P : MultiBlockCompression B S C)
    {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) :
    (P.conjTriangular ht hμ hdiag).coveringChain hC hD = P.coveringChain hC hD := by
  have hflag : (P.conjTriangular ht hμ hdiag).flag = P.flag :=
    funext (P.conjTriangular_flag ht hμ hdiag)
  unfold coveringChain
  congr 1

variable {κ : Type*} [DecidableEq κ] {D' : κ → ℕ} {S' : Finset κ}
  {C' : ∀ t, MPSTensor d (D' t)}
  (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
  (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)
  {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
  (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
  (hdiag : ∀ b, h.blockDiag' b = μ b • 1)
  {h' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
  (ht' : h'.BlockTriangular fun x => Q.ord x.1) {μ' : BlockIndex S' Q.z → ℂ}
  (hμ' : ∀ b, μ' b ≠ 0) (hdiag' : ∀ b, h'.blockDiag' b = μ' b • 1)
  {u : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
  (hu : u.BlockTriangular fun x => P.ord x.1) (hu1 : ∀ b, u.blockDiag' b = (1 : ℂ) • 1)
  {u' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
  (hu' : u'.BlockTriangular fun x => Q.ord x.1) (hu1' : ∀ b, u'.blockDiag' b = (1 : ℂ) • 1)

/-- **The matching depends only on the two flags** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 6.5, last sentence): `(σ, h g)` and `(σ_tilde, h_tilde g_tilde)` have the
matching of `(σ, g)` and `(σ_tilde, g_tilde)`. -/
theorem matching_conjTriangular :
    (P.conjTriangular ht hμ hdiag).matching (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' =
      P.matching Q hC hD hC' hD' := by
  unfold matching
  rw [coveringChain_conjTriangular, coveringChain_conjTriangular]
  rfl

theorem matching_conjTriangular_apply (k : Fin (S.card + P.z)) :
    (P.conjTriangular ht hμ hdiag).matching (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' k =
      P.matching Q hC hD hC' hD' k :=
  congrArg (fun e : Fin (S.card + P.z) ≃ Fin (S'.card + Q.z) => e k)
    (P.matching_conjTriangular Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag')

theorem matchedInter_conjTriangular (k : Fin (S.card + P.z)) :
    (P.conjTriangular ht hμ hdiag).matchedInter (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' k =
      P.matchedInter Q hC hD hC' hD' k := by
  unfold matchedInter
  congr 1
  · exact P.conjTriangular_flag ht hμ hdiag _
  · exact (Q.conjTriangular_flag ht' hμ' hdiag' _).trans (congrArg (fun j : Fin (S'.card + Q.z) =>
      Q.flag j.succ) (P.matching_conjTriangular_apply Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag' k))

theorem matchedKer_conjTriangular (k : Fin (S.card + P.z)) :
    (P.conjTriangular ht hμ hdiag).matchedKer (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' k =
      P.matchedKer Q hC hD hC' hD' k := by
  unfold matchedKer
  congr 1
  · exact P.conjTriangular_flag ht hμ hdiag _
  · exact (Q.conjTriangular_flag ht' hμ' hdiag' _).trans (congrArg (fun j : Fin (S'.card + Q.z) =>
      Q.flag j.succ) (P.matching_conjTriangular_apply Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag' k))

/-- **The same complements** (*The asymmetric fundamental theorem of matrix product states*, Theorem
6.5, last sentence): `(σ, h g)` and `(σ_tilde, h_tilde g_tilde)` have the complements `L_k` of
`(σ, g)` and `(σ_tilde, g_tilde)`, since these depend only on the two flags (`matchedCompl_congr`).
-/
theorem matchedCompl_conjTriangular (k : Fin (S.card + P.z)) :
    (P.conjTriangular ht hμ hdiag).matchedCompl (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' k =
      P.matchedCompl Q hC hD hC' hD' k :=
  matchedCompl_congr hC hD hC' hD'
    (P.matchedKer_conjTriangular Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag' k)
    (P.matchedInter_conjTriangular Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag' k)

/-- **The same `Γ`** (*The asymmetric fundamental theorem of matrix product states*, proof of the
last sentence of Theorem 6.5): for `u` unipotent in the order of `P`, the reading of `u g` on
`L_j ⊆ M_j` is that of `g`, so `(σ, u g)` and `(σ_tilde, h_tilde g_tilde)` have the change of basis
`Γ` of `(σ, g)` and `(σ_tilde, g_tilde)`. -/
theorem commonCoord_conjTriangular :
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).commonCoord
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' =
      P.commonCoord Q hC hD hC' hD' := by
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ ⨆ j, P.matchedCompl Q hC hD hC' hD' j := by
    rw [P.iSup_matchedCompl Q hC hD hC' hD']
    exact Submodule.mem_top
  refine Submodule.iSup_induction (P.matchedCompl Q hC hD hC' hD')
    (motive := fun x =>
      (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).commonCoord
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' x = P.commonCoord Q hC hD hC' hD' x) hx
    (fun j y hy => ?_) ?_ (fun y y' hy hy' => ?_)
  · obtain ⟨b, rfl⟩ := P.ord.surjective j
    have hy₂ : y ∈ (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).matchedCompl
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' (P.ord b) :=
      (congrArg (y ∈ ·) (P.matchedCompl_conjTriangular Q hC hD hC' hD' hu (fun _ => one_ne_zero) hu1
        ht' hμ' hdiag' (P.ord b))).mpr hy
    have hyU : y ∈ P.matchedInter Q hC hD hC' hD' (P.ord b) :=
      P.matchedCompl_le Q hC hD hC' hD' _ hy
    have e1 := commonCoord_of_mem _ _ _ _ _ _ hy₂
    have e2 := P.commonCoord_of_mem Q hC hD hC' hD' hy
    have e3 := P.leftRow_conjTriangular_mulVec_of_mem hu (fun _ => one_ne_zero) hu1
      (Submodule.mem_inf.1 hyU).1
    simp only [one_smul] at e3
    exact e1.trans ((congrArg (Matrix.blockEmbed (slotSize D) b *ᵥ ·) e3).trans e2.symm)
  · exact (map_zero _).trans (map_zero _).symm
  · exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hy hy').trans (map_add _ _ _).symm)

/-- The coordinates `P_X Γ` of a vector of `L_j` read by the slot at the matched position. -/
theorem commonCoord'_of_mem_of_matching_eq {j : Fin (S.card + P.z)} {b' : BlockIndex S' Q.z}
    (hj : P.matching Q hC hD hC' hD' j = Q.ord b') {x : B.WordModule}
    (hx : x ∈ P.matchedCompl Q hC hD hC' hD' j) :
    P.commonCoord' Q hC hD hC' hD' x =
      Matrix.blockEmbed (slotSize D') b' *ᵥ (Q.leftRow b' *ᵥ WordModule.toVec B x) := by
  have h : (P.matching Q hC hD hC' hD').symm (Q.ord b') = j := by
    rw [← hj, Equiv.symm_apply_apply]
  rw [← h] at hx
  exact P.commonCoord'_of_mem Q hC hD hC' hD' hx

/-- **The same `P_X Γ`** (*The asymmetric fundamental theorem of matrix product states*, proof of
the last sentence of Theorem 6.5): for `u_tilde` unipotent in the order of `Q`, the reading of
`u_tilde g_tilde` on `L_j ⊆ M_tilde_{π(j)}` is that of `g_tilde`. -/
theorem commonCoord'_conjTriangular :
    (P.conjTriangular ht hμ hdiag).commonCoord'
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      P.commonCoord' Q hC hD hC' hD' := by
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ ⨆ j, P.matchedCompl Q hC hD hC' hD' j := by
    rw [P.iSup_matchedCompl Q hC hD hC' hD']
    exact Submodule.mem_top
  refine Submodule.iSup_induction (P.matchedCompl Q hC hD hC' hD')
    (motive := fun x => (P.conjTriangular ht hμ hdiag).commonCoord'
      (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' x =
        P.commonCoord' Q hC hD hC' hD' x) hx
    (fun j y hy => ?_) ?_ (fun y y' hy hy' => ?_)
  · obtain ⟨b', hb'⟩ := Q.ord.surjective (P.matching Q hC hD hC' hD' j)
    have hy₂ : y ∈ (P.conjTriangular ht hμ hdiag).matchedCompl
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' j :=
      (congrArg (y ∈ ·) (P.matchedCompl_conjTriangular Q hC hD hC' hD' ht hμ hdiag hu'
        (fun _ => one_ne_zero) hu1' j)).mpr hy
    have hj₂ : (P.conjTriangular ht hμ hdiag).matching
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' j =
          Q.ord b' :=
      (P.matching_conjTriangular_apply Q hC hD hC' hD' ht hμ hdiag hu' (fun _ => one_ne_zero) hu1'
        j).trans hb'.symm
    have hyU : y ∈ P.matchedInter Q hC hD hC' hD' j := P.matchedCompl_le Q hC hD hC' hD' _ hy
    have hyQ : y ∈ Q.flag (Q.ord b').succ := by
      rw [hb']
      exact (Submodule.mem_inf.1 hyU).2
    have e1 := commonCoord'_of_mem_of_matching_eq _ _ _ _ _ _ hj₂ hy₂
    have e2 := P.commonCoord'_of_mem_of_matching_eq Q hC hD hC' hD' hb'.symm hy
    have e3 := Q.leftRow_conjTriangular_mulVec_of_mem hu' (fun _ => one_ne_zero) hu1' hyQ
    simp only [one_smul] at e3
    exact e1.trans ((congrArg (Matrix.blockEmbed (slotSize D') b' *ᵥ ·) e3).trans e2.symm)
  · exact (map_zero _).trans (map_zero _).symm
  · exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hy hy').trans (map_add _ _ _).symm)

theorem commonGauge_conjTriangular :
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).commonGauge
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' =
      P.commonGauge Q hC hD hC' hD' :=
  congrArg (fun Γ : B.WordModule ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) =>
    (WordModule.toVec B).symm.trans Γ)
    (P.commonCoord_conjTriangular Q hC hD hC' hD' ht' hμ' hdiag' hu hu1)

theorem commonGauge'_conjTriangular :
    (P.conjTriangular ht hμ hdiag).commonGauge'
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      P.commonGauge' Q hC hD hC' hD' :=
  congrArg (fun Γ : B.WordModule ≃ₗ[ℂ] (BlockSpace D' S' Q.z → ℂ) =>
    (WordModule.toVec B).symm.trans Γ)
    (P.commonCoord'_conjTriangular Q hC hD hC' hD' ht hμ hdiag hu' hu1')

/-- **The first unipotent factor of `(σ, u g)`** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 6.5, last sentence): `u 𝔄`, since `u g = (u 𝔄) Γ` with the same `Γ`. -/
theorem unipotentFactor_conjTriangular :
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).unipotentFactor
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' =
      u * P.unipotentFactor Q hC hD hC' hD' := by
  have key : gaugeMatrix (P.conjTriangularGauge hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1) *
      gaugeMatrixInv (P.commonGauge Q hC hD hC' hD') = u * P.unipotentFactor Q hC hD hC' hD' := by
    rw [gaugeMatrix_conjTriangularGauge, Matrix.mul_assoc]
    rfl
  exact (congrArg (fun Γ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) =>
    gaugeMatrix (P.conjTriangularGauge hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1) *
      gaugeMatrixInv Γ)
    (P.commonGauge_conjTriangular Q hC hD hC' hD' ht' hμ' hdiag' hu hu1)).trans key

/-- **The second unipotent factor of `(σ_tilde, u_tilde g_tilde)`** (*The asymmetric fundamental
theorem of matrix product states*, Theorem 6.5, last sentence): `u_tilde 𝔄_tilde`, since
`u_tilde g_tilde = (u_tilde 𝔄_tilde) P_X Γ` with the same `P_X Γ`. -/
theorem unipotentFactor'_conjTriangular :
    (P.conjTriangular ht hμ hdiag).unipotentFactor'
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      u' * P.unipotentFactor' Q hC hD hC' hD' := by
  have key : gaugeMatrix (Q.conjTriangularGauge hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') *
      gaugeMatrixInv (P.commonGauge' Q hC hD hC' hD') =
        u' * P.unipotentFactor' Q hC hD hC' hD' := by
    rw [gaugeMatrix_conjTriangularGauge, Matrix.mul_assoc]
    rfl
  exact (congrArg (fun Γ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D' S' Q.z → ℂ) =>
    gaugeMatrix (Q.conjTriangularGauge hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') *
      gaugeMatrixInv Γ)
    (P.commonGauge'_conjTriangular Q hC hD hC' hD' ht hμ hdiag hu' hu1')).trans key

/-- **The same block permutation matrix** (*The asymmetric fundamental theorem of matrix product
states*, Theorem 6.5, last sentence): `(σ, u g)` and `(σ_tilde, u_tilde g_tilde)` have the `P_X` of
`(σ, g)` and `(σ_tilde, g_tilde)`. -/
theorem matchingPermMatrix_conjTriangular :
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).matchingPermMatrix
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      P.matchingPermMatrix Q hC hD hC' hD' :=
  ((P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).matchingPermMatrix_eq_mul
    (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD').trans
    ((congrArg₂ (fun (Γ₁ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
        (Γ₂ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D' S' Q.z → ℂ)) => gaugeMatrix Γ₂ * gaugeMatrixInv Γ₁)
      (P.commonGauge_conjTriangular Q hC hD hC' hD' hu' (fun _ => one_ne_zero) hu1' hu hu1)
      (P.commonGauge'_conjTriangular Q hC hD hC' hD' hu (fun _ => one_ne_zero) hu1 hu' hu1')).trans
      (P.matchingPermMatrix_eq_mul Q hC hD hC' hD').symm)

/-- **Unipotent changes** (*The asymmetric fundamental theorem of matrix product states*, Theorem
6.5, last sentence, first part): for `u` unipotent in the order of `P` and `u_tilde` unipotent in
the order of `Q`, the reductions `(σ, u g)` and `(σ_tilde, u_tilde g_tilde)` have the flags of
`(σ, g)` and `(σ_tilde, g_tilde)`, the factors `u 𝔄` and `u_tilde 𝔄_tilde`, and the same `P_X`. The
complements `L_k`, the change of basis `Γ` and the intertwiners entering `P_X` are the same as well
(`matchedCompl_conjTriangular`, `commonGauge_conjTriangular`). -/
theorem flag_conjTriangular_and_unipotentFactor_conjTriangular :
    (∀ k, (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).flag k = P.flag k) ∧
    (∀ k', (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1').flag k' =
      Q.flag k') ∧
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).unipotentFactor
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      u * P.unipotentFactor Q hC hD hC' hD' ∧
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).unipotentFactor'
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      u' * P.unipotentFactor' Q hC hD hC' hD' ∧
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).matchingPermMatrix
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      P.matchingPermMatrix Q hC hD hC' hD' :=
  ⟨P.conjTriangular_flag _ _ _, Q.conjTriangular_flag _ _ _,
    P.unipotentFactor_conjTriangular Q hC hD hC' hD' _ _ _ hu hu1,
    P.unipotentFactor'_conjTriangular Q hC hD hC' hD' _ _ _ hu' hu1',
    P.matchingPermMatrix_conjTriangular Q hC hD hC' hD' hu hu1 hu' hu1'⟩

/-- The inverse of a matrix unipotent in the order of `P` is unipotent in that order. -/
theorem blockTriangular_inv_and_blockDiag'_inv_of_unipotent
    {A : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (hA : A.BlockTriangular fun x => P.ord x.1) (hA1 : ∀ b, A.blockDiag' b = 1) :
    A⁻¹.BlockTriangular (fun x => P.ord x.1) ∧ (∀ b, A⁻¹.blockDiag' b = 1) ∧ A⁻¹ * A = 1 := by
  have hA1' : ∀ b, A.blockDiag' b = (1 : ℂ) • 1 := fun b => by
    rw [hA1, one_smul]
  refine ⟨P.blockTriangular_inv_of_blockDiag'_eq_smul hA (fun _ => one_ne_zero) hA1',
    fun b => ?_, Matrix.nonsing_inv_mul A
      (P.isUnit_det_of_blockDiag'_eq_smul hA (fun _ => one_ne_zero) hA1')⟩
  rw [P.blockDiag'_inv_of_blockDiag'_eq_smul hA (fun _ => one_ne_zero) hA1' b, inv_one, one_smul]

/-- **Every pair of unipotent factors occurs** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 6.5, last sentence, second part): for every `𝔄₁` unipotent in the order of
`P` and every `𝔄₂` unipotent in the order of `Q` there are unipotent `u`, `u_tilde` such that
`(σ, u g)` and `(σ_tilde, u_tilde g_tilde)`, reductions with the flags of `(σ, g)` and
`(σ_tilde, g_tilde)`, have the factors `𝔄₁` and `𝔄₂` and the same `P_X`; take `u = 𝔄₁ 𝔄⁻¹` and
`u_tilde = 𝔄₂ 𝔄_tilde⁻¹`. -/
theorem exists_conjTriangular_unipotentFactor_eq
    (A₁ : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
    (hA₁ : A₁.BlockTriangular fun x => P.ord x.1) (hA₁' : ∀ b, A₁.blockDiag' b = 1)
    (A₂ : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ)
    (hA₂ : A₂.BlockTriangular fun x => Q.ord x.1) (hA₂' : ∀ b, A₂.blockDiag' b = 1) :
    ∃ (u : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
      (hu : u.BlockTriangular fun x => P.ord x.1) (hu1 : ∀ b, u.blockDiag' b = (1 : ℂ) • 1)
      (u' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ)
      (hu' : u'.BlockTriangular fun x => Q.ord x.1) (hu1' : ∀ b, u'.blockDiag' b = (1 : ℂ) • 1),
      (∀ k, (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).flag k = P.flag k) ∧
      (∀ k', (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1').flag k' =
        Q.flag k') ∧
      (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).unipotentFactor
          (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' = A₁ ∧
      (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).unipotentFactor'
          (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' = A₂ ∧
      (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).matchingPermMatrix
          (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
        P.matchingPermMatrix Q hC hD hC' hD' := by
  obtain ⟨hi, hi1, hinv⟩ := P.blockTriangular_inv_and_blockDiag'_inv_of_unipotent
    (P.blockTriangular_unipotentFactor Q hC hD hC' hD')
    (P.blockDiag'_unipotentFactor Q hC hD hC' hD')
  obtain ⟨hi', hi1', hinv'⟩ := Q.blockTriangular_inv_and_blockDiag'_inv_of_unipotent
    (P.blockTriangular_unipotentFactor' Q hC hD hC' hD')
    (P.blockDiag'_unipotentFactor' Q hC hD hC' hD')
  have hu : (A₁ * (P.unipotentFactor Q hC hD hC' hD')⁻¹).BlockTriangular fun x => P.ord x.1 :=
    hA₁.mul hi
  have hu1 : ∀ b, (A₁ * (P.unipotentFactor Q hC hD hC' hD')⁻¹).blockDiag' b = (1 : ℂ) • 1 :=
    fun b => by
      rw [Matrix.blockDiag'_mul_of_blockTriangular P.ord.injective hA₁ hi, hA₁', hi1,
        Matrix.one_mul, one_smul]
  have hu' : (A₂ * (P.unipotentFactor' Q hC hD hC' hD')⁻¹).BlockTriangular fun x => Q.ord x.1 :=
    hA₂.mul hi'
  have hu1' : ∀ b, (A₂ * (P.unipotentFactor' Q hC hD hC' hD')⁻¹).blockDiag' b = (1 : ℂ) • 1 :=
    fun b => by
      rw [Matrix.blockDiag'_mul_of_blockTriangular Q.ord.injective hA₂ hi', hA₂', hi1',
        Matrix.one_mul, one_smul]
  obtain ⟨hf, hf', h1, h2, h3⟩ :=
    P.flag_conjTriangular_and_unipotentFactor_conjTriangular Q hC hD hC' hD' hu hu1 hu' hu1'
  refine ⟨_, hu, hu1, _, hu', hu1', hf, hf', ?_, ?_, h3⟩
  · rw [h1, Matrix.mul_assoc, hinv, Matrix.mul_one]
  · rw [h2, Matrix.mul_assoc, hinv', Matrix.mul_one]

end UnipotentChange

/-! ### The set of all reductions -/

section FlagFiber

variable {P : MultiBlockCompression B S C}

/-- **The fiber over a flag** (blueprint `thm:asym_uniq_all`, *The set of all compressions*): a
reduction `(σ, g)` with the slots and order of `P` has the flag of `P` exactly when `g = h g_P` for
some `h ∈ T_σ`, a block upper triangular matrix with nonzero scalar diagonal blocks. So the
reductions with a given labelled flag form one `T_σ`-orbit, on which `T_σ` acts freely
(`MPSTensor.MultiBlockCompression.coordChange_conjTriangularGauge`). -/
theorem flag_withGauge_eq_iff_exists_eq_conjTriangularGauge (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s)
    (g : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b) :
    (∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) ↔
      ∃ (h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
        (ht : h.BlockTriangular fun x => P.ord x.1) (μ : BlockIndex S P.z → ℂ)
        (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, h.blockDiag' b = μ b • 1),
        g = P.conjTriangularGauge ht hμ hh := by
  constructor
  · intro hflag
    exact ⟨_, blockTriangular_coordChange_of_flag_eq hflag, _,
      coordChangeScalar_ne_zero hC hD hflag, blockDiag'_coordChange_eq_smul hC hflag,
      LinearEquiv.ext fun v => by
        rw [conjTriangularGauge_apply, coordChange_mulVec, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h, ht, μ, hμ, hh, rfl⟩ k
    exact P.conjTriangular_flag ht hμ hh k

end FlagFiber

/-! ### Which families admit a reduction, and the union over flags -/

section AllReductions

/-- **Which families admit a reduction** (*The asymmetric fundamental theorem of matrix product
states*, Theorem 6.6): `B` has a reduction onto `(C_s)` with `z` zero slots exactly when its word
module has a labelled invariant flag for `(C_s)` with `z` zero steps. No hypothesis on the blocks.
-/
theorem exists_z_eq_iff_exists_flagData (B : MPSTensor d DB) (S : Finset ι)
    (C : ∀ s, MPSTensor d (D s)) (z : ℕ) :
    (∃ P : MultiBlockCompression B S C, P.z = z) ↔
      ∃ F : FlagData B.WordModule S C, F.z = z :=
  ⟨fun ⟨P, hP⟩ => ⟨P.toFlagData, hP⟩, fun ⟨F, hF⟩ => ⟨F.toMultiBlockCompression, hF⟩⟩

omit [DecidableEq ι] in
/-- Two orders of the slots whose inverses agree, read as functions, agree. -/
theorem heq_of_heq_coe_symm {z z' : ℕ} (hz : z = z') {e : BlockIndex S z ≃ Fin (S.card + z)}
    {e' : BlockIndex S z' ≃ Fin (S.card + z')} (h : HEq ⇑e.symm ⇑e'.symm) : HEq e e' := by
  subst hz
  rw [← Equiv.symm_symm e, Equiv.coe_fn_injective (eq_of_heq h), Equiv.symm_symm]

/-- **A reduction with the labelled flag of another is in its `T_σ`-orbit** (blueprint
`thm:asym_uniq_same_flag`, *Two compressions with the same flag*; blueprint `thm:asym_uniq_all`,
*The set of all compressions*): if `R` and `P` have the same labelled flag, then `P = (σ_R, h g_R)`
for some `h ∈ T_{σ_R}`. -/
theorem exists_eq_conjTriangular_of_toFlagData_eq (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) {P R : MultiBlockCompression B S C}
    (h : R.toFlagData = P.toFlagData) :
    ∃ (h' : Matrix (BlockSpace D S R.z) (BlockSpace D S R.z) ℂ)
      (ht : h'.BlockTriangular fun x => R.ord x.1) (μ : BlockIndex S R.z → ℂ)
      (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, h'.blockDiag' b = μ b • 1), P = R.conjTriangular ht hμ hh := by
  have hz : P.z = R.z := congrArg FlagData.z h.symm
  have hl : HEq P.toFlagData.label R.toFlagData.label := by rw [h]
  have hord : HEq P.ord R.ord := heq_of_heq_coe_symm (e := P.ord) (e' := R.ord) hz hl
  obtain ⟨g, htri, hdiag, rfl⟩ := R.exists_eq_withGauge hz hord
  have hH' : HEq (R.withGauge g htri hdiag).toFlagData.H R.toFlagData.H := by rw [h]
  have hH := eq_of_heq hH'
  have hflag : ∀ k, (R.withGauge g htri hdiag).flag k = R.flag k := fun k => congrFun hH k
  exact ⟨_, _, _, _, _, withGauge_eq_conjTriangular hC hD hflag⟩

/-- **The set of all reductions** (blueprint `thm:asym_uniq_all`, *The set of all compressions*):
choose for each labelled invariant flag `F` one reduction `rep F` with labelled flag `F`. Every
reduction onto normal blocks of positive bond dimension is `(σ_F, h g_F)` for exactly one pair
`(F, h)` with `h ∈ T_{σ_F}`, and `F` is then its labelled flag. -/
theorem existsUnique_conjTriangular (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (rep : FlagData B.WordModule S C → MultiBlockCompression B S C)
    (hrep : ∀ F, (rep F).toFlagData = F) (P : MultiBlockCompression B S C) :
    (∃! p : (F : FlagData B.WordModule S C) ×
        Matrix (BlockSpace D S (rep F).z) (BlockSpace D S (rep F).z) ℂ,
      ∃ (ht : p.2.BlockTriangular fun x => (rep p.1).ord x.1) (μ : BlockIndex S (rep p.1).z → ℂ)
        (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, p.2.blockDiag' b = μ b • 1),
        P = (rep p.1).conjTriangular ht hμ hh) ∧
    ∀ p : (F : FlagData B.WordModule S C) ×
        Matrix (BlockSpace D S (rep F).z) (BlockSpace D S (rep F).z) ℂ,
      (∃ (ht : p.2.BlockTriangular fun x => (rep p.1).ord x.1)
        (μ : BlockIndex S (rep p.1).z → ℂ) (hμ : ∀ b, μ b ≠ 0)
        (hh : ∀ b, p.2.blockDiag' b = μ b • 1), P = (rep p.1).conjTriangular ht hμ hh) →
      p.1 = P.toFlagData := by
  have hfst : ∀ p : (F : FlagData B.WordModule S C) ×
        Matrix (BlockSpace D S (rep F).z) (BlockSpace D S (rep F).z) ℂ,
      (∃ (ht : p.2.BlockTriangular fun x => (rep p.1).ord x.1)
        (μ : BlockIndex S (rep p.1).z → ℂ) (hμ : ∀ b, μ b ≠ 0)
        (hh : ∀ b, p.2.blockDiag' b = μ b • 1), P = (rep p.1).conjTriangular ht hμ hh) →
      p.1 = P.toFlagData := by
    rintro ⟨F, h⟩ ⟨ht, μ, hμ, hh, rfl⟩
    rw [toFlagData_conjTriangular, hrep]
  refine ⟨?_, hfst⟩
  obtain ⟨h', ht, μ, hμ, hh, hP⟩ :=
    exists_eq_conjTriangular_of_toFlagData_eq hC hD (hrep P.toFlagData)
  refine ⟨⟨P.toFlagData, h'⟩, ⟨ht, μ, hμ, hh, hP⟩, fun p hp => ?_⟩
  have h1 := hfst p hp
  obtain ⟨F, h''⟩ := p
  obtain ⟨ht', μ', hμ', hh', hP'⟩ := hp
  dsimp only at h1
  subst h1
  obtain rfl : h'' = h' := (rep _).eq_of_conjTriangular_eq (hP'.symm.trans hP)
  rfl

end AllReductions

end MultiBlockCompression

namespace FlagData

variable {d DB : ℕ} {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- **Every labelled invariant flag is the flag of a reduction** (blueprint `thm:asym_uniq_all`,
*The set of all compressions*): for every labelled invariant flag `F` of the word module of `B` over
`(S, C)` there are a reduction `P` of `B` onto `(C_s)` and an identification
`F.r + 1 = S.card + P.z + 1` of the two index ranges under which the flag of `P` is the chain of
`F`, `P.flag k = F.H k` for every `k`. The statement concerns the chain only: that the reduction
`F.toMultiBlockCompression` used here orders its slots by the labels of `F` is
`toMultiBlockCompression_ord_symm`, and that its labelled flag is `F` is
`toMultiBlockCompression_toFlagData`. -/
theorem exists_multiBlockCompression_flag_eq (F : FlagData B.WordModule S C) :
    ∃ (P : MultiBlockCompression B S C) (h : F.r + 1 = S.card + P.z + 1),
      ∀ k, P.flag (Fin.cast h k) = F.H k :=
  ⟨F.toMultiBlockCompression, congrArg (· + 1) F.r_eq, F.toMultiBlockCompression_flag⟩

/-- The compression of a labelled invariant flag orders its slots by the positions of their labels
(blueprint `thm:asym_uniq_all`, *The set of all compressions*): the slot at the position of the step
`k` is the label of `k`. -/
theorem toMultiBlockCompression_ord_symm (F : FlagData B.WordModule S C) (k : Fin F.r) :
    F.toMultiBlockCompression.ord.symm (Fin.cast F.r_eq k) = F.label k :=
  rfl

/-- **The labelled flag of the compression of a labelled invariant flag is that flag** (blueprint
`thm:asym_uniq_all`, *The set of all compressions*): `F ↦ F.toMultiBlockCompression` is a right
inverse of the labelled flag map `P ↦ P.toFlagData`. -/
theorem toMultiBlockCompression_toFlagData (F : FlagData B.WordModule S C) :
    F.toMultiBlockCompression.toFlagData = F := by
  have hH := F.toMultiBlockCompression_flag
  have hr : F.r = S.card + F.z := F.r_eq
  obtain ⟨r, z, H, H0, Hl, Hm, label, lb, m, uf, us⟩ := F
  dsimp only at hr
  subst hr
  unfold MultiBlockCompression.toFlagData
  congr 1
  exact funext hH

/-- **A choice of one reduction for each labelled invariant flag** (blueprint `thm:asym_uniq_all`,
*The set of all compressions*): there is a map `rep` with `(rep F).toFlagData = F` for every `F`, so
the hypothesis of `MPSTensor.MultiBlockCompression.existsUnique_conjTriangular` can be met. -/
theorem exists_rightInverse_toFlagData :
    ∃ rep : FlagData B.WordModule S C → MultiBlockCompression B S C,
      ∀ F, (rep F).toFlagData = F :=
  ⟨toMultiBlockCompression, toMultiBlockCompression_toFlagData⟩

end FlagData

end MPSTensor
