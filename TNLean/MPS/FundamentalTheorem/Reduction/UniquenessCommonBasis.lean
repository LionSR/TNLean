/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessDifferentFlags
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessSameFlag

/-!
# A basis adapted to two flags

Let `P` and `Q` be two multi-block compressions of the same tensor `B` onto two families of normal
blocks of positive bond dimension (possibly the same family), with flags `M_k` and `M'_{k'}`, and
let `π` be the matching of their positions. For every position `k` put
$$U_k = M_k ∩ M'_{π(k)},\qquad K_k = M_{k-1} ∩ M'_{π(k)},$$
and choose a complex-linear complement `L_k` of `K_k` in `U_k`. Then
$$\mathcal B = L_1 ⊕ ⋯ ⊕ L_r,\qquad M_k = \bigoplus_{j ≤ k} L_j,\qquad
M'_{k'} = \bigoplus_{π(j) ≤ k'} L_j,$$
so the union of bases of the `L_j` is adapted to both flags. The change of coordinates `Γ` reading
`x = ∑_j x_j`, `x_j ∈ L_j`, as the vector whose block at the slot of position `j` is `W_{σ(j)} x_j`
is invertible, and
$$g = 𝔄 Γ,\qquad \widetilde g = \widetilde{𝔄} P_X Γ,\qquad
\widetilde g g^{-1} = \widetilde{𝔄} P_X 𝔄^{-1},$$
with `𝔄` block upper triangular with identity diagonal blocks in the order of `P`, `𝔄_tilde`
likewise in the order of `Q`, and `P_X` the block permutation matrix that sends the block of
position `j` to the block of position `π(j)` through the intertwiner `X_j` of *Two compressions with
different flags* (blueprint `thm:asym_uniq_different_flags`). This is *A basis adapted to both
flags* (blueprint `thm:asym_uniq_common_basis`; for two families, *The asymmetric fundamental
theorem of matrix product states*, Theorem 6.5).

## Main definitions

* `MPSTensor.slotAssembleEquiv`: the coordinates attached to a decomposition of a vector space into
  subspaces, one for each slot, each identified with the coordinates of its slot.
* `MPSTensor.MultiBlockCompression.matchedInter`, `MPSTensor.MultiBlockCompression.matchedKer`,
  `MPSTensor.MultiBlockCompression.matchedCompl`: the subspaces `U_k`, `K_k` and the chosen
  complement `L_k`.
* `MPSTensor.MultiBlockCompression.commonCoord`, `MPSTensor.MultiBlockCompression.commonCoord'`: the
  coordinates `Γ` and `P_X Γ` adapted to both flags.
* `MPSTensor.MultiBlockCompression.unipotentFactor`,
  `MPSTensor.MultiBlockCompression.unipotentFactor'`,
  `MPSTensor.MultiBlockCompression.matchingPermMatrix`: the factors `𝔄`, `𝔄_tilde` and `P_X`.

## Main results

* `MPSTensor.MultiBlockCompression.finrank_matchedCompl`: `dim L_k = n_k`.
* `MPSTensor.MultiBlockCompression.flag_eq_iSup_matchedCompl`,
  `MPSTensor.MultiBlockCompression.flag_eq_iSup_matchedCompl'`,
  `MPSTensor.MultiBlockCompression.iSup_matchedCompl`,
  `MPSTensor.MultiBlockCompression.iSupIndep_matchedCompl`: the decompositions of *A basis adapted
  to both flags*.
* `MPSTensor.MultiBlockCompression.blockTriangular_unipotentFactor`,
  `MPSTensor.MultiBlockCompression.blockDiag'_unipotentFactor` and their primed versions: the two
  factors are unipotent.
* `MPSTensor.MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq`: the factorization
  `g_tilde g⁻¹ = 𝔄_tilde P_X 𝔄⁻¹` of *A basis adapted to both flags*.

## References

Blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both flags*; *The asymmetric
fundamental theorem of matrix product states*, Theorem 6.5.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}

/-- A vector supported on one block reads, on that block, the vector it embeds. -/
theorem blockEmbed_mulVec_apply_self {z : ℕ} (b : BlockIndex S z) (v : Fin (slotSize D b) → ℂ)
    (i : Fin (slotSize D b)) : (Matrix.blockEmbed (slotSize D) b *ᵥ v) ⟨b, i⟩ = v i := by
  have h := congrFun (blockProj_mulVec b (Matrix.blockEmbed (slotSize D) b *ᵥ v)) i
  rw [Matrix.mulVec_mulVec, Matrix.blockProj_mul_blockEmbed_self, Matrix.one_mulVec] at h
  exact h.symm

/-! ### Chains with prescribed steps -/

/-- A chain of subspaces starting at `0` whose `m`-th step adds `G m` is the sum of the `G m`
over the steps below: `F_k = ∑_{m < k} G_m`. -/
theorem eq_iSup_castSucc_lt_of_eq_sup {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    {F : Fin (n + 1) → Submodule ℂ V} {G : Fin n → Submodule ℂ V} (h0 : F 0 = ⊥)
    (hs : ∀ m, F m.succ = F m.castSucc ⊔ G m) (k : Fin (n + 1)) :
    F k = ⨆ (m : Fin n) (_ : m.castSucc < k), G m := by
  induction k using Fin.induction with
  | zero =>
    rw [h0]
    exact (iSup₂_eq_bot.2 fun m hm => absurd hm (Fin.not_lt_zero _)).symm
  | succ k ih =>
    rw [hs, ih]
    refine le_antisymm (sup_le (iSup₂_le fun m hm => le_iSup₂_of_le m
      (hm.trans Fin.castSucc_lt_succ) le_rfl) (le_iSup₂_of_le k Fin.castSucc_lt_succ le_rfl))
      (iSup₂_le fun m hm => ?_)
    rcases eq_or_ne m k with rfl | hne
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup₂_of_le m (Fin.castSucc_lt_castSucc_iff.2
        (lt_of_le_of_ne (Fin.castSucc_lt_succ_iff.1 hm) hne)) le_rfl)

/-! ### Coordinates from a decomposition into slot subspaces -/

section SlotDecomposition

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {z : ℕ} {κ : Type*}
  (L : κ → Submodule ℂ V) (e : BlockIndex S z ≃ κ)
  (R : ∀ b : BlockIndex S z, V →ₗ[ℂ] (Fin (slotSize D b) → ℂ))
  (hR : ∀ b, Function.Bijective ((R b).domRestrict (L (e b))))

/-- The reading `R b` restricted to the subspace `L (e b)` of the slot `b`, as an identification
with the coordinates of `b`. -/
noncomputable def slotRestrictEquiv (b : BlockIndex S z) :
    L (e b) ≃ₗ[ℂ] (Fin (slotSize D b) → ℂ) :=
  LinearEquiv.ofBijective _ (hR b)

omit [DecidableEq ι] in
theorem slotRestrictEquiv_apply (b : BlockIndex S z) (x : L (e b)) :
    slotRestrictEquiv L e R hR b x = R b x := rfl

omit [DecidableEq ι] in
theorem slotRestrictEquiv_symm_apply_of_mem (b : BlockIndex S z) {x : V} (hx : x ∈ L (e b)) :
    ((slotRestrictEquiv L e R hR b).symm (R b x) : V) = x := by
  rw [← slotRestrictEquiv_apply L e R hR b ⟨x, hx⟩, LinearEquiv.symm_apply_apply]

/-- The vector of `V` with prescribed coordinates on every slot: the sum over the slots `b` of
the vector of `L (e b)` whose reading `R b` is the block of `b`. -/
noncomputable def slotAssemble : (BlockSpace D S z → ℂ) →ₗ[ℂ] V :=
  ∑ b, (L (e b)).subtype ∘ₗ
    ((slotRestrictEquiv L e R hR b).symm : (Fin (slotSize D b) → ℂ) →ₗ[ℂ] L (e b)) ∘ₗ
      (Matrix.blockProj (slotSize D) b).mulVecLin

theorem slotAssemble_apply (u : BlockSpace D S z → ℂ) :
    slotAssemble L e R hR u =
      ∑ b, ((slotRestrictEquiv L e R hR b).symm (Matrix.blockProj (slotSize D) b *ᵥ u) : V) := by
  simp [slotAssemble]

theorem slotAssemble_blockEmbed (b : BlockIndex S z) (v : Fin (slotSize D b) → ℂ) :
    slotAssemble L e R hR (Matrix.blockEmbed (slotSize D) b *ᵥ v) =
      ((slotRestrictEquiv L e R hR b).symm v : V) := by
  rw [slotAssemble_apply, Finset.sum_eq_single b]
  · rw [Matrix.mulVec_mulVec, Matrix.blockProj_mul_blockEmbed_self, Matrix.one_mulVec]
  · intro c _ hc
    rw [Matrix.mulVec_mulVec, Matrix.blockProj_mul_blockEmbed_of_ne hc, Matrix.zero_mulVec,
      map_zero, Submodule.coe_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem slotAssemble_surjective (htop : ⨆ j, L j = ⊤) :
    Function.Surjective (slotAssemble L e R hR) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← htop]
  refine iSup_le fun j x hx => ?_
  obtain ⟨b, rfl⟩ := e.surjective j
  exact LinearMap.mem_range.2 ⟨Matrix.blockEmbed (slotSize D) b *ᵥ R b x, by
    rw [slotAssemble_blockEmbed, slotRestrictEquiv_symm_apply_of_mem L e R hR b hx]⟩

variable [FiniteDimensional ℂ V]

/-- **The coordinates of a decomposition into slot subspaces** (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*, the change of basis `Γ`, inverted):
if the subspaces `L j` span `V`, each `L (e b)` is identified with the coordinates of the slot `b`
by `R b`, and the dimensions match, then assembling the slot vectors is a linear equivalence. -/
noncomputable def slotAssembleEquiv (htop : ⨆ j, L j = ⊤)
    (hdim : Module.finrank ℂ (BlockSpace D S z → ℂ) = Module.finrank ℂ V) :
    (BlockSpace D S z → ℂ) ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (slotAssemble L e R hR)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
      (slotAssemble_surjective L e R hR htop), slotAssemble_surjective L e R hR htop⟩

variable (htop : ⨆ j, L j = ⊤)
  (hdim : Module.finrank ℂ (BlockSpace D S z → ℂ) = Module.finrank ℂ V)

/-- A vector of the subspace of the slot `b` has coordinates supported on `b`, where they are its
reading `R b`. -/
theorem slotAssembleEquiv_symm_apply_of_mem {b : BlockIndex S z} {x : V} (hx : x ∈ L (e b)) :
    (slotAssembleEquiv L e R hR htop hdim).symm x = Matrix.blockEmbed (slotSize D) b *ᵥ R b x := by
  rw [LinearEquiv.symm_apply_eq]
  change x = slotAssemble L e R hR _
  rw [slotAssemble_blockEmbed, slotRestrictEquiv_symm_apply_of_mem L e R hR b hx]

/-- A vector lies in a sum of some of the slot subspaces exactly when its coordinates vanish on
the other slots. -/
theorem mem_iff_slotAssembleEquiv_symm_apply {q : κ → Prop} {F : Submodule ℂ V}
    (hF : F = ⨆ (j) (_ : q j), L j) (x : V) :
    x ∈ F ↔ ∀ y : BlockSpace D S z, ¬ q (e y.1) →
      (slotAssembleEquiv L e R hR htop hdim).symm x y = 0 := by
  set Γ := (slotAssembleEquiv L e R hR htop hdim).symm with hΓ
  constructor
  · intro hx
    let W : Submodule ℂ V :=
      { carrier := {x | ∀ y : BlockSpace D S z, ¬ q (e y.1) → Γ x y = 0}
        add_mem' := fun ha hb y hy => by
          rw [map_add, Pi.add_apply, ha y hy, hb y hy, add_zero]
        zero_mem' := fun y _ => by simp
        smul_mem' := fun c x hx y hy => by
          rw [map_smul, Pi.smul_apply, hx y hy, smul_zero] }
    have hFW : F ≤ W := by
      rw [hF]
      refine iSup₂_le fun j hj x hx y hy => ?_
      obtain ⟨b, rfl⟩ := e.surjective j
      rw [hΓ, slotAssembleEquiv_symm_apply_of_mem L e R hR htop hdim hx]
      exact blockEmbed_mulVec_apply_of_fst_ne _ fun h => hy (by rw [h]; exact hj)
    exact hFW hx
  · intro h
    have hx : x = slotAssemble L e R hR (Γ x) :=
      ((slotAssembleEquiv L e R hR htop hdim).apply_symm_apply x).symm
    rw [hx, slotAssemble_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : q (e b)
    · rw [hF]
      exact (le_iSup₂_of_le (e b) hb le_rfl : L (e b) ≤ ⨆ (j) (_ : q j), L j) (Submodule.coe_mem _)
    · have h0 : Matrix.blockProj (slotSize D) b *ᵥ Γ x = 0 := by
        rw [blockProj_mulVec]
        funext j
        exact h ⟨b, j⟩ hb
      rw [h0, map_zero, Submodule.coe_zero]
      exact F.zero_mem

omit [DecidableEq ι] in
include e R hR htop hdim in
/-- **The slot subspaces are independent** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted
to both flags*, the direct sum `𝓑 = L_1 ⊕ ⋯ ⊕ L_r`). -/
theorem iSupIndep_of_slotAssemble : iSupIndep L := by
  classical
  rw [iSupIndep_def]
  intro j
  obtain ⟨b, rfl⟩ := e.surjective j
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h := (mem_iff_slotAssembleEquiv_symm_apply L e R hR htop hdim
    (q := fun i => i ≠ e b) rfl x).1 hx'
  rw [slotAssembleEquiv_symm_apply_of_mem L e R hR htop hdim hx] at h
  have hR0 : R b x = 0 := funext fun i => by
    have := h ⟨b, i⟩ (not_not.2 rfl)
    rwa [blockEmbed_mulVec_apply_self] at this
  have h1 : (R b).domRestrict (L (e b)) ⟨x, hx⟩ = (R b).domRestrict (L (e b)) 0 := by
    rw [map_zero]
    exact hR0
  simpa using congrArg Subtype.val ((hR b).1 h1)

end SlotDecomposition

namespace MultiBlockCompression

variable {d DB : ℕ} {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-! ### The reading map on a complement -/

/-- The reading map `W_b` of the slot `b` at position `k` identifies a complement `L` of
`K = U ∩ M_{k-1}` in an invariant subspace `U` with `M_{k-1} + U = M_k` with the coordinates of `b`
(proof of blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both flags*: `W_b` restricted
to `U` has kernel `K` and is onto). -/
theorem bijective_leftRow_domRestrict (R : MultiBlockCompression B S C) {b : BlockIndex S R.z}
    {U : Submodule (WordAlgebra d) B.WordModule}
    (hU : R.flag (R.ord b).castSucc ⊔ U = R.flag (R.ord b).succ)
    {K L : Submodule ℂ B.WordModule} (hK : ∀ x, x ∈ K ↔ x ∈ U ⊓ R.flag (R.ord b).castSucc)
    (hdisj : Disjoint K L) (hsup : K ⊔ L = U.restrictScalars ℂ) :
    Function.Bijective
      (((R.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap).domRestrict L) := by
  have hLU : ∀ x ∈ L, x ∈ U := fun x hx => by
    have : x ∈ U.restrictScalars ℂ := hsup ▸ Submodule.mem_sup_right hx
    exact this
  have hUs : U ≤ R.flag (R.ord b).succ := hU ▸ le_sup_right
  refine ⟨(injective_iff_map_eq_zero _).2 fun x h0 => ?_, fun v => ?_⟩
  · have hx0 : R.leftRow b *ᵥ WordModule.toVec B (x : B.WordModule) = 0 := h0
    have hxU := hLU x x.2
    have hxK : (x : B.WordModule) ∈ K :=
      (hK _).2 ⟨hxU, R.mem_flag_of_leftRow_mulVec_eq_zero (hUs hxU) hx0⟩
    exact Subtype.ext ((Submodule.disjoint_def.1 hdisj) _ hxK x.2)
  · obtain ⟨u, hu, huv⟩ := R.leftRow_surjOn_of_sup_eq hU (Set.mem_univ v)
    have hu' : u ∈ K ⊔ L := by
      rw [hsup]
      exact hu
    obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.1 hu'
    refine ⟨⟨l, hl⟩, ?_⟩
    have hk0 : R.leftRow b *ᵥ WordModule.toVec B k = 0 :=
      R.leftRow_mulVec_eq_zero_of_mem ((hK k).1 hk).2
    change R.leftRow b *ᵥ WordModule.toVec B l = v
    rw [← huv]
    simp only [map_add, Matrix.mulVec_add, hk0, zero_add]

/-! ### The subspaces `U_k`, `K_k` and the complements `L_k` -/

section Matched

variable {κ : Type*} [DecidableEq κ] {D' : κ → ℕ} {S' : Finset κ}
  {C' : ∀ t, MPSTensor d (D' t)}
  (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
  (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)

/-- The subspace `U_k = M_k ∩ M'_{π(k)}` of the matched positions `k ↦ π(k)` (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*). -/
noncomputable def matchedInter (k : Fin (S.card + P.z)) : Submodule (WordAlgebra d) B.WordModule :=
  P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ

/-- The subspace `K_k = M_{k-1} ∩ M'_{π(k)}` of the matched positions `k ↦ π(k)` (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*). -/
noncomputable def matchedKer (k : Fin (S.card + P.z)) : Submodule (WordAlgebra d) B.WordModule :=
  P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ

theorem matchedKer_le_matchedInter (k : Fin (S.card + P.z)) :
    P.matchedKer Q hC hD hC' hD' k ≤ P.matchedInter Q hC hD hC' hD' k :=
  inf_le_inf_right _ (P.flag_mono (Fin.castSucc_le_succ k))

/-- **The chosen complement `L_k`** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*): a complex-linear complement of `K_k` in `U_k`. -/
noncomputable def matchedCompl (k : Fin (S.card + P.z)) : Submodule ℂ B.WordModule :=
  Classical.choose (IsModularLattice.exists_disjoint_and_sup_eq
    (Submodule.restrictScalars_mono ℂ (P.matchedKer_le_matchedInter Q hC hD hC' hD' k)))

theorem disjoint_matchedCompl (k : Fin (S.card + P.z)) :
    Disjoint ((P.matchedKer Q hC hD hC' hD' k).restrictScalars ℂ)
      (P.matchedCompl Q hC hD hC' hD' k) :=
  (Classical.choose_spec (IsModularLattice.exists_disjoint_and_sup_eq
    (Submodule.restrictScalars_mono ℂ (P.matchedKer_le_matchedInter Q hC hD hC' hD' k)))).1

theorem sup_matchedCompl (k : Fin (S.card + P.z)) :
    (P.matchedKer Q hC hD hC' hD' k).restrictScalars ℂ ⊔ P.matchedCompl Q hC hD hC' hD' k =
      (P.matchedInter Q hC hD hC' hD' k).restrictScalars ℂ :=
  (Classical.choose_spec (IsModularLattice.exists_disjoint_and_sup_eq
    (Submodule.restrictScalars_mono ℂ (P.matchedKer_le_matchedInter Q hC hD hC' hD' k)))).2

theorem matchedCompl_le (k : Fin (S.card + P.z)) :
    P.matchedCompl Q hC hD hC' hD' k ≤ (P.matchedInter Q hC hD hC' hD' k).restrictScalars ℂ :=
  P.sup_matchedCompl Q hC hD hC' hD' k ▸ le_sup_right

/-- **Equal subspaces give equal complements** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 6.5, last sentence): the complement `L_k` is a choice depending only on the
two subspaces `K_k ⊆ U_k`, so two pairs of reductions, possibly with different numbers of zero slots
or different positions, with the same `K` and the same `U` have the same complement. -/
theorem matchedCompl_congr {P₁ : MultiBlockCompression B S C} {Q₁ : MultiBlockCompression B S' C'}
    {P₂ : MultiBlockCompression B S C} {Q₂ : MultiBlockCompression B S' C'}
    {k₁ : Fin (S.card + P₁.z)} {k₂ : Fin (S.card + P₂.z)}
    (hK : P₁.matchedKer Q₁ hC hD hC' hD' k₁ = P₂.matchedKer Q₂ hC hD hC' hD' k₂)
    (hU : P₁.matchedInter Q₁ hC hD hC' hD' k₁ = P₂.matchedInter Q₂ hC hD hC' hD' k₂) :
    P₁.matchedCompl Q₁ hC hD hC' hD' k₁ = P₂.matchedCompl Q₂ hC hD hC' hD' k₂ := by
  have key : ∀ {K₁ U₁ K₂ U₂ : Submodule ℂ B.WordModule}, K₁ = K₂ → U₁ = U₂ →
      ∀ (h₁ : ∃ L, Disjoint K₁ L ∧ K₁ ⊔ L = U₁) (h₂ : ∃ L, Disjoint K₂ L ∧ K₂ ⊔ L = U₂),
        Classical.choose h₁ = Classical.choose h₂ := by
    rintro K U _ _ rfl rfl h₁ h₂
    rfl
  exact key (congrArg (Submodule.restrictScalars ℂ) hK) (congrArg (Submodule.restrictScalars ℂ) hU)
    _ _

/-- The reading map of the slot at position `k` of `P` identifies `L_k` with the coordinates of that
slot (proof of blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both flags*). -/
theorem bijective_leftRow_matchedCompl (b : BlockIndex S P.z) :
    Function.Bijective (((P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap).domRestrict
      (P.matchedCompl Q hC hD hC' hD' (P.ord b))) :=
  P.bijective_leftRow_domRestrict (U := P.matchedInter Q hC hD hC' hD' (P.ord b))
    (P.flag_sup_inf_eq Q hC hD hC' hD' (P.ord b))
    (fun x => by
      rw [Submodule.restrictScalars_mem, matchedInter, matchedKer,
        P.flag_inf_inf_eq Q hC hD hC' hD' (P.ord b)])
    (P.disjoint_matchedCompl Q hC hD hC' hD' _) (P.sup_matchedCompl Q hC hD hC' hD' _)

/-- The reading map of the slot at position `π(j)` of `Q` identifies `L_j` with the coordinates of
that slot (proof of blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both flags*). -/
theorem bijective_leftRow_matchedCompl' {j : Fin (S.card + P.z)} {b' : BlockIndex S' Q.z}
    (hj : P.matching Q hC hD hC' hD' j = Q.ord b') :
    Function.Bijective (((Q.leftRow b').mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap).domRestrict
      (P.matchedCompl Q hC hD hC' hD' j)) := by
  refine Q.bijective_leftRow_domRestrict (U := P.matchedInter Q hC hD hC' hD' j) ?_ (fun x => ?_)
    (P.disjoint_matchedCompl Q hC hD hC' hD' j) (P.sup_matchedCompl Q hC hD hC' hD' j)
  · rw [← hj]
    exact P.flag_sup_inf_eq' Q hC hD hC' hD' j
  · rw [Submodule.restrictScalars_mem, ← hj, matchedInter, matchedKer,
      P.flag_inf_inf_eq' Q hC hD hC' hD' j]

/-- **The dimension of `L_k`** (proof of blueprint `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*: `U_k / K_k ≅ M_k / M_{k-1}`, so `dim L_k = n_k`). -/
theorem finrank_matchedCompl (k : Fin (S.card + P.z)) :
    Module.finrank ℂ (P.matchedCompl Q hC hD hC' hD' k) = slotSize D (P.ord.symm k) := by
  obtain ⟨b, rfl⟩ := P.ord.surjective k
  rw [P.ord.symm_apply_apply]
  simpa using
    (LinearEquiv.ofBijective _ (P.bijective_leftRow_matchedCompl Q hC hD hC' hD' b)).finrank_eq

/-! ### The two decompositions -/

/-- `M_k = M_{k-1} + L_k` (proof of blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both
flags*). -/
theorem flag_succ_eq_sup_matchedCompl (k : Fin (S.card + P.z)) :
    (P.flag k.succ).restrictScalars ℂ =
      (P.flag k.castSucc).restrictScalars ℂ ⊔ P.matchedCompl Q hC hD hC' hD' k := by
  refine le_antisymm (fun x hx => ?_) (sup_le
    (Submodule.restrictScalars_mono ℂ (P.flag_mono (Fin.castSucc_le_succ k)))
    ((P.matchedCompl_le Q hC hD hC' hD' k).trans (Submodule.restrictScalars_mono ℂ inf_le_left)))
  rw [Submodule.restrictScalars_mem, ← P.flag_sup_inf_eq Q hC hD hC' hD' k] at hx
  obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
  have hu' : u ∈ (P.matchedKer Q hC hD hC' hD' k).restrictScalars ℂ ⊔
      P.matchedCompl Q hC hD hC' hD' k := by
    rw [P.sup_matchedCompl Q hC hD hC' hD' k]
    exact hu
  obtain ⟨c, hc, l, hl, rfl⟩ := Submodule.mem_sup.1 hu'
  have hc' : c ∈ P.flag k.castSucc := (Submodule.mem_inf.1 hc).1
  rw [← add_assoc]
  exact Submodule.add_mem_sup ((P.flag k.castSucc).add_mem ha hc') hl

/-- `M'_{π(j)} = M'_{π(j)-1} + L_j` (proof of blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*). -/
theorem flag_matching_succ_eq_sup_matchedCompl (j : Fin (S.card + P.z)) :
    (Q.flag (P.matching Q hC hD hC' hD' j).succ).restrictScalars ℂ =
      (Q.flag (P.matching Q hC hD hC' hD' j).castSucc).restrictScalars ℂ ⊔
        P.matchedCompl Q hC hD hC' hD' j := by
  refine le_antisymm (fun x hx => ?_) (sup_le
    (Submodule.restrictScalars_mono ℂ (Q.flag_mono (Fin.castSucc_le_succ _)))
    ((P.matchedCompl_le Q hC hD hC' hD' j).trans (Submodule.restrictScalars_mono ℂ inf_le_right)))
  rw [Submodule.restrictScalars_mem, ← P.flag_sup_inf_eq' Q hC hD hC' hD' j] at hx
  obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
  have hu' : u ∈ (P.matchedKer Q hC hD hC' hD' j).restrictScalars ℂ ⊔
      P.matchedCompl Q hC hD hC' hD' j := by
    rw [P.sup_matchedCompl Q hC hD hC' hD' j]
    exact hu
  obtain ⟨c, hc, l, hl, rfl⟩ := Submodule.mem_sup.1 hu'
  have hc'' : c ∈ P.flag j.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' j).castSucc := by
    rw [← P.flag_inf_eq Q hC hD hC' hD' j]
    exact hc
  rw [← add_assoc]
  exact Submodule.add_mem_sup ((Q.flag _).add_mem ha (Submodule.mem_inf.1 hc'').2) hl

/-- `M'_{m} = M'_{m-1} + L_{π⁻¹(m)}` (proof of blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*). -/
theorem flag_succ_eq_sup_matchedCompl' (m : Fin (S'.card + Q.z)) :
    (Q.flag m.succ).restrictScalars ℂ = (Q.flag m.castSucc).restrictScalars ℂ ⊔
      P.matchedCompl Q hC hD hC' hD' ((P.matching Q hC hD hC' hD').symm m) := by
  have := P.flag_matching_succ_eq_sup_matchedCompl Q hC hD hC' hD'
    ((P.matching Q hC hD hC' hD').symm m)
  rwa [Equiv.apply_symm_apply] at this

/-- **The first flag is a sum of complements** (blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*): `M_k = ⨁_{j < k} L_j`, positions counted from `0`. -/
theorem flag_eq_iSup_matchedCompl (k : Fin (S.card + P.z + 1)) :
    (P.flag k).restrictScalars ℂ =
      ⨆ (j : Fin (S.card + P.z)) (_ : j.castSucc < k), P.matchedCompl Q hC hD hC' hD' j :=
  eq_iSup_castSucc_lt_of_eq_sup (F := fun k => (P.flag k).restrictScalars ℂ)
    (by simp [P.flag_zero]) (P.flag_succ_eq_sup_matchedCompl Q hC hD hC' hD') k

/-- **The second flag is a sum of complements** (blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*): `M'_{k'} = ⨁_{π(j) < k'} L_j`, positions counted from `0`. -/
theorem flag_eq_iSup_matchedCompl' (k' : Fin (S'.card + Q.z + 1)) :
    (Q.flag k').restrictScalars ℂ =
      ⨆ (j : Fin (S.card + P.z)) (_ : (P.matching Q hC hD hC' hD' j).castSucc < k'),
        P.matchedCompl Q hC hD hC' hD' j := by
  have h : (Q.flag k').restrictScalars ℂ = ⨆ (m : Fin (S'.card + Q.z)) (_ : m.castSucc < k'),
      P.matchedCompl Q hC hD hC' hD' ((P.matching Q hC hD hC' hD').symm m) :=
    eq_iSup_castSucc_lt_of_eq_sup (F := fun k => (Q.flag k).restrictScalars ℂ)
      (by simp [Q.flag_zero]) (P.flag_succ_eq_sup_matchedCompl' Q hC hD hC' hD') k'
  rw [h]
  apply le_antisymm
  · refine iSup₂_le fun m hm => le_iSup₂_of_le ((P.matching Q hC hD hC' hD').symm m) ?_ le_rfl
    rwa [Equiv.apply_symm_apply]
  · refine iSup₂_le fun j hj => le_iSup₂_of_le (P.matching Q hC hD hC' hD' j) hj ?_
    rw [Equiv.symm_apply_apply]

/-- **The complements span the bond space** (blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*). -/
theorem iSup_matchedCompl : ⨆ j, P.matchedCompl Q hC hD hC' hD' j = ⊤ := by
  have h := P.flag_eq_iSup_matchedCompl Q hC hD hC' hD' (Fin.last _)
  rw [P.flag_last, Submodule.restrictScalars_top] at h
  rw [h]
  exact iSup_congr fun j =>
    (iSup_pos (f := fun _ => P.matchedCompl Q hC hD hC' hD' j) (Fin.castSucc_lt_last j)).symm

/-! ### The coordinates adapted to both flags -/

/-- **The change of basis `Γ`** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both
flags*): the vector `x = ∑_j x_j`, `x_j ∈ L_j`, goes to the vector whose block at the slot `b` of
position `j` is `W_b x_j`. -/
noncomputable def commonCoord : B.WordModule ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) :=
  (slotAssembleEquiv (P.matchedCompl Q hC hD hC' hD') P.ord
    (fun b => (P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    (P.bijective_leftRow_matchedCompl Q hC hD hC' hD') (P.iSup_matchedCompl Q hC hD hC' hD')
    P.coord.finrank_eq.symm).symm

/-- **The change of basis `P_X Γ`** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*): the vector `x = ∑_j x_j`, `x_j ∈ L_j`, goes to the vector whose block at the slot `b'`
of position `π(j)` of `Q` is `W'_{b'} x_j`. -/
noncomputable def commonCoord' : B.WordModule ≃ₗ[ℂ] (BlockSpace D' S' Q.z → ℂ) :=
  (slotAssembleEquiv (P.matchedCompl Q hC hD hC' hD')
    (Q.ord.trans (P.matching Q hC hD hC' hD').symm)
    (fun b' => (Q.leftRow b').mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    (fun _ => P.bijective_leftRow_matchedCompl' Q hC hD hC' hD' (Equiv.apply_symm_apply _ _))
    (P.iSup_matchedCompl Q hC hD hC' hD') Q.coord.finrank_eq.symm).symm

theorem commonCoord_of_mem {b : BlockIndex S P.z} {x : B.WordModule}
    (hx : x ∈ P.matchedCompl Q hC hD hC' hD' (P.ord b)) :
    P.commonCoord Q hC hD hC' hD' x =
      Matrix.blockEmbed (slotSize D) b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) :=
  slotAssembleEquiv_symm_apply_of_mem _ _ _ _ _ _ hx

theorem commonCoord'_of_mem {b' : BlockIndex S' Q.z} {x : B.WordModule}
    (hx : x ∈ P.matchedCompl Q hC hD hC' hD' ((P.matching Q hC hD hC' hD').symm (Q.ord b'))) :
    P.commonCoord' Q hC hD hC' hD' x =
      Matrix.blockEmbed (slotSize D') b' *ᵥ (Q.leftRow b' *ᵥ WordModule.toVec B x) :=
  slotAssembleEquiv_symm_apply_of_mem _ _ _ _ _ _ hx

/-- **`Γ` is adapted to the first flag** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted
to both flags*): `Γ` maps `M_k` onto the leading coordinate subspace `E_k`. -/
theorem mem_flag_iff_commonCoord (k : Fin (S.card + P.z + 1)) (x : B.WordModule) :
    x ∈ P.flag k ↔ P.commonCoord Q hC hD hC' hD' x ∈ P.leadingSpace k := by
  change x ∈ (P.flag k).restrictScalars ℂ ↔ _
  rw [mem_iff_slotAssembleEquiv_symm_apply (P.matchedCompl Q hC hD hC' hD') P.ord
    (fun b => (P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    (P.bijective_leftRow_matchedCompl Q hC hD hC' hD') (P.iSup_matchedCompl Q hC hD hC' hD')
    P.coord.finrank_eq.symm (P.flag_eq_iSup_matchedCompl Q hC hD hC' hD' k) x,
    P.mem_leadingSpace]
  simp only [not_lt]
  rfl

/-- **`P_X Γ` is adapted to the second flag** (blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*): `P_X Γ` maps `M'_{k'}` onto the leading coordinate subspace `E'_{k'}`. -/
theorem mem_flag_iff_commonCoord' (k' : Fin (S'.card + Q.z + 1)) (x : B.WordModule) :
    x ∈ Q.flag k' ↔ P.commonCoord' Q hC hD hC' hD' x ∈ Q.leadingSpace k' := by
  change x ∈ (Q.flag k').restrictScalars ℂ ↔ _
  rw [mem_iff_slotAssembleEquiv_symm_apply (P.matchedCompl Q hC hD hC' hD')
    (Q.ord.trans (P.matching Q hC hD hC' hD').symm)
    (fun b' => (Q.leftRow b').mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    (fun _ => P.bijective_leftRow_matchedCompl' Q hC hD hC' hD' (Equiv.apply_symm_apply _ _))
    (P.iSup_matchedCompl Q hC hD hC' hD') Q.coord.finrank_eq.symm
    (P.flag_eq_iSup_matchedCompl' Q hC hD hC' hD' k') x, Q.mem_leadingSpace]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, not_lt]
  rfl

/-- **The complements are independent** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*, `𝓑 = L_1 ⊕ ⋯ ⊕ L_r`). -/
theorem iSupIndep_matchedCompl : iSupIndep (P.matchedCompl Q hC hD hC' hD') :=
  iSupIndep_of_slotAssemble (P.matchedCompl Q hC hD hC' hD') P.ord
    (fun b => (P.leftRow b).mulVecLin ∘ₗ (WordModule.toVec B).toLinearMap)
    (P.bijective_leftRow_matchedCompl Q hC hD hC' hD') (P.iSup_matchedCompl Q hC hD hC' hD')
    P.coord.finrank_eq.symm

/-! ### The factorization -/

/-- `Γ` as a change of coordinates of the bond space. -/
noncomputable def commonGauge : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ) :=
  (WordModule.toVec B).symm.trans (P.commonCoord Q hC hD hC' hD')

/-- `P_X Γ` as a change of coordinates of the bond space. -/
noncomputable def commonGauge' : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D' S' Q.z → ℂ) :=
  (WordModule.toVec B).symm.trans (P.commonCoord' Q hC hD hC' hD')

/-- **The unipotent factor `𝔄 = g Γ⁻¹`** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted
to both flags*). -/
noncomputable def unipotentFactor : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ :=
  coordChange (P.commonGauge Q hC hD hC' hD') P.gauge

/-- **The unipotent factor `𝔄_tilde = g_tilde (P_X Γ)⁻¹`** (blueprint `thm:asym_uniq_common_basis`,
*A basis adapted to both flags*). -/
noncomputable def unipotentFactor' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ :=
  coordChange (P.commonGauge' Q hC hD hC' hD') Q.gauge

/-- **`𝔄` is block upper triangular** in the order of `P` (blueprint `thm:asym_uniq_common_basis`,
*A basis adapted to both flags*): `g` and `Γ` both map `M_k` onto `E_k`. -/
theorem blockTriangular_unipotentFactor :
    (P.unipotentFactor Q hC hD hC' hD').BlockTriangular fun x => P.ord x.1 := by
  refine P.blockTriangular_coordChange fun k => ?_
  ext v
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe]
  have h1 := P.mem_flag_iff_commonCoord Q hC hD hC' hD' k ((WordModule.toVec B).symm v)
  have h2 : (WordModule.toVec B).symm v ∈ P.flag k ↔ P.gauge v ∈ P.leadingSpace k := by
    rw [P.mem_flag_iff_toVec_mem_comap, LinearEquiv.apply_symm_apply]
    rfl
  exact h1.symm.trans h2

/-- **The diagonal blocks of `𝔄` are identities** (blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*): on `L_k` both `g` and `Γ` read the block of position `k` by `W_{σ(k)}`. -/
theorem blockDiag'_unipotentFactor (b : BlockIndex S P.z) :
    (P.unipotentFactor Q hC hD hC' hD').blockDiag' b = 1 := by
  rw [← Matrix.blockProj_mul_mul_blockEmbed]
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨⟨x, hx⟩, hxv⟩ := (P.bijective_leftRow_matchedCompl Q hC hD hC' hD' b).2 v
  have hxv' : P.leftRow b *ᵥ WordModule.toVec B x = v := hxv
  have hΓ : (P.commonGauge Q hC hD hC' hD').symm (Matrix.blockEmbed (slotSize D) b *ᵥ v) =
      WordModule.toVec B x := by
    rw [LinearEquiv.symm_apply_eq]
    change _ = P.commonCoord Q hC hD hC' hD' ((WordModule.toVec B).symm (WordModule.toVec B x))
    rw [LinearEquiv.symm_apply_apply, P.commonCoord_of_mem Q hC hD hC' hD' hx, hxv']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, unipotentFactor, coordChange_mulVec, hΓ,
    Matrix.one_mulVec, blockProj_mulVec, ← hxv', P.leftRow_mulVec]

/-- **`𝔄_tilde` is block upper triangular** in the order of `Q` (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*): `g_tilde` and `P_X Γ` both map
`M'_{k'}` onto `E'_{k'}`. -/
theorem blockTriangular_unipotentFactor' :
    (P.unipotentFactor' Q hC hD hC' hD').BlockTriangular fun x => Q.ord x.1 := by
  refine Q.blockTriangular_coordChange fun k => ?_
  ext v
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe]
  have h1 := P.mem_flag_iff_commonCoord' Q hC hD hC' hD' k ((WordModule.toVec B).symm v)
  have h2 : (WordModule.toVec B).symm v ∈ Q.flag k ↔ Q.gauge v ∈ Q.leadingSpace k := by
    rw [Q.mem_flag_iff_toVec_mem_comap, LinearEquiv.apply_symm_apply]
    rfl
  exact h1.symm.trans h2

/-- **The diagonal blocks of `𝔄_tilde` are identities** (blueprint `thm:asym_uniq_common_basis`, *A
basis adapted to both flags*). -/
theorem blockDiag'_unipotentFactor' (b' : BlockIndex S' Q.z) :
    (P.unipotentFactor' Q hC hD hC' hD').blockDiag' b' = 1 := by
  rw [← Matrix.blockProj_mul_mul_blockEmbed]
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨⟨x, hx⟩, hxv⟩ :=
    (P.bijective_leftRow_matchedCompl' Q hC hD hC' hD' (Equiv.apply_symm_apply _ (Q.ord b'))).2 v
  have hxv' : Q.leftRow b' *ᵥ WordModule.toVec B x = v := hxv
  have hΓ : (P.commonGauge' Q hC hD hC' hD').symm (Matrix.blockEmbed (slotSize D') b' *ᵥ v) =
      WordModule.toVec B x := by
    rw [LinearEquiv.symm_apply_eq]
    change _ =
      P.commonCoord' Q hC hD hC' hD' ((WordModule.toVec B).symm (WordModule.toVec B x))
    rw [LinearEquiv.symm_apply_apply, P.commonCoord'_of_mem Q hC hD hC' hD' hx, hxv']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, unipotentFactor', coordChange_mulVec, hΓ,
    Matrix.one_mulVec, blockProj_mulVec, ← hxv', Q.leftRow_mulVec]

/-- The slot matched with `b` sits at the matched position. -/
theorem ord_slotMatching (b : BlockIndex S P.z) :
    Q.ord (P.slotMatching Q hC hD hC' hD' b) = P.matching Q hC hD hC' hD' (P.ord b) := by
  rw [slotMatching_apply, Equiv.apply_symm_apply]

/-- **The intertwiner `X_j`** of *Two compressions with different flags* (blueprint
`thm:asym_uniq_different_flags`) for the slot `b` of position `j` and the matched slot of `Q`
(blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both flags*). -/
noncomputable def matchedIntertwiner (b : BlockIndex S P.z) :
    Matrix (Fin (slotSize D' (P.slotMatching Q hC hD hC' hD' b))) (Fin (slotSize D b)) ℂ :=
  Classical.choose (P.exists_intertwiner_of_matching Q hC hD hC' hD' (P.ord b) rfl
    (P.ord_slotMatching Q hC hD hC' hD' b))

/-- The intertwiner `X_j` is invertible and intertwines the diagonal blocks of the matched slots
(blueprint `thm:asym_uniq_different_flags`, *Two compressions with different flags*). -/
theorem matchedIntertwiner_spec (b : BlockIndex S P.z) :
    ∃ Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' (P.slotMatching Q hC hD hC' hD' b))) ℂ,
      P.matchedIntertwiner Q hC hD hC' hD' b * Y = 1 ∧
      Y * P.matchedIntertwiner Q hC hD hC' hD' b = 1 ∧
      ∀ i, P.matchedIntertwiner Q hC hD hC' hD' b * slotTensor C b i =
        slotTensor C' (P.slotMatching Q hC hD hC' hD' b) i *
          P.matchedIntertwiner Q hC hD hC' hD' b := by
  obtain ⟨Y, hXY, hYX, hint, -, -⟩ := Classical.choose_spec
    (P.exists_intertwiner_of_matching Q hC hD hC' hD' (P.ord b) rfl
      (P.ord_slotMatching Q hC hD hC' hD' b))
  exact ⟨Y, hXY, hYX, hint⟩

/-- On `U_j` the reading map of the matched slot of `Q` is `X_j` times the reading map of the slot
of `P` (blueprint `thm:asym_uniq_different_flags`, *Two compressions with different flags*). -/
theorem leftRow_slotMatching_mulVec (b : BlockIndex S P.z) {x : B.WordModule}
    (hx : x ∈ P.matchedInter Q hC hD hC' hD' (P.ord b)) :
    Q.leftRow (P.slotMatching Q hC hD hC' hD' b) *ᵥ WordModule.toVec B x =
      P.matchedIntertwiner Q hC hD hC' hD' b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) := by
  obtain ⟨-, -, -, -, h, -⟩ := Classical.choose_spec
    (P.exists_intertwiner_of_matching Q hC hD hC' hD' (P.ord b) rfl
      (P.ord_slotMatching Q hC hD hC' hD' b))
  exact h x hx

/-- **The block permutation matrix `P_X`** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted
to both flags*): it sends the block of the slot `b` to the block of the matched slot of `Q`,
applying `X_b`. -/
noncomputable def matchingPermMatrix : Matrix (BlockSpace D' S' Q.z) (BlockSpace D S P.z) ℂ :=
  ∑ b, Matrix.blockEmbed (slotSize D') (P.slotMatching Q hC hD hC' hD' b) *
    P.matchedIntertwiner Q hC hD hC' hD' b * Matrix.blockProj (slotSize D) b

theorem matchingPermMatrix_mul_blockEmbed (b : BlockIndex S P.z) :
    P.matchingPermMatrix Q hC hD hC' hD' * Matrix.blockEmbed (slotSize D) b =
      Matrix.blockEmbed (slotSize D') (P.slotMatching Q hC hD hC' hD' b) *
        P.matchedIntertwiner Q hC hD hC' hD' b := by
  rw [matchingPermMatrix, Matrix.sum_mul, Finset.sum_eq_single b]
  · rw [Matrix.mul_assoc, Matrix.blockProj_mul_blockEmbed_self, Matrix.mul_one]
  · intro c _ hc
    rw [Matrix.mul_assoc, Matrix.blockProj_mul_blockEmbed_of_ne hc, Matrix.mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- **`P_X Γ` is `P_X` times `Γ`** (proof of blueprint `thm:asym_uniq_common_basis`, *A basis
adapted to both flags*: on `L_j ⊆ U_j` the reading of the matched slot is `X_j W_{σ(j)}` by *Two
compressions with different flags* (blueprint `thm:asym_uniq_different_flags`)). -/
theorem commonCoord'_eq_mulVec (x : B.WordModule) :
    P.commonCoord' Q hC hD hC' hD' x =
      P.matchingPermMatrix Q hC hD hC' hD' *ᵥ P.commonCoord Q hC hD hC' hD' x := by
  have h : ⨆ j, P.matchedCompl Q hC hD hC' hD' j ≤
      LinearMap.eqLocus (P.commonCoord' Q hC hD hC' hD').toLinearMap
        ((P.matchingPermMatrix Q hC hD hC' hD').mulVecLin ∘ₗ
          (P.commonCoord Q hC hD hC' hD').toLinearMap) := by
    refine iSup_le fun j y hy => ?_
    obtain ⟨b, rfl⟩ := P.ord.surjective j
    have hy' : y ∈ P.matchedCompl Q hC hD hC' hD'
        ((P.matching Q hC hD hC' hD').symm (Q.ord (P.slotMatching Q hC hD hC' hD' b))) := by
      rw [P.ord_slotMatching Q hC hD hC' hD', Equiv.symm_apply_apply]
      exact hy
    rw [LinearMap.mem_eqLocus]
    simp only [LinearEquiv.coe_coe, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    rw [P.commonCoord'_of_mem Q hC hD hC' hD' hy', P.commonCoord_of_mem Q hC hD hC' hD' hy,
      P.leftRow_slotMatching_mulVec Q hC hD hC' hD' b (P.matchedCompl_le Q hC hD hC' hD' _ hy),
      Matrix.mulVec_mulVec _ (P.matchingPermMatrix Q hC hD hC' hD'),
      P.matchingPermMatrix_mul_blockEmbed, ← Matrix.mulVec_mulVec]
  exact h (show x ∈ ⨆ j, P.matchedCompl Q hC hD hC' hD' j by
    rw [P.iSup_matchedCompl Q hC hD hC' hD']
    exact Submodule.mem_top)

/-- `P_X Γ = P_X · Γ` as matrices (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both
flags*). -/
theorem gaugeMatrix_commonGauge' :
    gaugeMatrix (P.commonGauge' Q hC hD hC' hD') =
      P.matchingPermMatrix Q hC hD hC' hD' * gaugeMatrix (P.commonGauge Q hC hD hC' hD') := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [← Matrix.mulVec_mulVec, gaugeMatrix, gaugeMatrix, LinearMap.toMatrix'_mulVec,
    LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  exact P.commonCoord'_eq_mulVec Q hC hD hC' hD' _

/-- **A basis adapted to both flags, the first factorization** (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*, `g = 𝔄 Γ`). -/
theorem gaugeMatrix_eq_unipotentFactor_mul :
    gaugeMatrix P.gauge =
      P.unipotentFactor Q hC hD hC' hD' * gaugeMatrix (P.commonGauge Q hC hD hC' hD') :=
  gaugeMatrix_eq_coordChange_mul _ _

/-- **A basis adapted to both flags, the second factorization** (blueprint
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*, `g_tilde = 𝔄_tilde P_X Γ`). -/
theorem gaugeMatrix_eq_unipotentFactor'_mul :
    gaugeMatrix Q.gauge =
      P.unipotentFactor' Q hC hD hC' hD' * P.matchingPermMatrix Q hC hD hC' hD' *
        gaugeMatrix (P.commonGauge Q hC hD hC' hD') := by
  rw [Matrix.mul_assoc, ← P.gaugeMatrix_commonGauge']
  exact gaugeMatrix_eq_coordChange_mul _ _

/-- **A basis adapted to both flags** (blueprint `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*, the factorization): `g_tilde g⁻¹ = 𝔄_tilde P_X 𝔄⁻¹`, with `𝔄` and `𝔄_tilde` block upper
triangular with identity diagonal blocks in the orders of `P` and `Q`
(`blockTriangular_unipotentFactor`, `blockDiag'_unipotentFactor` and their primed versions) and
`P_X` the block permutation matrix of the matching through the intertwiners of *Two compressions
with different flags* (blueprint `thm:asym_uniq_different_flags`). The two reductions may be onto
two different families of normal blocks of positive bond dimension, the intertwiners then going from
the blocks of the first family to the matched blocks of the second (*The asymmetric fundamental
theorem of matrix product states*, Theorem 6.5). -/
theorem gaugeMatrix_mul_gaugeMatrixInv_eq :
    gaugeMatrix Q.gauge * gaugeMatrixInv P.gauge =
      P.unipotentFactor' Q hC hD hC' hD' * P.matchingPermMatrix Q hC hD hC' hD' *
        (P.unipotentFactor Q hC hD hC' hD')⁻¹ := by
  rw [unipotentFactor, coordChange_inv, unipotentFactor', coordChange, coordChange,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (P.matchingPermMatrix Q hC hD hC' hD'),
    ← P.gaugeMatrix_commonGauge', ← Matrix.mul_assoc (gaugeMatrixInv _),
    gaugeMatrixInv_mul_gaugeMatrix, Matrix.one_mul]

/-- `P_X = (P_X Γ) Γ⁻¹`: the block permutation matrix is determined by the two changes of basis
(*The asymmetric fundamental theorem of matrix product states*, Theorem 6.5). -/
theorem matchingPermMatrix_eq_mul :
    P.matchingPermMatrix Q hC hD hC' hD' =
      gaugeMatrix (P.commonGauge' Q hC hD hC' hD') *
        gaugeMatrixInv (P.commonGauge Q hC hD hC' hD') := by
  rw [gaugeMatrix_commonGauge', Matrix.mul_assoc, gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_one]

end Matched

end MultiBlockCompression

end MPSTensor
