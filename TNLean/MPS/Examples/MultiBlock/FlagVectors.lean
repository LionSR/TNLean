/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis

/-!
# The flag of a reduction read in coordinates

Reading tools shared by the multi-block examples (*The asymmetric fundamental theorem of matrix
product states*, Examples 6.13, 6.14 and 6.16): the member `M_k` of the flag of a reduction read in
`ℂ^{D_B}`, its membership for an explicit gauge, the reading maps and injections of an explicit
gauge, a criterion for the matching of two reductions, and the data `IsAdaptedFactorization` of
*A basis adapted to both flags* with explicitly chosen complements.

## Main definitions

* `MultiBlockExamples.flagVec`: the member `M_k` of the flag, read in `ℂ^{D_B}`.
* `MultiBlockExamples.IsAdaptedFactorization`: the factorization `g = 𝔄 Γ`, `g_tilde = 𝔄' P_X Γ`.

## Main results

* `MultiBlockExamples.mem_flagVec_gaugeOfMatrix`: membership in the flag of an explicit gauge.
* `MultiBlockExamples.leftRow_gaugeOfMatrix`, `MultiBlockExamples.rightCol_gaugeOfMatrix`: the
  reading maps and injections of an explicit gauge.
* `MultiBlockExamples.matching_eq_of_flagVec_inf`: a criterion for the matching.

## References

Blueprint `prop:asym_uniq_dictionary`, *A compression is a labelled flag with an adapted basis*,
`prop:asym_uniq_matching`, *The matching*, and `thm:asym_uniq_common_basis`, *A basis adapted to
both flags*; *The asymmetric fundamental theorem of matrix product states*, Theorem 6.5.
-/

open scoped Matrix

namespace MultiBlockExamples

open MPSTensor

section FlagVectors

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}

/-- The member `M_k` of the flag of a reduction, read in `ℂ^{D_B}`. -/
noncomputable abbrev flagVec (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1)) :
    Submodule ℂ (Fin DB → ℂ) :=
  ((P.flag k).restrictScalars ℂ).map (WordModule.toVec B).toLinearMap

theorem mem_flagVec_iff (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1))
    (v : Fin DB → ℂ) :
    v ∈ flagVec P k ↔ ∀ y : BlockSpace D S P.z, k ≤ (P.ord y.1).castSucc → P.gauge v y = 0 := by
  constructor
  · intro hv y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact P.mem_flag_iff.1 hx y hy
  · intro h
    refine Submodule.mem_map.2 ⟨(WordModule.toVec B).symm v, P.mem_flag_iff.2 fun y hy => ?_, ?_⟩
    · rw [MultiBlockCompression.coord_apply, LinearEquiv.apply_symm_apply]
      exact h y hy
    · simp

theorem mem_flag_iff_toVec_mem (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1))
    (x : B.WordModule) : x ∈ P.flag k ↔ WordModule.toVec B x ∈ flagVec P k := by
  constructor
  · intro hx
    exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    rwa [← (WordModule.toVec B).injective hyx]

/-- Two subspaces of the word module are equal when their readings in `ℂ^{D_B}` are. -/
theorem eq_of_map_toVec_eq {A A' : Submodule ℂ B.WordModule}
    (h : A.map (WordModule.toVec B).toLinearMap = A'.map (WordModule.toVec B).toLinearMap) :
    A = A' :=
  Submodule.map_injective_of_injective (WordModule.toVec B).injective h

/-- Reading an intersection of invariant subspaces in `ℂ^{D_B}`. -/
theorem map_toVec_inf (A A' : Submodule (WordAlgebra d) B.WordModule) :
    ((A ⊓ A').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap =
      (A.restrictScalars ℂ).map (WordModule.toVec B).toLinearMap ⊓
        (A'.restrictScalars ℂ).map (WordModule.toVec B).toLinearMap := by
  rw [Submodule.restrictScalars_inf, Submodule.map_inf _ (WordModule.toVec B).injective]

/-- Reading a sum of invariant subspaces in `ℂ^{D_B}`. -/
theorem map_toVec_sup (A A' : Submodule (WordAlgebra d) B.WordModule) :
    ((A ⊔ A').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap =
      (A.restrictScalars ℂ).map (WordModule.toVec B).toLinearMap ⊔
        (A'.restrictScalars ℂ).map (WordModule.toVec B).toLinearMap := by
  rw [Submodule.restrictScalars_sup, Submodule.map_sup]

/-- The first member of the flag is `0`. -/
theorem flagVec_eq_bot (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1))
    (hk : k.val = 0) : flagVec P k = ⊥ := by
  obtain rfl : k = 0 := Fin.ext hk
  rw [flagVec, P.flag_zero, Submodule.restrictScalars_bot, Submodule.map_bot]

/-- The last member of the flag is the whole space. -/
theorem flagVec_eq_top (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1))
    (hk : k.val = S.card + P.z) : flagVec P k = ⊤ := by
  obtain rfl : k = Fin.last _ := Fin.ext hk
  rw [flagVec, P.flag_last, Submodule.restrictScalars_top, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (WordModule.toVec B).surjective

/-- A member of the flag is invariant under every letter. -/
theorem mulVec_mem_flagVec (P : MultiBlockCompression B S C) (k : Fin (S.card + P.z + 1))
    (i : Fin d) {v : Fin DB → ℂ} (hv : v ∈ flagVec P k) : B i *ᵥ v ∈ flagVec P k := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
  refine Submodule.mem_map.2 ⟨(WordAlgebra.ofWord [i] : WordAlgebra d) • x,
    (P.flag k).smul_mem _ hx, ?_⟩
  exact asModuleEquiv_letter_smul B i x

/-- The injection of a slot lands in the flag at the step after its position. -/
theorem rightCol_mulVec_mem_flagVec (P : MultiBlockCompression B S C) (b : BlockIndex S P.z)
    (u : Fin (slotSize D b) → ℂ) : P.rightCol b *ᵥ u ∈ flagVec P (P.ord b).succ := by
  have h := (mem_flag_iff_toVec_mem P _ _).1 (P.rightCol_mulVec_mem_flag b u)
  rwa [LinearEquiv.apply_symm_apply] at h

/-- The reading map of a slot vanishes on the flag at the position of the slot. -/
theorem leftRow_mulVec_eq_zero_of_mem_flagVec (P : MultiBlockCompression B S C)
    {b : BlockIndex S P.z} {v : Fin DB → ℂ} (hv : v ∈ flagVec P (P.ord b).castSucc) :
    P.leftRow b *ᵥ v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
  exact P.leftRow_mulVec_eq_zero_of_mem hx

/-- The reading map of a slot intertwines on the flag at the step after its position. -/
theorem leftRow_mulVec_mulVec_of_mem_flagVec (P : MultiBlockCompression B S C)
    {b : BlockIndex S P.z} (i : Fin d) {v : Fin DB → ℂ} (hv : v ∈ flagVec P (P.ord b).succ) :
    P.leftRow b *ᵥ (B i *ᵥ v) = blockOf D C i b *ᵥ (P.leftRow b *ᵥ v) := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
  exact P.leftRow_mulVec_mulVec_of_mem i hx

/-- The reading map of a slot of a reduction with an explicit gauge reads off the rows of the
gauge matrix at the coordinates of that slot. -/
theorem leftRow_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (b : BlockIndex S P.z) :
    P.leftRow b = G.submatrix (fun i => τ ⟨b, i⟩) id := by
  ext i y
  rw [MultiBlockCompression.leftRow, hgauge, gaugeMatrix_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨b, i⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockProj, Matrix.blockEmbed]
  · intro x _ hx
    rw [Matrix.blockProj, Matrix.transpose_apply, Matrix.blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨b, i⟩ : BlockSpace D S P.z)) h

/-- The injection of a slot of a reduction with an explicit gauge reads off the columns of the
inverse gauge matrix at the coordinates of that slot. -/
theorem rightCol_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (b : BlockIndex S P.z) :
    P.rightCol b = Ginv.submatrix id fun j => τ ⟨b, j⟩ := by
  ext x j
  rw [MultiBlockCompression.rightCol, hgauge, gaugeMatrixInv_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨b, j⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockEmbed]
  · intro y _ hy
    rw [Matrix.blockEmbed_apply_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (⟨b, j⟩ : BlockSpace D S P.z)) h

/-- Membership in the flag of a reduction with an explicit gauge `G`: the coordinates `G v` at
the slots of positions `≥ k` vanish. -/
theorem mem_flagVec_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (k : Fin (S.card + P.z + 1))
    (v : Fin DB → ℂ) :
    v ∈ flagVec P k ↔ ∀ y : BlockSpace D S P.z, k ≤ (P.ord y.1).castSucc → (G *ᵥ v) (τ y) = 0 := by
  rw [mem_flagVec_iff, hgauge]
  rfl

variable {κ : Type*} [DecidableEq κ] {D' : κ → ℕ} {S' : Finset κ} {C' : ∀ t, MPSTensor d (D' t)}

/-- **A criterion for the matching** (*The asymmetric fundamental theorem of matrix product states*,
Section 5): the position `k` of `P` is matched with `j` when `M_k ∩ M'_j ⊄ M_{k-1}` and
`M_k ∩ M'_{j'} ⊆ M_{k-1}` for every `j' < j`. -/
theorem matching_eq_of_flagVec_inf (P : MultiBlockCompression B S C)
    (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)
    (k : Fin (S.card + P.z)) (j : Fin (S'.card + Q.z))
    (hj : ∃ v ∈ flagVec P k.succ, v ∈ flagVec Q j.succ ∧ v ∉ flagVec P k.castSucc)
    (hlt : ∀ j' < j, ∀ v ∈ flagVec P k.succ, v ∈ flagVec Q j'.succ → v ∈ flagVec P k.castSucc) :
    P.matching Q hC hD hC' hD' k = j := by
  rw [MultiBlockCompression.matching_apply]
  refine le_antisymm (CoveringMatching.CoveringChain.jump_le_of_not_inf_le _ _ k ?_) ?_
  · obtain ⟨v, hv1, hv2, hv3⟩ := hj
    intro hle
    have hx1 : (WordModule.toVec B).symm v ∈ P.flag k.succ :=
      (mem_flag_iff_toVec_mem P _ _).2 (by rwa [LinearEquiv.apply_symm_apply])
    have hx2 : (WordModule.toVec B).symm v ∈ Q.flag j.succ :=
      (mem_flag_iff_toVec_mem Q _ _).2 (by rwa [LinearEquiv.apply_symm_apply])
    have h := (mem_flag_iff_toVec_mem P _ _).1 (hle ⟨hx1, hx2⟩)
    rw [LinearEquiv.apply_symm_apply] at h
    exact hv3 h
  · by_contra hcon
    rw [not_le] at hcon
    refine CoveringMatching.CoveringChain.not_inf_jump_succ_le (P.coveringChain hC hD)
      (Q.coveringChain hC' hD') k ?_
    intro x hx
    have h := hlt _ hcon (WordModule.toVec B x) ((mem_flag_iff_toVec_mem P _ _).1 hx.1)
      ((mem_flag_iff_toVec_mem Q _ _).1 hx.2)
    exact (mem_flag_iff_toVec_mem P _ _).2 h

/-- **The data of *A basis adapted to both flags* for two reductions onto two families with chosen
complements** (*The asymmetric fundamental theorem of matrix product states*, Theorem 6.5): `π` is
the matching read on slots, `L j` a complement of `K_j = M_{j-1} ∩ M'_{π(j)}` in
`U_j = M_j ∩ M'_{π(j)}`, `Γ` reads `x ∈ L_j` by the slot of position `j`, `X b` the intertwiner of
*Two compressions with different flags*, `𝔄`, `𝔄'` unipotent in the two orders, and `g = 𝔄 Γ`,
`g_tilde = 𝔄' P_X Γ`. The examples record their supplied complements and explicit matrix factors;
the general `unipotentFactor` construction also accepts these complements. -/
def IsAdaptedFactorization (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)
    (π : BlockIndex S P.z ≃ BlockIndex S' Q.z) (L : Fin (S.card + P.z) → Submodule ℂ B.WordModule)
    (Γ : (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (𝔄 : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
    (𝔄' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ)
    (X : ∀ b, Matrix (Fin (slotSize D' (π b))) (Fin (slotSize D b)) ℂ) : Prop :=
  (∀ b, Q.ord (π b) = P.matching Q hC hD hC' hD' (P.ord b)) ∧
  (∀ j, Disjoint
      ((P.flag j.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' j).succ).restrictScalars ℂ)
      (L j) ∧
    (P.flag j.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' j).succ).restrictScalars ℂ ⊔ L j =
      (P.flag j.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' j).succ).restrictScalars ℂ) ∧
  (∀ b, ∀ x ∈ L (P.ord b), Γ (WordModule.toVec B x) =
      Matrix.blockEmbed (slotSize D) b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) ∧
  (∀ b, (∃ Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' (π b))) ℂ,
      X b * Y = 1 ∧ Y * X b = 1) ∧
    (∀ i, X b * slotTensor C b i = slotTensor C' (π b) i * X b) ∧
    ∀ x ∈ P.flag (P.ord b).succ ⊓ Q.flag (P.matching Q hC hD hC' hD' (P.ord b)).succ,
      Q.leftRow (π b) *ᵥ WordModule.toVec B x = X b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) ∧
  (𝔄.BlockTriangular fun x => P.ord x.1) ∧ (∀ b, 𝔄.blockDiag' b = 1) ∧
  (𝔄'.BlockTriangular fun x => Q.ord x.1) ∧ (∀ b', 𝔄'.blockDiag' b' = 1) ∧
  gaugeMatrix P.gauge = 𝔄 * gaugeMatrix Γ ∧
  gaugeMatrix Q.gauge = 𝔄' * (∑ b, Matrix.blockEmbed (slotSize D') (π b) * X b *
      Matrix.blockProj (slotSize D) b) * gaugeMatrix Γ

end FlagVectors

/-- A one-dimensional subspace of `ℂⁿ` is the line through one of its nonzero vectors. -/
theorem exists_eq_span_singleton_of_finrank_eq_one {n : ℕ} (W : Submodule ℂ (Fin n → ℂ))
    (h : Module.finrank ℂ W = 1) : ∃ v : Fin n → ℂ, v ≠ 0 ∧ W = Submodule.span ℂ {v} := by
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h
  refine ⟨v, fun h0 => hv (Subtype.ext h0), le_antisymm (fun w hw => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hall ⟨w, hw⟩
    exact Submodule.mem_span_singleton.2 ⟨c, by simpa using congrArg Subtype.val hc⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 v.2
end MultiBlockExamples
