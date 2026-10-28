/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import TNLean.MPS.Examples.MultiBlock.Periodic
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis

/-!
# The running example

The tensor `B = diag(1, 2)` with one letter (lecture note AsymmetricFT, Examples 1.2, 3.4, 4.4
and 6.14; milestone V, V3.2, V3.3, V3.4) has the two one-dimensional blocks `C₁ = (1)` and
`C₂ = (2)`. Its invariant subspaces are `0`, `ℂ e₁`, `ℂ e₂`, `ℂ²`, so every reduction onto
`(C₁, C₂)` without zero block has the flag `0 ⊂ ℂ e₁ ⊂ ℂ²` and the order `(1, 2)`, or the flag
`0 ⊂ ℂ e₂ ⊂ ℂ²` and the order `(2, 1)`. The reductions with the first flag are the upper
triangular gauges `h = [[α, β], [0, δ]]`, those with the second flag the gauges
`g̃ = [[β̃, α̃], [δ̃, 0]]`. Against `g = 1` the gauge `g̃` matches block `1` with block `1` at the
other position, with scalars `λ₁ = δ̃`, `λ₂ = α̃`, and `g̃ = 𝔄̃ P_X 𝔄⁻¹` with `𝔄 = 1`.

The first section collects reading tools shared by the examples of milestone V: the flag read
in `ℂ^{D_B}`, its membership for an explicit gauge, the reading maps of an explicit gauge, and a
criterion for the matching.

## Main results

* `MultiBlockExamples.Running.V3_2a_one`, `V3_2a_h`, `V3_2a_conj`, `V3_2b`, `V3_2c`,
  `V3_2d_invariant`, `V3_2d_reductions`, `V3_2d_both`: milestone V, V3.2.
* `MultiBlockExamples.Running.V3_3a`, `V3_3a_converse`, `V3_3b`, `V3_3b_converse`, `V3_3c`,
  `V3_3d`: V3.3.
* `MultiBlockExamples.Running.V3_4a`, `V3_4b`: V3.4.

## References

Lecture note AsymmetricFT, Examples 1.2, 3.4, 4.4, 6.14; milestone V, V3.2-V3.4.
-/

open scoped Matrix

namespace MultiBlockExamples

open MPSTensor

section Tools

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι}
  {C : ∀ s, MPSTensor d (D s)} {B : MPSTensor d DB}

/-- The member `M_k` of the flag of a reduction, read in `ℂ^{D_B}` (milestone V, Section 3). -/
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

/-- **A criterion for the matching** (lecture note AsymmetricFT, Section 5; milestone V,
Section 3): the position `k` of `P` is matched with `j` when `M_k ∩ M'_j ⊄ M_{k-1}` and
`M_k ∩ M'_{j'} ⊆ M_{k-1}` for every `j' < j`. -/
theorem matching_eq_of (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
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

/-- **The data of Theorem E for two reductions onto two families with chosen complements**
(lecture note AsymmetricFT, Theorem 6.5; milestone V, Section 3): `π` is the matching read on
slots, `L j` a complement of `K_j = M_{j-1} ∩ M'_{π(j)}` in `U_j = M_j ∩ M'_{π(j)}`, `Γ` reads
`x ∈ L_j` by the slot of position `j`, `X b` the intertwiner of Theorem C, `𝔄`, `𝔄'` unipotent in
the two orders, and `g = 𝔄 Γ`, `g̃ = 𝔄' P_X Γ`. The examples choose the complements explicitly,
which the library's `unipotentFactor` (a choice of complements) does not allow. -/
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

end Tools

/-- A one-dimensional subspace of `ℂⁿ` is the line through one of its nonzero vectors. -/
theorem exists_eq_span_singleton_of_finrank_eq_one {n : ℕ} (W : Submodule ℂ (Fin n → ℂ))
    (h : Module.finrank ℂ W = 1) : ∃ v : Fin n → ℂ, v ≠ 0 ∧ W = Submodule.span ℂ {v} := by
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h
  refine ⟨v, fun h0 => hv (Subtype.ext h0), le_antisymm (fun w hw => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hall ⟨w, hw⟩
    exact Submodule.mem_span_singleton.2 ⟨c, by simpa using congrArg Subtype.val hc⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 v.2

namespace Running

/-- **The running example** `B = diag(1, 2)`, one letter (lecture note AsymmetricFT,
Example 1.2; milestone V, V3.2). -/
noncomputable def tensorB : MPSTensor 1 2 := fun _ => !![1, 0; 0, 2]

/-- Labels of the two blocks. -/
abbrev labels : Finset (Fin 2) := Finset.univ

/-- Both blocks are one-dimensional. -/
abbrev dims : Fin 2 → ℕ := fun _ => 1

/-- The blocks `C₁ = (1)`, `C₂ = (2)` (labels `0`, `1`). -/
noncomputable def blocks : ∀ s : Fin 2, MPSTensor 1 (dims s) := fun s _ => !![(s.val + 1 : ℂ)]

/-- The slot of `C₁`. -/
abbrev slot0 : {s // s ∈ labels} := ⟨0, Finset.mem_univ _⟩

/-- The slot of `C₂`. -/
abbrev slot1 : {s // s ∈ labels} := ⟨1, Finset.mem_univ _⟩

/-- The order `(1, 2)`. -/
def ord12 : BlockIndex labels 0 ≃ Fin 2 where
  toFun
    | Sum.inl s => s.1
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨n, Finset.mem_univ n⟩
  left_inv := by decide
  right_inv := by decide

/-- The order `(2, 1)`. -/
def ord21 : BlockIndex labels 0 ≃ Fin 2 where
  toFun
    | Sum.inl s => 1 - s.1
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨1 - n, Finset.mem_univ _⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates in the order `(1, 2)`. -/
def tau12 : BlockSpace dims labels 0 ≃ Fin 2 where
  toFun x := ord12 x.1
  invFun n := ⟨Sum.inl ⟨n, Finset.mem_univ n⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The bond coordinates in the order `(2, 1)`. -/
def tau21 : BlockSpace dims labels 0 ≃ Fin 2 where
  toFun x := ord21 x.1
  invFun n := ⟨Sum.inl ⟨1 - n, Finset.mem_univ _⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

theorem tensorB_apply (i : Fin 1) : tensorB i = !![1, 0; 0, 2] := rfl

/-- A reduction of the running example from an explicit complex gauge `G` (lecture note
AsymmetricFT, Definition 1.1): `G B G⁻¹` is upper triangular with the block of the slot at
position `p` on the diagonal entry `p`. -/
noncomputable def red (ord : BlockIndex labels 0 ≃ Fin 2) (τ : BlockSpace dims labels 0 ≃ Fin 2)
    (hτ : ∀ x, τ x = ord x.1) (G Ginv : Matrix (Fin 2) (Fin 2) ℂ) (hG : G * Ginv = 1)
    (hG' : Ginv * G = 1) (h10 : (G * tensorB 0 * Ginv) 1 0 = 0)
    (hdiag : ∀ s : {s // s ∈ labels},
      (G * tensorB 0 * Ginv) (ord (Sum.inl s)) (ord (Sum.inl s)) = s.1.val + 1) :
    MultiBlockCompression tensorB labels blocks where
  z := 0
  ord := ord
  gauge := gaugeOfMatrix τ G Ginv hG hG'
  triangular i x y hxy := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hτ, hτ]
    have key : ∀ a b : Fin 2, b < a → (G * tensorB 0 * Ginv) a b = 0 := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | exact h10
    exact key _ _ hxy
  matched i s := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hτ]
    simpa [blocks] using hdiag s
  unmatched _ t := t.elim0

section RedMaps

variable (ord : BlockIndex labels 0 ≃ Fin 2) (τ : BlockSpace dims labels 0 ≃ Fin 2)
  (hτ : ∀ x, τ x = ord x.1) (G Ginv : Matrix (Fin 2) (Fin 2) ℂ) (hG : G * Ginv = 1)
  (hG' : Ginv * G = 1) (h10 : (G * tensorB 0 * Ginv) 1 0 = 0)
  (hdiag : ∀ s : {s // s ∈ labels},
    (G * tensorB 0 * Ginv) (ord (Sum.inl s)) (ord (Sum.inl s)) = s.1.val + 1)

theorem red_z : (red ord τ hτ G Ginv hG hG' h10 hdiag).z = 0 := rfl

theorem red_left (s : {s // s ∈ labels}) :
    (red ord τ hτ G Ginv hG hG' h10 hdiag).left s =
      Matrix.of fun (_ : Fin 1) j => G (ord (Sum.inl s)) j := by
  rw [MultiBlockCompression.left_gaugeOfMatrix _ (τ := τ) (hG := hG) (hG' := hG') rfl s]
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
  exact congrArg (fun r => G r j) (hτ ⟨Sum.inl s, 0⟩)

theorem red_right (s : {s // s ∈ labels}) :
    (red ord τ hτ G Ginv hG hG' h10 hdiag).right s =
      Matrix.of fun i (_ : Fin 1) => Ginv i (ord (Sum.inl s)) := by
  rw [MultiBlockCompression.right_gaugeOfMatrix _ (τ := τ) (hG := hG) (hG' := hG') rfl s]
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
  exact congrArg (fun c => Ginv i c) (hτ ⟨Sum.inl s, 0⟩)

end RedMaps

theorem hτ12 : ∀ x, tau12 x = ord12 x.1 := fun _ => rfl

theorem hτ21 : ∀ x, tau21 x = ord21 x.1 := fun _ => rfl

/-- The gauge `h = [[α, β], [0, δ]]` and its inverse. -/
theorem upper_mul_inv {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![α, β; 0, δ] * !![α⁻¹, -β / (α * δ); 0, δ⁻¹] = 1 ∧
      !![α⁻¹, -β / (α * δ); 0, δ⁻¹] * !![α, β; 0, δ] = 1 := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, mul_zero, zero_mul, add_zero, zero_add] <;>
    (try field_simp) <;> ring_nf

/-- The gauge `g̃ = [[β̃, α̃], [δ̃, 0]]` and its inverse. -/
theorem swap_mul_inv {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![β, α; δ, 0] * !![0, δ⁻¹; α⁻¹, -β / (α * δ)] = 1 ∧
      !![0, δ⁻¹; α⁻¹, -β / (α * δ)] * !![β, α; δ, 0] = 1 := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero,
      not_false_eq_true, mul_zero, zero_mul, add_zero, zero_add] <;>
    (try field_simp) <;> ring_nf

/-- The conjugated letter of the upper triangular gauge. -/
theorem upper_conj {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![α, β; 0, δ] * tensorB 0 * !![α⁻¹, -β / (α * δ); 0, δ⁻¹] = !![1, β / δ; 0, 2] := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring

/-- The conjugated letter of the swapped gauge. -/
theorem swap_conj {α β δ : ℂ} (h : α * δ ≠ 0) :
    !![β, α; δ, 0] * tensorB 0 * !![0, δ⁻¹; α⁻¹, -β / (α * δ)] = !![2, -β / δ; 0, 1] := by
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring

/-- The reduction `h = [[α, β], [0, δ]]` in the order `(1, 2)` (lecture note AsymmetricFT,
Example 6.14, (6.14); milestone V, V3.3(a)). -/
noncomputable def redUpper (α β δ : ℂ) (h : α * δ ≠ 0) :
    MultiBlockCompression tensorB labels blocks :=
  red ord12 tau12 hτ12 !![α, β; 0, δ] !![α⁻¹, -β / (α * δ); 0, δ⁻¹] (upper_mul_inv h).1
    (upper_mul_inv h).2 (by rw [upper_conj h]; simp)
    (fun s => by
      rw [upper_conj h]
      obtain ⟨s, hs⟩ := s
      fin_cases s <;> simp [ord12]
      norm_num)

/-- The reduction `g̃ = [[β̃, α̃], [δ̃, 0]]` in the order `(2, 1)` (lecture note AsymmetricFT,
Example 6.14, (6.15); milestone V, V3.3(b)). -/
noncomputable def redSwap (α β δ : ℂ) (h : α * δ ≠ 0) :
    MultiBlockCompression tensorB labels blocks :=
  red ord21 tau21 hτ21 !![β, α; δ, 0] !![0, δ⁻¹; α⁻¹, -β / (α * δ)] (swap_mul_inv h).1
    (swap_mul_inv h).2 (by rw [swap_conj h]; simp)
    (fun s => by
      rw [swap_conj h]
      obtain ⟨s, hs⟩ := s
      fin_cases s <;> simp [ord21]
      norm_num)

/-! ### V3.2 -/

/-- **V3.2(a)** (lecture note AsymmetricFT, Examples 1.2 and 3.4; milestone V, V3.2(a)): `g = 1`
is a reduction in the order `(1, 2)`, with `W₁ = (1, 0)`, `W₂ = (0, 1)`. -/
theorem V3_2a_one : ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
    P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
    P.left slot0 = !![1, 0] ∧ P.left slot1 = !![0, 1] := by
  refine ⟨redUpper 1 0 1 (by norm_num), rfl, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]

/-- **V3.2(a)** (lecture note AsymmetricFT, Examples 1.2 and 3.4; milestone V, V3.2(a)):
`g̃ = h = [[1, 1], [0, 1]]` is a reduction in the order `(1, 2)` with `W̃₁ = (1, 1)`,
`W̃₂ = (0, 1)`, `Ṽ₁ = e₁`, `Ṽ₂ = (-1, 1)ᵀ`. -/
theorem V3_2a_h : ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
    P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
    P.left slot0 = !![1, 1] ∧ P.left slot1 = !![0, 1] ∧
    P.right slot0 = !![1; 0] ∧ P.right slot1 = !![-1; 1] := by
  refine ⟨redUpper 1 1 1 (by norm_num), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]

/-- **V3.2(a)** (lecture note AsymmetricFT, Example 3.4; milestone V, V3.2(a)):
`h B h⁻¹ = [[1, 1], [0, 2]]`. -/
theorem V3_2a_conj : !![(1 : ℂ), 1; 0, 1] * tensorB 0 * !![1, -1; 0, 1] = !![1, 1; 0, 2] := by
  rw [tensorB_apply, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem tensorB_pow (n : ℕ) : tensorB 0 ^ n = !![1, 0; 0, (2 : ℂ) ^ n] := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_fin_two]; simp
  | succ n ih =>
    rw [pow_succ, ih, tensorB_apply, Matrix.mul_fin_two]
    simp [pow_succ]

/-- **V3.2(b)** (lecture note AsymmetricFT, Example 3.4; milestone V, V3.2(b)): `W₁ Bⁿ = (1, 0)`
and `W̃₁ Bⁿ = (1, 2ⁿ)` for every `n ≥ 0`, and these are never proportional. -/
theorem V3_2b (n : ℕ) :
    !![(1 : ℂ), 0] * tensorB 0 ^ n = !![1, 0] ∧ !![(1 : ℂ), 1] * tensorB 0 ^ n = !![1, 2 ^ n] ∧
    ¬ ∃ c : ℂ, !![(1 : ℂ), 1] * tensorB 0 ^ n = c • (!![(1 : ℂ), 0] * tensorB 0 ^ n) := by
  have h1 : !![(1 : ℂ), 0] * tensorB 0 ^ n = !![1, 0] := by
    rw [tensorB_pow]; ext i j; fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]
  have h2 : !![(1 : ℂ), 1] * tensorB 0 ^ n = !![1, 2 ^ n] := by
    rw [tensorB_pow]; ext i j; fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]
  refine ⟨h1, h2, ?_⟩
  rintro ⟨c, hc⟩
  rw [h1, h2] at hc
  have := congrFun (congrFun hc 0) 1
  simp at this

/-- **V3.2(c)** (lecture note AsymmetricFT, Example 1.2; milestone V, V3.2(c)): the remainder
`B - V₁ C₁ W₁ = diag(0, 2)` has no vanishing power. -/
theorem V3_2c :
    tensorB 0 - !![(1 : ℂ); 0] * blocks 0 0 * !![(1 : ℂ), 0] = !![0, 0; 0, 2] ∧
    ∀ n : ℕ, (!![(0 : ℂ), 0; 0, 2]) ^ n ≠ 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [tensorB_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [blocks]
  · have hpow : ∀ m : ℕ, ((!![(0 : ℂ), 0; 0, 2]) ^ m) 1 1 = 2 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, ih]
        simp [pow_succ]
    have := hpow n
    rw [hn] at this
    exact absurd this.symm (pow_ne_zero _ two_ne_zero)

/-- The line `ℂ e₁` is invariant. -/
theorem isInvariant_span_e0 : Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {e 0}) :=
  (isInvariantSubmodule_span_singleton_iff _ _).2 fun i =>
    ⟨1, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct]⟩

/-- The line `ℂ e₂` is invariant. -/
theorem isInvariant_span_e1 : Matrix.IsInvariantSubmodule tensorB (Submodule.span ℂ {e 1}) :=
  (isInvariantSubmodule_span_singleton_iff _ _).2 fun i =>
    ⟨2, by ext j; fin_cases j <;> simp [tensorB, Matrix.mulVec, dotProduct]⟩

/-- **V3.2(d)** (lecture note AsymmetricFT, Example 3.4; milestone V, V3.2(d)): the subspaces
invariant under `B` are `0`, `ℂ e₁`, `ℂ e₂`, `ℂ²`. -/
theorem V3_2d_invariant (W : Submodule ℂ (Fin 2 → ℂ)) :
    Matrix.IsInvariantSubmodule tensorB W ↔
      W = ⊥ ∨ W = Submodule.span ℂ {e 0} ∨ W = Submodule.span ℂ {e 1} ∨ W = ⊤ := by
  constructor
  · intro hW
    have hle : Module.finrank ℂ W ≤ 2 := by
      simpa using Submodule.finrank_le W
    interval_cases h : Module.finrank ℂ W
    · exact Or.inl (Submodule.finrank_eq_zero.1 h)
    · obtain ⟨v, hv, rfl⟩ := exists_eq_span_singleton_of_finrank_eq_one W h
      obtain ⟨c, hc⟩ := (isInvariantSubmodule_span_singleton_iff _ _).1 hW 0
      have a0 : v 0 = c * v 0 := by
        simpa [tensorB, Matrix.mulVec, dotProduct] using congrFun hc 0
      have a1 : 2 * v 1 = c * v 1 := by
        simpa [tensorB, Matrix.mulVec, dotProduct] using congrFun hc 1
      by_cases hv0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [hv0, h1])
        refine Or.inr (Or.inr (Or.inl (span_singleton_eq_of_eq_smul hv1 ?_)))
        ext i; fin_cases i <;> simp [hv0]
      · have hc : c = 1 := by
          have h' : (c - 1) * v 0 = 0 := by linear_combination -a0
          exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv0)
        have hv1 : v 1 = 0 := by
          rw [hc] at a1
          linear_combination a1
        refine Or.inr (Or.inl (span_singleton_eq_of_eq_smul hv0 ?_))
        ext i; fin_cases i <;> simp [hv1]
    · refine Or.inr (Or.inr (Or.inr (Submodule.eq_top_of_finrank_eq ?_)))
      simpa using h
  · rintro (rfl | rfl | rfl | rfl)
    · intro i v hv
      rw [Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact isInvariant_span_e0
    · exact isInvariant_span_e1
    · intro i v _
      exact Submodule.mem_top

/-- The member `M₁` of the flag of a reduction whose positions `0`, `1` carry the slots `s`, `s'`
is the eigenline `ℂ e_s` of the block `C_s`. -/
theorem flagVec_eq_of_ord (P : MultiBlockCompression tensorB labels blocks)
    (s s' : {s // s ∈ labels}) (hs : (P.ord (Sum.inl s)).val = 0)
    (hs' : (P.ord (Sum.inl s')).val = 1) (k : Fin (labels.card + P.z + 1)) (hk : k.val = 1) :
    flagVec P k = Submodule.span ℂ {e s.1} := by
  have hks : (P.ord (Sum.inl s)).succ = k := Fin.ext (by rw [Fin.val_succ, hs, hk])
  have hks' : (P.ord (Sum.inl s')).castSucc = k := Fin.ext (by rw [Fin.val_castSucc, hs', hk])
  set u := P.rightCol (Sum.inl s) *ᵥ (fun _ => (1 : ℂ)) with hu_def
  have hu : u ∈ flagVec P k := hks ▸ rightCol_mulVec_mem_flagVec P (Sum.inl s) _
  have hWu : P.leftRow (Sum.inl s) *ᵥ u = fun _ => 1 := by
    rw [hu_def, Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec]
  have hu0 : u ≠ 0 := fun h0 => by
    have := congrFun hWu 0
    rw [h0, Matrix.mulVec_zero] at this
    simp at this
  have hu' : P.rightCol (Sum.inl s') *ᵥ (fun _ => (1 : ℂ)) ∉ flagVec P k := fun hin => by
    have h0 := leftRow_mulVec_eq_zero_of_mem_flagVec P (b := Sum.inl s') (hks'.symm ▸ hin)
    rw [Matrix.mulVec_mulVec, P.leftRow_mul_rightCol_self, Matrix.one_mulVec] at h0
    simpa using congrFun h0 0
  have hinv : Matrix.IsInvariantSubmodule tensorB (flagVec P k) :=
    fun i v hv => mulVec_mem_flagVec P k i hv
  have heig : ∀ j : Fin 2, flagVec P k = Submodule.span ℂ {e j} → j = s.1 := by
    intro j hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hj ▸ hu)
    have hBu : tensorB 0 *ᵥ u = ((j.val : ℂ) + 1) • u := by
      rw [← ha]
      ext i; fin_cases i <;> fin_cases j <;>
        simp only [tensorB, Matrix.mulVec, dotProduct, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
          Matrix.cons_val_one, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero, zero_mul, one_mul, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          CharP.cast_eq_zero, Nat.cast_one, zero_ne_one, one_ne_zero, mul_eq_mul_right_iff]
      first | ring1 | (left; norm_num)
    have hW := leftRow_mulVec_mulVec_of_mem_flagVec P (b := Sum.inl s) 0 (hks.symm ▸ hu)
    rw [hBu, Matrix.mulVec_smul, hWu] at hW
    have h0 : (j.val : ℂ) + 1 = (s.1.val : ℂ) + 1 := by
      have := congrFun hW 0
      simpa [blockOf, blocks, Matrix.mulVec, dotProduct] using this
    have : (j.val : ℂ) = s.1.val := by linear_combination h0
    exact Fin.ext (by exact_mod_cast this)
  rcases (V3_2d_invariant _).1 hinv with h | h | h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hu)) hu0
  · rw [h, heig 0 h]
  · rw [h, heig 1 h]
  · exact absurd (h ▸ Submodule.mem_top) hu'

/-- **V3.2(d)** (lecture note AsymmetricFT, Example 3.4; milestone V, V3.2(d)): a reduction
without zero block has the flag `0 ⊂ ℂ e₁ ⊂ ℂ²` and the order `(1, 2)`, or the flag
`0 ⊂ ℂ e₂ ⊂ ℂ²` and the order `(2, 1)`. -/
theorem V3_2d_reductions (P : MultiBlockCompression tensorB labels blocks) (hz : P.z = 0) :
    (P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
      ∀ k : Fin (labels.card + P.z + 1), k.val = 1 → flagVec P k = Submodule.span ℂ {e 0}) ∨
    (P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) ∧
      ∀ k : Fin (labels.card + P.z + 1), k.val = 1 → flagVec P k = Submodule.span ℂ {e 1}) := by
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h0 : (P.ord (Sum.inl slot0)).val < 2 := lt_of_lt_of_eq (P.ord _).isLt hn
  have h1 : (P.ord (Sum.inl slot1)).val < 2 := lt_of_lt_of_eq (P.ord _).isLt hn
  have hne : (P.ord (Sum.inl slot0)).val ≠ (P.ord (Sum.inl slot1)).val := fun h =>
    absurd (P.ord.injective (Fin.ext h)) (by simp)
  rcases (show (P.ord (Sum.inl slot0)).val = 0 ∧ (P.ord (Sum.inl slot1)).val = 1 ∨
      (P.ord (Sum.inl slot0)).val = 1 ∧ (P.ord (Sum.inl slot1)).val = 0 by omega) with
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨Fin.lt_def.2 (by omega), fun k hk => flagVec_eq_of_ord P slot0 slot1 ha hb k hk⟩
  · exact Or.inr ⟨Fin.lt_def.2 (by omega), fun k hk => flagVec_eq_of_ord P slot1 slot0 hb ha k hk⟩

/-- **V3.2(d)** (lecture note AsymmetricFT, Example 3.4; milestone V, V3.2(d)): both cases
occur. -/
theorem V3_2d_both :
    (∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1)) ∧
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) := by
  refine ⟨⟨redUpper 1 0 1 (by norm_num), rfl, ?_⟩, ⟨redSwap 1 0 1 (by norm_num), rfl, ?_⟩⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · change ord21 (Sum.inl slot1) < ord21 (Sum.inl slot0)
    decide

/-! ### V3.3(a), (b) -/

/-- A vector read as zero by both reading maps of a reduction without zero block is zero. -/
theorem eq_zero_of_left_mulVec_eq_zero (P : MultiBlockCompression tensorB labels blocks)
    (hz : P.z = 0) {v : Fin 2 → ℂ} (h : ∀ s, P.left s *ᵥ v = 0) : v = 0 := by
  have hg : P.gauge v = 0 := by
    funext y
    obtain ⟨b, j⟩ := y
    rcases b with s | t
    · have := congrFun (h s) j
      rw [← MultiBlockCompression.leftRow_inl, MultiBlockCompression.leftRow_mulVec] at this
      exact this
    · exact absurd t.isLt (by omega)
  exact P.gauge.map_eq_zero_iff.1 hg

theorem left_mulVec_e (P : MultiBlockCompression tensorB labels blocks) (s : {s // s ∈ labels})
    (j : Fin 2) : (P.left s *ᵥ e j) 0 = P.left s 0 j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The entry of `W_s V_s = 1`. -/
theorem left_mul_right_apply (P : MultiBlockCompression tensorB labels blocks)
    (s : {s // s ∈ labels}) :
    P.left s 0 0 * P.right s 0 0 + P.left s 0 1 * P.right s 1 0 = 1 := by
  have := congrFun (congrFun (P.left_mul_right_self s) 0) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

/-- **V3.3(a)** (lecture note AsymmetricFT, Example 6.14, (6.14); milestone V, V3.3(a)):
`h = [[α, β], [0, δ]]` with `αδ ≠ 0` is a reduction in the order `(1, 2)`, with
`W₁ = (α, β)`, `W₂ = (0, δ)`, `V₁ = (α⁻¹, 0)ᵀ`, `V₂ = (-β/(αδ), δ⁻¹)ᵀ`. -/
theorem V3_3a (α β δ : ℂ) (h : α * δ ≠ 0) :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1) ∧
      P.left slot0 = !![α, β] ∧ P.left slot1 = !![0, δ] ∧
      P.right slot0 = !![α⁻¹; 0] ∧ P.right slot1 = !![-β / (α * δ); δ⁻¹] := by
  refine ⟨redUpper α β δ h, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord12 (Sum.inl slot0) < ord12 (Sum.inl slot1)
    decide
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]

/-- **V3.3(a), converse** (lecture note AsymmetricFT, Example 6.14; milestone V, V3.3(a)): every
reduction with the first flag (no zero block, order `(1, 2)`) has `W₁ = (α, β)`, `W₂ = (0, δ)`
with `αδ ≠ 0`, that is the gauge `[[α, β], [0, δ]]`. -/
theorem V3_3a_converse (P : MultiBlockCompression tensorB labels blocks) (hz : P.z = 0)
    (hord : P.ord (Sum.inl slot0) < P.ord (Sum.inl slot1)) :
    ∃ α β δ : ℂ, α * δ ≠ 0 ∧ P.left slot0 = !![α, β] ∧ P.left slot1 = !![0, δ] := by
  have hflag : ∀ k : Fin (labels.card + P.z + 1), k.val = 1 →
      flagVec P k = Submodule.span ℂ {e 0} := by
    rcases V3_2d_reductions P hz with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hord (lt_asymm h)
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h1 : (P.ord (Sum.inl slot1)).val = 1 := by
    have := lt_of_lt_of_eq (P.ord (Sum.inl slot1)).isLt hn
    have := Fin.lt_def.1 hord
    omega
  have hW : P.left slot1 *ᵥ e 0 = 0 := by
    rw [← MultiBlockCompression.leftRow_inl]
    refine leftRow_mulVec_eq_zero_of_mem_flagVec P ?_
    rw [hflag _ (by rw [Fin.val_castSucc]; exact h1)]
    exact Submodule.mem_span_singleton_self _
  have h10 : P.left slot1 0 0 = 0 := by rw [← left_mulVec_e, hW]; rfl
  refine ⟨P.left slot0 0 0, P.left slot0 0 1, P.left slot1 0 1, mul_ne_zero ?_ ?_, ?_, ?_⟩
  · intro hα
    refine absurd (eq_zero_of_left_mulVec_eq_zero P hz (v := e 0) fun s => ?_) (by simp)
    obtain ⟨s, hs⟩ := s
    ext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    fin_cases s
    · rw [left_mulVec_e]; exact hα
    · rw [left_mulVec_e]; exact h10
  · intro hδ
    have := left_mul_right_apply P slot1
    rw [h10, hδ] at this
    simp at this
  · ext i j; fin_cases i; fin_cases j <;> rfl
  · ext i j; fin_cases i; fin_cases j
    · exact h10
    · rfl

/-- **V3.3(b)** (lecture note AsymmetricFT, Example 6.14, (6.15); milestone V, V3.3(b)):
`g̃ = [[β̃, α̃], [δ̃, 0]]` with `α̃δ̃ ≠ 0` is a reduction in the order `(2, 1)`, with
`W̃₂ = (β̃, α̃)`, `W̃₁ = (δ̃, 0)`, `Ṽ₂ = (0, α̃⁻¹)ᵀ`, `Ṽ₁ = (δ̃⁻¹, -β̃/(α̃δ̃))ᵀ`. -/
theorem V3_3b (α β δ : ℂ) (h : α * δ ≠ 0) :
    ∃ P : MultiBlockCompression tensorB labels blocks, P.z = 0 ∧
      P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0) ∧
      P.left slot1 = !![β, α] ∧ P.left slot0 = !![δ, 0] ∧
      P.right slot1 = !![0; α⁻¹] ∧ P.right slot0 = !![δ⁻¹; -β / (α * δ)] := by
  refine ⟨redSwap α β δ h, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ord21 (Sum.inl slot1) < ord21 (Sum.inl slot0)
    decide
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]

/-- **V3.3(b), converse** (lecture note AsymmetricFT, Example 6.14; milestone V, V3.3(b)): every
reduction with the second flag (no zero block, order `(2, 1)`) has `W̃₂ = (β̃, α̃)`,
`W̃₁ = (δ̃, 0)` with `α̃δ̃ ≠ 0`, that is the gauge `[[β̃, α̃], [δ̃, 0]]`. -/
theorem V3_3b_converse (P : MultiBlockCompression tensorB labels blocks) (hz : P.z = 0)
    (hord : P.ord (Sum.inl slot1) < P.ord (Sum.inl slot0)) :
    ∃ α β δ : ℂ, α * δ ≠ 0 ∧ P.left slot1 = !![β, α] ∧ P.left slot0 = !![δ, 0] := by
  have hflag : ∀ k : Fin (labels.card + P.z + 1), k.val = 1 →
      flagVec P k = Submodule.span ℂ {e 1} := by
    rcases V3_2d_reductions P hz with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd hord (lt_asymm h)
    · exact h
  have hn : labels.card + P.z = 2 := by rw [hz]; rfl
  have h0 : (P.ord (Sum.inl slot0)).val = 1 := by
    have := lt_of_lt_of_eq (P.ord (Sum.inl slot0)).isLt hn
    have := Fin.lt_def.1 hord
    omega
  have hW : P.left slot0 *ᵥ e 1 = 0 := by
    rw [← MultiBlockCompression.leftRow_inl]
    refine leftRow_mulVec_eq_zero_of_mem_flagVec P ?_
    rw [hflag _ (by rw [Fin.val_castSucc]; exact h0)]
    exact Submodule.mem_span_singleton_self _
  have h01 : P.left slot0 0 1 = 0 := by rw [← left_mulVec_e, hW]; rfl
  refine ⟨P.left slot1 0 1, P.left slot1 0 0, P.left slot0 0 0, mul_ne_zero ?_ ?_, ?_, ?_⟩
  · intro hα
    refine absurd (eq_zero_of_left_mulVec_eq_zero P hz (v := e 1) fun s => ?_) (by simp)
    obtain ⟨s, hs⟩ := s
    ext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    fin_cases s
    · rw [left_mulVec_e]; exact h01
    · rw [left_mulVec_e]; exact hα
  · intro hδ
    have := left_mul_right_apply P slot0
    rw [h01, hδ] at this
    simp at this
  · ext i j; fin_cases i; fin_cases j <;> rfl
  · ext i j; fin_cases i; fin_cases j
    · rfl
    · exact h01

/-! ### V3.3(c) -/

/-- The blocks `(1)`, `(2)` are normal. -/
theorem isNormal_blocks : ∀ s ∈ labels, Kraus.IsNormal (blocks s) := by
  intro s _
  refine Kraus.IsInjective.isNormal (Submodule.eq_top_of_forall_single_mem _ fun x y => ?_)
  obtain rfl : x = 0 := Subsingleton.elim x 0
  obtain rfl : y = 0 := Subsingleton.elim y 0
  have hs : ((s.val : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero s.val
  have h1 : Matrix.single (0 : Fin 1) (0 : Fin 1) (1 : ℂ) = ((s.val : ℂ) + 1)⁻¹ • blocks s 0 := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [blocks, hs]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

theorem dims_pos : ∀ s ∈ labels, 0 < dims s := fun _ _ => Nat.one_pos

theorem redUpper_spec (α β δ : ℂ) (h : α * δ ≠ 0) :
    (redUpper α β δ h).left slot0 = !![α, β] ∧ (redUpper α β δ h).left slot1 = !![0, δ] ∧
      (redUpper α β δ h).right slot0 = !![α⁻¹; 0] ∧
      (redUpper α β δ h).right slot1 = !![-β / (α * δ); δ⁻¹] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]
  · rw [redUpper, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord12]

theorem redSwap_spec (α β δ : ℂ) (h : α * δ ≠ 0) :
    (redSwap α β δ h).left slot1 = !![β, α] ∧ (redSwap α β δ h).left slot0 = !![δ, 0] ∧
      (redSwap α β δ h).right slot1 = !![0; α⁻¹] ∧
      (redSwap α β δ h).right slot0 = !![δ⁻¹; -β / (α * δ)] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_left]
    ext i j; fin_cases i; fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]
  · rw [redSwap, red_right]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ord21]

theorem flagVec_redUpper (α β δ : ℂ) (h : α * δ ≠ 0)
    (k : Fin (labels.card + (redUpper α β δ h).z + 1)) (hk : k.val = 1) :
    flagVec (redUpper α β δ h) k = Submodule.span ℂ {e 0} :=
  flagVec_eq_of_ord _ slot0 slot1 rfl rfl k hk

theorem flagVec_redSwap (α β δ : ℂ) (h : α * δ ≠ 0)
    (k : Fin (labels.card + (redSwap α β δ h).z + 1)) (hk : k.val = 1) :
    flagVec (redSwap α β δ h) k = Submodule.span ℂ {e 1} :=
  flagVec_eq_of_ord _ slot1 slot0 rfl rfl k hk

theorem eq_zero_of_mem_span_e0_of_mem_span_e1 {v : Fin 2 → ℂ}
    (h0 : v ∈ Submodule.span ℂ {e 0}) (h1 : v ∈ Submodule.span ℂ {e 1}) : v = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h0
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h1
  have := congrFun hb 0
  simp only [Fin.isValue, Pi.smul_apply, ne_eq, zero_ne_one, not_false_eq_true,
    Pi.single_eq_of_ne, smul_eq_mul, mul_zero, Pi.single_eq_same, mul_one] at this
  rw [← this, zero_smul]

/-- The reduction `g = 1`. -/
noncomputable abbrev gOne : MultiBlockCompression tensorB labels blocks :=
  redUpper 1 0 1 (by norm_num)

theorem matching_slot0 (α β δ : ℂ) (h : α * δ ≠ 0) :
    gOne.matching (redSwap α β δ h) isNormal_blocks dims_pos isNormal_blocks dims_pos
      (gOne.ord (Sum.inl slot0)) = (redSwap α β δ h).ord (Sum.inl slot0) := by
  refine matching_eq_of _ _ _ _ _ _ _ _ ⟨e 0, ?_, ?_, ?_⟩ ?_
  · rw [flagVec_redUpper _ _ _ _ _ rfl]; exact Submodule.mem_span_singleton_self _
  · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
  · rw [flagVec_eq_bot _ _ rfl]; simp
  · intro j hj v hv1 hv2
    have hj0 : j.val = 0 := by
      have := Fin.lt_def.1 hj
      have h1 : ((redSwap α β δ h).ord (Sum.inl slot0)).val = 1 := rfl
      omega
    rw [flagVec_redUpper _ _ _ _ _ rfl] at hv1
    rw [flagVec_redSwap _ _ _ _ _ (by rw [Fin.val_succ, hj0])] at hv2
    rw [eq_zero_of_mem_span_e0_of_mem_span_e1 hv1 hv2]
    exact Submodule.zero_mem _

theorem matching_slot1 (α β δ : ℂ) (h : α * δ ≠ 0) :
    gOne.matching (redSwap α β δ h) isNormal_blocks dims_pos isNormal_blocks dims_pos
      (gOne.ord (Sum.inl slot1)) = (redSwap α β δ h).ord (Sum.inl slot1) := by
  refine matching_eq_of _ _ _ _ _ _ _ _ ⟨e 1, ?_, ?_, ?_⟩ ?_
  · rw [flagVec_eq_top _ _ rfl]; exact Submodule.mem_top
  · rw [flagVec_redSwap _ _ _ _ _ rfl]; exact Submodule.mem_span_singleton_self _
  · rw [flagVec_redUpper _ _ _ _ _ rfl]
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrFun ha 1
    simp at this
  · intro j hj
    exfalso
    have := Fin.lt_def.1 hj
    have h0 : ((redSwap α β δ h).ord (Sum.inl slot1)).val = 0 := rfl
    omega

/-- **V3.3(c)** (lecture note AsymmetricFT, Example 6.14; milestone V, V3.3(c)): between `g = 1`
and `g̃ = [[β̃, α̃], [δ̃, 0]]` the matching is `π(1) = 2`, `π(2) = 1`; for block `1`,
`U = ℂ e₁`, `N = ℂ e₂`, `W̃₁ = λ₁ W₁` on `U` with `λ₁ = δ̃`, and
`Ṽ₁ - δ̃⁻¹ V₁ = (0, -β̃/(α̃δ̃))ᵀ`; for block `2`, `U = ℂ e₂`, `N = ℂ e₁`, `W̃₂ = λ₂ W₂` on `U` with
`λ₂ = α̃`, and `Ṽ₂ = α̃⁻¹ V₂`. -/
theorem V3_3c (α β δ : ℂ) (h : α * δ ≠ 0) :
    let Q := redSwap α β δ h
    let π := gOne.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
    let k₁ := gOne.ord (Sum.inl slot0)
    let k₂ := gOne.ord (Sum.inl slot1)
    π k₁ = Q.ord (Sum.inl slot0) ∧ π k₂ = Q.ord (Sum.inl slot1) ∧
    k₁.val = 0 ∧ (Q.ord (Sum.inl slot0)).val = 1 ∧
    k₂.val = 1 ∧ (Q.ord (Sum.inl slot1)).val = 0 ∧
    ((gOne.flag k₁.succ ⊓ Q.flag (π k₁).succ).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 0} ∧
    ((gOne.flag k₁.castSucc ⊔ Q.flag (π k₁).castSucc).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 1} ∧
    (∀ v ∈ Submodule.span ℂ {e 0}, Q.left slot0 *ᵥ v = δ • (gOne.left slot0 *ᵥ v)) ∧
    Q.right slot0 - δ⁻¹ • gOne.right slot0 = !![0; -β / (α * δ)] ∧
    ((gOne.flag k₂.succ ⊓ Q.flag (π k₂).succ).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 1} ∧
    ((gOne.flag k₂.castSucc ⊔ Q.flag (π k₂).castSucc).restrictScalars ℂ).map
        (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {e 0} ∧
    (∀ v ∈ Submodule.span ℂ {e 1}, Q.left slot1 *ᵥ v = α • (gOne.left slot1 *ᵥ v)) ∧
    Q.right slot1 = α⁻¹ • gOne.right slot1 := by
  intro Q π k₁ k₂
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨hW1, hW0, hV1, hV0⟩ := redSwap_spec α β δ h
  obtain ⟨gW0, gW1, gV0, gV1⟩ := redUpper_spec 1 0 1 (by norm_num)
  have hm1 : π k₁ = Q.ord (Sum.inl slot0) := matching_slot0 α β δ h
  have hm2 : π k₂ = Q.ord (Sum.inl slot1) := matching_slot1 α β δ h
  refine ⟨hm1, hm2, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm1, map_toVec_inf]
    change flagVec gOne _ ⊓ flagVec Q _ = _
    rw [flagVec_redUpper _ _ _ _ _ rfl, flagVec_eq_top _ _ rfl, inf_top_eq]
  · rw [hm1, map_toVec_sup]
    change flagVec gOne _ ⊔ flagVec Q _ = _
    rw [flagVec_eq_bot _ _ rfl, flagVec_redSwap _ _ _ _ _ rfl, bot_sup_eq]
  · intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [hW0, gW0]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]
  · rw [hV0, gV0]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [hm2, map_toVec_inf]
    change flagVec gOne _ ⊓ flagVec Q _ = _
    rw [flagVec_eq_top _ _ rfl, flagVec_redSwap _ _ _ _ _ rfl, top_inf_eq]
  · rw [hm2, map_toVec_sup]
    change flagVec gOne _ ⊔ flagVec Q _ = _
    rw [flagVec_redUpper _ _ _ _ _ rfl, flagVec_eq_bot _ _ rfl, sup_bot_eq]
  · intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [hW1, gW1]
    ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]
  · rw [hV1, gV1]
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### V3.3(d) -/

/-- The scalar intertwiners of V3.3(c): `X₁ = δ̃`, `X₂ = α̃`. -/
noncomputable def xRun (α δ : ℂ) : BlockIndex labels 0 → ℂ
  | Sum.inl s => if s.1 = 0 then δ else α
  | Sum.inr t => t.elim0

/-- The complements `L₁ = ℂ e₁`, `L₂ = ℂ e₂` (in the word module). -/
noncomputable def lRun (j : Fin (labels.card + gOne.z)) : Submodule ℂ tensorB.WordModule :=
  Submodule.span ℂ {(WordModule.toVec tensorB).symm fun i => if i.val = j.val then 1 else 0}

theorem gauge_gOne (v : Fin 2 → ℂ) (y : BlockSpace dims labels gOne.z) :
    gOne.gauge v y = v (tau12 y) := by
  change (!![(1 : ℂ), 0; 0, 1] *ᵥ v) (tau12 y) = v (tau12 y)
  generalize tau12 y = n
  fin_cases n <;> simp [Matrix.mulVec, dotProduct]

theorem blockIndex_cases {z : ℕ} (b : BlockIndex labels z) (hz : z = 0) :
    b = Sum.inl slot0 ∨ b = Sum.inl slot1 := by
  rcases b with ⟨s, hs⟩ | t
  · fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact absurd t.isLt (by omega)

theorem map_lRun (j : Fin (labels.card + gOne.z)) :
    (lRun j).map (WordModule.toVec tensorB).toLinearMap =
      Submodule.span ℂ {fun i : Fin 2 => if i.val = j.val then (1 : ℂ) else 0} := by
  rw [lRun, Submodule.map_span, Set.image_singleton]
  simp

/-- **V3.3(d)** (lecture note AsymmetricFT, Example 6.14; milestone V, V3.3(d)): with
`L₁ = ℂ e₁`, `L₂ = ℂ e₂`, the data of Theorem E for `g = 1` and
`g̃ = [[β̃, α̃], [δ̃, 0]]` are `Γ = 1`, `𝔄 = 1`, `P_X = [[0, α̃], [δ̃, 0]]`,
`𝔄̃ = [[1, β̃/δ̃], [0, 1]]` (in the bond coordinates of the two reductions), and
`g̃ g⁻¹ = 𝔄̃ P_X 𝔄⁻¹`. -/
theorem V3_3d (α β δ : ℂ) (h : α * δ ≠ 0) :
    let Q := redSwap α β δ h
    let PX : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ :=
      (!![0, α; δ, 0]).submatrix tau21 tau12
    let 𝔄' : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ :=
      (!![1, β / δ; 0, 1]).submatrix tau21 tau21
    IsAdaptedFactorization gOne Q isNormal_blocks dims_pos isNormal_blocks dims_pos (Equiv.refl _)
      lRun gOne.gauge 1 𝔄'
      (fun b => xRun α δ b • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) ∧
    gaugeMatrix gOne.gauge = (1 : Matrix (Fin 2) (Fin 2) ℂ).submatrix tau12 id ∧
    (∑ b, Matrix.blockEmbed (slotSize dims) b * (xRun α δ b •
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *
        Matrix.blockProj (slotSize dims) b) = PX ∧
    gaugeMatrix Q.gauge * gaugeMatrixInv gOne.gauge =
      𝔄' * PX * (1 : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ)⁻¹ := by
  intro Q PX 𝔄'
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨hm1, hm2, -, -, -, -, hU1, -, hl1, -, hU2, -, hl2, -⟩ := V3_3c α β δ h
  have hxne : ∀ b, xRun α δ b ≠ 0 := by
    intro b
    rcases blockIndex_cases b rfl with rfl | rfl
    · simp [xRun, hδ]
    · simp [xRun, hα]
  have hG1 : gaugeMatrix gOne.gauge = (1 : Matrix (Fin 2) (Fin 2) ℂ).submatrix tau12 id := by
    rw [show gOne.gauge = gaugeOfMatrix tau12 !![(1 : ℂ), 0; 0, 1] !![1⁻¹, -0 / (1 * 1); 0, 1⁻¹]
        (upper_mul_inv (by norm_num)).1 (upper_mul_inv (by norm_num)).2 from rfl]
    erw [gaugeMatrix_gaugeOfMatrix]
    congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have hPX : (∑ b, Matrix.blockEmbed (slotSize dims) b * (xRun α δ b •
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *
        Matrix.blockProj (slotSize dims) b) = PX := by
    rw [Matrix.sum_blockEmbed_mul_mul_blockProj]
    ext ⟨x, p⟩ ⟨y, q⟩
    rcases blockIndex_cases x rfl with rfl | rfl <;>
      rcases blockIndex_cases y rfl with rfl | rfl <;>
      obtain rfl : p = 0 := Subsingleton.elim p 0 <;>
      obtain rfl : q = 0 := Subsingleton.elim q 0 <;>
      simp [PX, Matrix.blockDiagonal'_apply, xRun, tau21, tau12, ord21, ord12]
  have hQg : gaugeMatrix Q.gauge =
      𝔄' * PX * (1 : Matrix (Fin 2) (Fin 2) ℂ).submatrix tau12 id := by
    rw [show Q.gauge = gaugeOfMatrix tau21 !![β, α; δ, 0] !![0, δ⁻¹; α⁻¹, -β / (α * δ)]
        (swap_mul_inv h).1 (swap_mul_inv h).2 from rfl]
    erw [gaugeMatrix_gaugeOfMatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have hj : ∀ j : Fin (labels.card + gOne.z),
      j = gOne.ord (Sum.inl slot0) ∨ j = gOne.ord (Sum.inl slot1) := by
    intro j
    have hlt : j.val < 2 := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  refine ⟨⟨?_, ?_, ?_, fun b => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, hG1, hPX, ?_⟩
  · intro b
    rcases blockIndex_cases b rfl with rfl | rfl
    · exact hm1.symm
    · exact hm2.symm
  · intro j
    rcases hj j with rfl | rfl
    · have hK : (gOne.flag (gOne.ord (Sum.inl slot0)).castSucc ⊓
          Q.flag (gOne.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
            (gOne.ord (Sum.inl slot0))).succ).restrictScalars ℂ = ⊥ := by
        apply eq_of_map_toVec_eq
        rw [Submodule.map_bot, map_toVec_inf]
        change flagVec gOne _ ⊓ flagVec Q _ = ⊥
        rw [flagVec_eq_bot gOne _ rfl, bot_inf_eq]
      have hU : (gOne.flag (gOne.ord (Sum.inl slot0)).succ ⊓
          Q.flag (gOne.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
            (gOne.ord (Sum.inl slot0))).succ).restrictScalars ℂ =
              lRun (gOne.ord (Sum.inl slot0)) := by
        apply eq_of_map_toVec_eq
        rw [hU1, map_lRun]
        congr 2
        funext i; fin_cases i <;> rfl
      exact ⟨hK ▸ disjoint_bot_left, by rw [hK, hU, bot_sup_eq]⟩
    · have hK : (gOne.flag (gOne.ord (Sum.inl slot1)).castSucc ⊓
          Q.flag (gOne.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
            (gOne.ord (Sum.inl slot1))).succ).restrictScalars ℂ = ⊥ := by
        apply eq_of_map_toVec_eq
        rw [Submodule.map_bot, map_toVec_inf, hm2]
        change flagVec gOne _ ⊓ flagVec Q _ = ⊥
        rw [flagVec_redUpper _ _ _ _ _ rfl, flagVec_redSwap _ _ _ _ _ rfl, eq_bot_iff]
        intro v hv
        exact (Submodule.mem_bot ℂ).2 (eq_zero_of_mem_span_e0_of_mem_span_e1
          (Submodule.mem_inf.1 hv).1 (Submodule.mem_inf.1 hv).2)
      have hU : (gOne.flag (gOne.ord (Sum.inl slot1)).succ ⊓
          Q.flag (gOne.matching Q isNormal_blocks dims_pos isNormal_blocks dims_pos
            (gOne.ord (Sum.inl slot1))).succ).restrictScalars ℂ =
              lRun (gOne.ord (Sum.inl slot1)) := by
        apply eq_of_map_toVec_eq
        rw [hU2, map_lRun]
        congr 2
        funext i; fin_cases i <;> rfl
      exact ⟨hK ▸ disjoint_bot_left, by rw [hK, hU, bot_sup_eq]⟩
  · intro b x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [MultiBlockCompression.leftRow_mulVec]
    funext y
    rw [gauge_gOne]
    simp only [gauge_gOne]
    by_cases hy : y.1 = b
    · obtain ⟨b', i⟩ := y
      dsimp only at hy
      subst hy
      rw [blockEmbed_mulVec_apply_self]
    · rw [blockEmbed_mulVec_apply_of_fst_ne _ hy]
      have hne : (tau12 y).val ≠ (gOne.ord b).val := fun he =>
        hy (gOne.ord.injective (Fin.ext he))
      rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, ite_eq_right hne,
        smul_zero]
  · refine ⟨(xRun α δ b)⁻¹ • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ),
      ?_, ?_⟩
    · change xRun α δ b • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
        ((xRun α δ b)⁻¹ • 1) = 1
      simp [hxne b]
    · change (xRun α δ b)⁻¹ • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
        (xRun α δ b • 1) = 1
      simp [hxne b]
  · intro i
    change xRun α δ b • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
      slotTensor blocks b i = slotTensor blocks b i * (xRun α δ b • 1)
    simp
  · intro x hx
    change Q.leftRow b *ᵥ WordModule.toVec tensorB x =
      (xRun α δ b • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *ᵥ
        (gOne.leftRow b *ᵥ WordModule.toVec tensorB x)
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rcases blockIndex_cases b rfl with rfl | rfl
    · rw [hm1] at hx
      have hv : WordModule.toVec tensorB x ∈ Submodule.span ℂ {e 0} := by
        rw [← hU1, hm1]; exact Submodule.mem_map_of_mem hx
      have e : xRun α δ (Sum.inl slot0) = δ := by simp [xRun]
      erw [e]
      exact hl1 _ hv
    · rw [hm2] at hx
      have hv : WordModule.toVec tensorB x ∈ Submodule.span ℂ {e 1} := by
        rw [← hU2, hm2]; exact Submodule.mem_map_of_mem hx
      have e : xRun α δ (Sum.inl slot1) = α := by simp [xRun]
      erw [e]
      exact hl2 _ hv
  · exact Matrix.blockTriangular_one
  · intro b
    rw [Matrix.blockDiag'_one]
    rfl
  · intro x y hxy
    change (!![1, β / δ; 0, 1]) (ord21 x.1) (ord21 y.1) = 0
    change ord21 y.1 < ord21 x.1 at hxy
    revert hxy
    generalize ord21 x.1 = a
    generalize ord21 y.1 = a'
    intro hxy
    fin_cases a <;> fin_cases a' <;> simp_all
  · intro b
    rcases blockIndex_cases b rfl with rfl | rfl
    · ext p q
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      change (!![(1 : ℂ), β / δ; 0, 1]) 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
      simp
    · ext p q
      obtain rfl : p = 0 := Subsingleton.elim p 0
      obtain rfl : q = 0 := Subsingleton.elim q 0
      change (!![(1 : ℂ), β / δ; 0, 1]) 0 0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0
      simp
  · exact (Matrix.one_mul _).symm
  · rw [hQg, ← hPX, ← hG1]
    rfl
  · erw [hQg, ← hG1, Matrix.mul_assoc (𝔄' * PX), gaugeMatrix_mul_gaugeMatrixInv, Matrix.mul_one,
      inv_one, Matrix.mul_one]

/-! ### V3.4 -/

/-- **V3.4(a)** (lecture note AsymmetricFT, Example 4.4; milestone V, V3.4(a)): for distinct
nonzero `ν_j` and any `y_j` there is a polynomial `a` with `a(0) = 0` and `a(ν_j) = y_j`, namely
`a = X p` with `p` the Lagrange interpolant of `y_j / ν_j` at the nodes `ν_j`. -/
theorem V3_4a {m : ℕ} (ν y : Fin m → ℂ) (hinj : Function.Injective ν) (hne : ∀ j, ν j ≠ 0) :
    ∃ a : Polynomial ℂ, a.eval 0 = 0 ∧ ∀ j, a.eval (ν j) = y j := by
  refine ⟨Polynomial.X * Lagrange.interpolate Finset.univ ν (fun j => y j / ν j), by simp,
    fun j => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_X,
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ j)]
  field_simp [hne j]

/-- **V3.4(b)** (lecture note AsymmetricFT, Example 4.4; milestone V, V3.4(b)): if
`c₁ + c₂ 2ⁿ = 1 + 2ⁿ` for every `n ≥ 1`, then `c₁ = c₂ = 1`. -/
theorem V3_4b (c₁ c₂ : ℂ) (h : ∀ n : ℕ, 1 ≤ n → c₁ + c₂ * 2 ^ n = 1 + 2 ^ n) :
    c₁ = 1 ∧ c₂ = 1 := by
  have h1 := h 1 le_rfl
  have h2 := h 2 (by norm_num)
  norm_num at h1 h2
  constructor
  · linear_combination 2 * h1 - h2
  · linear_combination (h2 - h1) / 2

end Running

end MultiBlockExamples
