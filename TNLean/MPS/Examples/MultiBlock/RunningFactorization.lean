/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import TNLean.MPS.Examples.MultiBlock.Running

/-!
# The running example: the matching, the factorization and the density theorem

For the running example `B = diag(1, 2)` with one letter and the blocks `C₁ = (1)`, `C₂ = (2)`
(`TNLean.MPS.Examples.MultiBlock.Running`), the reduction `g = 1` with the order `(1, 2)` and the
reduction `g̃ = [[β̃, α̃], [δ̃, 0]]` with the order `(2, 1)` are matched block by block, with
scalars `λ₁ = δ̃` and `λ₂ = α̃`, and `g̃ = 𝔄̃ P_X 𝔄⁻¹` with `𝔄 = 1` (*The asymmetric fundamental
theorem of matrix product states*, Example 6.14). The last section is the density theorem for one
letter (Example 4.4): interpolation without constant term, and the multiplicities determined by
the traces.

## Main results

* `MultiBlockExamples.Running.matching_left_right_gOne_redSwap`: the matching and the scalars.
* `MultiBlockExamples.Running.isAdaptedFactorization_gOne_redSwap`: the factorization of *A basis
  adapted to both flags*.
* `MultiBlockExamples.Running.exists_eval_zero_eq_zero_and_eval_eq`,
  `MultiBlockExamples.Running.eq_one_and_eq_one_of_forall_add_mul_pow_eq`: Example 4.4.

## References

*The asymmetric fundamental theorem of matrix product states*, Examples 4.4 and 6.14; blueprint
`thm:asym_uniq_different_flags`, *Two compressions with different flags*, and
`thm:asym_uniq_common_basis`, *A basis adapted to both flags*.
-/

open scoped Matrix

namespace MultiBlockExamples

open MPSTensor

namespace Running

/-! ### The matching and the intertwiners -/

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
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨e 0, ?_, ?_, ?_⟩ ?_
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
  refine matching_eq_of_flagVec_inf _ _ _ _ _ _ _ _ ⟨e 1, ?_, ?_, ?_⟩ ?_
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

/-- **The matching and the intertwiners** (*The asymmetric fundamental theorem of matrix product
states*, Example 6.14): between `g = 1` and `g̃ = [[β̃, α̃], [δ̃, 0]]` the matching is `π(1) = 2`,
`π(2) = 1`; for block `1`, `U = ℂ e₁`, `N = ℂ e₂`, `W̃₁ = λ₁ W₁` on `U` with `λ₁ = δ̃`, and
`Ṽ₁ - δ̃⁻¹ V₁ = (0, -β̃/(α̃δ̃))ᵀ`; for block `2`, `U = ℂ e₂`, `N = ℂ e₁`, `W̃₂ = λ₂ W₂` on `U` with
`λ₂ = α̃`, and `Ṽ₂ = α̃⁻¹ V₂`. -/
theorem matching_left_right_gOne_redSwap (α β δ : ℂ) (h : α * δ ≠ 0) :
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

/-! ### The factorization -/

/-- The scalar intertwiners of `matching_left_right_gOne_redSwap`: `X₁ = δ̃`, `X₂ = α̃`. -/
noncomputable def intertwinerScalar (α δ : ℂ) : BlockIndex labels 0 → ℂ
  | Sum.inl s => if s.1 = 0 then δ else α
  | Sum.inr t => t.elim0

/-- The complements `L₁ = ℂ e₁`, `L₂ = ℂ e₂` (in the word module). -/
noncomputable def complement (j : Fin (labels.card + gOne.z)) : Submodule ℂ tensorB.WordModule :=
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

theorem map_complement (j : Fin (labels.card + gOne.z)) :
    (complement j).map (WordModule.toVec tensorB).toLinearMap =
      Submodule.span ℂ {fun i : Fin 2 => if i.val = j.val then (1 : ℂ) else 0} := by
  rw [complement, Submodule.map_span, Set.image_singleton]
  simp

/-- **The factorization** (*The asymmetric fundamental theorem of matrix product states*, Example
6.14): with `L₁ = ℂ e₁`, `L₂ = ℂ e₂`, the data of *A basis adapted to both flags* for `g = 1` and
`g̃ = [[β̃, α̃], [δ̃, 0]]` are `Γ = 1`, `𝔄 = 1`, `P_X = [[0, α̃], [δ̃, 0]]`,
`𝔄̃ = [[1, β̃/δ̃], [0, 1]]` (in the bond coordinates of the two reductions), and
`g̃ g⁻¹ = 𝔄̃ P_X 𝔄⁻¹`. -/
theorem isAdaptedFactorization_gOne_redSwap (α β δ : ℂ) (h : α * δ ≠ 0) :
    let Q := redSwap α β δ h
    let PX : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ :=
      (!![0, α; δ, 0]).submatrix tau21 tau12
    let 𝔄' : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ :=
      (!![1, β / δ; 0, 1]).submatrix tau21 tau21
    IsAdaptedFactorization gOne Q isNormal_blocks dims_pos isNormal_blocks dims_pos (Equiv.refl _)
      complement gOne.gauge 1 𝔄'
      (fun b => intertwinerScalar α δ b •
        (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) ∧
    gaugeMatrix gOne.gauge = (1 : Matrix (Fin 2) (Fin 2) ℂ).submatrix tau12 id ∧
    (∑ b, Matrix.blockEmbed (slotSize dims) b * (intertwinerScalar α δ b •
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *
        Matrix.blockProj (slotSize dims) b) = PX ∧
    gaugeMatrix Q.gauge * gaugeMatrixInv gOne.gauge =
      𝔄' * PX * (1 : Matrix (BlockSpace dims labels 0) (BlockSpace dims labels 0) ℂ)⁻¹ := by
  intro Q PX 𝔄'
  have hα : α ≠ 0 := left_ne_zero_of_mul h
  have hδ : δ ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨hm1, hm2, -, -, -, -, hU1, -, hl1, -, hU2, -, hl2, -⟩ :=
    matching_left_right_gOne_redSwap α β δ h
  have hxne : ∀ b, intertwinerScalar α δ b ≠ 0 := by
    intro b
    rcases blockIndex_cases b rfl with rfl | rfl
    · simp [intertwinerScalar, hδ]
    · simp [intertwinerScalar, hα]
  have hG1 : gaugeMatrix gOne.gauge = (1 : Matrix (Fin 2) (Fin 2) ℂ).submatrix tau12 id := by
    rw [show gOne.gauge = gaugeOfMatrix tau12 !![(1 : ℂ), 0; 0, 1] !![1⁻¹, -0 / (1 * 1); 0, 1⁻¹]
        (upper_mul_inv (by norm_num)).1 (upper_mul_inv (by norm_num)).2 from rfl]
    erw [gaugeMatrix_gaugeOfMatrix]
    congr 1
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have hPX : (∑ b, Matrix.blockEmbed (slotSize dims) b * (intertwinerScalar α δ b •
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *
        Matrix.blockProj (slotSize dims) b) = PX := by
    rw [Matrix.sum_blockEmbed_mul_mul_blockProj]
    ext ⟨x, p⟩ ⟨y, q⟩
    rcases blockIndex_cases x rfl with rfl | rfl <;>
      rcases blockIndex_cases y rfl with rfl | rfl <;>
      obtain rfl : p = 0 := Subsingleton.elim p 0 <;>
      obtain rfl : q = 0 := Subsingleton.elim q 0 <;>
      simp [PX, Matrix.blockDiagonal'_apply, intertwinerScalar, tau21, tau12, ord21, ord12]
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
              complement (gOne.ord (Sum.inl slot0)) := by
        apply eq_of_map_toVec_eq
        rw [hU1, map_complement]
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
              complement (gOne.ord (Sum.inl slot1)) := by
        apply eq_of_map_toVec_eq
        rw [hU2, map_complement]
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
  · refine ⟨(intertwinerScalar α δ b)⁻¹ •
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ), ?_, ?_⟩
    · change intertwinerScalar α δ b •
        (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
        ((intertwinerScalar α δ b)⁻¹ • 1) = 1
      simp [hxne b]
    · change (intertwinerScalar α δ b)⁻¹ •
        (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
        (intertwinerScalar α δ b • 1) = 1
      simp [hxne b]
  · intro i
    change intertwinerScalar α δ b •
        (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) *
      slotTensor blocks b i = slotTensor blocks b i * (intertwinerScalar α δ b • 1)
    simp
  · intro x hx
    change Q.leftRow b *ᵥ WordModule.toVec tensorB x =
      (intertwinerScalar α δ b • (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ)) *ᵥ
        (gOne.leftRow b *ᵥ WordModule.toVec tensorB x)
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rcases blockIndex_cases b rfl with rfl | rfl
    · rw [hm1] at hx
      have hv : WordModule.toVec tensorB x ∈ Submodule.span ℂ {e 0} := by
        rw [← hU1, hm1]; exact Submodule.mem_map_of_mem hx
      have e : intertwinerScalar α δ (Sum.inl slot0) = δ := by simp [intertwinerScalar]
      erw [e]
      exact hl1 _ hv
    · rw [hm2] at hx
      have hv : WordModule.toVec tensorB x ∈ Submodule.span ℂ {e 1} := by
        rw [← hU2, hm2]; exact Submodule.mem_map_of_mem hx
      have e : intertwinerScalar α δ (Sum.inl slot1) = α := by simp [intertwinerScalar]
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

/-! ### The density theorem for one letter -/

/-- **Interpolation without constant term** (*The asymmetric fundamental theorem of matrix product
states*, Example 4.4): for distinct nonzero `ν_j` and any `y_j` there is a polynomial `a` with
`a(0) = 0` and `a(ν_j) = y_j`, namely `a = X p` with `p` the Lagrange interpolant of `y_j / ν_j` at
the nodes `ν_j`. -/
theorem exists_eval_zero_eq_zero_and_eval_eq {m : ℕ} (ν y : Fin m → ℂ) (hinj : Function.Injective ν)
    (hne : ∀ j, ν j ≠ 0) :
    ∃ a : Polynomial ℂ, a.eval 0 = 0 ∧ ∀ j, a.eval (ν j) = y j := by
  refine ⟨Polynomial.X * Lagrange.interpolate Finset.univ ν (fun j => y j / ν j), by simp,
    fun j => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_X,
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ j)]
  field_simp [hne j]

/-- **The multiplicities are determined by the traces** (*The asymmetric fundamental theorem of
matrix product states*, Example 4.4): if `c₁ + c₂ 2ⁿ = 1 + 2ⁿ` for every `n ≥ 1`, then
`c₁ = c₂ = 1`. -/
theorem eq_one_and_eq_one_of_forall_add_mul_pow_eq (c₁ c₂ : ℂ)
    (h : ∀ n : ℕ, 1 ≤ n → c₁ + c₂ * 2 ^ n = 1 + 2 ^ n) :
    c₁ = 1 ∧ c₂ = 1 := by
  have h1 := h 1 le_rfl
  have h2 := h 2 (by norm_num)
  norm_num at h1 h2
  constructor
  · linear_combination 2 * h1 - h2
  · linear_combination (h2 - h1) / 2

end Running

end MultiBlockExamples
