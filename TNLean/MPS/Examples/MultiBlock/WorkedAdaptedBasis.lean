/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Worked

/-!
# The worked example: the dimension matrix and a basis adapted to both flags

For the two reductions `g = g₀` and `g̃ = h P g₀` of the worked example
(`TNLean.MPS.Examples.MultiBlock.Worked`; *The asymmetric fundamental theorem of matrix product
states*, Example 6.16), this file computes the dimension matrix `dim (M_k ∩ M̃_{k'})` of the two
flags and the factorization `g = 𝔄 Γ`, `g̃ = 𝔄̃ P_X Γ` of *A basis adapted to both flags*, with
explicit complements `L_k` and integer matrices `𝔄`, `𝔄̃` and `Γ`.

## Main results

* `MultiBlockExamples.Worked.finrank_flagVec_redG_inf_flagVec_redGt`: the dimension matrix.
* `MultiBlockExamples.Worked.isAdaptedFactorization_redG_redGt`: the factorization of *A basis
  adapted to both flags*.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.16, with the letters as
printed there; the numbers are those of `check/worked_example_normal.py` and
`check/example-2x2-normal.tex`. Blueprint `thm:asym_uniq_common_basis`, *A basis adapted to both
flags*.
-/

open scoped Matrix

namespace MultiBlockExamples

namespace Worked

open MPSTensor

/-! ### The dimension matrix -/

theorem card_add_z_redG : 4 = labels.card + redG.z + 1 := by decide

theorem card_add_z_redGt : 4 = labels.card + redGt.z + 1 := by decide

/-- The position `k = i + 1` of the flag of `g`. -/
noncomputable def posG (i : Fin 3) : Fin (labels.card + redG.z + 1) :=
  Fin.cast card_add_z_redG i.succ

/-- The position `k' = j + 1` of the flag of `g̃`. -/
noncomputable def posGt (j : Fin 3) : Fin (labels.card + redGt.z + 1) :=
  Fin.cast card_add_z_redGt j.succ

theorem finrank_span_pair {x y : Fin 4 → ℂ} (h : LinearIndependent ℂ ![x, y]) :
    Module.finrank ℂ (Submodule.span ℂ {x, y}) = 2 := by
  have := finrank_span_eq_card h
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this

theorem finrank_span_triple {x y w : Fin 4 → ℂ} (h : LinearIndependent ℂ ![x, y, w]) :
    Module.finrank ℂ (Submodule.span ℂ {x, y, w}) = 3 := by
  have := finrank_span_eq_card h
  rwa [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union,
    Fintype.card_fin] at this

theorem finrank_span_redG_one : Module.finrank ℂ (Submodule.span ℂ
    {(![1, 0, -1, 0] : Fin 4 → ℂ), ![-1, 1, -1, 1]}) = 2 := by
  refine finrank_span_pair (Fintype.linearIndependent_iff.2 fun g hg => ?_)
  have c0 : g 0 * 1 + g 1 * (-1) = 0 := by simpa [Fin.sum_univ_two] using congrFun hg 0
  have c1 : g 0 * 0 + g 1 * 1 = 0 := by simpa [Fin.sum_univ_two] using congrFun hg 1
  have g1 : g 1 = 0 := by linear_combination c1
  have g0 : g 0 = 0 := by linear_combination c0 + c1
  intro i; fin_cases i
  · exact g0
  · exact g1

theorem finrank_span_redG_two : Module.finrank ℂ (Submodule.span ℂ
    {(![1, 0, -1, 0] : Fin 4 → ℂ), ![-1, 1, -1, 1], ![-1, 0, 2, 0]}) = 3 := by
  refine finrank_span_triple (Fintype.linearIndependent_iff.2 fun g hg => ?_)
  have c0 : g 0 * 1 + g 1 * (-1) + g 2 * (-1) = 0 := by
    simpa [Fin.sum_univ_three] using congrFun hg 0
  have c1 : g 0 * 0 + g 1 * 1 + g 2 * 0 = 0 := by simpa [Fin.sum_univ_three] using congrFun hg 1
  have c2 : g 0 * (-1) + g 1 * (-1) + g 2 * 2 = 0 := by
    simpa [Fin.sum_univ_three] using congrFun hg 2
  have g1 : g 1 = 0 := by linear_combination c1
  have g2 : g 2 = 0 := by linear_combination c0 + c2 + 2 * c1
  have g0 : g 0 = 0 := by linear_combination c0 + c1 + g2
  intro i; fin_cases i
  · exact g0
  · exact g1
  · exact g2

theorem finrank_span_redGt_one :
    Module.finrank ℂ (Submodule.span ℂ {(![-1, 0, 2, 0] : Fin 4 → ℂ)}) = 1 := by
  refine finrank_span_singleton fun h => ?_
  have := congrFun h 0
  simp at this

theorem finrank_span_redGt_two : Module.finrank ℂ (Submodule.span ℂ
    {(![-1, 0, 2, 0] : Fin 4 → ℂ), ![2, -1, -2, 0]}) = 2 := by
  refine finrank_span_pair (Fintype.linearIndependent_iff.2 fun g hg => ?_)
  have c0 : g 0 * (-1) + g 1 * 2 = 0 := by simpa [Fin.sum_univ_two] using congrFun hg 0
  have c1 : g 0 * 0 + g 1 * (-1) = 0 := by simpa [Fin.sum_univ_two] using congrFun hg 1
  have g1 : g 1 = 0 := by linear_combination -c1
  have g0 : g 0 = 0 := by linear_combination -c0 - 2 * c1
  intro i; fin_cases i
  · exact g0
  · exact g1

theorem flagVec_redG_one_inf_flagVec_redGt_one :
    flagVec redG (posG 0) ⊓ flagVec redGt (posGt 0) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [mem_flagVec_redG_one _ rfl] at hv1
  rw [mem_flagVec_redGt_one _ rfl] at hv2
  obtain ⟨a, b⟩ := hv1
  obtain ⟨c1, c, e⟩ := hv2
  rw [Submodule.mem_bot]
  ext i; fin_cases i
  · simp; linear_combination -a + b + c - 2 * e
  · simp; linear_combination -b + e
  · simp; linear_combination 2 * a - c
  · simp; linear_combination e

theorem flagVec_redG_one_inf_flagVec_redGt_two :
    flagVec redG (posG 0) ⊓ flagVec redGt (posGt 1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  rw [mem_flagVec_redG_one _ rfl] at hv1
  rw [mem_flagVec_redGt_two _ rfl] at hv2
  obtain ⟨a, b⟩ := hv1
  obtain ⟨c, e⟩ := hv2
  rw [Submodule.mem_bot]
  ext i; fin_cases i
  · simp; linear_combination -a + b + c - 2 * e
  · simp; linear_combination -b + e
  · simp; linear_combination 2 * a - c
  · simp; linear_combination e

theorem flagVec_redG_two_inf_flagVec_redGt_two :
    flagVec redG ⟨2, by decide⟩ ⊓ flagVec redGt ⟨2, by decide⟩ =
    Submodule.span ℂ {![-1, 0, 2, 0]} := by
  ext v
  rw [Submodule.mem_inf, mem_flagVec_redG_two _ rfl, mem_flagVec_redGt_two _ rfl,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h3', h2, h3⟩
    have e1 : v 1 = 0 := by linear_combination -h3' + h3
    have e2 : v 2 = -2 * v 0 := by linear_combination h2 - 2 * e1 - 2 * h3
    refine ⟨-v 0, ?_⟩
    ext i
    fin_cases i <;> simp [e1, e2, h3]
    ring
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp
    ring

/-- **The dimension matrix** (*The asymmetric fundamental theorem of matrix product states*, Example
6.16): `dim (M_k ∩ M̃_{k'})` for `k, k' = 1, 2, 3` (rows `k`, columns `k'`) is
`[[0, 0, 2], [1, 1, 3], [1, 2, 4]]`. -/
theorem finrank_flagVec_redG_inf_flagVec_redGt :
    (Matrix.of fun i j : Fin 3 =>
      Module.finrank ℂ ↥(flagVec redG (posG i) ⊓ flagVec redGt (posGt j))) =
      !![0, 0, 2; 1, 1, 3; 1, 2, 4] := by
  obtain ⟨hM1, hM2, hMt1, hMt2, -⟩ := flagVec_redG_redGt_and_matching
  have eM1 : flagVec redG (posG 0) = _ := hM1 _ rfl
  have eM2 : flagVec redG (posG 1) = _ := hM2 _ rfl
  have eMt1 : flagVec redGt (posGt 0) = _ := hMt1 _ rfl
  have eMt2 : flagVec redGt (posGt 1) = _ := hMt2 _ rfl
  have eM3 : flagVec redG (posG 2) = ⊤ := flagVec_eq_top _ _ rfl
  have eMt3 : flagVec redGt (posGt 2) = ⊤ := flagVec_eq_top _ _ rfl
  have d11 : Module.finrank ℂ ↥(flagVec redG (posG 0) ⊓ flagVec redGt (posGt 0)) = 0 := by
    rw [flagVec_redG_one_inf_flagVec_redGt_one, finrank_bot]
  have d12 : Module.finrank ℂ ↥(flagVec redG (posG 0) ⊓ flagVec redGt (posGt 1)) = 0 := by
    rw [flagVec_redG_one_inf_flagVec_redGt_two, finrank_bot]
  have d13 : Module.finrank ℂ ↥(flagVec redG (posG 0) ⊓ flagVec redGt (posGt 2)) = 2 := by
    rw [eMt3, inf_top_eq, eM1, finrank_span_redG_one]
  have d21 : Module.finrank ℂ ↥(flagVec redG (posG 1) ⊓ flagVec redGt (posGt 0)) = 1 := by
    rw [eM2, eMt1, inf_eq_right.2 (Submodule.span_mono (by simp)), finrank_span_redGt_one]
  have d22 : Module.finrank ℂ ↥(flagVec redG (posG 1) ⊓ flagVec redGt (posGt 1)) = 1 := by
    have h : flagVec redG (posG 1) ⊓ flagVec redGt (posGt 1) =
        Submodule.span ℂ {(![-1, 0, 2, 0] : Fin 4 → ℂ)} := flagVec_redG_two_inf_flagVec_redGt_two
    rw [h, finrank_span_redGt_one]
  have d23 : Module.finrank ℂ ↥(flagVec redG (posG 1) ⊓ flagVec redGt (posGt 2)) = 3 := by
    rw [eMt3, inf_top_eq, eM2, finrank_span_redG_two]
  have d31 : Module.finrank ℂ ↥(flagVec redG (posG 2) ⊓ flagVec redGt (posGt 0)) = 1 := by
    rw [eM3, top_inf_eq, eMt1, finrank_span_redGt_one]
  have d32 : Module.finrank ℂ ↥(flagVec redG (posG 2) ⊓ flagVec redGt (posGt 1)) = 2 := by
    rw [eM3, top_inf_eq, eMt2, finrank_span_redGt_two]
  have d33 : Module.finrank ℂ ↥(flagVec redG (posG 2) ⊓ flagVec redGt (posGt 2)) = 4 := by
    rw [eM3, eMt3, inf_top_eq, finrank_top, Module.finrank_fin_fun]
  ext i j
  fin_cases i <;> fin_cases j
  exacts [d11, d12, d13, d21, d22, d23, d31, d32, d33]

/-! ### A basis adapted to both flags -/

/-- `𝔄` (in the bond coordinates of `g`). -/
def aInt : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

/-- `𝔄⁻¹`. -/
def aInvInt : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1; 0, 0, 0, 1]

/-- `𝔄̃` (in the bond coordinates of `g̃`). -/
def atInt : Matrix (Fin 4) (Fin 4) ℤ := !![1, 2, 1, -1; 0, 1, -1, 2; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `P_X` (rows in the coordinates of `g̃`, columns in those of `g`). -/
def pxInt : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 1, 0, 0; 0, 1, 0, 0]

/-- `Γ = 𝔄⁻¹ g`. -/
def gammaInt : Matrix (Fin 4) (Fin 4) ℤ := !![2, 2, 1, 1; 0, 0, 0, 1; 1, 2, 1, 0; 0, -1, 0, 1]

/-- `Γ⁻¹ = g⁻¹ 𝔄`: its columns are the bases of `L₁`, `L₂`, `L₃`. -/
def gammaInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, -1, 0; 0, 1, 0, -1; -1, -1, 2, 2; 0, 1, 0, 0]

theorem gammaInt_mul_gammaInvInt : gammaInt * gammaInvInt = 1 := by decide +kernel

theorem gammaInvInt_mul_gammaInt : gammaInvInt * gammaInt = 1 := by decide +kernel

theorem aInvInt_mul_aInt : aInvInt * aInt = 1 := by decide +kernel

theorem aInt_mul_gammaInt : aInt * gammaInt = g0Int := by decide +kernel

theorem atInt_mul_pxInt_mul_gammaInt : atInt * pxInt * gammaInt = gtInt := by decide +kernel

theorem gtInt_mul_g0InvInt : gtInt * g0InvInt = atInt * pxInt * aInvInt := by decide +kernel

/-- `Γ` as a change of coordinates. -/
noncomputable def gammaGauge : (Fin 4 → ℂ) ≃ₗ[ℂ] (BlockSpace dims labels 1 → ℂ) :=
  gaugeOfMatrix tauG (toC gammaInt) (toC gammaInvInt)
    (complexOfRing_mul_eq_one _ gammaInt_mul_gammaInvInt)
    (complexOfRing_mul_eq_one _ gammaInvInt_mul_gammaInt)

theorem gaugeMatrix_gammaGauge : gaugeMatrix gammaGauge = (toC gammaInt).submatrix tauG id :=
  gaugeMatrix_gaugeOfMatrix _ _ _ _ _

theorem gaugeMatrix_redG : gaugeMatrix redG.gauge = (toC g0Int).submatrix tauG id := by
  erw [gauge_redG, gaugeMatrix_gaugeOfMatrix]
  rfl

theorem gaugeMatrix_redGt : gaugeMatrix redGt.gauge = (toC gtInt).submatrix tauGt id := by
  erw [gauge_redGt, gaugeMatrix_gaugeOfMatrix]
  rfl

theorem gaugeMatrixInv_redG : gaugeMatrixInv redG.gauge = (toC g0InvInt).submatrix id tauG := by
  erw [gauge_redG, gaugeMatrixInv_gaugeOfMatrix]
  rfl

/-- The complements `L₁ = M₁`, `L₂ = M̃₁`, `L₃ = ℂ (V_{C₂} + V₀) = ℂ (0, -1, 2, 0)` in `ℂ⁴`. -/
noncomputable def complementVec (j : Fin (labels.card + redG.z)) : Submodule ℂ (Fin 4 → ℂ) :=
  if j.val = 0 then Submodule.span ℂ {![1, 0, -1, 0], ![-1, 1, -1, 1]}
  else if j.val = 1 then Submodule.span ℂ {![-1, 0, 2, 0]}
  else Submodule.span ℂ {![0, -1, 2, 0]}

/-- The complements in the word module. -/
noncomputable def complement (j : Fin (labels.card + redG.z)) : Submodule ℂ tensorB.WordModule :=
  (complementVec j).map (WordModule.toVec tensorB).symm.toLinearMap

theorem map_complement (j : Fin (labels.card + redG.z)) :
    (complement j).map (WordModule.toVec tensorB).toLinearMap = complementVec j := by
  rw [complement, ← Submodule.map_comp]
  simp

/-- The intertwiners `X_{C₁} = Y`, `X₀ = 1`, `X_{C₂} = 1`. -/
noncomputable def intertwiner :
    ∀ b : BlockIndex labels 1, Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ
  | Sum.inl ⟨0, _⟩ => matY
  | Sum.inl ⟨1, _⟩ => 1
  | Sum.inr _ => 1

theorem slot_cases {z : ℕ} (b : BlockIndex labels z) (hz : z = 1) :
    b = Sum.inl slotC1 ∨ b = Sum.inr ⟨0, by omega⟩ ∨ b = Sum.inl slotC2 := by
  subst hz
  rcases b with ⟨s, hs⟩ | t
  · fin_cases s
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (by rw [Subsingleton.elim t ⟨0, Nat.one_pos⟩]))

theorem toC_gammaInt_mulVec (v : Fin 4 → ℂ) :
    toC gammaInt *ᵥ v = ![2 * v 0 + 2 * v 1 + v 2 + v 3, v 3, v 0 + 2 * v 1 + v 2, -v 1 + v 3] := by
  ext i
  fin_cases i <;>
    simp [gammaInt, toC, complexOfRing_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem blockEmbed_mulVec_apply {z : ℕ} (b : BlockIndex labels z) (f : BlockSpace dims labels z → ℂ)
    (y : BlockSpace dims labels z) :
    (Matrix.blockEmbed (slotSize dims) b *ᵥ fun j => f ⟨b, j⟩) y = if y.1 = b then f y else 0 := by
  by_cases h : y.1 = b
  · obtain ⟨c, i⟩ := y
    dsimp only at h
    subst h
    rw [blockEmbed_mulVec_apply_self]
    simp
  · rw [blockEmbed_mulVec_apply_of_fst_ne _ h]
    simp [h]

/-- `P_X = ∑_b E_{π(b)} X_b P_b` is the printed permutation-like matrix. -/
theorem sum_blockEmbed_mul_intertwiner_mul_blockProj :
    (∑ b, Matrix.blockEmbed (slotSize dims) b * intertwiner b *
      Matrix.blockProj (slotSize dims) b) = (toC pxInt).submatrix tauGt tauG := by
  rw [Matrix.sum_blockEmbed_mul_mul_blockProj]
  ext x y
  obtain ⟨m, rfl⟩ := tauGt.symm.surjective x
  obtain ⟨n, rfl⟩ := tauG.symm.surjective y
  fin_cases m <;> fin_cases n <;>
    simp [tauGt, tauG, Matrix.blockDiagonal'_apply, intertwiner, matY, toC, complexOfRing_apply,
      pxInt] <;>
    rfl

theorem aInt_apply_eq_zero_of_lt : ∀ x y : BlockSpace dims labels 1, ordG y.1 < ordG x.1 →
    aInt (tauG x) (tauG y) = 0 := by
  decide

theorem atInt_apply_eq_zero_of_lt : ∀ x y : BlockSpace dims labels 1, ordGt y.1 < ordGt x.1 →
    atInt (tauGt x) (tauGt y) = 0 := by
  decide

/-- The complements: `K_j ⊕ L_j = U_j` for the three positions. -/
theorem disjoint_complement_and_sup_eq (j : Fin (labels.card + redG.z)) :
    Disjoint ((redG.flag j.castSucc ⊓ redGt.flag (positionMatching j).succ).restrictScalars ℂ)
      (complement j) ∧
    (redG.flag j.castSucc ⊓ redGt.flag (positionMatching j).succ).restrictScalars ℂ ⊔ complement j =
      (redG.flag j.succ ⊓ redGt.flag (positionMatching j).succ).restrictScalars ℂ := by
  obtain ⟨-, hK1, -, -, -, -, -, -, hK0, -, -⟩ := inf_sup_intertwiner_redG_redGt
  obtain ⟨b, rfl⟩ := redG.ord.surjective j
  rcases slot_cases b rfl with rfl | rfl | rfl
  · have hK : (redG.flag (redG.ord (Sum.inl slotC1)).castSucc ⊓
        redGt.flag (positionMatching (redG.ord (Sum.inl slotC1))).succ).restrictScalars ℂ = ⊥ := by
      apply eq_of_map_toVec_eq
      rw [Submodule.map_bot]
      exact hK1
    have hU : (redG.flag (redG.ord (Sum.inl slotC1)).succ ⊓
        redGt.flag (positionMatching (redG.ord (Sum.inl slotC1))).succ).restrictScalars ℂ =
          complement (redG.ord (Sum.inl slotC1)) := by
      apply eq_of_map_toVec_eq
      rw [map_complement, map_toVec_inf, positionMatching_ord_slotC1]
      change flagVec redG _ ⊓ flagVec redGt _ = _
      rw [flagVec_eq_top redGt _ rfl, inf_top_eq, flagVec_redG_redGt_and_matching.1 _ rfl]
      simp only [complementVec, show (redG.ord (Sum.inl slotC1)).val = 0 from rfl, ite_true]
    exact ⟨hK ▸ disjoint_bot_left, by rw [hK, hU, bot_sup_eq]⟩
  · change Disjoint ((redG.flag (redG.ord zeroSlot).castSucc ⊓
        redGt.flag (positionMatching (redG.ord zeroSlot)).succ).restrictScalars ℂ)
        (complement (redG.ord zeroSlot)) ∧
      (redG.flag (redG.ord zeroSlot).castSucc ⊓
          redGt.flag (positionMatching (redG.ord zeroSlot)).succ).restrictScalars ℂ ⊔
          complement (redG.ord zeroSlot) =
        (redG.flag (redG.ord zeroSlot).succ ⊓
          redGt.flag (positionMatching (redG.ord zeroSlot)).succ).restrictScalars ℂ
    have hK : (redG.flag (redG.ord zeroSlot).castSucc ⊓
        redGt.flag (positionMatching (redG.ord zeroSlot)).succ).restrictScalars ℂ = ⊥ := by
      apply eq_of_map_toVec_eq
      rw [Submodule.map_bot]
      exact Submodule.finrank_eq_zero.1 hK0
    have hU : (redG.flag (redG.ord zeroSlot).succ ⊓
        redGt.flag (positionMatching (redG.ord zeroSlot)).succ).restrictScalars ℂ =
        complement (redG.ord zeroSlot) := by
      apply eq_of_map_toVec_eq
      rw [map_complement, map_toVec_inf, positionMatching_ord_zeroSlot]
      change flagVec redG _ ⊓ flagVec redGt _ = _
      rw [flagVec_redG_redGt_and_matching.2.1 _ rfl, flagVec_redG_redGt_and_matching.2.2.1 _ rfl]
      simp only [complementVec, show (redG.ord zeroSlot).val = 1 from rfl, ite_true, one_ne_zero,
        ite_false]
      refine inf_eq_right.2 (Submodule.span_mono ?_)
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      simp
    exact ⟨hK ▸ disjoint_bot_left, by rw [hK, hU, bot_sup_eq]⟩
  · have hKv : ((redG.flag (redG.ord (Sum.inl slotC2)).castSucc ⊓
        redGt.flag (positionMatching (redG.ord (Sum.inl slotC2))).succ).restrictScalars ℂ).map
          (WordModule.toVec tensorB).toLinearMap = Submodule.span ℂ {![-1, 0, 2, 0]} := by
      rw [map_toVec_inf, positionMatching_ord_slotC2]
      exact flagVec_redG_two_inf_flagVec_redGt_two
    have hUv : ((redG.flag (redG.ord (Sum.inl slotC2)).succ ⊓
        redGt.flag (positionMatching (redG.ord (Sum.inl slotC2))).succ).restrictScalars ℂ).map
          (WordModule.toVec tensorB).toLinearMap =
            Submodule.span ℂ {![-1, 0, 2, 0], ![2, -1, -2, 0]} := by
      rw [map_toVec_inf, positionMatching_ord_slotC2]
      change flagVec redG _ ⊓ flagVec redGt _ = _
      rw [flagVec_eq_top redG _ rfl, top_inf_eq]
      exact flagVec_redG_redGt_and_matching.2.2.2.1 _ rfl
    have hLv : (complement (redG.ord (Sum.inl slotC2))).map (WordModule.toVec tensorB).toLinearMap =
        Submodule.span ℂ {![0, -1, 2, 0]} := by
      rw [map_complement]
      simp only [complementVec, show (redG.ord (Sum.inl slotC2)).val = 2 from rfl]
      rfl
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxL
      have h1 := Submodule.mem_map_of_mem (f := (WordModule.toVec tensorB).toLinearMap) hxK
      have h2 := Submodule.mem_map_of_mem (f := (WordModule.toVec tensorB).toLinearMap) hxL
      rw [hKv] at h1
      rw [hLv] at h2
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
      have e0 := congrFun (ha.trans hc.symm) 0
      have h0 : a = 0 := by simpa using e0
      apply (WordModule.toVec tensorB).injective
      simpa [h0] using ha.symm
    · apply eq_of_map_toVec_eq
      rw [Submodule.map_sup, hKv, hLv, hUv, ← Submodule.span_insert]
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact Submodule.subset_span (by simp)
        · rw [SetLike.mem_coe, Submodule.mem_span_pair]
          exact ⟨2, 1, by ext i; fin_cases i <;> simp; norm_num⟩
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact Submodule.subset_span (by simp)
        · rw [SetLike.mem_coe, Submodule.mem_span_pair]
          exact ⟨-2, 1, by ext i; fin_cases i <;> simp; norm_num⟩

/-- `Γ` reads `x ∈ L_j` by the slot of position `j`. -/
theorem gammaGauge_apply_of_mem_complement (b : BlockIndex labels 1) (x : tensorB.WordModule)
    (hx : x ∈ complement (redG.ord b)) :
    gammaGauge (WordModule.toVec tensorB x) =
      Matrix.blockEmbed (slotSize dims) b *ᵥ (redG.leftRow b *ᵥ WordModule.toVec tensorB x) := by
  have hv : WordModule.toVec tensorB x ∈ complementVec (redG.ord b) := by
    rw [← map_complement]; exact Submodule.mem_map_of_mem hx
  have hrow : redG.leftRow b *ᵥ WordModule.toVec tensorB x =
      fun j => redG.gauge (WordModule.toVec tensorB x) ⟨b, j⟩ :=
    redG.leftRow_mulVec b _
  erw [hrow]
  funext y
  erw [blockEmbed_mulVec_apply (z := 1) b (fun y => redG.gauge (WordModule.toVec tensorB x) y) y]
  obtain ⟨n, rfl⟩ := tauG.symm.surjective y
  have e1 : gammaGauge (WordModule.toVec tensorB x) (tauG.symm n) =
      (toC gammaInt *ᵥ WordModule.toVec tensorB x) n := by
    change (toC gammaInt *ᵥ _) (tauG (tauG.symm n)) = _
    rw [Equiv.apply_symm_apply]
  have e2 : redG.gauge (WordModule.toVec tensorB x) (tauG.symm n) =
      (toC g0Int *ᵥ WordModule.toVec tensorB x) n := by
    change (toC g0Int *ᵥ _) (tauG (tauG.symm n)) = _
    rw [Equiv.apply_symm_apply]
  rw [e1, e2, toC_gammaInt_mulVec, toC_g0Int_mulVec]
  rcases slot_cases b rfl with rfl | rfl | rfl
  · rw [complementVec, ite_eq_left (by decide)] at hv
    obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.1 hv
    rw [← hac]
    fin_cases n <;> simp [tauG]
    ring
  · rw [complementVec, ite_eq_right (by decide), ite_eq_left (by decide)] at hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hv
    rw [← ha]
    fin_cases n <;> simp [tauG]
    ring
  · rw [complementVec, ite_eq_right (by decide), ite_eq_right (by decide)] at hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hv
    rw [← ha]
    fin_cases n <;> simp [tauG] <;> ring

theorem matY_mul : matY * !![1, -1; 0, 1] = 1 := by
  ext a c; fin_cases a <;> fin_cases c <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_matY : !![1, -1; 0, 1] * matY = 1 := by
  ext a c; fin_cases a <;> fin_cases c <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_two]

/-- The intertwiners of *Two compressions with different flags* for the three pairs. -/
theorem intertwiner_spec (b : BlockIndex labels 1) :
    (∃ Y : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ,
      intertwiner b * Y = 1 ∧ Y * intertwiner b = 1) ∧
    (∀ i, intertwiner b * slotTensor blocks b i = slotTensor blocks' b i * intertwiner b) ∧
    ∀ x ∈ redG.flag (redG.ord b).succ ⊓ redGt.flag (positionMatching (redG.ord b)).succ,
      redGt.leftRow b *ᵥ WordModule.toVec tensorB x =
        intertwiner b *ᵥ (redG.leftRow b *ᵥ WordModule.toVec tensorB x) := by
  obtain ⟨-, -, -, hl1, hY, -, -, hl0, -, hl2, -⟩ := inf_sup_intertwiner_redG_redGt
  rcases slot_cases b rfl with rfl | rfl | rfl
  · exact ⟨⟨!![1, -1; 0, 1], matY_mul, mul_matY⟩, fun i => hY i,
      fun x hx => hl1 _ (Submodule.mem_map_of_mem hx)⟩
  · refine ⟨⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), mul_one 1, mul_one 1⟩, fun i => ?_,
      fun x hx => ?_⟩
    · exact (by simp : (1 : Matrix (Fin 1) (Fin 1) ℂ) * 0 = 0 * 1)
    · change _ = (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ _
      rw [Matrix.one_mulVec]
      exact hl0 _ (Submodule.mem_map_of_mem hx)
  · refine ⟨⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), mul_one 1, mul_one 1⟩, fun i => ?_,
      fun x hx => ?_⟩
    · exact (by simp : (1 : Matrix (Fin 1) (Fin 1) ℂ) * tensorC₂ i = tensorC₂ i * 1)
    · change _ = (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ _
      erw [Matrix.one_mulVec]
      exact hl2 _ (Submodule.mem_map_of_mem hx)

theorem toC_aInt_apply_eq_zero_of_lt (x y : BlockSpace dims labels 1) (h : ordG y.1 < ordG x.1) :
    toC aInt (tauG x) (tauG y) = 0 := by
  change complexOfRing (Int.castRingHom ℂ) aInt (tauG x) (tauG y) = 0
  rw [complexOfRing_apply, aInt_apply_eq_zero_of_lt x y h, map_zero]

theorem toC_atInt_apply_eq_zero_of_lt (x y : BlockSpace dims labels 1) (h : ordGt y.1 < ordGt x.1) :
    toC atInt (tauGt x) (tauGt y) = 0 := by
  change complexOfRing (Int.castRingHom ℂ) atInt (tauGt x) (tauGt y) = 0
  rw [complexOfRing_apply, atInt_apply_eq_zero_of_lt x y h, map_zero]

theorem aInt_apply_diag (b : BlockIndex labels 1) (p q : Fin (slotSize dims b)) :
    aInt (tauG ⟨b, p⟩) (tauG ⟨b, q⟩) = if p = q then 1 else 0 := by
  rcases slot_cases b rfl with rfl | rfl | rfl <;> revert p q <;> decide

theorem atInt_apply_diag (b : BlockIndex labels 1) (p q : Fin (slotSize dims b)) :
    atInt (tauGt ⟨b, p⟩) (tauGt ⟨b, q⟩) = if p = q then 1 else 0 := by
  rcases slot_cases b rfl with rfl | rfl | rfl <;> revert p q <;> decide

theorem toC_aInt_apply_diag (b : BlockIndex labels 1) (p q : Fin (slotSize dims b)) :
    toC aInt (tauG ⟨b, p⟩) (tauG ⟨b, q⟩) =
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) p q := by
  change complexOfRing (Int.castRingHom ℂ) aInt (tauG ⟨b, p⟩) (tauG ⟨b, q⟩) = _
  rw [complexOfRing_apply, aInt_apply_diag, Matrix.one_apply]
  split_ifs <;> simp

theorem toC_atInt_apply_diag (b : BlockIndex labels 1) (p q : Fin (slotSize dims b)) :
    toC atInt (tauGt ⟨b, p⟩) (tauGt ⟨b, q⟩) =
      (1 : Matrix (Fin (slotSize dims b)) (Fin (slotSize dims b)) ℂ) p q := by
  change complexOfRing (Int.castRingHom ℂ) atInt (tauGt ⟨b, p⟩) (tauGt ⟨b, q⟩) = _
  rw [complexOfRing_apply, atInt_apply_diag, Matrix.one_apply]
  split_ifs <;> simp

/-- The matching read on slots is the identity of labels. -/
theorem ord_redGt_eq_matching (b : BlockIndex labels 1) :
    redGt.ord b = positionMatching (redG.ord b) := by
  rcases slot_cases b rfl with rfl | rfl | rfl
  · exact positionMatching_ord_slotC1.symm
  · exact positionMatching_ord_zeroSlot.symm
  · exact positionMatching_ord_slotC2.symm

/-- `g = 𝔄 Γ`. -/
theorem gaugeMatrix_redG_eq_mul : gaugeMatrix redG.gauge =
    (toC aInt).submatrix tauG tauG * gaugeMatrix gammaGauge := by
  rw [gaugeMatrix_redG, gaugeMatrix_gammaGauge, Matrix.submatrix_mul_equiv, ← complexOfRing_mul,
    aInt_mul_gammaInt]

/-- `g̃ = 𝔄̃ P_X Γ`. -/
theorem gaugeMatrix_redGt_eq_mul : gaugeMatrix redGt.gauge = (toC atInt).submatrix tauGt tauGt *
    (∑ b, Matrix.blockEmbed (slotSize dims) b * intertwiner b *
      Matrix.blockProj (slotSize dims) b) * gaugeMatrix gammaGauge := by
  rw [sum_blockEmbed_mul_intertwiner_mul_blockProj, gaugeMatrix_redGt, gaugeMatrix_gammaGauge,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← complexOfRing_mul,
    ← complexOfRing_mul, atInt_mul_pxInt_mul_gammaInt]

theorem blockTriangular_aInt :
    ((toC aInt).submatrix tauG tauG).BlockTriangular fun x => redG.ord x.1 :=
  fun x y hxy => toC_aInt_apply_eq_zero_of_lt x y hxy

theorem blockDiag'_aInt (b : BlockIndex labels 1) :
    ((toC aInt).submatrix tauG tauG).blockDiag' b = 1 := by
  ext p q
  rw [Matrix.blockDiag'_apply, Matrix.submatrix_apply]
  exact toC_aInt_apply_diag b p q

theorem blockTriangular_atInt :
    ((toC atInt).submatrix tauGt tauGt).BlockTriangular fun x => redGt.ord x.1 :=
  fun x y hxy => toC_atInt_apply_eq_zero_of_lt x y hxy

theorem blockDiag'_atInt (b : BlockIndex labels 1) :
    ((toC atInt).submatrix tauGt tauGt).blockDiag' b = 1 := by
  ext p q
  rw [Matrix.blockDiag'_apply, Matrix.submatrix_apply]
  exact toC_atInt_apply_diag b p q

/-- `g̃ g⁻¹ = 𝔄̃ P_X 𝔄⁻¹`, in the bond coordinates. -/
theorem gt_mul_g0Inv_submatrix : (toC gtInt).submatrix tauGt id * (toC g0InvInt).submatrix id tauG =
    (toC atInt).submatrix tauGt tauGt * (toC pxInt).submatrix tauGt tauG *
      ((toC aInt).submatrix tauG tauG)⁻¹ := by
  have hinvA : (toC aInvInt).submatrix tauG tauG * (toC aInt).submatrix tauG tauG = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← complexOfRing_mul, aInvInt_mul_aInt, complexOfRing_one]
    exact Matrix.submatrix_one_equiv tauG
  have hL : ∀ M N : Matrix (Fin 4) (Fin 4) ℂ,
      M.submatrix tauGt id * N.submatrix id tauG = (M * N).submatrix tauGt tauG :=
    fun M N => (Matrix.submatrix_mul M N _ _ _ Function.bijective_id).symm
  rw [Matrix.inv_eq_left_inv hinvA, hL, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    ← complexOfRing_mul, ← complexOfRing_mul, ← complexOfRing_mul, gtInt_mul_g0InvInt]

/-- **The factorization** (*The asymmetric fundamental theorem of matrix product states*, Example
6.16): with the complements `L₁ = M₁`, `L₂ = M̃₁` (forced, `K = 0` at both positions) and
`L₃ = ℂ (V_{C₂} + V₀) = ℂ (0, -1, 2, 0)`, the intertwiners `X_{C₁} = Y`, `X₀ = X_{C₂} = 1` and
`Γ = 𝔄⁻¹ g`, the factors `𝔄`, `P_X`, `𝔄̃` are the printed matrices (in the bond coordinates of `g`
and `g̃`), `𝔄` and `𝔄̃` are unipotent in the two orders, and `g̃ g⁻¹ = 𝔄̃ P_X 𝔄⁻¹`. The matching
read on slots is the identity of labels (`C₁ ↦ C₁'`, `0 ↦ 0`, `C₂ ↦ C₂`). -/
theorem isAdaptedFactorization_redG_redGt :
    let 𝔄 : Matrix (BlockSpace dims labels 1) (BlockSpace dims labels 1) ℂ :=
      (toC aInt).submatrix tauG tauG
    let 𝔄' : Matrix (BlockSpace dims labels 1) (BlockSpace dims labels 1) ℂ :=
      (toC atInt).submatrix tauGt tauGt
    let PX : Matrix (BlockSpace dims labels 1) (BlockSpace dims labels 1) ℂ :=
      (toC pxInt).submatrix tauGt tauG
    IsAdaptedFactorization redG redGt isNormal_blocks dims_pos isNormal_blocks' dims_pos
      (Equiv.refl (BlockIndex labels 1)) complement gammaGauge 𝔄 𝔄' intertwiner ∧
    (∑ b, Matrix.blockEmbed (slotSize dims) b * intertwiner b *
      Matrix.blockProj (slotSize dims) b) = PX ∧
    gaugeMatrix redG.gauge = (toC g0Int).submatrix tauG id ∧
    gaugeMatrix redGt.gauge = (toC gtInt).submatrix tauGt id ∧
    gaugeMatrix gammaGauge = (toC gammaInt).submatrix tauG id ∧
    gaugeMatrix redGt.gauge * gaugeMatrixInv redG.gauge = 𝔄' * PX * 𝔄⁻¹ :=
  ⟨⟨ord_redGt_eq_matching, disjoint_complement_and_sup_eq, gammaGauge_apply_of_mem_complement,
    intertwiner_spec, blockTriangular_aInt,
    blockDiag'_aInt, blockTriangular_atInt, blockDiag'_atInt, gaugeMatrix_redG_eq_mul,
    gaugeMatrix_redGt_eq_mul⟩, sum_blockEmbed_mul_intertwiner_mul_blockProj, gaugeMatrix_redG,
    gaugeMatrix_redGt, gaugeMatrix_gammaGauge,
    (congrArg₂ (· * ·) gaugeMatrix_redGt gaugeMatrixInv_redG).trans gt_mul_g0Inv_submatrix⟩

end Worked

end MultiBlockExamples
