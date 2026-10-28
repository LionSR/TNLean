/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoveringMatching
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlock
import TNLean.MPS.FundamentalTheorem.Reduction.LongWords
import TNLean.MPS.FundamentalTheorem.Reduction.SplitUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessDifferentFlags
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessLongWords
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessSameFlag

/-!
# Statement probes and axiom checks for the uniqueness of multi-block reductions

Each main theorem on the uniqueness of multi-block compressions (blueprint `sec:asym_uniqueness`) is
instantiated at explicit types: two letters, bond dimension three, and families of blocks
labelled by `Fin 2` and `Fin 3`. Each probe restates the conclusion and closes it by the
theorem itself, so a change of statement fails here. The axiom checks pin the standard axioms.
-/

open scoped Matrix
open MPSTensor

/-! ### Matching of covering chains (blueprint `prop:asym_uniq_matching`, *The matching*) -/

example (c c' : CoveringMatching.CoveringChain (Submodule ℂ (Fin 3 → ℂ)) 2) (k : Fin 2) :
    c.toFun k.castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (c.jump c' k).succ) = c.toFun k.succ ∧
      c'.toFun (c.jump c' k).castSucc ⊔ (c.toFun k.succ ⊓ c'.toFun (c.jump c' k).succ) =
        c'.toFun (c.jump c' k).succ ∧
      c.toFun k.succ ⊓ c'.toFun (c.jump c' k).succ ⊓ c.toFun k.castSucc =
        c.toFun k.castSucc ⊓ c'.toFun (c.jump c' k).succ ∧
      c.toFun k.succ ⊓ c'.toFun (c.jump c' k).succ ⊓ c'.toFun (c.jump c' k).castSucc =
        c.toFun k.castSucc ⊓ c'.toFun (c.jump c' k).succ ∧
      c.toFun k.castSucc ⊓ c'.toFun (c.jump c' k).succ =
        c.toFun k.succ ⊓ c'.toFun (c.jump c' k).castSucc :=
  c.jump_sup_eq c' k

/-! ### Compressions as labelled invariant flags (blueprint `prop:asym_uniq_dictionary`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (F : FlagData B.WordModule S C) (k : Fin (F.r + 1)) :
    F.toMultiBlockCompression.flag (Fin.cast (congrArg (· + 1) F.r_eq) k) = F.H k :=
  F.toMultiBlockCompression_flag k

/-! ### Long words (blueprint `lem:asym_uniq_long_words`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P : MultiBlockCompression B S C) (w : List (Fin 2)) (hw : P.z ≤ w.length)
    {x y : BlockSpace D S P.z}
    (hS : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) ∉ Set.Icc (P.ord x.1) (P.ord y.1)) :
    conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_notMem w hw hS

/-! ### The blocks are unique (blueprint `thm:asym_uniq_blocks`) -/

example {D : Fin 2 → ℕ} {D' : Fin 3 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
    {S' : Finset (Fin 3)} {C : ∀ s, MPSTensor 2 (D s)} {C' : ∀ t, MPSTensor 2 (D' t)}
    (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t) :
    P.z = Q.z ∧ ∃ τ : {s // s ∈ S} ≃ {t // t ∈ S'},
      ∀ s, IsGaugeRelated (C s.1) (C' (τ s).1) :=
  P.z_eq_and_exists_equiv_isGaugeRelated Q hC hD hC' hD'

/-! ### Two compressions with the same flag (blueprint `thm:asym_uniq_same_flag`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P : MultiBlockCompression B S C} {g : (Fin 3 → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
    {htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1}
    {hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b}
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (P.withGauge g htri hdiag).leftRow b = P.coordChangeScalar g b • P.leftRow b +
      ∑ c with P.ord b < P.ord c,
        (coordChange P.gauge g).submatrix (Sigma.mk b) (Sigma.mk c) * P.leftRow c :=
  MultiBlockCompression.leftRow_withGauge hC hflag b

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P : MultiBlockCompression B S C} {g : (Fin 3 → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ)}
    {htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1}
    {hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b}
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hflag : ∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) (b : BlockIndex S P.z) :
    (P.withGauge g htri hdiag).rightCol b = (P.coordChangeScalar g b)⁻¹ • P.rightCol b +
      ∑ c with P.ord c < P.ord b,
        P.rightCol c * (coordChange P.gauge g)⁻¹.submatrix (Sigma.mk c) (Sigma.mk b) :=
  MultiBlockCompression.rightCol_withGauge hC hD hflag b

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P : MultiBlockCompression B S C) {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1) (k : Fin (S.card + P.z + 1)) :
    (P.conjTriangular ht hμ hdiag).flag k = P.flag k :=
  P.conjTriangular_flag ht hμ hdiag k

/-! ### Two compressions with different flags (blueprint `thm:asym_uniq_different_flags`) -/

example {D : Fin 2 → ℕ} {D' : Fin 3 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
    {S' : Finset (Fin 3)} {C : ∀ s, MPSTensor 2 (D s)} {C' : ∀ t, MPSTensor 2 (D' t)}
    (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)
    (k : Fin (S.card + P.z)) {b : BlockIndex S P.z} (hb : P.ord b = k) {b' : BlockIndex S' Q.z}
    (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k) :
    ∃ (X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ)
      (Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ),
      X * Y = 1 ∧ Y * X = 1 ∧ (∀ i, X * slotTensor C b i = slotTensor C' b' i * X) ∧
      (∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
        Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) ∧
      ∀ v, (WordModule.toVec B).symm (Q.rightCol b' *ᵥ v - P.rightCol b *ᵥ (Y *ᵥ v)) ∈
        P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC' hD' k).castSucc :=
  P.exists_intertwiner_of_matching Q hC hD hC' hD' k hb hb'

example {D : Fin 2 → ℕ} {D' : Fin 3 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
    {S' : Finset (Fin 3)} {C : ∀ s, MPSTensor 2 (D s)} {C' : ∀ t, MPSTensor 2 (D' t)}
    (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)
    (k : Fin (S.card + P.z)) {b : BlockIndex S P.z} (hb : P.ord b = k) {b' : BlockIndex S' Q.z}
    (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k) :
    ∃! X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ,
      (∀ i, X * slotTensor C b i = slotTensor C' b' i * X) ∧
      ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
        Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) :=
  P.existsUnique_intertwiner_of_matching Q hC hD hC' hD' k hb hb'

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (k : Fin (S.card + P.z)) (s : {s // s ∈ S})
    (hk : P.ord (Sum.inl s) = k) (hk' : Q.ord (Sum.inl s) = P.matching Q hC hD hC hD k) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC hD k).succ,
        Q.leftRow (Sum.inl s) *ᵥ WordModule.toVec B x =
          c • (P.leftRow (Sum.inl s) *ᵥ WordModule.toVec B x)) ∧
      ∀ v, (WordModule.toVec B).symm
          (Q.rightCol (Sum.inl s) *ᵥ v - c⁻¹ • (P.rightCol (Sum.inl s) *ᵥ v)) ∈
        P.flag k.castSucc ⊔ Q.flag (P.matching Q hC hD hC hD k).castSucc :=
  P.exists_smul_of_matching_inl Q hC hD k s hk hk'

/-! ### Split reductions (blueprint `prop:asym_uniq_split`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P Q : MultiBlockCompression B S C} (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    Q.left s = P.splitScalar Q s • P.left s :=
  MultiBlockCompression.left_eq_smul_of_split_of_pairwise_not_isGaugeRelated hP hQ hC hsep s

/-! ### A basis adapted to both flags (blueprint `thm:asym_uniq_common_basis`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) :
    gaugeMatrix Q.gauge * gaugeMatrixInv P.gauge =
      P.unipotentFactor' Q hC hD hC hD * P.matchingPermMatrix Q hC hD hC hD *
        (P.unipotentFactor Q hC hD hC hD)⁻¹ :=
  P.gaugeMatrix_mul_gaugeMatrixInv_eq Q hC hD hC hD

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (k : Fin (S.card + P.z + 1)) :
    (P.flag k).restrictScalars ℂ =
      ⨆ (j : Fin (S.card + P.z)) (_ : j.castSucc < k), P.matchedCompl Q hC hD hC hD j :=
  P.flag_eq_iSup_matchedCompl Q hC hD hC hD k

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) : iSupIndep (P.matchedCompl Q hC hD hC hD) :=
  P.iSupIndep_matchedCompl Q hC hD hC hD

/-! ### The set of all compressions (blueprint `thm:asym_uniq_all`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P : MultiBlockCompression B S C} (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (g : (Fin 3 → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b) :
    (∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) ↔
      ∃ (h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
        (ht : h.BlockTriangular fun x => P.ord x.1) (μ : BlockIndex S P.z → ℂ)
        (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, h.blockDiag' b = μ b • 1),
        g = P.conjTriangularGauge ht hμ hh :=
  MultiBlockCompression.flag_withGauge_eq_iff_exists_eq_conjTriangularGauge hC hD g htri hdiag

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (F : FlagData B.WordModule S C) :
    ∃ (P : MultiBlockCompression B S C) (h : F.r + 1 = S.card + P.z + 1),
      ∀ k, P.flag (Fin.cast h k) = F.H k :=
  F.exists_multiBlockCompression_flag_eq

/-! ### Bare uniqueness at the ends of the flag; the one-block theorem
(blueprint `cor:asym_uniq_one_block`) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) {s : {s // s ∈ S}} (hS : ∀ t ∈ S, t = s.1) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ w : List (Fin 2), 3 - D s.1 ≤ w.length →
      Q.left s * Kraus.evalWord B w = c • (P.left s * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * Q.right s = c⁻¹ • (Kraus.evalWord B w * P.right s) :=
  P.exists_smul_single_block Q hC hD hS

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P Q : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) {s : {s // s ∈ S}}
    (hs : ∀ t ∈ S, IsGaugeRelated (C s.1) (C t) → t = s.1)
    (hP : ∀ b, P.ord b ≤ P.ord (Sum.inl s)) (hQ : ∀ b, Q.ord b ≤ Q.ord (Sum.inl s)) :
    ∃ c : ℂ, c ≠ 0 ∧ Q.left s = c • P.left s :=
  P.exists_left_eq_smul_of_last Q hC hD hs hP hQ

/-! ### Sharpness of the bound (*The asymmetric fundamental theorem of matrix product states*,
Examples 6.10 and 6.15) -/

example : ¬ ∃ c : ℂ,
    MultiBlockExamples.SharpnessOneBlock.lastCompression.left oneSlotMem =
      c • MultiBlockExamples.SharpnessOneBlock.firstCompression.left oneSlotMem :=
  MultiBlockExamples.SharpnessOneBlock.not_exists_left_eq_smul

example (w : List (Fin 1)) (hw : w ≠ []) :
    MultiBlockExamples.SharpnessOneBlock.lastCompression.left oneSlotMem *
        Kraus.evalWord MultiBlockExamples.SharpnessOneBlock.tensorB w =
      MultiBlockExamples.SharpnessOneBlock.firstCompression.left oneSlotMem *
        Kraus.evalWord MultiBlockExamples.SharpnessOneBlock.tensorB w :=
  MultiBlockExamples.SharpnessOneBlock.left_mul_evalWord_eq w hw

/-! ### Axioms -/

set_option linter.hashCommand false in
/--
info: 'CoveringMatching.CoveringChain.jump_sup_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoveringMatching.CoveringChain.jump_sup_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.z_eq_and_exists_equiv_isGaugeRelated'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.z_eq_and_exists_equiv_isGaugeRelated

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.leftRow_withGauge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.leftRow_withGauge

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.rightCol_withGauge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.rightCol_withGauge

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.conjTriangular_flag'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.conjTriangular_flag

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_intertwiner_of_matching'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.exists_intertwiner_of_matching

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.existsUnique_intertwiner_of_matching'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.existsUnique_intertwiner_of_matching

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_smul_of_matching_inl'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.exists_smul_of_matching_inl

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.left_eq_smul_of_split_of_pairwise_not_isGaugeRelated'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.left_eq_smul_of_split_of_pairwise_not_isGaugeRelated

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_forall_notMem'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.conjMatrix_evalWord_eq_zero_of_forall_notMem

set_option linter.hashCommand false in
/--
info: 'MPSTensor.FlagData.toMultiBlockCompression_flag'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FlagData.toMultiBlockCompression_flag

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.flag_eq_iSup_matchedCompl'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.flag_eq_iSup_matchedCompl

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.iSupIndep_matchedCompl'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.iSupIndep_matchedCompl

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.flag_withGauge_eq_iff_exists_eq_conjTriangularGauge'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.flag_withGauge_eq_iff_exists_eq_conjTriangularGauge

set_option linter.hashCommand false in
/--
info: 'MPSTensor.FlagData.exists_multiBlockCompression_flag_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FlagData.exists_multiBlockCompression_flag_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_smul_single_block'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.exists_smul_single_block

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_left_eq_smul_of_last'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.exists_left_eq_smul_of_last

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.not_exists_left_eq_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.not_exists_left_eq_smul

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.left_mul_evalWord_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.left_mul_evalWord_eq
