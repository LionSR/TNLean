/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoveringMatching
import TNLean.MPS.Examples.SharpnessOneBlock
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

Each main theorem of the uniqueness programme (lecture note MultiBlockUniqueness) is
instantiated at explicit types: two letters, bond dimension three, and families of blocks
labelled by `Fin 2` and `Fin 3`. Each probe restates the conclusion and closes it by the
theorem itself, so a change of statement fails here. The axiom checks pin the standard axioms.
-/

open scoped Matrix
open MPSTensor

/-! ### Matching of covering chains (Proposition 4.2 (The matching)) -/

example (c c' : CoveringMatching.CoveringChain (Submodule ℂ (Fin 3 → ℂ)) 2) (k : Fin 2) :
    c.M k.castSucc ⊔ (c.M k.succ ⊓ c'.M (c.jump c' k).succ) = c.M k.succ ∧
      c'.M (c.jump c' k).castSucc ⊔ (c.M k.succ ⊓ c'.M (c.jump c' k).succ) =
        c'.M (c.jump c' k).succ ∧
      c.M k.succ ⊓ c'.M (c.jump c' k).succ ⊓ c.M k.castSucc =
        c.M k.castSucc ⊓ c'.M (c.jump c' k).succ ∧
      c.M k.succ ⊓ c'.M (c.jump c' k).succ ⊓ c'.M (c.jump c' k).castSucc =
        c.M k.castSucc ⊓ c'.M (c.jump c' k).succ ∧
      c.M k.castSucc ⊓ c'.M (c.jump c' k).succ = c.M k.succ ⊓ c'.M (c.jump c' k).castSucc :=
  c.jump_sup_eq c' k

/-! ### Compressions as labelled invariant flags
(Proposition 2.3 (Reductions are labelled flags with an adapted basis)) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (F : FlagData B.WordModule S C) (k : Fin (F.r + 1)) :
    F.toMultiBlockCompression.flag (Fin.cast (congrArg (· + 1) F.r_eq) k) = F.H k :=
  F.toMultiBlockCompression_flag k

/-! ### Long words (Lemma 5.6 (Long words in a triangular form)) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P : MultiBlockCompression B S C) (w : List (Fin 2)) (hw : P.z ≤ w.length)
    {x y : BlockSpace D S P.z}
    (hS : ∀ s : {s // s ∈ S}, P.ord (Sum.inl s) ∉ Set.Icc (P.ord x.1) (P.ord y.1)) :
    conjMatrix P.gauge (Kraus.evalWord B w) x y = 0 :=
  P.conjMatrix_evalWord_eq_zero_of_forall_notMem w hw hS

/-! ### Theorem A (Theorem 4.3 (A: the blocks are unique)) -/

example {D : Fin 2 → ℕ} {D' : Fin 3 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
    {S' : Finset (Fin 3)} {C : ∀ s, MPSTensor 2 (D s)} {C' : ∀ t, MPSTensor 2 (D' t)}
    (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t) :
    P.z = Q.z ∧ ∃ τ : {s // s ∈ S} ≃ {t // t ∈ S'},
      ∀ s, IsGaugeRelated (C s.1) (C' (τ s).1) :=
  P.z_eq_and_exists_equiv_isGaugeRelated Q hC hD hC' hD'

/-! ### Theorem B (Theorem 5.2 (B: two reductions with the same flag)) -/

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
    (P.conjT ht hμ hdiag).flag k = P.flag k :=
  P.conjT_flag ht hμ hdiag k

/-! ### Theorem C (Theorem 5.3 (C: two reductions with different flags)) -/

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

/-! ### Split reductions (Proposition 5.11 (Uniqueness of split reductions)) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P Q : MultiBlockCompression B S C} (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬ IsGaugeRelated (C s) (C t)) (s : {s // s ∈ S}) :
    Q.left s = P.splitScalar Q s • P.left s :=
  MultiBlockCompression.left_eq_smul_of_split_of_pairwise_not_isGaugeRelated hP hQ hC hsep s

/-! ### Theorem E (Theorem 5.4 (E: a basis adapted to both flags)) -/

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

/-! ### Theorem D (Theorem 5.5 (D: the set of all reductions)) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P : MultiBlockCompression B S C} (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) (g : (Fin 3 → ℂ) ≃ₗ[ℂ] (BlockSpace D S P.z → ℂ))
    (htri : ∀ i, (conjMatrix g (B i)).BlockTriangular fun x => P.ord x.1)
    (hdiag : ∀ i b, (conjMatrix g (B i)).blockDiag' b = blockOf D C i b) :
    (∀ k, (P.withGauge g htri hdiag).flag k = P.flag k) ↔
      ∃ (h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
        (ht : h.BlockTriangular fun x => P.ord x.1) (μ : BlockIndex S P.z → ℂ)
        (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, h.blockDiag' b = μ b • 1),
        g = P.conjTGauge ht hμ hh :=
  MultiBlockCompression.flag_fibre_eq_orbit hC hD g htri hdiag

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (F : FlagData B.WordModule S C) :
    ∃ (P : MultiBlockCompression B S C) (h : F.r + 1 = S.card + P.z + 1),
      ∀ k, P.flag (Fin.cast h k) = F.H k :=
  F.exists_multiBlockCompression_flag_eq

/-! ### Corollaries C1 and C2 (Corollary 5.7 (C1: bare uniqueness at the ends of the flag),
Corollary 5.8 (C2: the one-block theorem)) -/

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

/-! ### Sharpness of the bound (Example 5.9 (Sharpness of the bound), Example 5.13 (Two different
flags with one block)) -/

example : ¬ ∃ c : ℂ,
    SharpnessOneBlock.lastCompression.left oneSlotMem =
      c • SharpnessOneBlock.firstCompression.left oneSlotMem :=
  SharpnessOneBlock.not_exists_left_eq_smul

example (w : List (Fin 1)) (hw : w ≠ []) :
    SharpnessOneBlock.lastCompression.left oneSlotMem *
        Kraus.evalWord SharpnessOneBlock.tensorB w =
      SharpnessOneBlock.firstCompression.left oneSlotMem *
        Kraus.evalWord SharpnessOneBlock.tensorB w :=
  SharpnessOneBlock.left_mul_evalWord_eq w hw

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
info: 'MPSTensor.MultiBlockCompression.conjT_flag'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.conjT_flag

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
info: 'MPSTensor.MultiBlockCompression.flag_fibre_eq_orbit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockCompression.flag_fibre_eq_orbit

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
info: 'SharpnessOneBlock.not_exists_left_eq_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SharpnessOneBlock.not_exists_left_eq_smul

set_option linter.hashCommand false in
/--
info: 'SharpnessOneBlock.left_mul_evalWord_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SharpnessOneBlock.left_mul_evalWord_eq
