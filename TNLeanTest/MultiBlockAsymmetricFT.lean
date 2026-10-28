/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoveringMatching
import TNLean.MPS.Examples.MultiBlock.NoGauge
import TNLean.MPS.Examples.MultiBlock.OneBlock
import TNLean.MPS.Examples.MultiBlock.Periodic
import TNLean.MPS.Examples.MultiBlock.Running
import TNLean.MPS.Examples.MultiBlock.Multiplicity
import TNLean.MPS.Examples.MultiBlock.Worked
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlock
import TNLean.MPS.FundamentalTheorem.Reduction.Flag
import TNLean.MPS.FundamentalTheorem.Reduction.IrreducibleTensor
import TNLean.MPS.FundamentalTheorem.Reduction.SplitUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessDifferentFlags
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessFlag
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessMatrixForm
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessSameFlag
import TNLean.MPS.Symmetry.MPOSymmetry.ZipperUniqueness

/-!
# Statement probes and axiom checks for the asymmetric fundamental theorem

The library formalizes *The asymmetric fundamental theorem of matrix product states* (blueprint
`sec:asym_uniqueness`): the lemmas on irreducible tensors and the comparison of two reductions,
possibly onto two different families of blocks, including the components of *A basis adapted to
both flags*. Each library declaration of the first two groups of sections below is instantiated at
explicit types: two letters, bond dimension three, and families of blocks labelled by `Fin 2` and
`Fin 3`. Each probe restates the conclusion and closes it by the theorem itself, so a change of
statement fails here. The axiom checks pin the standard axioms for every library declaration and
for the worked examples.
-/

open scoped Matrix
open MPSTensor WordAlgebra

/-! ### Irreducible tensors and simple modules -/

example (C : MPSTensor 2 3) :
    Matrix.IsIrreducibleAction C ∧ 0 < 3 ↔ IsSimpleModule (WordAlgebra 2) C.WordModule :=
  isIrreducibleAction_and_pos_iff_isSimpleModule C

example (C : MPSTensor 2 3) (hC : Kraus.IsNormal C) (hD : 0 < 3) :
    Matrix.IsIrreducibleAction C :=
  isIrreducibleAction_of_isNormal C hC hD

example {A : MPSTensor 2 3} (hA : Kraus.IsNormal A) : ∃ i, A i ≠ 0 :=
  exists_ne_zero_of_isNormal hA

/-! ### Schur's lemma (*The asymmetric fundamental theorem of matrix product states*, Lemma 3.1) -/

example {C : MPSTensor 2 3} {C' : MPSTensor 2 2} (hC : Matrix.IsIrreducibleAction C)
    (hC' : Matrix.IsIrreducibleAction C') {X : Matrix (Fin 2) (Fin 3) ℂ}
    (hX : ∀ i, X * C i = C' i * X) :
    X = 0 ∨ ∃ Y : Matrix (Fin 3) (Fin 2) ℂ, X * Y = 1 ∧ Y * X = 1 ∧ 3 = 2 :=
  eq_zero_or_exists_inverse_of_intertwines hC hC' hX

example {C : MPSTensor 2 3} (hC : Matrix.IsIrreducibleAction C) {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : ∀ i, X * C i = C i * X) : ∃ c : ℂ, X = c • 1 :=
  exists_eq_smul_one_of_intertwines hC hX

example {C : MPSTensor 2 3} {C' : MPSTensor 2 2} (hC : Matrix.IsIrreducibleAction C)
    {X₀ : Matrix (Fin 2) (Fin 3) ℂ} {Y₀ : Matrix (Fin 3) (Fin 2) ℂ}
    (hXY : X₀ * Y₀ = 1) (hYX : Y₀ * X₀ = 1) (hX₀ : ∀ i, X₀ * C i = C' i * X₀)
    {X : Matrix (Fin 2) (Fin 3) ℂ} (hX : ∀ i, X * C i = C' i * X) :
    ∃ c : ℂ, X = c • X₀ :=
  exists_eq_smul_of_intertwines hC hXY hYX hX₀ hX

/-! ### Traces along a flag
(*The asymmetric fundamental theorem of matrix product states*, Lemma 4.1) -/

example (B : MPSTensor 2 3) (M : Fin (2 + 1) → Submodule (WordAlgebra 2) B.WordModule)
    (h0 : M 0 = ⊥) (hlast : M (Fin.last 2) = ⊤) (hmono : Monotone M) (w : List (Fin 2)) :
    (Kraus.evalWord B w).trace =
      ∑ k : Fin 2, traceWord (Submodule.subquot (M k.castSucc) (M k.succ)) w :=
  trace_evalWord_eq_sum_traceWord_subquot B M h0 hlast hmono w

/-! ### Density (*The asymmetric fundamental theorem of matrix product states*, Theorem 4.2) -/

example {D : Fin 2 → ℕ} (C : ∀ j, MPSTensor 2 (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k))
    (Y : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) :
    ∃ a : WordAlgebra 2, ∀ j, LinearMap.toMatrix' ((C j).wordRep.asAlgebraHom a) = Y j :=
  exists_eval_eq_of_pairwise_not_isGaugeRelated C hirr hne Y

example {D : Fin 2 → ℕ} (C : ∀ j, MPSTensor 2 (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k)) (hlet : ∀ j, ∃ i, C j i ≠ 0)
    (Y : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) :
    ∃ a : WordAlgebra 2, aug a = 0 ∧
      ∀ j, LinearMap.toMatrix' ((C j).wordRep.asAlgebraHom a) = Y j :=
  exists_aug_eq_zero_eval_eq_of_pairwise_not_isGaugeRelated C hirr hne hlet Y

/-! ### Independence of traces
(*The asymmetric fundamental theorem of matrix product states*, Corollary 4.3) -/

example {D : Fin 2 → ℕ} (C : ∀ j, MPSTensor 2 (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k)) (hlet : ∀ j, ∃ i, C j i ≠ 0)
    (c : Fin 2 → ℂ)
    (h : ∀ w : List (Fin 2), w ≠ [] → ∑ j, c j * (Kraus.evalWord (C j) w).trace = 0) :
    c = 0 :=
  eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero C hirr hne hlet c h

/-! ### The maps (*The asymmetric fundamental theorem of matrix product states*, equation (1.2)) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P : MultiBlockCompression B S C) {b b' : BlockIndex S P.z} (h : b ≠ b') :
    P.leftRow b * P.rightCol b' = 0 :=
  P.leftRow_mul_rightCol_of_ne h

/-! ### The torsor (blueprint `thm:asym_uniq_same_flag`, *Two compressions with the same flag*) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (P : MultiBlockCompression B S C) (hC : ∀ s ∈ S, Kraus.IsNormal (C s))
    (hD : ∀ s ∈ S, 0 < D s) :
    Set.BijOn
      (fun p : {p : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ × (BlockIndex S P.z → ℂ) //
          p.1.BlockTriangular (fun x => P.ord x.1) ∧ (∀ b, p.2 b ≠ 0) ∧
            ∀ b, p.1.blockDiag' b = p.2 b • 1} =>
        P.conjTriangular p.2.1 p.2.2.1 p.2.2.2)
      Set.univ
      {Q : MultiBlockCompression B S C | ∃ hz : Q.z = P.z, HEq Q.ord P.ord ∧
          ∀ k, Q.flag (Fin.cast (by rw [hz]) k) = P.flag k} :=
  P.bijOn_conjTriangular hC hD

/-! ### The set of all reductions
(blueprint `thm:asym_uniq_all`, *The set of all compressions*) -/

example (B : MPSTensor 2 3) (S : Finset (Fin 2)) {D : Fin 2 → ℕ} (C : ∀ s, MPSTensor 2 (D s))
    (z : ℕ) :
    (∃ P : MultiBlockCompression B S C, P.z = z) ↔
      ∃ F : FlagData B.WordModule S C, F.z = z :=
  MultiBlockCompression.exists_z_eq_iff_exists_flagData B S C z

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
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
      p.1 = P.toFlagData :=
  MultiBlockCompression.existsUnique_conjTriangular hC hD rep hrep P

/- The hypothesis `hrep` of `existsUnique_conjTriangular` can be met: the compression of a
labelled flag has that labelled flag. -/
example {D : Fin 2 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)}
    (F : FlagData B.WordModule S C) : F.toMultiBlockCompression.toFlagData = F :=
  F.toMultiBlockCompression_toFlagData

example {D : Fin 2 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)}
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
    (P : MultiBlockCompression B S C) :
    (∃! p : (F : FlagData B.WordModule S C) ×
        Matrix (BlockSpace D S F.toMultiBlockCompression.z)
          (BlockSpace D S F.toMultiBlockCompression.z) ℂ,
      ∃ (ht : p.2.BlockTriangular fun x => p.1.toMultiBlockCompression.ord x.1)
        (μ : BlockIndex S p.1.toMultiBlockCompression.z → ℂ)
        (hμ : ∀ b, μ b ≠ 0) (hh : ∀ b, p.2.blockDiag' b = μ b • 1),
        P = p.1.toMultiBlockCompression.conjTriangular ht hμ hh) ∧
    ∀ p : (F : FlagData B.WordModule S C) ×
        Matrix (BlockSpace D S F.toMultiBlockCompression.z)
          (BlockSpace D S F.toMultiBlockCompression.z) ℂ,
      (∃ (ht : p.2.BlockTriangular fun x => p.1.toMultiBlockCompression.ord x.1)
        (μ : BlockIndex S p.1.toMultiBlockCompression.z → ℂ) (hμ : ∀ b, μ b ≠ 0)
        (hh : ∀ b, p.2.blockDiag' b = μ b • 1),
        P = p.1.toMultiBlockCompression.conjTriangular ht hμ hh) →
      p.1 = P.toFlagData :=
  MultiBlockCompression.existsUnique_conjTriangular hC hD FlagData.toMultiBlockCompression
    FlagData.toMultiBlockCompression_toFlagData P

example {D : Fin 2 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
    {C : ∀ s, MPSTensor 2 (D s)} :
    ∃ rep : FlagData B.WordModule S C → MultiBlockCompression B S C,
      ∀ F, (rep F).toFlagData = F :=
  FlagData.exists_rightInverse_toFlagData

/-! ### One step against another; matched steps
(blueprint `lem:asym_uniq_step`, `prop:asym_uniq_matching`) -/

example {B : MPSTensor 2 3} {P₁ Q₁ P₂ Q₂ : Submodule (WordAlgebra 2) B.WordModule}
    (h₁ : P₁ ⋖ Q₁) (h₂ : P₂ ⋖ Q₂) (h : P₁ ⊔ Q₁ ⊓ P₂ < P₁ ⊔ Q₁ ⊓ Q₂) :
    (∃ e : Submodule.subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[WordAlgebra 2] Submodule.subquot P₁ Q₁,
      ∀ x : ↥(Q₁ ⊓ Q₂), e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨x.1, (Submodule.mem_inf.1 x.2).1⟩) ∧
    (∃ e : Submodule.subquot (P₁ ⊓ Q₂) (Q₁ ⊓ Q₂) ≃ₗ[WordAlgebra 2] Submodule.subquot P₂ Q₂,
      ∀ x : ↥(Q₁ ⊓ Q₂), e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨x.1, (Submodule.mem_inf.1 x.2).2⟩) :=
  Submodule.exists_subquotEquiv_of_covBy_of_lt h₁ h₂ h

/- Two covering chains of one modular lattice have the same length, so the probe takes both of
length two. -/
example {B : MPSTensor 2 3}
    (c : CoveringMatching.CoveringChain (Submodule (WordAlgebra 2) B.WordModule) 2)
    (c' : CoveringMatching.CoveringChain (Submodule (WordAlgebra 2) B.WordModule) 2)
    (k : Fin 2) :
    Nonempty (Submodule.subquot (c.toFun k.castSucc) (c.toFun k.succ) ≃ₗ[WordAlgebra 2]
      Submodule.subquot (c'.toFun (c.jumpEquiv c' k).castSucc)
        (c'.toFun (c.jumpEquiv c' k).succ)) :=
  c.nonempty_subquotEquiv_jumpEquiv c' k

section TwoFamilies

variable {D : Fin 2 → ℕ} {D' : Fin 3 → ℕ} {B : MPSTensor 2 3} {S : Finset (Fin 2)}
  {S' : Finset (Fin 3)} {C : ∀ s, MPSTensor 2 (D s)} {C' : ∀ t, MPSTensor 2 (D' t)}
  (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')
  (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)

/-! ### Equal blocks give a scalar
(*The asymmetric fundamental theorem of matrix product states*, Theorem 2.2(c)) -/

example {b : BlockIndex S P.z} {b' : BlockIndex S' Q.z}
    (hdim : slotSize D b = slotSize D' b')
    (heq : ∀ i, Matrix.reindex (finCongr hdim) (finCongr hdim) (slotTensor C b i) =
      slotTensor C' b' i)
    {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    {Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ} (hXY : X * Y = 1)
    (hint : ∀ i, X * slotTensor C b i = slotTensor C' b' i * X) :
    ∃ c : ℂ, c ≠ 0 ∧
      X = c • Matrix.reindex (finCongr hdim) (Equiv.refl _)
        (1 : Matrix (Fin (slotSize D b)) (Fin (slotSize D b)) ℂ) :=
  P.exists_ne_zero_eq_smul_of_slotTensor_eq Q hC hD hdim heq hXY hint

/-! ### A basis adapted to both flags, for two families
(*The asymmetric fundamental theorem of matrix product states*, Theorem 6.5) -/

example (k : Fin (S.card + P.z)) :
    Disjoint ((P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ).restrictScalars ℂ)
      (P.matchedCompl Q hC hD hC' hD' k) :=
  P.disjoint_matchedCompl Q hC hD hC' hD' k

example (k : Fin (S.card + P.z)) :
    (P.flag k.castSucc ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ).restrictScalars ℂ ⊔
        P.matchedCompl Q hC hD hC' hD' k =
      (P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ).restrictScalars ℂ :=
  P.sup_matchedCompl Q hC hD hC' hD' k

example {b : BlockIndex S P.z} {x : B.WordModule}
    (hx : x ∈ P.matchedCompl Q hC hD hC' hD' (P.ord b)) :
    P.commonCoord Q hC hD hC' hD' x =
      Matrix.blockEmbed (slotSize D) b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) :=
  P.commonCoord_of_mem Q hC hD hC' hD' hx

example (b : BlockIndex S P.z) :
    ∃ Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' (P.slotMatching Q hC hD hC' hD' b))) ℂ,
      P.matchedIntertwiner Q hC hD hC' hD' b * Y = 1 ∧
      Y * P.matchedIntertwiner Q hC hD hC' hD' b = 1 ∧
      ∀ i, P.matchedIntertwiner Q hC hD hC' hD' b * slotTensor C b i =
        slotTensor C' (P.slotMatching Q hC hD hC' hD' b) i *
          P.matchedIntertwiner Q hC hD hC' hD' b :=
  P.matchedIntertwiner_spec Q hC hD hC' hD' b

example (b : BlockIndex S P.z) {x : B.WordModule}
    (hx : x ∈ P.flag (P.ord b).succ ⊓ Q.flag (P.matching Q hC hD hC' hD' (P.ord b)).succ) :
    Q.leftRow (P.slotMatching Q hC hD hC' hD' b) *ᵥ WordModule.toVec B x =
      P.matchedIntertwiner Q hC hD hC' hD' b *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x) :=
  P.leftRow_slotMatching_mulVec Q hC hD hC' hD' b hx

example : (P.unipotentFactor Q hC hD hC' hD').BlockTriangular fun x => P.ord x.1 :=
  P.blockTriangular_unipotentFactor Q hC hD hC' hD'

example (b : BlockIndex S P.z) : (P.unipotentFactor Q hC hD hC' hD').blockDiag' b = 1 :=
  P.blockDiag'_unipotentFactor Q hC hD hC' hD' b

example : (P.unipotentFactor' Q hC hD hC' hD').BlockTriangular fun x => Q.ord x.1 :=
  P.blockTriangular_unipotentFactor' Q hC hD hC' hD'

example (b' : BlockIndex S' Q.z) : (P.unipotentFactor' Q hC hD hC' hD').blockDiag' b' = 1 :=
  P.blockDiag'_unipotentFactor' Q hC hD hC' hD' b'

example :
    gaugeMatrix P.gauge =
      P.unipotentFactor Q hC hD hC' hD' * gaugeMatrix (P.commonGauge Q hC hD hC' hD') :=
  P.gaugeMatrix_eq_unipotentFactor_mul Q hC hD hC' hD'

/-- The block permutation matrix is restated in full: `P_X = ∑_b E_{π b} X_b E_bᵀ`. -/
example :
    gaugeMatrix Q.gauge =
      P.unipotentFactor' Q hC hD hC' hD' *
        (∑ b, Matrix.blockEmbed (slotSize D') (P.slotMatching Q hC hD hC' hD' b) *
          P.matchedIntertwiner Q hC hD hC' hD' b * Matrix.blockProj (slotSize D) b) *
        gaugeMatrix (P.commonGauge Q hC hD hC' hD') :=
  P.gaugeMatrix_eq_unipotentFactor'_mul Q hC hD hC' hD'

example :
    gaugeMatrix Q.gauge * gaugeMatrixInv P.gauge =
      P.unipotentFactor' Q hC hD hC' hD' * P.matchingPermMatrix Q hC hD hC' hD' *
        (P.unipotentFactor Q hC hD hC' hD')⁻¹ :=
  P.gaugeMatrix_mul_gaugeMatrixInv_eq Q hC hD hC' hD'

/-! ### Unipotent changes
(*The asymmetric fundamental theorem of matrix product states*, Theorem 6.5, last sentence) -/

example {u : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (hu : u.BlockTriangular fun x => P.ord x.1) (hu1 : ∀ b, u.blockDiag' b = (1 : ℂ) • 1)
    {u' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
    (hu' : u'.BlockTriangular fun x => Q.ord x.1) (hu1' : ∀ b, u'.blockDiag' b = (1 : ℂ) • 1) :
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
  P.flag_conjTriangular_and_unipotentFactor_conjTriangular Q hC hD hC' hD' hu hu1 hu' hu1'

example {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1)
    {h' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
    (ht' : h'.BlockTriangular fun x => Q.ord x.1) {μ' : BlockIndex S' Q.z → ℂ}
    (hμ' : ∀ b, μ' b ≠ 0) (hdiag' : ∀ b, h'.blockDiag' b = μ' b • 1) (k : Fin (S.card + P.z)) :
    (P.conjTriangular ht hμ hdiag).matchedCompl (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' k =
      P.matchedCompl Q hC hD hC' hD' k :=
  P.matchedCompl_conjTriangular Q hC hD hC' hD' ht hμ hdiag ht' hμ' hdiag' k

example {h' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
    (ht' : h'.BlockTriangular fun x => Q.ord x.1) {μ' : BlockIndex S' Q.z → ℂ}
    (hμ' : ∀ b, μ' b ≠ 0) (hdiag' : ∀ b, h'.blockDiag' b = μ' b • 1)
    {u : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (hu : u.BlockTriangular fun x => P.ord x.1) (hu1 : ∀ b, u.blockDiag' b = (1 : ℂ) • 1) :
    (P.conjTriangular hu (μ := fun _ => 1) (fun _ => one_ne_zero) hu1).commonGauge
        (Q.conjTriangular ht' hμ' hdiag') hC hD hC' hD' =
      P.commonGauge Q hC hD hC' hD' :=
  P.commonGauge_conjTriangular Q hC hD hC' hD' ht' hμ' hdiag' hu hu1

example {h : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ}
    (ht : h.BlockTriangular fun x => P.ord x.1) {μ : BlockIndex S P.z → ℂ} (hμ : ∀ b, μ b ≠ 0)
    (hdiag : ∀ b, h.blockDiag' b = μ b • 1)
    {u' : Matrix (BlockSpace D' S' Q.z) (BlockSpace D' S' Q.z) ℂ}
    (hu' : u'.BlockTriangular fun x => Q.ord x.1) (hu1' : ∀ b, u'.blockDiag' b = (1 : ℂ) • 1) :
    (P.conjTriangular ht hμ hdiag).commonGauge'
        (Q.conjTriangular hu' (μ := fun _ => 1) (fun _ => one_ne_zero) hu1') hC hD hC' hD' =
      P.commonGauge' Q hC hD hC' hD' :=
  P.commonGauge'_conjTriangular Q hC hD hC' hD' ht hμ hdiag hu' hu1'

example (A₁ : Matrix (BlockSpace D S P.z) (BlockSpace D S P.z) ℂ)
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
        P.matchingPermMatrix Q hC hD hC' hD' :=
  P.exists_conjTriangular_unipotentFactor_eq Q hC hD hC' hD' A₁ hA₁ hA₁' A₂ hA₂ hA₂'

/-! ### The matching as a rank test
(*The asymmetric fundamental theorem of matrix product states*, Remark 5.3) -/

example (k : Fin (S.card + P.z + 1)) :
    LinearMap.range (P.leadingCols k).mulVecLin =
      ((P.flag k).restrictScalars ℂ).map (WordModule.toVec B).toLinearMap :=
  P.range_leadingCols k

example (k : Fin (S.card + P.z + 1)) (k' : Fin (S'.card + Q.z + 1)) :
    (Matrix.fromCols (P.leadingCols k) (Q.leadingCols k')).rank =
      Module.finrank ℂ ↥(P.flag k ⊔ Q.flag k') :=
  P.rank_fromCols_leadingCols Q k k'

example (k : Fin (S.card + P.z + 1)) (k' : Fin (S'.card + Q.z + 1)) :
    LinearMap.range (Matrix.fromCols (P.leadingCols k) (Q.leadingCols k')).mulVecLin =
      ((P.flag k ⊔ Q.flag k').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap :=
  P.range_fromCols_leadingCols Q k k'

example (k : Fin (S.card + P.z)) :
    IsLeast {j : Fin (S'.card + Q.z + 1) |
        (Matrix.fromCols (P.leadingCols k.castSucc) (Q.leadingCols j)).rank =
          (Matrix.fromCols (P.leadingCols k.succ) (Q.leadingCols j)).rank}
      (P.matching Q hC hD hC' hD' k).succ :=
  P.isLeast_rank_fromCols_leadingCols_eq Q hC hD hC' hD' k

example (k : Fin (S.card + P.z + 1)) (k' : Fin (S'.card + Q.z + 1)) :
    ((((P.flag k ⊓ Q.flag k').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap :
        Submodule ℂ (Fin 3 → ℂ)) : Set (Fin 3 → ℂ)) =
      {v | ∃ a a', v = P.leadingCols k *ᵥ a ∧ P.leadingCols k *ᵥ a = Q.leadingCols k' *ᵥ a'} :=
  P.coe_map_inf_eq_leadingCols Q k k'

/-! ### Two compressions with different flags in matrices
(*The asymmetric fundamental theorem of matrix product states*, Corollary 6.4) -/

example (k : Fin (S.card + P.z)) {b : BlockIndex S P.z} {b' : BlockIndex S' Q.z}
    {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    (hread : ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
      Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x))
    (YU : Matrix (Fin 3) (Fin 2) ℂ)
    (hYU : ∀ j, (WordModule.toVec B).symm (fun i => YU i j) ∈
      P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ) :
    Q.leftRow b' * YU = X * P.leftRow b * YU :=
  P.leftRow_mul_eq_mul_leftRow_mul Q hC hD hC' hD' k hread YU hYU

example (k : Fin (S.card + P.z)) {b : BlockIndex S P.z} (hb : P.ord b = k)
    {b' : BlockIndex S' Q.z} (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k)
    {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    {Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ} (hYX : Y * X = 1)
    (hread : ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
      Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) :
    ∃ R, Q.rightCol b' - P.rightCol b * Y =
      Matrix.fromCols (P.leadingCols k.castSucc)
        (Q.leadingCols (P.matching Q hC hD hC' hD' k).castSucc) * R :=
  P.exists_rightCol_sub_mul_eq_fromCols_mul Q hC hD hC' hD' k hb hb' hYX hread

end TwoFamilies

/-! ### Split reductions, subspace form
(*The asymmetric fundamental theorem of matrix product states*, Proposition 6.12) -/

example {D : Fin 2 → ℕ} {S : Finset (Fin 2)} {C : ∀ s, MPSTensor 2 (D s)} {B : MPSTensor 2 3}
    {P Q : MultiBlockCompression B S C} (hP : P.remainder = 0) (hQ : Q.remainder = 0)
    (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s) (b : BlockIndex S P.z) :
    LinearMap.range (P.rightCol b).mulVecLin ≤
      ⨆ (b' : BlockIndex S Q.z) (_ : IsGaugeRelated (slotTensor C b) (slotTensor C b')),
        LinearMap.range (Q.rightCol b').mulVecLin :=
  MultiBlockCompression.range_rightCol_le_iSup_range_rightCol hP hQ hC hD b

/-! ### Axioms of the library declarations -/

set_option linter.hashCommand false in
/--
info: 'MPSTensor.isIrreducibleAction_and_pos_iff_isSimpleModule'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.isIrreducibleAction_and_pos_iff_isSimpleModule

set_option linter.hashCommand false in
/--
info: 'MPSTensor.isIrreducibleAction_of_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.isIrreducibleAction_of_isNormal

set_option linter.hashCommand false in
/--
info: 'MPSTensor.exists_ne_zero_of_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_ne_zero_of_isNormal

set_option linter.hashCommand false in
/--
info: 'MPSTensor.eq_zero_or_exists_inverse_of_intertwines'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.eq_zero_or_exists_inverse_of_intertwines

set_option linter.hashCommand false in
/--
info: 'MPSTensor.exists_eq_smul_one_of_intertwines'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_eq_smul_one_of_intertwines

set_option linter.hashCommand false in
/--
info: 'MPSTensor.exists_eq_smul_of_intertwines'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_eq_smul_of_intertwines

set_option linter.hashCommand false in
/--
info: 'MPSTensor.trace_evalWord_eq_sum_traceWord_subquot'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.trace_evalWord_eq_sum_traceWord_subquot

set_option linter.hashCommand false in
/--
info: 'MPSTensor.exists_eval_eq_of_pairwise_not_isGaugeRelated'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_eval_eq_of_pairwise_not_isGaugeRelated

set_option linter.hashCommand false in
/--
info: 'MPSTensor.exists_aug_eq_zero_eval_eq_of_pairwise_not_isGaugeRelated'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_aug_eq_zero_eval_eq_of_pairwise_not_isGaugeRelated

set_option linter.hashCommand false in
/--
info: 'MPSTensor.eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.leftRow_mul_rightCol_of_ne'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.leftRow_mul_rightCol_of_ne

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.bijOn_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.bijOn_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_z_eq_iff_exists_flagData'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.exists_z_eq_iff_exists_flagData

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.existsUnique_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.existsUnique_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.FlagData.toMultiBlockCompression_toFlagData'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.FlagData.toMultiBlockCompression_toFlagData

set_option linter.hashCommand false in
/--
info: 'MPSTensor.FlagData.exists_rightInverse_toFlagData'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.FlagData.exists_rightInverse_toFlagData

set_option linter.hashCommand false in
/--
info: 'Submodule.exists_subquotEquiv_of_covBy_of_lt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.exists_subquotEquiv_of_covBy_of_lt

set_option linter.hashCommand false in
/--
info: 'CoveringMatching.CoveringChain.nonempty_subquotEquiv_jumpEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoveringMatching.CoveringChain.nonempty_subquotEquiv_jumpEquiv

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_ne_zero_eq_smul_of_slotTensor_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.exists_ne_zero_eq_smul_of_slotTensor_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.disjoint_matchedCompl'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.disjoint_matchedCompl

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.sup_matchedCompl'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.sup_matchedCompl

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.commonCoord_of_mem'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.commonCoord_of_mem

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.matchedIntertwiner_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.matchedIntertwiner_spec

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.leftRow_slotMatching_mulVec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.leftRow_slotMatching_mulVec

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.blockTriangular_unipotentFactor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.blockTriangular_unipotentFactor

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.blockDiag'_unipotentFactor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.blockDiag'_unipotentFactor

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.blockTriangular_unipotentFactor''
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.blockTriangular_unipotentFactor'

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.blockDiag'_unipotentFactor''
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.blockDiag'_unipotentFactor'

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.gaugeMatrix_eq_unipotentFactor_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.gaugeMatrix_eq_unipotentFactor_mul

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.gaugeMatrix_eq_unipotentFactor'_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.gaugeMatrix_eq_unipotentFactor'_mul

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.gaugeMatrix_mul_gaugeMatrixInv_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.flag_conjTriangular_and_unipotentFactor_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.flag_conjTriangular_and_unipotentFactor_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.matchedCompl_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.matchedCompl_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.commonGauge_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.commonGauge_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.commonGauge'_conjTriangular'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.commonGauge'_conjTriangular

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_conjTriangular_unipotentFactor_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.exists_conjTriangular_unipotentFactor_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.range_leadingCols'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.range_leadingCols

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.rank_fromCols_leadingCols'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.rank_fromCols_leadingCols

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.range_fromCols_leadingCols'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.range_fromCols_leadingCols

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.isLeast_rank_fromCols_leadingCols_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.isLeast_rank_fromCols_leadingCols_eq

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.coe_map_inf_eq_leadingCols'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.coe_map_inf_eq_leadingCols

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.leftRow_mul_eq_mul_leftRow_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.leftRow_mul_eq_mul_leftRow_mul

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.exists_rightCol_sub_mul_eq_fromCols_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.exists_rightCol_sub_mul_eq_fromCols_mul

set_option linter.hashCommand false in
/--
info: 'MPSTensor.MultiBlockCompression.range_rightCol_le_iSup_range_rightCol'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MultiBlockCompression.range_rightCol_le_iSup_range_rightCol

/-! ### Axioms of the examples -/

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.wordSpan_tensorC_of_odd'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.wordSpan_tensorC_of_odd

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.wordSpan_tensorC_of_even'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.wordSpan_tensorC_of_even

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.finrank_wordSpan_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.finrank_wordSpan_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.not_isNormal_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.not_isNormal_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Periodic.isIrreducibleAction_tensorC'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Periodic.isIrreducibleAction_tensorC

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_gauge_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_gauge_one

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_gauge_unipotent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_gauge_unipotent

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.unipotent_conj_tensorB'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.unipotent_conj_tensorB

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.left_mul_pow_ne_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.left_mul_pow_ne_smul

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.remainder_pow_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.remainder_pow_ne_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.isInvariantSubmodule_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.isInvariantSubmodule_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.ord_flagVec_cases_of_z_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.ord_flagVec_cases_of_z_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_each_order'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_each_order

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_upper'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_upper

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_left_eq_upper_of_ord_lt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_left_eq_upper_of_ord_lt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_multiBlockCompression_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_multiBlockCompression_swap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_left_eq_swap_of_ord_gt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_left_eq_swap_of_ord_gt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.matching_left_right_gOne_redSwap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.matching_left_right_gOne_redSwap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.isAdaptedFactorization_gOne_redSwap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.isAdaptedFactorization_gOne_redSwap

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.exists_eval_zero_eq_zero_and_eval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.exists_eval_zero_eq_zero_and_eval_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Running.eq_one_and_eq_one_of_forall_add_mul_pow_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Running.eq_one_and_eq_one_of_forall_add_mul_pow_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_one_of_eq_replicate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_one_of_eq_replicate

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_zero_of_ne_replicate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.trace_evalWord_tensorB'_eq_zero_of_ne_replicate

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.tensorB_one_mul_zero_and_tensorB'_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.tensorB_one_mul_zero_and_tensorB'_commute

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB'_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.isInvariantSubmodule_span_tensorB'_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.NoGauge.not_exists_conj_tensorB_eq_tensorB''
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.NoGauge.not_exists_conj_tensorB_eq_tensorB'

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.isInvariantSubmodule_span_tensorB_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.isInvariantSubmodule_span_tensorB_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.z_eq_one_and_gInt_conj'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.z_eq_one_and_gInt_conj

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.flagVec_one_firstCompression_and_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.flagVec_one_firstCompression_and_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.eq_toFlagData_firstCompression_or_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.eq_toFlagData_firstCompression_or_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.left_right_matching_firstCompression_lastCompression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.left_right_matching_firstCompression_lastCompression

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.left_mulVec_e_one_and_left_mul_tensorB'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.OneBlock.left_mulVec_e_one_and_left_mul_tensorB

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.OneBlock.remainder_lastCompression_eq_zero_and_firstCompression_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  MultiBlockExamples.OneBlock.remainder_lastCompression_eq_zero_and_firstCompression_ne_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.tensorBGen_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.tensorBGen_one

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.SharpnessOneBlock.tensorBGen_two'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.SharpnessOneBlock.tensorBGen_two

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.wordSpan_tensorC_three_eq_top_and_isNormal

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.isInvariantSubmodule_lineTensor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.isInvariantSubmodule_lineTensor

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.span_eq_of_lineTensor_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.span_eq_of_lineTensor_eq

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.commute_tensorB_iff_eq_kronMat'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.commute_tensorB_iff_eq_kronMat

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_split_multiBlockCompression_kronRow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_split_multiBlockCompression_kronRow

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_left_eq_kronRow_of_remainder_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_left_eq_kronRow_of_remainder_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.exists_left_mul_evalWord_eq_smul_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.exists_left_mul_evalWord_eq_smul_iff

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.matching_left_splitRed_of_span_ne'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.matching_left_splitRed_of_span_ne

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Multiplicity.matching_left_redOne_redAt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Multiplicity.matching_left_redOne_redAt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.wordSpan_tensorC₁_three_eq_top_and_isNormal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.wordSpan_tensorC₁_three_eq_top_and_isNormal

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.isInvariantSubmodule_span_tensorT_iff_and_mulVec_eq_zero

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.redG_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.redG_spec

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.redGt_spec'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.redGt_spec

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.flagVec_redG_redGt_and_matching'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.flagVec_redG_redGt_and_matching

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.finrank_flagVec_redG_inf_flagVec_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.finrank_flagVec_redG_inf_flagVec_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.inf_sup_intertwiner_redG_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.inf_sup_intertwiner_redG_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.isAdaptedFactorization_redG_redGt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.isAdaptedFactorization_redG_redGt

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.not_exists_left_redGt_eq_smul_left_redG'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.not_exists_left_redGt_eq_smul_left_redG

set_option linter.hashCommand false in
/--
info: 'MultiBlockExamples.Worked.trace_evalWord_tensorB_eq_add'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MultiBlockExamples.Worked.trace_evalWord_tensorB_eq_add
