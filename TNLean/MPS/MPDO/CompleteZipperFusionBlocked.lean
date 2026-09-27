/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionOfCompression
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients
import TNLean.MPS.MPDO.SourceBNTBlocking

/-!
# Complete zipper fusion families after blocking

The extraction of the $F$-symbols in arXiv:1511.08090 applies a simultaneous left inverse of
the labelled block tensors, which asks that the one-site map
$v\mapsto(\sum_{ij}v_{ij}B_c^{ij})_c$ onto $\bigoplus_c M_{D_c}$ be surjective.  The source
derives it from injectivity of each block (line 269), which does not suffice at one site
(`docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`).  This file removes that input after
blocking.  For normal blocks of positive bond dimension, no two of which are gauge equivalent up
to a nonzero scalar, the words of one common positive length $L$ span the direct sum, so the
blocked tensors have a simultaneous left inverse at one blocked site.  A split compression of
each pairwise product stays split after blocking, with the same compression maps, so the
construction `CompleteZipperFusionFamily.ofCompression` applies to the blocked tensors without a
supplied left inverse.

## Main definitions

* `MPSTensor.MultiBlockCompression.ofWords`: a multi-block compression transported to tensors
  whose letters are fixed nonempty words of the original letters.
* `MPOTensor.CompleteZipperFusionFamily.PairCompression.blockTensor`: the blocked split
  compression of a pairwise product.
* `MPOTensor.CompleteZipperFusionFamily.jointBlockLength`: a positive blocking length at which
  the labelled blocks span the direct sum of their matrix algebras in one letter.
* `MPOTensor.CompleteZipperFusionFamily.ofCompressionBlocked`,
  `MPOTensor.CompleteZipperFusionFamily.ofStarBlocked`: the complete zipper fusion families of
  the blocked tensors, with no simultaneous left inverse among the inputs.

## Main statements

* `MPOTensor.exists_blockTensor_isMPOBlockLeftInverse`: normal, pairwise inequivalent MPO blocks
  have a simultaneous left inverse after one common positive blocking.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200, the simultaneous inverse at line 269,
  and the common blocking at lines 427--431.
* arXiv:1606.00608, block injectivity at lines 317--345.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPSTensor.MultiBlockCompression

variable {ι : Type*} [DecidableEq ι] {d d' DB : ℕ} {D : ι → ℕ} {S : Finset ι}

/-- Word evaluation of a family of block-diagonal matrices is block diagonal. -/
private theorem evalWord_blockDiagonal'_of {o : Type*} [Fintype o] [DecidableEq o]
    {n : o → ℕ} (X : Fin d → ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (w : List (Fin d)) :
    _root_.evalWord (fun i => Matrix.blockDiagonal' (X i)) w =
      Matrix.blockDiagonal' fun k => _root_.evalWord (fun i => X i k) w := by
  induction w with
  | nil =>
    change (1 : Matrix ((k : o) × Fin (n k)) _ ℂ) = Matrix.blockDiagonal' 1
    simp
  | cons i w ih => simp [_root_.evalWord, ih, Matrix.blockDiagonal'_mul]

/-- The evaluation of a nonempty word in the zero family vanishes. -/
private theorem evalWord_zero_of_ne_nil {n : Type*} [Fintype n] [DecidableEq n]
    {w : List (Fin d)} (hw : w ≠ []) :
    _root_.evalWord (fun _ => (0 : Matrix n n ℂ)) w = 0 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [_root_.evalWord]

/-- The generic word evaluation agrees with `Kraus.evalWord` on square matrices over `Fin n`. -/
private theorem evalWord_eq_kraus_evalWord {n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (w : List (Fin d)) : _root_.evalWord A w = Kraus.evalWord A w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [_root_.evalWord, Kraus.evalWord, ih]

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- **Transport of a compression along words.** If every letter of `B'` is the evaluation of a
fixed nonempty word `u j` in the letters of `B`, and every letter of `C' s` is the evaluation of
the same word in the letters of `C s`, then a multi-block compression of `B` onto the tensors
`C s` gives one of `B'` onto the tensors `C' s`, with the same change of coordinates.

Blocking is the case where `u j` runs over the words of a fixed positive length. -/
noncomputable def ofWords (P : MultiBlockCompression B S C) (u : Fin d' → List (Fin d))
    (hu : ∀ j, u j ≠ []) {B' : MPSTensor d' DB} (hB' : ∀ j, B' j = Kraus.evalWord B (u j))
    {C' : ∀ s, MPSTensor d' (D s)} (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j)) :
    MultiBlockCompression B' S C' where
  z := P.z
  ord := P.ord
  gauge := P.gauge
  triangular j := by
    rw [hB', ← evalWord_conjMatrix]
    exact Matrix.blockTriangular_evalWord P.triangular _
  matched j s := by
    rw [hB', ← evalWord_conjMatrix, Matrix.blockDiag'_evalWord P.ord.injective P.triangular,
      hC']
    simp only [P.matched]
    exact evalWord_eq_kraus_evalWord _ _
  unmatched j t := by
    rw [hB', ← evalWord_conjMatrix, Matrix.blockDiag'_evalWord P.ord.injective P.triangular]
    simp only [P.unmatched]
    exact evalWord_zero_of_ne_nil (hu j)

/-- The compression maps of `ofWords` are those of the original compression. -/
theorem ofWords_left (P : MultiBlockCompression B S C) (u : Fin d' → List (Fin d))
    (hu : ∀ j, u j ≠ []) {B' : MPSTensor d' DB} (hB' : ∀ j, B' j = Kraus.evalWord B (u j))
    {C' : ∀ s, MPSTensor d' (D s)} (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j))
    (s : {s // s ∈ S}) :
    (P.ofWords u hu hB' hC').left s = P.left s := rfl

/-- The compression maps of `ofWords` are those of the original compression. -/
theorem ofWords_right (P : MultiBlockCompression B S C) (u : Fin d' → List (Fin d))
    (hu : ∀ j, u j ≠ []) {B' : MPSTensor d' DB} (hB' : ∀ j, B' j = Kraus.evalWord B (u j))
    {C' : ∀ s, MPSTensor d' (D s)} (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j))
    (s : {s // s ∈ S}) :
    (P.ofWords u hu hB' hC').right s = P.right s := rfl

/-- A vanishing remainder means that every letter is block diagonal in the block coordinates. -/
theorem conjMatrix_eq_blockDiagonal'_of_remainder_eq_zero (P : MultiBlockCompression B S C)
    (hP : P.remainder = 0) (i : Fin d) :
    conjMatrix P.gauge (B i) =
      Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' := by
  have h := P.conjMatrix_remainder i
  rw [hP, Pi.zero_apply, conjMatrix_zero] at h
  exact (sub_eq_zero.1 h.symm)

/-- **A split compression stays split along words.** The remainder of `ofWords` vanishes when
the remainder of the original compression does. -/
theorem remainder_ofWords_eq_zero (P : MultiBlockCompression B S C) (hP : P.remainder = 0)
    (u : Fin d' → List (Fin d)) (hu : ∀ j, u j ≠ []) {B' : MPSTensor d' DB}
    (hB' : ∀ j, B' j = Kraus.evalWord B (u j)) {C' : ∀ s, MPSTensor d' (D s)}
    (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j)) :
    (P.ofWords u hu hB' hC').remainder = 0 := by
  funext j
  apply conjMatrix_injective P.gauge
  have hdiag : conjMatrix P.gauge (B' j) = Matrix.blockDiagonal' fun k =>
      _root_.evalWord (fun i => (conjMatrix P.gauge (B i)).blockDiag' k) (u j) := by
    rw [hB', ← evalWord_conjMatrix,
      show (fun i => conjMatrix P.gauge (B i)) = fun i =>
        Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' from
        funext (P.conjMatrix_eq_blockDiagonal'_of_remainder_eq_zero hP),
      evalWord_blockDiagonal'_of]
  have h := (P.ofWords u hu hB' hC').conjMatrix_remainder j
  change conjMatrix P.gauge _ = conjMatrix P.gauge (B' j) -
    Matrix.blockDiagonal' (conjMatrix P.gauge (B' j)).blockDiag' at h
  rw [h, hdiag, Matrix.blockDiag'_blockDiagonal', sub_self, Pi.zero_apply, conjMatrix_zero]

end MPSTensor.MultiBlockCompression

namespace MPSTensor

/-- Rescaling each block by a nonzero scalar does not change whether the word tuples of one
length span the direct sum: the words of length `L` of `μ_j B_j` are `μ_j^L` times those of
`B_j`. -/
theorem wordTupleSpanTop_of_smul {d r : ℕ} {dim : Fin r → ℕ}
    {B : (j : Fin r) → MPSTensor d (dim j)} {μ : Fin r → ℂ} (hμ : ∀ j, μ j ≠ 0) {L : ℕ}
    (h : WordTupleSpanTop (fun j => fun i => μ j • B j i) L) : WordTupleSpanTop B L := by
  let Φ : ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ]
      ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :=
    LinearMap.pi fun j => (μ j ^ L) • LinearMap.proj j
  have hΦ : Function.Injective Φ := by
    intro X Y hXY
    funext j
    have := congrFun hXY j
    simp only [Φ, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval] at this
    exact smul_right_injective _ (pow_ne_zero L (hμ j)) this
  have hrange : Set.range (wordTuple (fun j => fun i => μ j • B j i) L) =
      Φ '' Set.range (wordTuple B L) := by
    rw [← Set.range_comp]
    congr 1
    funext w
    funext j
    simp [Φ, wordTuple, Kraus.evalWord_smul]
  unfold WordTupleSpanTop at h ⊢
  rw [hrange, ← Submodule.map_span] at h
  refine top_unique fun X _ => ?_
  obtain ⟨Y, hY, hYX⟩ := (Submodule.mem_map).1 (h ▸ Submodule.mem_top : Φ X ∈ _)
  exact hΦ hYX ▸ hY

end MPSTensor

namespace MPOTensor

variable {p : ℕ}

/-- The paired word of a blocked doubled physical index: the ket and bra words of the block,
paired letter by letter. -/
noncomputable def blockedPairWord (p L : ℕ) (I : Fin (MPSTensor.blockPhysDim p L *
    MPSTensor.blockPhysDim p L)) : List (Fin (p * p)) :=
  Kraus.wordOfBlock (p * p) L (blockedDoubledIndexEquiv p L I)

theorem blockedPairWord_ne_nil {L : ℕ} (hL : 0 < L)
    (I : Fin (MPSTensor.blockPhysDim p L * MPSTensor.blockPhysDim p L)) :
    blockedPairWord p L I ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [blockedPairWord, Kraus.length_wordOfBlock, List.length_nil] at this
  omega

/-- A letter of a blocked MPO tensor, read as a tensor on the doubled alphabet, is the
evaluation of the paired word. -/
theorem toMPSTensor_blockTensor_apply {D : ℕ} (M : MPOTensor p D) (L : ℕ)
    (I : Fin (MPSTensor.blockPhysDim p L * MPSTensor.blockPhysDim p L)) :
    (blockTensor M L).toMPSTensor I = Kraus.evalWord M.toMPSTensor (blockedPairWord p L I) :=
  congrFun (toMPSTensor_blockTensor M) I

/-- **Simultaneous left inverse after blocking.** Let `T_1, …, T_g` be MPO tensors whose
doubled-alphabet tensors are normal, of positive bond dimension, and pairwise not gauge
equivalent up to a nonzero scalar.  Then there is a positive blocking length `L` at which the
blocked tensors are injective and have a simultaneous left inverse: one matrix `K` with
`∑_{ik} K_{(c,x,y),(i,k)} (T_d^{[L]})^{ik}_{x'y'} = δ_{cd} δ_{xx'} δ_{yy'}`.

This is relation `B_d^+ B_{d'} = δ_{dd'} 1 ⊗ 1` of arXiv:1511.08090, `AnyonsPEPS.tex`,
line 269, at the common blocking length of lines 427--431.  At one unblocked site it can fail
(`docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`); the scalar in the non-equivalence
hypothesis is needed, since `T` and `-T` have no simultaneous left inverse at any length.

Source: the joint span is `MPSTensor.exists_positive_wordTupleSpanTop_of_isNormal`,
arXiv:1606.00608, lines 317--345. -/
theorem exists_blockTensor_isMPOBlockLeftInverse {g : ℕ} {D : Fin g → ℕ}
    (T : ∀ c, MPOTensor p (D c)) (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor)
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (d := p * p) fun c => (T c).toMPSTensor) :
    ∃ L : ℕ, 0 < L ∧ (∀ c, Kraus.IsInjective (blockTensor (T c) L).toMPSTensor) ∧
      ∃ K : Matrix (MPSTensor.BlockEntryIndex D) (Fin (MPSTensor.blockPhysDim p L) ×
          Fin (MPSTensor.blockPhysDim p L)) ℂ,
        MPSTensor.IsMPOBlockLeftInverse (fun c => blockTensor (T c) L) K := by
  have hScaled : ∀ c, ∃ ζ : ℂ, ζ ≠ 0 ∧
      MPSTensor.IsNormalTensor (ζ • (T c).toMPSTensor) := by
    intro c
    have : NeZero (D c) := ⟨(hD c).ne'⟩
    obtain ⟨B, ζ, hζ, hGauge, -, -, hB⟩ :=
      MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal (hT c)
    exact ⟨ζ, hζ, MPSTensor.IsNormalTensor.of_gaugeEquiv hB hGauge⟩
  choose scale hscale hNormal using hScaled
  obtain ⟨L, hL, hSpan⟩ := MPSTensor.exists_positive_wordTupleSpanTop_of_isNormal hNormal hD
    (fun j k hjk hdim hGPE => hne j k hjk hdim
      (MPSTensor.gaugePhaseEquiv_of_smul_smul_cast hdim (hscale j) (hscale k) hGPE))
  replace hSpan := MPSTensor.wordTupleSpanTop_of_smul hscale hSpan
  have hSpan1 := MPSTensor.wordTupleSpanTop_blockTensor_one _ hSpan
  have hSpanBlocked : MPSTensor.WordTupleSpanTop
      (fun c ↦ (blockTensor (T c) L).toMPSTensor) 1 := by
    have hFamily : (fun c ↦ (blockTensor (T c) L).toMPSTensor) =
        fun c ↦ Kraus.reindexPhysical (blockedDoubledIndexEquiv p L)
          (Kraus.blockTensor (T c).toMPSTensor L) :=
      funext fun c ↦ toMPSTensor_blockTensor (T c)
    rw [hFamily]
    exact (MPSTensor.wordTupleSpanTop_reindexPhysical_equiv
      (blockedDoubledIndexEquiv p L) _ 1).2 hSpan1
  exact ⟨L, hL, fun c ↦ hSpanBlocked.isInjective_one c,
    hSpanBlocked.exists_mpo_block_left_inverse⟩

namespace CompleteZipperFusionFamily

variable {g : ℕ} {D : Fin g → ℕ} {T : ∀ c, MPOTensor p (D c)}
  {N : Fin g → Fin g → Fin g → ℕ}

/-- **Blocking a split compression.** A multi-block compression of the product `O_a O_b` onto
`N_{ab}^c` copies of each `O_c` gives one of the blocked product onto the blocked blocks, with
the same compression maps.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 181--200 (the compression pairs are the
fusion tensors, which are independent of the blocking) and lines 427--431 (common blocking). -/
noncomputable def PairCompression.blockTensor {a b : Fin g} (P : PairCompression T N a b)
    {L : ℕ} (hL : 0 < L) :
    PairCompression (fun c => MPOTensor.blockTensor (T c) L) N a b :=
  P.ofWords (blockedPairWord p L) (blockedPairWord_ne_nil hL)
    (fun I => by
      rw [← blockTensor_mulTensor]
      exact toMPSTensor_blockTensor_apply _ L I)
    (fun s I => toMPSTensor_blockTensor_apply (T s.1) L I)

theorem PairCompression.remainder_blockTensor_eq_zero {a b : Fin g}
    (P : PairCompression T N a b) (hP : P.remainder = 0) {L : ℕ} (hL : 0 < L) :
    (P.blockTensor hL).remainder = 0 :=
  P.remainder_ofWords_eq_zero hP _ _ _ _

/-- A positive blocking length at which the blocks are injective and have a simultaneous left
inverse, chosen by `MPOTensor.exists_blockTensor_isMPOBlockLeftInverse`. -/
noncomputable def jointBlockLength (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (d := p * p) fun c => (T c).toMPSTensor) : ℕ :=
  (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose

theorem jointBlockLength_pos (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c) (hne) :
    0 < jointBlockLength T hT hD hne :=
  (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose_spec.1

/-- **Complete zipper fusion family of the blocked tensors from split compressions.** Let the
MPO blocks `O_a` be normal, of positive bond dimension, and pairwise not gauge equivalent up to a
nonzero scalar, and for every pair `(a, b)` let `P a b` be a multi-block compression of
`O_a O_b` onto `N_{ab}^c` copies of each `O_c` with vanishing remainder.  After blocking
`jointBlockLength` sites, the compression pairs are the fusion tensors and left inverses of a
complete zipper fusion family of the blocked tensors.  No simultaneous left inverse is an
input: it is derived at the blocking length.

**Scope restriction (arXiv:1511.08090, line 269):** the family is built for the blocked tensors
at one positive length, as in the common blocking of lines 427--431 of the source.  The
one-site statement of line 269 is false in general, and the pairwise inequivalence is taken up
to a nonzero scalar.  Documented in `docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200 and 269--277. -/
noncomputable def ofCompressionBlocked (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor)
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (d := p * p) fun c => (T c).toMPSTensor)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0) :
    CompleteZipperFusionFamily (Fin g)
      (MPSTensor.blockPhysDim p (jointBlockLength T hT hD hne)) :=
  let hspec := (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose_spec
  ofCompression hD hspec.2.1
    (fun a b => (P a b).blockTensor hspec.1)
    (fun a b => (P a b).remainder_blockTensor_eq_zero (hP a b) hspec.1)
    hspec.2.2.choose hspec.2.2.choose_spec

/-- The tensors of `ofCompressionBlocked` are the blocked tensors. -/
theorem ofCompressionBlocked_tensor (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor)
    (hD : ∀ c, 0 < D c) (hne) (P : ∀ a b, PairCompression T N a b)
    (hP : ∀ a b, (P a b).remainder = 0) (c : Fin g) :
    (ofCompressionBlocked hT hD hne P hP).tensor c =
      MPOTensor.blockTensor (T c) (jointBlockLength T hT hD hne) := rfl

/-- The fusion tensor `X^c_{ab,μ}` of `ofCompressionBlocked` is the compression map `V_{(c,μ)}`
of the unblocked compression of `O_a O_b`. -/
theorem ofCompressionBlocked_fusionTensor (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor)
    (hD : ∀ c, 0 < D c) (hne) (P : ∀ a b, PairCompression T N a b)
    (hP : ∀ a b, (P a b).remainder = 0) (a b c : Fin g) (μ : Fin (N a b c))
    (x : Fin (D a) × Fin (D b)) (z : Fin (D c)) :
    (ofCompressionBlocked hT hD hne P hP).fusionTensor a b c μ x z =
      (P a b).right (pairSlot c μ) (finProdFinEquiv x) z := rfl

/-- The left inverse `X^{c+}_{ab,μ}` of `ofCompressionBlocked` is the compression map
`W_{(c,μ)}` of the unblocked compression of `O_a O_b`. -/
theorem ofCompressionBlocked_fusionTensorLeftInverse
    (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c) (hne)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0) (a b c : Fin g)
    (μ : Fin (N a b c)) (z : Fin (D c)) (x : Fin (D a) × Fin (D b)) :
    (ofCompressionBlocked hT hD hne P hP).fusionTensorLeftInverse a b c μ z x =
      (P a b).left (pairSlot c μ) z (finProdFinEquiv x) := rfl

/-- **Complete zipper fusion family of the blocked tensors in the star-closed case.** Under the
fusion rules on word traces and the star closure of every product tensor, the split
compressions of `exists_pairCompression_remainder_eq_zero_of_star` give, after blocking
`jointBlockLength` sites, a complete zipper fusion family with no simultaneous left inverse
among the inputs.

**Scope restriction (arXiv:1511.08090, line 269):** as for `ofCompressionBlocked`, the family is
built for the blocked tensors.  Documented in
`docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`.

Source: arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200 and 269--277; arXiv:2203.12563,
`REsubmission.tex`, lines 361--362 (the fusion rules). -/
noncomputable def ofStarBlocked (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor)
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (d := p * p) fun c => (T c).toMPSTensor)
    (htr : ∀ a b, ∀ w : List (Fin (p * p)), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor (T a) (T b)).toMPSTensor w) =
        ∑ s : (c : Fin g) × Fin (N a b c),
          Matrix.trace (Kraus.evalWord (T s.1).toMPSTensor w))
    (hstar : ∀ a b, ∀ i, ((mulTensor (T a) (T b)).toMPSTensor i)ᴴ ∈
      Algebra.adjoin ℂ (Set.range (mulTensor (T a) (T b)).toMPSTensor)) :
    CompleteZipperFusionFamily (Fin g)
      (MPSTensor.blockPhysDim p (jointBlockLength T hT hD hne)) :=
  ofCompressionBlocked hT hD hne
    (fun a b => (MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star
      (D := fun s : (c : Fin g) × Fin (N a b c) => D s.1) Finset.univ
      (fun s : (c : Fin g) × Fin (N a b c) => (T s.1).toMPSTensor)
      (fun s _ => hT s.1) (fun s _ => hD s.1) _ (htr a b) (hstar a b)).choose)
    (fun a b => (MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star
      (D := fun s : (c : Fin g) × Fin (N a b c) => D s.1) Finset.univ
      (fun s : (c : Fin g) × Fin (N a b c) => (T s.1).toMPSTensor)
      (fun s _ => hT s.1) (fun s _ => hD s.1) _ (htr a b) (hstar a b)).choose_spec)

end CompleteZipperFusionFamily

end MPOTensor
