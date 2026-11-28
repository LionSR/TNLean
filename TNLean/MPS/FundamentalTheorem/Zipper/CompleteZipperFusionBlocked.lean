/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.OperatorProduct.CompleteZipperFusionOfCompression
import TNLean.MPS.Operator.Product.PhysicalBlocking
import TNLean.MPS.FundamentalTheorem.SectorBNT.PowerSumCoefficients
import TNLean.MPS.CanonicalForm.BlockSeparation.SimultaneousBlocking
import TNLean.MPS.Operator.Boundary.BoundaryBlockFusion

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
* `MPOTensor.IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective`,
  `MPOTensor.IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective`: source-block
  fusion and action tensors from arbitrary-boundary closedness.

## References

* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 156--200, the simultaneous inverse at line 269,
  and the common blocking at lines 427--431.
* arXiv:1606.00608, block injectivity at lines 317--345.

## Simultaneous word spans of unnormalized injective blocks

Pairwise inequivalent injective blocks of positive dimension have a common
positive word length at which their tuples span the full product matrix
algebra. Spectral normalization of the original blocks is unnecessary:
independent nonzero scalar normalizations give normal tensors, and the
resulting simultaneous span transfers back at the same length.

This is the common-blocking step in Garre-Rubio, Lootens and Molnár,
arXiv:2203.12563v3, Appendix A, using the block-injectivity theorem of
arXiv:1606.00608, lines 317--345.

**Bridge (T.2b):** The proof of `exists_positive_wordTupleSpanTop_of_isInjective` and
`toMPSTensor_blockTensor_apply` still reads an operator tensor through `MPOTensor.toMPSTensor`,
because the Fin-encoded blocking `Kraus.blockTensor` (with `MPOTensor.toMPSTensor_blockTensor`,
`MPOTensor.toMPSTensor_blockTwo`) is stated on the alphabet `Fin (d * d)`. The bridge is removed
when the blocking moves to `Kraus.block` (step T.2b of `docs/tensor_type_unification.md`).
-/

open MPTensor

section CompleteZipperFusionBlocked

section

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPSTensor.MultiBlockCompression

variable {ι : Type*} [DecidableEq ι] {α α' : Type*} {DB : ℕ} {D : ι → ℕ} {S : Finset ι}

/-- The evaluation of a nonempty word in the zero family vanishes. -/
private theorem evalWord_zero_of_ne_nil {n : Type*} [Fintype n] [DecidableEq n]
    {w : List α} (hw : w ≠ []) :
    Kraus.evalWord (fun _ => (0 : Matrix n n ℂ)) w = 0 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [Kraus.evalWord]

variable {B : MPTensor α (Fin DB)} {C : ∀ s, MPTensor α (Fin (D s))}

/-- **Transport of a compression along words.** If every letter of `B'` is the evaluation of a
fixed nonempty word `u j` in the letters of `B`, and every letter of `C' s` is the evaluation of
the same word in the letters of `C s`, then a multi-block compression of `B` onto the tensors
`C s` gives one of `B'` onto the tensors `C' s`, with the same change of coordinates.

Blocking is the case where `u j` runs over the words of a fixed positive length. -/
noncomputable def ofWords (P : MultiBlockCompression B S C) (u : α' → List α)
    (hu : ∀ j, u j ≠ []) {B' : MPTensor α' (Fin DB)} (hB' : ∀ j, B' j = Kraus.evalWord B (u j))
    {C' : ∀ s, MPTensor α' (Fin (D s))} (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j)) :
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
  unmatched j t := by
    rw [hB', ← evalWord_conjMatrix, Matrix.blockDiag'_evalWord P.ord.injective P.triangular]
    simp only [P.unmatched]
    exact evalWord_zero_of_ne_nil (hu j)

/-- A vanishing remainder means that every letter is block diagonal in the block coordinates. -/
theorem conjMatrix_eq_blockDiagonal'_of_remainder_eq_zero (P : MultiBlockCompression B S C)
    (hP : P.remainder = 0) (i : α) :
    conjMatrix P.gauge (B i) =
      Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' := by
  have h := P.conjMatrix_remainder i
  rw [hP, Pi.zero_apply, conjMatrix_zero] at h
  exact (sub_eq_zero.1 h.symm)

/-- **A split compression stays split along words.** The remainder of `ofWords` vanishes when
the remainder of the original compression does. -/
theorem remainder_ofWords_eq_zero (P : MultiBlockCompression B S C) (hP : P.remainder = 0)
    (u : α' → List α) (hu : ∀ j, u j ≠ []) {B' : MPTensor α' (Fin DB)}
    (hB' : ∀ j, B' j = Kraus.evalWord B (u j)) {C' : ∀ s, MPTensor α' (Fin (D s))}
    (hC' : ∀ s j, C' s j = Kraus.evalWord (C s) (u j)) :
    (P.ofWords u hu hB' hC').remainder = 0 := by
  funext j
  apply conjMatrix_injective P.gauge
  have hdiag : conjMatrix P.gauge (B' j) = Matrix.blockDiagonal' fun k =>
      Kraus.evalWord (fun i => (conjMatrix P.gauge (B i)).blockDiag' k) (u j) := by
    rw [hB', ← evalWord_conjMatrix,
      show (fun i => conjMatrix P.gauge (B i)) = fun i =>
        Matrix.blockDiagonal' (conjMatrix P.gauge (B i)).blockDiag' from
        funext (P.conjMatrix_eq_blockDiagonal'_of_remainder_eq_zero hP),
      Kraus.evalWord_blockDiagonal']
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

/-- **Simultaneous left inverse after blocking.** Let `T_1, …, T_g` be MPO tensors that are
normal on the pair alphabet, of positive bond dimension, and pairwise not gauge
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
    (T : ∀ c, MPOTensor p (D c)) (hT : ∀ c, Kraus.IsNormal (T c))
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv T) :
    ∃ L : ℕ, 0 < L ∧ (∀ c, Kraus.IsInjective (blockTensor (T c) L)) ∧
      ∃ K : Matrix (MPSTensor.BlockEntryIndex D) (Fin (Kraus.blockPhysDim p L) ×
          Fin (Kraus.blockPhysDim p L)) ℂ,
        MPSTensor.IsMPOBlockLeftInverse (fun c => blockTensor (T c) L) K := by
  have hScaled : ∀ c, ∃ ζ : ℂ, ζ ≠ 0 ∧
      MPTensor.IsNormalTensor (ζ • (T c).toMPSTensor) := by
    intro c
    have : NeZero (D c) := ⟨(hD c).ne'⟩
    obtain ⟨B, ζ, hζ, hGauge, -, -, hB⟩ :=
      MPSTensor.exists_leftCanonical_normalTensor_scale_of_isNormal
        ((isNormal_toMPSTensor_iff _).2 (hT c))
    exact ⟨ζ, hζ, MPTensor.IsNormalTensor.of_gaugeEquiv hB hGauge⟩
  choose scale hscale hNormal using hScaled
  have hne' : MPSTensor.BlocksNotGaugePhaseEquiv fun c => (T c).toMPSTensor :=
    hne.reindexPhysical finProdFinEquiv.symm
  obtain ⟨L, hL, hSpan⟩ := MPSTensor.exists_positive_wordTupleSpanTop_of_isNormal hNormal hD
    (fun j k hjk hdim hGPE => hne' j k hjk hdim
      (MPSTensor.gaugePhaseEquiv_of_smul_smul_cast hdim (hscale j) (hscale k) hGPE))
  replace hSpan := MPSTensor.wordTupleSpanTop_of_smul hscale hSpan
  have hSpan1 := MPSTensor.wordTupleSpanTop_block_one _ hSpan
  have hSpanBlocked : MPSTensor.WordTupleSpanTop
      (fun c ↦ (blockTensor (T c) L).toMPSTensor) 1 := by
    have hFamily : (fun c ↦ (blockTensor (T c) L).toMPSTensor) =
        fun c ↦ Kraus.reindexPhysical (blockedDoubledIndexEquiv p L)
          (Kraus.block (T c).toMPSTensor L) :=
      funext fun c ↦ toMPSTensor_blockTensor (T c)
    rw [hFamily]
    exact (MPSTensor.wordTupleSpanTop_reindexPhysical_equiv
      (blockedDoubledIndexEquiv p L) _ 1).2 hSpan1
  have hSpanPair : MPSTensor.WordTupleSpanTop (fun c ↦ blockTensor (T c) L) 1 :=
    (MPSTensor.wordTupleSpanTop_reindexPhysical_equiv finProdFinEquiv.symm _ 1).1 hSpanBlocked
  exact ⟨L, hL, fun c ↦ hSpanPair.isInjective_one c, hSpanPair.exists_mpo_block_left_inverse⟩

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
  P.ofWords (fun I => List.ofFn (blockedPairIndexEquiv p L I))
    (fun _ => mt List.ofFn_eq_nil_iff.1 hL.ne')
    (fun I => by
      rw [← blockTensor_mulTensor]
      rfl)
    (fun _ _ => rfl)

theorem PairCompression.remainder_blockTensor_eq_zero {a b : Fin g}
    (P : PairCompression T N a b) (hP : P.remainder = 0) {L : ℕ} (hL : 0 < L) :
    (P.blockTensor hL).remainder = 0 :=
  P.remainder_ofWords_eq_zero hP _ _ _ _

/-- A positive blocking length at which the blocks are injective and have a simultaneous left
inverse, chosen by `MPOTensor.exists_blockTensor_isMPOBlockLeftInverse`. -/
noncomputable def jointBlockLength (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c)) (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv T) : ℕ :=
  (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose

theorem jointBlockLength_pos (T : ∀ c, MPOTensor p (D c))
    (hT : ∀ c, Kraus.IsNormal (T c)) (hD : ∀ c, 0 < D c) (hne) :
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
noncomputable def ofCompressionBlocked (hT : ∀ c, Kraus.IsNormal (T c))
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv T)
    (P : ∀ a b, PairCompression T N a b) (hP : ∀ a b, (P a b).remainder = 0) :
    CompleteZipperFusionFamily (Fin g)
      (Kraus.blockPhysDim p (jointBlockLength T hT hD hne)) :=
  let hspec := (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose_spec
  ofCompression hD hspec.2.1
    (fun a b => (P a b).blockTensor hspec.1)
    (fun a b => (P a b).remainder_blockTensor_eq_zero (hP a b) hspec.1)
    hspec.2.2.choose hspec.2.2.choose_spec

/-- The tensors of `ofCompressionBlocked` are the blocked tensors. -/
theorem ofCompressionBlocked_tensor (hT : ∀ c, Kraus.IsNormal (T c))
    (hD : ∀ c, 0 < D c) (hne) (P : ∀ a b, PairCompression T N a b)
    (hP : ∀ a b, (P a b).remainder = 0) (c : Fin g) :
    (ofCompressionBlocked hT hD hne P hP).tensor c =
      MPOTensor.blockTensor (T c) (jointBlockLength T hT hD hne) := rfl

/-- The fusion tensor `X^c_{ab,μ}` of `ofCompressionBlocked` is the compression map `V_{(c,μ)}`
of the unblocked compression of `O_a O_b`. -/
theorem ofCompressionBlocked_fusionTensor (hT : ∀ c, Kraus.IsNormal (T c))
    (hD : ∀ c, 0 < D c) (hne) (P : ∀ a b, PairCompression T N a b)
    (hP : ∀ a b, (P a b).remainder = 0) (a b c : Fin g) (μ : Fin (N a b c))
    (x : Fin (D a) × Fin (D b)) (z : Fin (D c)) :
    (ofCompressionBlocked hT hD hne P hP).fusionTensor a b c μ x z =
      (P a b).right (pairSlot c μ) (finProdFinEquiv x) z := rfl

/-- The left inverse `X^{c+}_{ab,μ}` of `ofCompressionBlocked` is the compression map
`W_{(c,μ)}` of the unblocked compression of `O_a O_b`. -/
theorem ofCompressionBlocked_fusionTensorLeftInverse
    (hT : ∀ c, Kraus.IsNormal (T c)) (hD : ∀ c, 0 < D c) (hne)
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
noncomputable def ofStarBlocked (hT : ∀ c, Kraus.IsNormal (T c))
    (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv T)
    (htr : ∀ a b, ∀ w : List (Fin p × Fin p), w ≠ [] →
      Matrix.trace (Kraus.evalWord (mulTensor (T a) (T b)) w) =
        ∑ s : (c : Fin g) × Fin (N a b c),
          Matrix.trace (Kraus.evalWord (T s.1) w))
    (hstar : ∀ a b, ∀ i, (mulTensor (T a) (T b) i)ᴴ ∈
      Algebra.adjoin ℂ (Set.range (mulTensor (T a) (T b)))) :
    CompleteZipperFusionFamily (Fin g)
      (Kraus.blockPhysDim p (jointBlockLength T hT hD hne)) :=
  let hsplit : ∀ a b, ∃ P : PairCompression T N a b, P.remainder = 0 := fun a b =>
    MPSTensor.exists_multiBlockCompression_remainder_eq_zero_of_star
      (D := fun s : (c : Fin g) × Fin (N a b c) => D s.1) Finset.univ
      (fun s : (c : Fin g) × Fin (N a b c) => T s.1) (fun s _ => hT s.1) (fun s _ => hD s.1) _
      (htr a b) (hstar a b)
  ofCompressionBlocked hT hD hne (fun a b => (hsplit a b).choose)
    (fun a b => (hsplit a b).choose_spec)

end CompleteZipperFusionFamily

end MPOTensor

end

section

namespace MPSTensor

/-- Individually injective, pairwise gauge-phase-inequivalent blocks have a
common positive simultaneous spanning length, without a spectral-radius-one
assumption on any original block. -/
private theorem exists_positive_wordTupleSpanTop_of_isInjective_fin
    {d g : ℕ} {dim : Fin g → ℕ}
    {B : (j : Fin g) → MPSTensor d (dim j)}
    (hInj : ∀ j, Kraus.IsInjective (B j)) (hdimPos : ∀ j, 0 < dim j)
    (hDistinct : BlocksNotGaugePhaseEquiv (α := Fin d) B) :
    ∃ L : ℕ, 0 < L ∧ WordTupleSpanTop B L := by
  have hScaled : ∀ j, ∃ ζ : ℂ, ζ ≠ 0 ∧ IsNormalTensor (ζ • B j) := by
    intro j
    have : NeZero (dim j) := ⟨(hdimPos j).ne'⟩
    obtain ⟨A, ζ, hζ, hGauge, -, -, hA⟩ :=
      exists_leftCanonical_normalTensor_scale_of_isNormal (hInj j).isNormal
    exact ⟨ζ, hζ, IsNormalTensor.of_gaugeEquiv hA hGauge⟩
  choose scale hscale hNormal using hScaled
  obtain ⟨L, hL, hSpan⟩ := exists_positive_wordTupleSpanTop_of_isNormal hNormal hdimPos
    (fun j k hjk hdim hGPE => hDistinct j k hjk hdim
      (gaugePhaseEquiv_of_smul_smul_cast hdim (hscale j) (hscale k) hGPE))
  exact ⟨L, hL, wordTupleSpanTop_of_smul hscale hSpan⟩

/-- Individually injective, pairwise gauge-phase-inequivalent blocks over any finite physical
alphabet have a common positive simultaneous spanning length, without a spectral-radius-one
assumption on any original block. -/
theorem exists_positive_wordTupleSpanTop_of_isInjective
    {α : Type*} [Finite α] {g : ℕ} {dim : Fin g → ℕ}
    {B : (j : Fin g) → MPTensor α (Fin (dim j))}
    (hInj : ∀ j, Kraus.IsInjective (B j)) (hdimPos : ∀ j, 0 < dim j)
    (hDistinct : BlocksNotGaugePhaseEquiv B) :
    ∃ L : ℕ, 0 < L ∧ WordTupleSpanTop B L := by
  have := Fintype.ofFinite α
  let e := (Fintype.equivFin α).symm
  obtain ⟨L, hL, hSpan⟩ := exists_positive_wordTupleSpanTop_of_isInjective_fin
    (B := fun j ↦ Kraus.reindexPhysical e (B j))
    (fun j ↦ (isInjective_reindexPhysical_equiv e (B j)).2 (hInj j)) hdimPos
    (hDistinct.reindexPhysical e)
  exact ⟨L, hL, (wordTupleSpanTop_reindexPhysical_equiv e B L).1 hSpan⟩

end MPSTensor

end

end CompleteZipperFusionBlocked

section BoundarySourceDecomposition

/-!
## Source-block fusion and action tensors from arbitrary-boundary closedness

The source assumptions are length-independent arbitrary-boundary closedness
or compatibility, an unweighted block decomposition, and injective,
positive-dimensional target blocks with no gauge-scalar duplicates.
The common simultaneous inverse is derived, not assumed. The resulting
fusion and action tensors are exact and biorthogonal on each incoming pair.

### References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, block assumptions at
  lines 317--323, `algcond`, `eq:compatible`, and Appendix A.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- The arbitrary-boundary closedness and block hypotheses of GLM23 yield
exact fusion tensors for each pair of incoming blocks. The simultaneous
word-spanning length is derived from individual injectivity and block
separation. Source: `fusiontensors`, `eq:orthoW`, and Appendix A. -/
theorem IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective
    {d r : ℕ} {dim : Fin r → ℕ}
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPOTensor d (dim c))
    (hBlocks : T = MPTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    (hInj : ∀ c, Kraus.IsInjective (A c))
    (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv A)
    (a b : Fin r) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (dim a * dim b)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (dim a * dim b)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (A a) (A b))
        (fun q : (c : Fin r) × Fin (m c) ↦ A q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hDim hDistinct
  exact hT.exists_blockFusionDecomposition A hBlocks hL hSpan a b

/-- The arbitrary-boundary compatibility and block hypotheses of GLM23
yield exact action tensors for each operator/state incoming pair.
Only the target state blocks require injectivity and pairwise separation.
Source: `fusiontensors2`, `eq:orthoV`, and Appendix A, final paragraph. -/
theorem IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective
    {d r s : ℕ} {opDim : Fin r → ℕ} {dim : Fin s → ℕ}
    {T : MPOTensor d (∑ a : Fin r, opDim a)}
    {A : MPSTensor d (∑ c : Fin s, dim c)} (h : IsBoundaryCompatible T A)
    (S : (a : Fin r) → MPOTensor d (opDim a))
    (B : (c : Fin s) → MPSTensor d (dim c))
    (hT : T = MPTensor.toTensorFromBlocks (fun _ ↦ 1) S)
    (hA : A = MPTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    (hInj : ∀ c, Kraus.IsInjective (B c)) (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv B)
    (a : Fin r) (x : Fin s) :
    ∃ (m : Fin s → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (opDim a * dim x)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (opDim a * dim x)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (actTensor (S a) (B x))
        (fun q : (c : Fin s) × Fin (m c) ↦ B q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hDim hDistinct
  exact h.exists_blockActionDecomposition S B hT hA hL hSpan a x

end MPOTensor

end BoundarySourceDecomposition
