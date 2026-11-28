/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BlockSeparation.DirectSumSelectors
import TNLean.MPS.MPDO.BNTSectors.BNTBoundaryDecomposition
import TNLean.MPS.CanonicalForm.SimpleMPO.BNTProjectorSelection
import TNLean.MPS.MPDO.Entropy.LocalOrthogonalSumAreaLaw
import TNLean.MPS.Examples.NonCartesianSectors.NeighboringTraceObstructionAmbientBlocks
import TNLean.MPS.MPDO.PhysicalSector.PhysicalSectorActiveNeighboring
import TNLean.MPS.MPDO.PhysicalSector.PhysicalSectorGaugeTransport
import TNLean.MPS.MPDO.Entropy.SALTraceTransfer
import TNLean.MPS.CanonicalForm.SimpleMPO.Simple

/-!
# An ambient neighboring-trace obstruction in simple biCF form

This module assembles the rank-one neighboring-trace obstruction and the
terminal product block from `NeighboringTraceObstructionAmbientBlocks` into a
single five-letter matrix product density operator.  Its horizontal
presentation is the literal two-sector basis-of-normal-tensors decomposition:
the obstruction coefficient is absorbed only in the assembled tensor, while
the displayed basis tensor remains normal, and the terminal coefficient is
one.

The assembly follows the standing simple-biCF setting and the block-diagonal
argument of CPSV16, Appendix C.2, lines 1628--1782.  The finite simultaneous
word span and the entropy argument used below are proved in TNLean; they are
not attributed to that passage beyond their stated source roles.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.NeighboringTraceObstructionAmbientCounterexample

open NeighboringTraceObstructionAmbientBlocks PhysicalSectorFactorization

/-- The two-sector decomposition used for the ambient construction. -/
@[reducible] def sectors (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    MPSTensor.SectorDecomposition (Fin 5 × Fin 5) :=
  obstructionTerminalDecomposition mu B hmu

/-- The five-letter ambient MPO obtained from the weighted two-sector BNT.

Source role: this is the literal canonical-form assembly in CPSV16,
Appendix C.2, lines 1628--1665. -/
def ambient (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    MPOTensor 5 3 :=
  (sectors mu B hmu).toTensor

/-- The two one-copy coefficients are copy independent. -/
theorem sectors_weight_copy_independent
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    ∀ (j : Fin (sectors mu B hmu).basisCount)
      (q q' : Fin ((sectors mu B hmu).copies j)),
      (sectors mu B hmu).weight j q = (sectors mu B hmu).weight j q' := by
  intro j q q'
  fin_cases j <;> exact Subsingleton.elim q q' ▸ rfl

/-- The terminal block evaluates to the identity at its terminal physical
letter. -/
theorem terminalBlock_terminal_letter :
    terminalBlock ((4 : Fin 5), (4 : Fin 5)) = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [terminalBlock, changePhysicalBasis, physicalSlice,
    Matrix.mul_apply, terminalPhysicalInclusion]

/-- The terminal block on the alphabet `Fin (5 * 5)`, where the pair word-tuple span
criterion is stated.  This relabelling is a bridge until the vertical alphabet moves to pairs
(T.2c). -/
private noncomputable def terminalBlockFin : MPSTensor (5 * 5) 1 :=
  Kraus.reindexPhysical finProdFinEquiv.symm terminalBlock

private theorem pairWordTupleSpanTop_obstruction_terminal
    (B : MPSTensor (5 * 5) 2)
    (hInjective : Kraus.IsInjective B)
    (hSupport : physicalSupportProj (verticalBNTMPO B) =
      obstructionPhysicalSupport) :
    MPSTensor.PairWordTupleSpanTop B terminalBlockFin 1 := by
  unfold MPSTensor.PairWordTupleSpanTop
  apply top_unique
  rintro ⟨X, y⟩ _hy
  let terminalLetter : Fin (5 * 5) :=
    finProdFinEquiv ((4 : Fin 5), (4 : Fin 5))
  let terminalWord : Fin 1 → Fin (5 * 5) := fun _ ↦ terminalLetter
  have hBTerminal : B terminalLetter = 0 := by
    ext β α
    have hFix :=
      physicalSupportProj_mul_physicalSlice (verticalBNTMPO B) β α
    rw [hSupport] at hFix
    have hEntry := congrFun (congrFun hFix (4 : Fin 5)) (4 : Fin 5)
    symm
    simpa [obstructionPhysicalSupport, physicalInclusion, Matrix.mul_apply,
      Fin.sum_univ_four, physicalSlice, terminalLetter] using hEntry
  have hTerminalTuple :
      MPSTensor.pairWordTuple B terminalBlockFin 1 terminalWord =
        (0, 1) := by
    apply Prod.ext
    · simpa [MPSTensor.pairWordTuple, terminalWord, terminalLetter]
        using hBTerminal
    · have hLetter : terminalBlockFin terminalLetter = 1 := by
        change terminalBlock (finProdFinEquiv.symm terminalLetter) = 1
        rw [Equiv.symm_apply_apply]
        exact terminalBlock_terminal_letter
      simpa [MPSTensor.pairWordTuple, terminalWord] using hLetter
  have hTerminalMem : (0, 1) ∈ Submodule.span ℂ
      (Set.range
        (MPSTensor.pairWordTuple B terminalBlockFin 1)) := by
    rw [← hTerminalTuple]
    exact Submodule.subset_span (Set.mem_range_self terminalWord)
  have hX : X ∈ Submodule.span ℂ (Set.range B) := by
    rw [hInjective]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  let Z := ∑ i : Fin (5 * 5), c i •
    MPSTensor.pairWordTuple B terminalBlockFin 1 (fun _ ↦ i)
  have hZMem : Z ∈ Submodule.span ℂ
      (Set.range
        (MPSTensor.pairWordTuple B terminalBlockFin 1)) := by
    apply Submodule.sum_mem
    intro i _hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self (fun _ : Fin 1 ↦ i)))
  have hZFirst : Z.1 = X := by
    ext a b
    have hcEntry := congrFun (congrFun hc a) b
    simpa [Z, MPSTensor.pairWordTuple, Prod.fst_sum, Prod.smul_fst,
      Finset.sum_apply] using hcEntry
  have hEq : (X, y) = Z + (y 0 0 - Z.2 0 0) • (0, 1) := by
    apply Prod.ext
    · simp [hZFirst]
    · ext a b
      fin_cases a
      fin_cases b
      simp
  rw [hEq]
  exact Submodule.add_mem _ hZMem (Submodule.smul_mem _ _ hTerminalMem)

private theorem pairWordTupleSpanTop_terminal_obstruction
    (B : MPSTensor (5 * 5) 2)
    (hPair : MPSTensor.PairWordTupleSpanTop B terminalBlockFin 1) :
    MPSTensor.PairWordTupleSpanTop terminalBlockFin B 1 := by
  unfold MPSTensor.PairWordTupleSpanTop at hPair ⊢
  apply top_unique
  rintro ⟨y, X⟩ _h
  have hSwap : (X, y) ∈ Submodule.span ℂ
      (Set.range
        (MPSTensor.pairWordTuple B terminalBlockFin 1)) := by
    rw [hPair]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp hSwap
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, ?_⟩
  apply Prod.ext
  · ext a b
    have hSecond := congrFun (congrFun (congrArg Prod.snd hc) a) b
    simpa [MPSTensor.pairWordTuple, Prod.snd_sum, Prod.smul_snd,
      Prod.fst_sum, Prod.smul_fst, Finset.sum_apply] using hSecond
  · ext a b
    have hFirst := congrFun (congrFun (congrArg Prod.fst hc) a) b
    simpa [MPSTensor.pairWordTuple, Prod.snd_sum, Prod.smul_snd,
      Prod.fst_sum, Prod.smul_fst, Finset.sum_apply] using hFirst

/-- The displayed obstruction and terminal representatives simultaneously span
their full matrix spaces using words of literal length one. -/
theorem sectors_wordTupleSpanTop_one
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hInjective : Kraus.IsInjective B)
    (hSupport : physicalSupportProj B = obstructionPhysicalSupport) :
    MPSTensor.WordTupleSpanTop (sectors mu B hmu).basis 1 := by
  -- The pair word-tuple spans are stated on a `Fin` alphabet: relabel along `finProdFinEquiv`.
  let e := (finProdFinEquiv (m := 5) (n := 5)).symm
  have hVertical : verticalBNTMPO (Kraus.reindexPhysical e B) = B := by
    funext ab
    simp [verticalBNTMPO, e, Kraus.reindexPhysical]
  have hPair := pairWordTupleSpanTop_obstruction_terminal (Kraus.reindexPhysical e B)
    ((MPSTensor.isInjective_reindexPhysical_equiv e B).2 hInjective)
    (by rw [hVertical]; exact hSupport)
  have hPairSymm := pairWordTupleSpanTop_terminal_obstruction _ hPair
  have hr : 2 ≤ (sectors mu B hmu).basisCount := by
    change 2 ≤ 2
    omega
  have hSpan :=
    MPSTensor.wordTupleSpanTop_mul_pred_of_forall_pairWordTupleSpanTop
      (fun k ↦ Kraus.reindexPhysical e ((sectors mu B hmu).basis k)) hr (S := 1)
      (fun k j hjk ↦ by
        change Fin 2 at k j
        fin_cases k <;> fin_cases j
        · exact absurd rfl hjk
        · exact hPair
        · exact hPairSymm
        · exact absurd rfl hjk)
  norm_num at hSpan
  exact (MPSTensor.wordTupleSpanTop_reindexPhysical_equiv e _ 1).1 hSpan

/-- Both representatives displayed by the ambient decomposition are normal. -/
theorem sectors_basis_isNormalTensor
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hBNormal : MPTensor.IsNormalTensor B) :
    ∀ j, MPTensor.IsNormalTensor ((sectors mu B hmu).basis j) := by
  intro j
  change Fin 2 at j
  fin_cases j
  · exact hBNormal
  · exact terminalBlock_isNormalTensor

/-- Bond dimensions of the two physical sectors. -/
@[reducible] def sectorDim : Fin 2 → ℕ :=
  Fin.cons 2 (fun _ : Fin 1 ↦ 1)

/-- The actual entropy sectors: the embedded obstruction and the terminal
product block. -/
def physicalSector : (s : Fin 2) → MPOTensor 5 (sectorDim s) :=
  Fin.cons embeddedObstruction (fun _ : Fin 1 ↦ terminalBlock)

/-- The corresponding orthogonal one-site support projections. -/
def sectorProjection : Fin 2 → Matrix (Fin 5) (Fin 5) ℂ :=
  Fin.cons obstructionPhysicalSupport (fun _ : Fin 1 ↦ terminalPhysicalSupport)

/-- Each chosen projection is the joint column support of its physical
sector. -/
theorem physicalSector_physicalSupportProj (s : Fin 2) :
    physicalSupportProj (physicalSector s) = sectorProjection s := by
  fin_cases s
  · exact embeddedObstruction_physicalSupportProj
  · exact terminalBlock_physicalSupportProj

/-- The chosen one-site supports are orthogonal projections. -/
theorem sectorProjection_isOrthogonal (s : Fin 2) :
    IsOrthogonalProjection (sectorProjection s) := by
  rw [← physicalSector_physicalSupportProj s]
  exact (Matrix.posSemidef_self_mul_conjTranspose
    (physicalSliceColumns (physicalSector s))).isOrthogonalProjection_supportProj

/-- Distinct physical sectors have orthogonal one-site supports. -/
theorem sectorProjection_mul_eq_zero {s t : Fin 2} (hst : s ≠ t) :
    sectorProjection s * sectorProjection t = 0 := by
  fin_cases s <;> fin_cases t
  · exact absurd rfl hst
  · exact obstructionPhysicalSupport_mul_terminalPhysicalSupport
  · exact terminalPhysicalSupport_mul_obstructionPhysicalSupport
  · exact absurd rfl hst

/-- A tensor's physical support projection fixes it on the ket index.  This
is the tensor-level support identity used in the local orthogonal-sum entropy
argument. -/
private theorem ketLeftMul_physicalSupportProj {d D : ℕ} (K : MPOTensor d D) :
    K.ketLeftMul (physicalSupportProj K) = K := by
  ext ⟨i, j⟩ β α
  have h := congrFun (congrFun (physicalSupportProj_mul_physicalSlice K β α) i) j
  simpa [ketLeftMul, physicalSlice, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using h

/-- Every nonempty prefix marginal of a physical sector remains in its
chosen one-site support. -/
theorem physicalSector_reducedBlockState_supported
    (s : Fin 2) (N L : ℕ) (_hN : 2 ≤ N) (hL : L + 1 ≤ N) :
    firstSiteMatrix (sectorProjection s) L *
        reducedBlockState (physicalSector s) N (L + 1) hL =
      reducedBlockState (physicalSector s) N (L + 1) hL := by
  apply firstSiteMatrix_mul_reducedBlockState_of_ketLeftMul_eq
  rw [← physicalSector_physicalSupportProj s]
  exact ketLeftMul_physicalSupportProj (physicalSector s)

/-- Gauge-equivalent operator tensors have identical closed MPOs. -/
private theorem mpo_eq_of_gaugeEquiv {d D : ℕ} {K L : MPOTensor d D}
    (hGauge : MPTensor.GaugeEquiv K L) (N : ℕ) :
    mpo K N = mpo L N := by
  ext σ τ
  rw [← mpv_pair, ← mpv_pair]
  exact hGauge.sameMPV N _

/-- The first common-weight-absorbed BNT sector is the absorbed obstruction
tensor. -/
private theorem firstAbsorbedSector_eq
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    (sectors mu B hmu).commonWeightAbsorbedBasis
      (sectors_weight_copy_independent mu B hmu) 0 = mu • B :=
  rfl

/-- The second common-weight-absorbed BNT sector is the terminal block. -/
private theorem secondAbsorbedSector_eq
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    (sectors mu B hmu).commonWeightAbsorbedBasis
      (sectors_weight_copy_independent mu B hmu) (Fin.succ 0) = terminalBlock := by
  change (fun i ↦ (1 : ℂ) • terminalBlock i) = terminalBlock
  simp

/-- Taking a diagonal block after flattening a dependent block-diagonal matrix
recovers the selected block. -/
private theorem finSigmaDiagonalBlock_reindex_blockDiagonal
    {r : ℕ} {dim : Fin r → ℕ}
    (C : (s : Fin r) → Matrix (Fin (dim s)) (Fin (dim s)) ℂ)
    (s : Fin r) :
    Matrix.finSigmaDiagonalBlock
        (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
          (Matrix.blockDiagonal' C)) s = C s := by
  ext a b
  simp [Matrix.finSigmaDiagonalBlock]

/-- The family of virtual boundary blocks that carries `X` on the obstruction
copy and zero on every other copy. -/
private def obstructionSectorBoundaryBlock
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Fin (sectors mu B hmu).totalCopies) :
    Matrix (Fin ((sectors mu B hmu).flatDim s))
      (Fin ((sectors mu B hmu).flatDim s)) ℂ :=
  let S := sectors mu B hmu
  let firstCopy : Fin S.totalCopies := S.flatIndexEquiv ⟨0, 0⟩
  if hs : s = firstCopy then
    cast (congrArg (fun n ↦ Matrix (Fin n) (Fin n) ℂ) (by
      have hdim : S.flatDim firstCopy = 2 := by
        unfold firstCopy
        exact (S.flatDim_flatIndexEquiv ⟨(0 : Fin S.basisCount), 0⟩).trans (by rfl)
      exact hdim.symm.trans (congrArg S.flatDim hs.symm))) X
  else 0

/-- Embed a boundary matrix into the obstruction block of the ambient virtual
space, with zero boundary on the terminal block. This is the two-sector
coordinate form of the arbitrary-boundary BNT assembly in CPSV16, Appendix
C.2, lines 1646--1665. -/
private def obstructionSectorBoundary
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (sectors mu B hmu).totalDim)
      (Fin (sectors mu B hmu).totalDim) ℂ :=
  Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
    (Matrix.blockDiagonal' (obstructionSectorBoundaryBlock mu B hmu X))

/-- Each flattened diagonal block of the ambient obstruction boundary is its
defining boundary block. -/
@[simp] private theorem finSigmaDiagonalBlock_obstructionSectorBoundary
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Fin (sectors mu B hmu).totalCopies) :
    Matrix.finSigmaDiagonalBlock (obstructionSectorBoundary mu B hmu X) s =
      obstructionSectorBoundaryBlock mu B hmu X s :=
  finSigmaDiagonalBlock_reindex_blockDiagonal _ _

/-- The obstruction representative sees precisely the embedded boundary. -/
private theorem representativeBoundary_obstructionSectorBoundary_zero
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    representativeBoundary (sectors mu B hmu)
        (obstructionSectorBoundary mu B hmu X) 0 = X := by
  rw [representativeBoundary, Fin.sum_univ_one,
    finSigmaDiagonalBlock_obstructionSectorBoundary]
  apply eq_of_heq
  exact cast_heq _ _

/-- The terminal representative sees the zero boundary. -/
private theorem representativeBoundary_obstructionSectorBoundary_one
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    representativeBoundary (sectors mu B hmu)
        (obstructionSectorBoundary mu B hmu X)
        (Fin.succ 0) = 0 := by
  rw [representativeBoundary, Fin.sum_univ_one,
    finSigmaDiagonalBlock_obstructionSectorBoundary]
  have hBlock : obstructionSectorBoundaryBlock mu B hmu X
      ((sectors mu B hmu).flatIndexEquiv ⟨Fin.succ 0, 0⟩) = 0 := by
    simp [obstructionSectorBoundaryBlock, sectors,
      obstructionTerminalDecomposition]
  rw [hBlock]
  apply eq_of_heq
  exact cast_heq _ _

/-- Conjugating a virtual boundary transports a gauge-equivalent physical
closure back to the original tensor. -/
private theorem physCloseN_gauge_obstructionSector
    {K L : MPOTensor 5 2} (G : GL (Fin 2) ℂ)
    (hG : ∀ i, L i =
      (G : Matrix (Fin 2) (Fin 2) ℂ) * K i *
        (↑(G⁻¹) : Matrix (Fin 2) (Fin 2) ℂ))
    (N : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physCloseN L N
        ((G : Matrix (Fin 2) (Fin 2) ℂ) * X *
          (↑(G⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)) =
      physCloseN K N X := by
  ext σ τ
  rw [physCloseN_apply, physCloseN_apply,
    ← kraus_evalWord_ofFn_pair, ← kraus_evalWord_ofFn_pair]
  simpa [Matrix.mul_assoc] using MPSTensor.trace_evalWord_gauge_mul G hG
    (List.ofFn fun k ↦ (σ k, τ k))
    ((G : Matrix (Fin 2) (Fin 2) ℂ) * X *
      (↑(G⁻¹) : Matrix (Fin 2) (Fin 2) ℂ))

/-- A single ambient virtual boundary isolates the embedded obstruction sector
at every chain length.

The same boundary is used for all lengths, as required when the two channel
equations in CPSV16 Proposition C.15 are compared. This is the arbitrary-
boundary specialization of the BNT assembly in CPSV16, Appendix C.2, lines
1646--1665 and 1810--1825. -/
theorem exists_ambient_boundary_physCloseN_eq_embeddedObstruction
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ Y : Matrix (Fin 3) (Fin 3) ℂ, ∀ N : ℕ,
      physCloseN (ambient mu B hmu) N Y = physCloseN embeddedObstruction N X := by
  let S := sectors mu B hmu
  change ∃ Y : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ, ∀ N : ℕ,
    physCloseN S.toTensor N Y = physCloseN embeddedObstruction N X
  obtain ⟨G, hG⟩ := hGauge
  let XG := (G : Matrix (Fin 2) (Fin 2) ℂ) * X *
    (↑(G⁻¹) : Matrix (Fin 2) (Fin 2) ℂ)
  refine ⟨obstructionSectorBoundary mu B hmu XG, fun N ↦ ?_⟩
  have hAmbient : ∀ i, S.toTensor i =
      (1 : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (↑((1 : GL (Fin S.totalDim) ℂ)⁻¹) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    intro i
    simp
  rw [physCloseN_eq_sum_commonWeightAbsorbedBasis_of_gauge_toTensor
    S (sectors_weight_copy_independent mu B hmu)
    S.toTensor (1 : GL (Fin S.totalDim) ℂ) hAmbient N
    (obstructionSectorBoundary mu B hmu XG)]
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  dsimp only [S]
  rw [Fin.sum_univ_two,
    representativeBoundary_obstructionSectorBoundary_zero]
  have hTerminalBoundary : representativeBoundary (sectors mu B hmu)
      (obstructionSectorBoundary mu B hmu XG) (1 : Fin 2) = 0 := by
    simpa using representativeBoundary_obstructionSectorBoundary_one mu B hmu XG
  rw [hTerminalBoundary]
  simp only [map_zero, add_zero]
  apply physCloseN_gauge_obstructionSector G (N := N) (X := X)
  intro i
  apply eq_of_heq
  exact (heq_of_eq (congrFun (firstAbsorbedSector_eq mu B hmu) i)).trans
    (heq_of_eq (hG i))

/-- The identity presentation gives equality of the positive-length MPV
families of the ambient tensor and its BNT assembly. -/
theorem ambient_sameMPV₂Pos_sectors_toTensor
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0) :
    MPTensor.SameMPV₂Pos (ambient mu B hmu)
      (sectors mu B hmu).toTensor := by
  intro N _hN ρ
  rfl

/-- At every positive length, the ambient periodic operator is the sum of
the actual embedded obstruction and terminal periodic operators.

This is the two-sector specialization of the coefficient-absorption identity
in CPSV16, Appendix C.2, lines 1660--1665 and 1753--1770. -/
theorem mpo_ambient_eq_sum_physicalSector
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (N : ℕ) (hN : 0 < N) :
    mpo (ambient mu B hmu) N = ∑ s : Fin 2, mpo (physicalSector s) N := by
  rw [mpo_eq_sum_copies_smul_commonWeightAbsorbedBasis
    (ambient mu B hmu) (sectors mu B hmu)
    (ambient_sameMPV₂Pos_sectors_toTensor mu B hmu)
    (sectors_weight_copy_independent mu B hmu) hN]
  have hFirst :
      mpo ((sectors mu B hmu).commonWeightAbsorbedBasis
        (sectors_weight_copy_independent mu B hmu) 0) N =
        mpo embeddedObstruction N :=
    (mpo_eq_of_gaugeEquiv (by rw [firstAbsorbedSector_eq]; exact hGauge) N).symm
  have hSecond :
      mpo ((sectors mu B hmu).commonWeightAbsorbedBasis
        (sectors_weight_copy_independent mu B hmu) (Fin.succ 0)) N =
        mpo terminalBlock N := by
    apply mpo_eq_of_gaugeEquiv (N := N)
    rw [secondAbsorbedSector_eq]
    exact MPTensor.GaugeEquiv.refl _
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hCopiesZero : (sectors mu B hmu).copies 0 = 1 := rfl
  have hSecond' :
      mpo ((sectors mu B hmu).commonWeightAbsorbedBasis
        (sectors_weight_copy_independent mu B hmu) (1 : Fin 2)) N =
        mpo terminalBlock N := by
    simpa using hSecond
  rw [hCopiesZero]
  norm_num only [Nat.cast_one]
  rw [one_smul, one_smul, hFirst, hSecond']
  rfl

/-- Positivity of the two actual sectors makes the ambient tensor an MPDO. -/
theorem ambient_isMPDO
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    IsMPDO (ambient mu B hmu) := by
  intro N hN
  rw [mpo_ambient_eq_sum_physicalSector mu B hmu hGauge N hN]
  rw [Fin.sum_univ_two]
  exact (embeddedObstruction_isMPDO N hN).add (terminalBlock_isMPDO N hN)

/-- The local orthogonal-sum entropy decomposition transports SAL from the
embedded obstruction and terminal sectors to the ambient tensor. -/
theorem ambient_isSAL
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    IsSAL (ambient mu B hmu) := by
  apply isSAL_of_localOrthogonalSum
    (ambient mu B hmu) physicalSector (fun _ : Fin 2 ↦ 1) sectorProjection
  · intro s
    exact Nat.one_pos
  · exact sectorProjection_isOrthogonal
  · intro s t hst
    exact sectorProjection_mul_eq_zero hst
  · intro N hN
    simpa using mpo_ambient_eq_sum_physicalSector mu B hmu hGauge N hN
  · exact physicalSector_reducedBlockState_supported
  · intro s
    fin_cases s
    · exact embeddedObstruction_isSAL
    · exact terminalBlock_isSAL

/-- Scalar multiplication of a doubled-index tensor scales its physical-trace
transfer by the same scalar. -/
private theorem physTraceTransfer_smul {d D : ℕ}
    (c : ℂ) (A : MPOTensor d D) :
    physTraceTransfer (c • A) = c • physTraceTransfer A := by
  simp [physTraceTransfer, Finset.smul_sum]

/-- The doubled physical-trace transfers of gauge-equivalent tensors are
similar matrices. -/
private theorem exists_physTraceTransfer_eq_conj_of_gaugeEquiv
    {d D : ℕ} {A B : MPOTensor d D}
    (hGauge : MPTensor.GaugeEquiv A B) :
    ∃ X : GL (Fin D) ℂ,
      physTraceTransfer B =
        (X : Matrix (Fin D) (Fin D) ℂ) * physTraceTransfer A *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨X, hX⟩ := hGauge
  refine ⟨X, ?_⟩
  rw [physTraceTransfer, physTraceTransfer,
    Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ hX (i, i)

/-- The absorbed obstruction block inherits literal transfer idempotence from
the actual embedded obstruction by virtual gauge similarity. -/
theorem firstAbsorbed_physTraceTransfer_idempotent
    (mu : ℂ) (B : MPOTensor 5 2)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    IsIdempotentElem (physTraceTransfer (mu • B)) := by
  obtain ⟨X, hTransfer⟩ :=
    exists_physTraceTransfer_eq_conj_of_gaugeEquiv hGauge
  rw [hTransfer]
  calc
    ((X : Matrix (Fin 2) (Fin 2) ℂ) *
          physTraceTransfer embeddedObstruction *
          ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((X : Matrix (Fin 2) (Fin 2) ℂ) *
          physTraceTransfer embeddedObstruction *
          ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
      (X : Matrix (Fin 2) (Fin 2) ℂ) *
        (physTraceTransfer embeddedObstruction *
          physTraceTransfer embeddedObstruction) *
        ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp [Matrix.mul_assoc]
    _ = (X : Matrix (Fin 2) (Fin 2) ℂ) *
        physTraceTransfer embeddedObstruction *
        ((X⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [embeddedObstruction_physTraceTransfer_idempotent]

/-- The unabsorbed obstruction representative has nonnilpotent
physical-trace transfer.  The proof uses only SAL nonvanishing for the actual
embedded sector, its literal idempotence, nonzero scalar absorption, and
virtual gauge transport. -/
theorem obstructionBasis_physTraceTransfer_not_isNilpotent
    (mu : ℂ) (B : MPOTensor 5 2)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    ¬ IsNilpotent (physTraceTransfer B) := by
  intro hNil
  have hScaled : IsNilpotent (physTraceTransfer (mu • B)) := by
    rw [physTraceTransfer_smul]
    exact hNil.smul mu
  have hEmbedded :
      IsNilpotent (physTraceTransfer embeddedObstruction) :=
    (isNilpotent_physTraceTransfer_iff_of_gaugePhaseEquiv
      hGauge.toGaugePhaseEquiv).mpr hScaled
  have hIdempotent : IsIdempotentElem (physTraceTransfer embeddedObstruction) :=
    embeddedObstruction_physTraceTransfer_idempotent
  exact embeddedObstruction_isSAL.physTraceTransfer_ne_zero
    (hIdempotent.eq_zero_of_isNilpotent hEmbedded)

/-- Neither unabsorbed representative of the displayed BNT has nilpotent
physical-trace transfer. -/
theorem sectors_basis_physTraceTransfer_not_isNilpotent
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (j : Fin (sectors mu B hmu).basisCount) :
    ¬ IsNilpotent (physTraceTransfer ((sectors mu B hmu).basis j)) := by
  change Fin 2 at j
  by_cases hj : j = 0
  · subst j
    rw [(obstructionTerminalDecomposition_basis mu B hmu).1]
    exact obstructionBasis_physTraceTransfer_not_isNilpotent
      mu B hGauge
  · have hj' : j = Fin.succ 0 := by
      fin_cases j <;> simp_all
    subst j
    let S := sectors mu B hmu
    have hDim : S.basisDim (Fin.succ 0) = 1 :=
      (obstructionTerminalDecomposition_basisDim mu B hmu).2
    intro hNil
    have hCast : IsNilpotent
        (physTraceTransfer
          (cast (congr_arg (MPOTensor 5) hDim) (S.basis (Fin.succ 0)))) :=
      (isNilpotent_physTraceTransfer_cast_iff hDim
        (S.basis (Fin.succ 0))).mpr hNil
    have hBasis : S.basis (Fin.succ 0) = terminalBlock :=
      (obstructionTerminalDecomposition_basis mu B hmu).2
    have hCastEq :
        cast (congr_arg (MPOTensor 5) hDim) (S.basis (Fin.succ 0)) =
          terminalBlock := by
      apply eq_of_heq
      exact (cast_heq _ _).trans (heq_of_eq hBasis)
    rw [hCastEq, terminalBlock_physTraceTransfer_eq_one] at hCast
    exact not_isNilpotent_one hCast

private theorem isIdempotentElem_smul_physTraceTransfer_cast_iff
    {d D₁ D₂ : ℕ} (hdim : D₁ = D₂) (c : ℂ)
    (A : MPOTensor d D₁) :
    IsIdempotentElem
        (c • physTraceTransfer
          (cast (congr_arg (MPOTensor d) hdim) A)) ↔
      IsIdempotentElem (c • physTraceTransfer A) := by
  subst D₂
  rfl

/-- Every flattened weighted block of the ambient BNT has idempotent
physical-trace transfer. -/
private theorem sectors_flatWeightedTransfer_idempotent
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (s : Fin (sectors mu B hmu).totalCopies) :
    IsIdempotentElem
      ((sectors mu B hmu).flatWeight s •
        physTraceTransfer ((sectors mu B hmu).flatBasis s)) := by
  let S := sectors mu B hmu
  change IsIdempotentElem
    (S.flatWeight s • physTraceTransfer (S.flatBasis s))
  obtain ⟨⟨j, q⟩, rfl⟩ := S.flatIndexEquiv.surjective s
  rw [MPSTensor.SectorDecomposition.flatWeight_flatIndexEquiv]
  have hDim := S.flatDim_flatIndexEquiv ⟨j, q⟩
  apply (isIdempotentElem_smul_physTraceTransfer_cast_iff hDim
    (S.weight j q) (S.flatBasis (S.flatIndexEquiv ⟨j, q⟩))).mp
  have hBasisCast :
      cast (congr_arg (MPOTensor 5) hDim)
          (S.flatBasis (S.flatIndexEquiv ⟨j, q⟩)) = S.basis j := by
    apply eq_of_heq
    exact (cast_heq _ _).trans (S.flatBasis_flatIndexEquiv_heq ⟨j, q⟩)
  rw [hBasisCast]
  change Fin 2 at j
  fin_cases j
  · fin_cases q
    change IsIdempotentElem (mu • physTraceTransfer B)
    rw [← physTraceTransfer_smul]
    exact firstAbsorbed_physTraceTransfer_idempotent mu B hGauge
  · fin_cases q
    change IsIdempotentElem
      ((1 : ℂ) • physTraceTransfer terminalBlock)
    rw [one_smul, terminalBlock_physTraceTransfer_eq_one]
    exact one_mul 1

/-- The ambient tensor satisfies the physical-trace zero-correlation-length
identity without rescaling.

Source: CPSV16, Definition 4.2, lines 735--739, in the standing Appendix C.2
setting at lines 1628--1782. -/
theorem ambient_literal_physTrace_ZCL
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    physTraceTransfer (ambient mu B hmu) *
        physTraceTransfer (ambient mu B hmu) =
      physTraceTransfer (ambient mu B hmu) := by
  let S := sectors mu B hmu
  have hS :
      physTraceTransfer S.toTensor *
          physTraceTransfer S.toTensor =
        physTraceTransfer S.toTensor := by
    have hBlocks :
        (fun s : Fin S.totalCopies ↦
            (S.flatWeight s • physTraceTransfer (S.flatBasis s)) *
              (S.flatWeight s • physTraceTransfer (S.flatBasis s))) =
          fun s ↦ S.flatWeight s • physTraceTransfer (S.flatBasis s) := by
      funext s
      exact sectors_flatWeightedTransfer_idempotent mu B hmu hGauge s
    rw [physTraceTransfer_toTensor]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [← Matrix.blockDiagonal'_mul, hBlocks]
  exact hS

/-- The ambient tensor has the displayed simple canonical form.  The terminal
block supplies the single global unit coefficient, and both unabsorbed BNT
representatives have nonnilpotent physical-trace transfer.

Source: CPSV16, canonical form at lines 224--246, simplicity at lines
815--822, and the standing Appendix C.2 hypothesis at line 1628. -/
theorem ambient_isSimpleCanonicalForm
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (hBNT : MPSTensor.IsLeftCanonicalBNTPresentation (sectors mu B hmu)) :
    IsSimpleCanonicalForm (ambient mu B hmu) := by
  refine ⟨ambient_isMPDO mu B hmu hGauge, sectors mu B hmu, hBNT,
    sectors_basis_physTraceTransfer_not_isNilpotent mu B hmu hGauge, ?_⟩
  let S := sectors mu B hmu
  have hTotal : S.totalDim = 3 := by rfl
  let X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ := fun _ ↦ 1
  refine ⟨hTotal, X, ?_⟩
  have hGlobal : MPSTensor.globalGaugeOfBlocks X = 1 := by
    change Units.map _ (Units.map _ ((MulEquiv.piUnits).symm X)) = 1
    rw [show X = 1 by rfl]
    simp
  intro p
  simp only [hGlobal, Units.val_one, inv_one, one_mul, mul_one]
  exact (cast_eq _ _).symm

/-- The ambient tensor is simple in the sense of CPSV16, Definition 4.7.
This follows from its displayed simple canonical form.

Source: CPSV16, Definition 4.7, lines 815--822, under the standing Appendix
C.2 hypothesis at line 1628. -/
theorem ambient_isSimple
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    (hBNT : MPSTensor.IsLeftCanonicalBNTPresentation (sectors mu B hmu)) :
    IsSimple (ambient mu B hmu) :=
  (ambient_isSimpleCanonicalForm mu B hmu hGauge hBNT).isSimple

/-- Every positive-length ambient periodic operator has strictly positive
normalization.  This is the normalization clause used in the Appendix C.2
standing MPDO and SAL hypotheses.

Source: CPSV16, lines 623--630, 811--815, and 1760--1780. -/
theorem trace_mpo_ambient_pos
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B))
    {N : ℕ} (hN : 0 < N) :
    0 < Matrix.trace (mpo (ambient mu B hmu) N) := by
  exact trace_mpo_pos_of_isMPDO_isSourceZCL (ambient mu B hmu)
    (ambient_isMPDO mu B hmu hGauge)
    ((ambient_isSAL mu B hmu hGauge).isSourceZCL_of_physTraceTransfer_sq
      (ambient_literal_physTrace_ZCL mu B hmu hGauge)) hN

/-- The first common-weight-absorbed representative admits no normalized
rank-one neighboring-trace factorization.

The contradiction transports a hypothetical factorization through the
virtual gauge to the embedded obstruction and then descends it through the
isometric physical inclusion to the four-letter obstruction.  The gauge and
isometric descent arguments are proved in TNLean; CPSV16 uses the asserted
factorization at Appendix C.2, lines 1740--1782, but does not supply these
results. -/
theorem firstCommonWeightAbsorbed_not_exists_neighboringTraceFactorization
    (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0)
    (hGauge : MPTensor.GaugeEquiv embeddedObstruction (mu • B)) :
    ¬ ∃ F : PhysicalSectorFactorization
        ((sectors mu B hmu).commonWeightAbsorbedBasis
          (sectors_weight_copy_independent mu B hmu) 0),
      Nonempty F.NeighboringTraceFactorization := by
  intro hAbsorbed
  have hGaugeAbsorbed : MPTensor.GaugeEquiv embeddedObstruction
      ((sectors mu B hmu).commonWeightAbsorbedBasis
        (sectors_weight_copy_independent mu B hmu) 0) := by
    rw [firstAbsorbedSector_eq]
    exact hGauge
  have hEmbedded :
      ∃ F : PhysicalSectorFactorization embeddedObstruction,
        Nonempty F.NeighboringTraceFactorization :=
    (PhysicalSectorFactorization.exists_neighboringTraceFactorization_iff_of_gaugeEquiv
        hGaugeAbsorbed).mpr hAbsorbed
  have hSource :
      ∃ F : PhysicalSectorFactorization
          MPOTensor.NonCartesianActiveSectorCandidate.tensor,
        Nonempty F.NeighboringTraceFactorization := by
    exact
      exists_neighboringTraceFactorization_of_changePhysicalBasis_of_isometry
        physicalInclusion physicalInclusion_isometry
        MPOTensor.NonCartesianActiveSectorCandidate.tensor_isInjective
        tensor_physicalSupportProj_eq_one hEmbedded
  exact MPOTensor.NonCartesianActiveSectorCandidate.not_exists_neighboringTraceFactorization
    hSource

/-- There is a five-letter ambient tensor satisfying the complete standing
simple-biCF, MPDO, SAL, and literal physical-trace ZCL conditions used in
CPSV16, Appendix C.2.  Its displayed BNT has one obstruction block with strict
coefficient bound `0 < ‖mu‖ < 1` and one terminal block with coefficient
exactly one, which is the single global unit-weight witness.  Both displayed
representatives are normal, and their simultaneous word span is top at length
one.

The simultaneous word span behind biCF and the local orthogonal-sum entropy
argument are proved in TNLean.  The displayed canonical assembly, global
normalization, and literal ZCL condition are the source hypotheses at
CPSV16, lines 224--246, 623--630, 735--739, 811--822, and 1628--1782. -/
theorem exists_ambient_simpleBiCF_neighboringTraceObstruction :
    ∃ (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0),
      0 < ‖mu‖ ∧ ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPTensor.IsLeftCanonical B ∧
      MPTensor.IsNormalTensor B ∧
      MPTensor.GaugeEquiv embeddedObstruction (mu • B) ∧
      let S := sectors mu B hmu
      let K := ambient mu B hmu
      IsMPDO K ∧
      (∀ N, 0 < N → 0 < Matrix.trace (mpo K N)) ∧
      IsSAL K ∧
      IsSimpleCanonicalForm K ∧
      IsSimple K ∧
      MPSTensor.IsLeftCanonicalBNTPresentation S ∧
      MPSTensor.WordTupleSpanTop S.basis 1 ∧
      (∀ j, MPTensor.IsNormalTensor (S.basis j)) ∧
      K = S.toTensor ∧
      (∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
        S.weight j q = S.weight j q') ∧
      S.basisCount = 2 ∧
      S.copies 0 = 1 ∧
      S.copies (Fin.succ 0) = 1 ∧
      S.basisDim 0 = 2 ∧
      S.basisDim (Fin.succ 0) = 1 ∧
      S.basis 0 = B ∧
      S.basis (Fin.succ 0) = terminalBlock ∧
      S.weight 0 0 = mu ∧
      S.weight (Fin.succ 0) 0 = 1 ∧
      physicalSupportProj embeddedObstruction = obstructionPhysicalSupport ∧
      physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
      obstructionPhysicalSupport * terminalPhysicalSupport = 0 ∧
      terminalPhysicalSupport * obstructionPhysicalSupport = 0 ∧
      obstructionPhysicalSupport + terminalPhysicalSupport = 1 ∧
      physTraceTransfer K * physTraceTransfer K = physTraceTransfer K := by
  obtain ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hGauge,
    hBasisCount, hCopiesZero, hCopiesOne, hDimZero, hDimOne,
    hBasisZero, hBasisOne, hWeightZero, hWeightOne, hBSupport,
    _hTerminalSupport, _hSupportZeroTerminal, _hTerminalZeroSupport,
    _hSupportSum, hBNT⟩ := exists_obstruction_terminal_twoBlock_BNT_witness
  have hmuNormPos : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  refine ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, ?_⟩
  dsimp only
  exact ⟨ambient_isMPDO mu B hmu hGauge,
    fun N hN ↦ trace_mpo_ambient_pos mu B hmu hGauge hN,
    ambient_isSAL mu B hmu hGauge,
    ambient_isSimpleCanonicalForm mu B hmu hGauge hBNT,
    ambient_isSimple mu B hmu hGauge hBNT,
    hBNT, sectors_wordTupleSpanTop_one mu B hmu hBInj hBSupport,
    sectors_basis_isNormalTensor mu B hmu hBNormal,
    rfl,
    sectors_weight_copy_independent mu B hmu,
    hBasisCount, hCopiesZero, hCopiesOne, hDimZero, hDimOne,
    hBasisZero, hBasisOne, hWeightZero, hWeightOne,
    embeddedObstruction_physicalSupportProj,
    terminalBlock_physicalSupportProj,
    obstructionPhysicalSupport_mul_terminalPhysicalSupport,
    terminalPhysicalSupport_mul_obstructionPhysicalSupport,
    obstructionPhysicalSupport_add_terminalPhysicalSupport,
    ambient_literal_physTrace_ZCL mu B hmu hGauge⟩

/-- The representativewise neighboring-trace conclusion used in the printed
CPSV16 Theorem 4.9 implication `(ii) ⇒ (iv)` is false under its standing
hypotheses.  The witness is an MPDO with positive normalization at every
positive length, SAL, literal physical-trace ZCL, and the displayed simple
biCF canonical form.  Every displayed representative is normal, and their
simultaneous word span is top at literal length one.  Its BNT coefficients have
the strict values `0 < ‖mu‖ < 1` and `1`, so the terminal block supplies exactly
the global unit-weight witness required at line 246.  Nevertheless, the first
common-weight-absorbed representative admits no normalized rank-one
neighboring-trace factorization.

The finite simultaneous-span, local orthogonal-sum entropy, virtual-gauge, and
isometric-embedding descent arguments are proved in TNLean.  The counterexample
addresses the source assertion and proof path at
CPSV16, Theorem 4.9(iv), lines 864--889, and Appendix C.2, lines 1628--1782.
See
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>. -/
theorem printed_theorem49_ii_to_iv_is_false :
    ∃ (mu : ℂ) (B : MPOTensor 5 2) (hmu : mu ≠ 0),
      0 < ‖mu‖ ∧ ‖mu‖ < 1 ∧
      Kraus.IsInjective B ∧
      MPTensor.IsLeftCanonical B ∧
      MPTensor.IsNormalTensor B ∧
      MPTensor.GaugeEquiv embeddedObstruction (mu • B) ∧
      let S := sectors mu B hmu
      let K := ambient mu B hmu
      (IsMPDO K ∧
        (∀ N, 0 < N → 0 < Matrix.trace (mpo K N)) ∧
        IsSAL K ∧
        IsSimpleCanonicalForm K ∧
        IsSimple K ∧
        MPSTensor.IsLeftCanonicalBNTPresentation S ∧
        MPSTensor.WordTupleSpanTop S.basis 1 ∧
        (∀ j, MPTensor.IsNormalTensor (S.basis j)) ∧
        K = S.toTensor ∧
        (∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q') ∧
        S.basisCount = 2 ∧
        S.copies 0 = 1 ∧
        S.copies (Fin.succ 0) = 1 ∧
        S.basisDim 0 = 2 ∧
        S.basisDim (Fin.succ 0) = 1 ∧
        S.basis 0 = B ∧
        S.basis (Fin.succ 0) = terminalBlock ∧
        S.weight 0 0 = mu ∧
        S.weight (Fin.succ 0) 0 = 1 ∧
        physicalSupportProj embeddedObstruction = obstructionPhysicalSupport ∧
        physicalSupportProj terminalBlock = terminalPhysicalSupport ∧
        obstructionPhysicalSupport * terminalPhysicalSupport = 0 ∧
        terminalPhysicalSupport * obstructionPhysicalSupport = 0 ∧
        obstructionPhysicalSupport + terminalPhysicalSupport = 1 ∧
        physTraceTransfer K * physTraceTransfer K = physTraceTransfer K) ∧
      ¬ ∃ F : PhysicalSectorFactorization
          (S.commonWeightAbsorbedBasis (sectors_weight_copy_independent mu B hmu) 0),
        Nonempty F.NeighboringTraceFactorization := by
  obtain ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, hStanding⟩ := exists_ambient_simpleBiCF_neighboringTraceObstruction
  refine ⟨mu, B, hmu, hmuNormPos, hmuNorm, hBInj, hBLeft, hBNormal,
    hGauge, ?_⟩
  dsimp only at hStanding ⊢
  exact ⟨hStanding,
    firstCommonWeightAbsorbed_not_exists_neighboringTraceFactorization
      mu B hmu hGauge⟩

end MPOTensor.NeighboringTraceObstructionAmbientCounterexample
